# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import Stage, Environment, Stack, Duration, aws_iam as iam, pipelines
from aws_cdk.pipelines import CodeBuildStep
from constructs import Construct

from cdk.ecr_stack import EcrStack
from cdk.linux_docker_image_batch_build_stack import LinuxDockerImageBatchBuildStack
from pipeline.deploy_util import DeployEnvironmentType
from util.metadata import LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO, AWS_ACCOUNT, AWS_REGION


class LinuxDockerImageBuildStage(Stage):
    def __init__(
            self,
            scope: Construct,
            id,
            **kwargs
    ):
        super().__init__(
            scope,
            id,
            **kwargs,
        )

        env=Environment(account=AWS_ACCOUNT, region=AWS_REGION)

        # Define AWS ECR stacks.
        # ECR holds the docker images, which are pre-built to accelerate the code builds/tests of git pull requests.
        self.ecr_linux_x86_stack = EcrStack(
            self,
            "aws-lc-ecr-linux-x86",
            LINUX_X86_ECR_REPO,
            env=env,
            stack_name="aws-lc-ecr-linux-x86"
        )
        self.ecr_linux_aarch_stack = EcrStack(
            self,
            "aws-lc-ecr-linux-aarch",
            LINUX_AARCH_ECR_REPO,
            env=env,
            stack_name="aws-lc-ecr-linux-aarch"
        )

        # Define CodeBuild Batch job for building Docker images.
        self.linux_docker_build_stack = LinuxDockerImageBatchBuildStack(
            self,
            "aws-lc-docker-image-build-linux",
            env=env,
            stack_name="aws-lc-docker-image-build-linux"
        )
        self.linux_docker_build_stack.add_dependency(self.ecr_linux_x86_stack)
        self.linux_docker_build_stack.add_dependency(self.ecr_linux_aarch_stack)

        self.ecr_repo_names = [LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO]
        self.need_rebuild = None

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]

    def add_stage_to_wave(
            self,
            wave: pipelines.Wave,
            input: pipelines.FileSet,
            role: iam.Role,
            deploy_environment: str,
            max_retry: int=2,
            additional_stacks: list[Stack]=[],
            env={},
    ):
        stacks = self.stacks + additional_stacks
        stack_names = [stack.stack_name for stack in stacks]

        docker_build_step = CodeBuildStep(
            "StartWait",
            input=input,
            commands=[
                "cd tests/ci/cdk/pipeline/scripts",
                "chmod +x trigger_condition_check.sh build_target.sh",
                "trigger_conditions=$(./trigger_condition_check.sh --build-type docker --platform linux --stacks \"${STACKS}\")",
                "export NEED_REBUILD=$(echo $trigger_conditions | sed -n -e 's/.*\(NEED_REBUILD=[0-9]*\).*/\\1/p' | cut -d'=' -f2 )",
                "./build_target.sh --build-type docker --platform linux --max-retry ${MAX_RETRY} --timeout ${TIMEOUT}"
            ],
            env={
                **env,
                "STACKS": " ".join(stack_names),
                "MAX_RETRY": str(max_retry),
                "TIMEOUT": str(180), # 3 hours
            },
            role=role,
            timeout=Duration.minutes(180)
            # project_name=f"{self.stage_name}-StartWait"
        )

        wave.add_stage(
            self,
            post=[
                # DockerBuildStep(
                #     f"{deploy_environment}-BuildStep",
                #     name_prefix=self.stage_name,
                #     input=input,
                #     stacks=[stack.stack_name for stack in stacks],
                #     platform="linux",
                #     max_retry=max_retry,
                #     env=env,
                #     role=role
                # )
                docker_build_step
            ]
        )

        self.need_rebuild = docker_build_step.exported_variable("NEED_REBUILD")

