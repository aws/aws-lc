# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import Stage, Environment, Stack, Duration, aws_iam as iam, pipelines
from aws_cdk.pipelines import CodeBuildStep
from constructs import Construct

from cdk.ecr_stack import EcrStack
from cdk.linux_docker_image_batch_build_stack import LinuxDockerImageBatchBuildStack
from util.metadata import LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO


class LinuxDockerImageBuildStage(Stage):
    def __init__(
        self,
        scope: Construct,
        id: str,
        pipeline_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        deploy_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ):
        super().__init__(
            scope,
            id,
            env=pipeline_environment,
            **kwargs,
        )

        # Define AWS ECR stacks.
        # ECR holds the docker images, which are pre-built to accelerate the code builds/tests of git pull requests.
        self.ecr_linux_x86_stack = EcrStack(
            self,
            "aws-lc-ecr-linux-x86",
            LINUX_X86_ECR_REPO,
            env=deploy_environment,
            stack_name="aws-lc-ecr-linux-x86",
        )
        self.ecr_linux_aarch_stack = EcrStack(
            self,
            "aws-lc-ecr-linux-aarch",
            LINUX_AARCH_ECR_REPO,
            env=deploy_environment,
            stack_name="aws-lc-ecr-linux-aarch",
        )

        # Define CodeBuild Batch job for building Docker images.
        self.linux_docker_build_stack = LinuxDockerImageBatchBuildStack(
            self,
            "aws-lc-docker-image-build-linux",
            env=deploy_environment,
            stack_name="aws-lc-docker-image-build-linux",
        )
        self.linux_docker_build_stack.add_dependency(self.ecr_linux_x86_stack)
        self.linux_docker_build_stack.add_dependency(self.ecr_linux_aarch_stack)

        self.ecr_repo_names = [LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO]
        self.need_rebuild = None

    @property
    def stacks(self) -> typing.List[Stack]:
        return [child for child in self.node.children if isinstance(child, Stack)]

    def add_stage_to_wave(
        self,
        wave: pipelines.Wave,
        input: pipelines.FileSet,
        role: iam.Role,
        max_retry: typing.Optional[int] = 2,
        additional_stacks: typing.Optional[typing.List[str]] = None,
        env: typing.Optional[typing.Mapping[str, str]] = None,
    ):
        stacks = self.stacks + (additional_stacks if additional_stacks else [])
        stack_names = [stack.stack_name for stack in stacks]

        env = env if env else {}
        timeout = (max_retry + 1) * 120

        docker_build_step = CodeBuildStep(
            "StartWait",
            input=input,
            commands=[
                "cd tests/ci/cdk/pipeline/scripts",
                './cleanup_orphaned_images.sh --repos "${ECR_REPOS}"',
                'trigger_conditions=$(./check_trigger_conditions.sh --build-type docker --platform linux --stacks "${STACKS}")',
                "export NEED_REBUILD=$(echo $trigger_conditions | sed -n -e 's/.*\(NEED_REBUILD=[0-9]*\).*/\\1/p' | cut -d'=' -f2 )",
                "./build_target.sh --build-type docker --platform linux --max-retry ${MAX_RETRY} --timeout ${TIMEOUT}",
            ],
            env={
                **env,
                "STACKS": " ".join(stack_names),
                "ECR_REPOS": " ".join(self.ecr_repo_names),
                "MAX_RETRY": str(max_retry),
                "TIMEOUT": str(timeout),
            },
            role=role,
            timeout=Duration.minutes(timeout),
        )

        wave.add_stage(self, post=[docker_build_step])

        self.need_rebuild = docker_build_step.exported_variable("NEED_REBUILD")
