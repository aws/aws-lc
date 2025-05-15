# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import Stage, Environment, Stack, Duration, aws_iam as iam, pipelines
from aws_cdk.pipelines import CodeBuildStep
from constructs import Construct

from cdk.ecr_stack import EcrStack
from cdk.windows_docker_image_build_stack import WindowsDockerImageBuildStack
from util.metadata import (
    WINDOWS_X86_ECR_REPO,
    WIN_EC2_TAG_KEY,
    WIN_EC2_TAG_VALUE,
    SSM_DOCUMENT_NAME,
)


class WindowsDockerImageBuildStage(Stage):
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

        self.ecr_windows_x86 = EcrStack(
            self,
            "aws-lc-ecr-windows-x86",
            WINDOWS_X86_ECR_REPO,
            env=deploy_environment,
            stack_name="aws-lc-ecr-windows-x86",
        )

        self.windows_docker_build_stack = WindowsDockerImageBuildStack(
            self,
            "aws-lc-docker-image-build-windows",
            env=deploy_environment,
            stack_name="aws-lc-docker-image-build-windows",
        )
        self.windows_docker_build_stack.add_dependency(self.ecr_windows_x86)

        self.ecr_repo_names = [WINDOWS_X86_ECR_REPO]
        self.s3_bucket_name = self.windows_docker_build_stack.output["s3_bucket_name"]

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
                'trigger_conditions=$(./check_trigger_conditions.sh --build-type docker --platform windows --stacks "${STACKS}")',
                "export NEED_REBUILD=$(echo $trigger_conditions | sed -n -e 's/.*\(NEED_REBUILD=[0-9]*\).*/\\1/p' | cut -d'=' -f2 )",
                "./build_target.sh --build-type docker --platform windows --max-retry ${MAX_RETRY} --timeout ${TIMEOUT}",
            ],
            env={
                **env,
                "STACKS": " ".join(stack_names),
                "ECR_REPOS": " ".join(self.ecr_repo_names),
                "MAX_RETRY": str(max_retry),
                "TIMEOUT": str(timeout),
                "WIN_EC2_TAG_KEY": WIN_EC2_TAG_KEY,
                "WIN_EC2_TAG_VALUE": WIN_EC2_TAG_VALUE,
                "WIN_DOCKER_BUILD_SSM_DOCUMENT": SSM_DOCUMENT_NAME,
                "S3_FOR_WIN_DOCKER_IMG_BUILD": self.s3_bucket_name,
            },
            role=role,
            timeout=Duration.minutes(timeout),
        )

        wave.add_stage(self, post=[docker_build_step])

        self.need_rebuild = docker_build_step.exported_variable("NEED_REBUILD")
