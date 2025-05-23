# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import builtins
import re
import typing

from aws_cdk import (
    Stage,
    Environment,
    Duration,
    pipelines,
    aws_iam as iam,
    aws_codebuild as codebuild,
)
from constructs import Construct

from cdk.aws_lc_base_ci_stack import AwsLcBaseCiStack
from pipeline.ci_util import add_ci_stacks
from pipeline.codebuild_batch_step import CodeBuildBatchStep
from util.metadata import (
    PRE_PROD_ACCOUNT,
    GITHUB_TOKEN_SECRET_NAME,
    STAGING_GITHUB_REPO_OWNER,
    STAGING_GITHUB_REPO_NAME,
)


class CiStage(Stage):
    def __init__(
        self,
        scope: Construct,
        id: str,
        pipeline_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        deploy_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs,
    ):
        super().__init__(
            scope,
            id,
            env=pipeline_environment,
            **kwargs,
        )

        # Add CodeBuild Batch job for testing code.
        add_ci_stacks(self, env=deploy_environment)

    @property
    def stacks(self) -> typing.List[AwsLcBaseCiStack]:
        return [
            child for child in self.node.children if isinstance(child, AwsLcBaseCiStack)
        ]

    def add_stage_to_pipeline(
        self,
        pipeline: pipelines.CodePipeline,
        input: pipelines.FileSet,
        role: iam.Role,
        max_retry: typing.Optional[int] = 2,
        env: typing.Optional[typing.Mapping[str, str]] = None,
    ):
        stack_names = [stack.stack_name for stack in self.stacks]

        private_repo_sync_step = None

        if self.stacks[0].account == PRE_PROD_ACCOUNT:
            private_repo_sync_step = pipelines.CodeBuildStep(
                "PrivateRepoSync",
                build_environment=codebuild.BuildEnvironment(
                    environment_variables={
                        "GITHUB_PAT": codebuild.BuildEnvironmentVariable(
                            type=codebuild.BuildEnvironmentVariableType.SECRETS_MANAGER,
                            value=GITHUB_TOKEN_SECRET_NAME,
                        ),
                    }
                ),
                commands=[
                    "env",
                    'curl -H "Authorization: token ${GITHUB_PAT}" https://api.github.com/user',
                    "git clone https://${GITHUB_PAT}@github.com/${STAGING_GITHUB_REPO_OWNER}/${STAGING_GITHUB_REPO_NAME}.git",
                    "git remote add upstream https://github.com/aws/aws-lc.git",
                    "git fetch upstream",
                    "git checkout main",
                    "git merge --ff-only upstream/main",
                    "git remote set-url origin https://${GITHUB_PAT}@github.com/${STAGING_GITHUB_REPO_OWNER}/${STAGING_GITHUB_REPO_NAME}.git",
                    "git push origin main",
                ],
                env={
                    "STAGING_GITHUB_REPO_OWNER": STAGING_GITHUB_REPO_OWNER,
                    "STAGING_GITHUB_REPO_NAME": STAGING_GITHUB_REPO_NAME,
                },
                role=role,
                timeout=Duration.minutes(60),
            )

        env = env or {}

        prebuild_check_step = pipelines.CodeBuildStep(
            "PrebuildCheck",
            input=input,
            commands=[
                "cd tests/ci/cdk/pipeline/scripts",
                'trigger_conditions=$(./check_trigger_conditions.sh --build-type ci --stacks "${STACKS}")',
                "export NEED_REBUILD=$(echo $trigger_conditions | sed -n 's/.*\(NEED_REBUILD=[0-9]*\).*/\\1/p' | cut -d'=' -f2 )",
            ],
            env={
                **env,
                "STACKS": " ".join(stack_names),
            },
            role=role,
            timeout=Duration.minutes(60),
        )

        batch_timeout = max([stack.timeout for stack in self.stacks]) * (max_retry + 1)
        batch_build_jobs = {
            "build-list": [
                {
                    "identifier": re.sub(r"[^a-zA-Z0-9]", "_", stack.stack_name),
                    "ignore-failure": stack.ignore_failure,
                    "env": {
                        "variables": {
                            "PROJECT": stack.stack_name,
                            "TIMEOUT": batch_timeout,
                        }
                    },
                }
                for stack in self.stacks
            ]
        }

        ci_run_step = CodeBuildBatchStep(
            f"BuildStep",
            action_name="StartWait",
            input=input,
            commands=[
                "cd tests/ci/cdk/pipeline/scripts",
                "./build_target.sh --build-type ci --project ${PROJECT} --max-retry ${MAX_RETRY} --timeout ${TIMEOUT}",
            ],
            role=role,
            timeout=batch_timeout,
            project_description=f"Pipeline step AwsLcCiPipeline/{self.stage_name}/StartWait",
            partial_batch_build_spec=batch_build_jobs,
            env={
                **env,
                "MAX_RETRY": max_retry,
                "NEED_REBUILD": prebuild_check_step.exported_variable("NEED_REBUILD"),
            },
        )

        ci_run_step.add_step_dependency(prebuild_check_step)

        pipeline.add_stage(
            self,
            pre=[private_repo_sync_step] if private_repo_sync_step else None,
            post=[prebuild_check_step, ci_run_step],
        )
