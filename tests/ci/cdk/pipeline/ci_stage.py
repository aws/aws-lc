# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import builtins
import re
import typing

from aws_cdk import Stage, Environment, Duration, pipelines, aws_iam as iam, Stack
from constructs import Construct

from cdk.aws_lc_analytics_stack import AwsLcGitHubAnalyticsStack
from cdk.aws_lc_android_ci_stack import AwsLcAndroidCIStack
from cdk.aws_lc_ec2_test_framework_ci_stack import AwsLcEC2TestingCIStack
from cdk.aws_lc_github_ci_stack import AwsLcGitHubCIStack
from cdk.aws_lc_github_fuzz_ci_stack import AwsLcGitHubFuzzCIStack
from pipeline.codebuild_batch_step import CodeBuildBatchStep

class CiStage(Stage):
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

        self.build_options = []

        # Define CodeBuild Batch job for testing code.
        x86_build_spec_file = "cdk/codebuild/github_ci_linux_x86_omnibus.yaml"
        self.ci_linux_x86_stack = AwsLcGitHubCIStack(
            self,
            "aws-lc-ci-linux-x86",
            x86_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-linux-x86",
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-linux-x86",
            ignore_failure=False,
        ))

        arm_stack_name = "aws-lc-ci-linux-arm"
        arm_build_spec_file = "cdk/codebuild/github_ci_linux_arm_omnibus.yaml"
        self.ci_linux_aarch_stack = AwsLcGitHubCIStack(
            self,
            arm_stack_name,
            arm_build_spec_file,
            env=deploy_environment,
            stack_name=arm_stack_name,
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-linux-arm",
            ignore_failure=False,
        ))

        integration_build_spec_file = "cdk/codebuild/github_ci_integration_omnibus.yaml"
        self.ci_integration_stack = AwsLcGitHubCIStack(
            self,
            "aws-lc-ci-integration",
            integration_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-integration",
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-integration",
            ignore_failure=True,
        ))

        fuzz_build_spec_file = "cdk/codebuild/github_ci_fuzzing_omnibus.yaml"
        self.ci_fuzzing_stack = AwsLcGitHubFuzzCIStack(
            self,
            "aws-lc-ci-fuzzing",
            fuzz_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-fuzzing",
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-fuzzing",
            ignore_failure=False,
        ))

        analytics_build_spec_file = "cdk/codebuild/github_ci_analytics_omnibus.yaml"
        self.ci_analytics_stack = AwsLcGitHubAnalyticsStack(
            self,
            "aws-lc-ci-analytics",
            analytics_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-analytics",
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-analytics",
            ignore_failure=True,
        ))

        # bm_framework_build_spec_file = "cdk/codebuild/bm_framework_omnibus.yaml"
        # BmFrameworkStack(app, "aws-lc-ci-bm-framework", bm_framework_build_spec_file, env=env)
        ec2_test_framework_build_spec_file = (
            "cdk/codebuild/ec2_test_framework_omnibus.yaml"
        )
        self.ci_ec2_test_framework_stack = AwsLcEC2TestingCIStack(
            self,
            "aws-lc-ci-ec2-test-framework",
            ec2_test_framework_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-ec2-test-framework",
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-ec2-test-framework",
            ignore_failure=True,
        ))

        android_build_spec_file = "cdk/codebuild/github_ci_android_omnibus.yaml"
        self.ci_android_stack = AwsLcAndroidCIStack(
            self,
            "aws-lc-ci-devicefarm-android",
            android_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-devicefarm-android",
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-devicefarm-android",
            ignore_failure=False,
        ))

        win_x86_build_spec_file = "cdk/codebuild/github_ci_windows_x86_omnibus.yaml"
        self.ci_windows_x86_stack = AwsLcGitHubCIStack(
            self,
            "aws-lc-ci-windows-x86",
            win_x86_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-windows-x86",
        )
        self.build_options.append(BatchBuildOptions(
            project="aws-lc-ci-windows-x86",
            ignore_failure=False,
        ))

    @property
    def stacks(self) -> typing.List[Stack]:
        return [child for child in self.node.children if isinstance(child, Stack)]

    def add_stage_to_pipeline(
            self,
            pipeline: pipelines.CodePipeline,
            input: pipelines.FileSet,
            role: iam.Role,
            max_retry: typing.Optional[int] = 2,
            env: typing.Optional[typing.Mapping[str, str]] = None,
    ):
        stack_names = [stack.stack_name for stack in self.stacks]

        env = env or {}

        prebuild_check_step = pipelines.CodeBuildStep(
            "PrebuildCheck",
            input=input,
            commands=[
                "cd tests/ci/cdk/pipeline/scripts",
                "chmod +x check_trigger_conditions.sh",
                "trigger_conditions=$(./check_trigger_conditions.sh --build-type ci --stacks \"${STACKS}\")",
                "export NEED_REBUILD=$(echo $trigger_conditions | sed -n 's/.*\(NEED_REBUILD=[0-9]*\).*/\\1/p' | cut -d'=' -f2 )"
            ],
            env={
                **env,
                "STACKS": " ".join(stack_names),
            },
            role=role,
            timeout=Duration.minutes(60)
        )

        batch_build_jobs = {
            "build-list": [
                {
                    "identifier": options.identifier,
                    "ignore-failure": options.ignore_failure,
                    "env": {
                        "variables": {
                            "PROJECT": options.project,
                            "TIMEOUT": str(max_retry * options.timeout),
                            **options.env,
                        }
                    }
                }
                for options in self.build_options
            ]
        }

        ci_run_step = CodeBuildBatchStep(
            f"BuildStep",
            action_name="StartWait",
            input=input,
            commands=[
                "cd tests/ci/cdk/pipeline/scripts",
                "chmod +x build_target.sh",
                "./build_target.sh --build-type ci --project ${PROJECT} --max-retry ${MAX_RETRY} --timeout ${TIMEOUT}"
            ],
            role=role,
            timeout=300,
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
            post=[
                prebuild_check_step,
                ci_run_step
            ]
        )

class BatchBuildOptions:
    def __init__(
            self,
            project: str,
            identifier: str = None,
            ignore_failure: bool = False,
            timeout: int = 120,
            env: typing.Optional[typing.Mapping[str, str]] = None
    ):
        self.project = project
        self.identifier = identifier or re.sub(r'[^a-zA-Z0-9]', '_', project)
        self.ignore_failure = ignore_failure
        self.timeout = timeout
        self.env = env or {}