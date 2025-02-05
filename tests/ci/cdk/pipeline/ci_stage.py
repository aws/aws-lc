# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import Stage, Environment, Duration, pipelines, aws_iam as iam, Stack
from constructs import Construct

from cdk.aws_lc_analytics_stack import AwsLcGitHubAnalyticsStack
from cdk.aws_lc_android_ci_stack import AwsLcAndroidCIStack
from cdk.aws_lc_ec2_test_framework_ci_stack import AwsLcEC2TestingCIStack
from cdk.aws_lc_github_ci_stack import AwsLcGitHubCIStack
from cdk.aws_lc_github_fuzz_ci_stack import AwsLcGitHubFuzzCIStack
from pipeline.codebuild_batch_step import BatchBuildTargetOptions, CodeBuildBatchStep


class CiStage(Stage):
    def __init__(
            self,
            scope: Construct,
            id,
            pipeline_environment,
            deploy_environment,
            **kwargs
    ):
        super().__init__(
            scope,
            id,
            env=pipeline_environment,
            **kwargs,
        )

        self.build_targets = []

        # Define CodeBuild Batch job for testing code.
        x86_build_spec_file = "cdk/codebuild/github_ci_linux_x86_omnibus.yaml"
        self.ci_linux_x86_stack = AwsLcGitHubCIStack(
            self,
            "aws-lc-ci-linux-x86",
            x86_build_spec_file,
            env=deploy_environment,
            stack_name="aws-lc-ci-linux-x86",
        )
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-linux-x86",
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
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-linux-arm",
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
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-integration",
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
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-fuzzing",
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
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-analytics",
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
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-ec2-test-framework",
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
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-devicefarm-android",
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
        self.build_targets.append(BatchBuildTargetOptions(
            target="aws-lc-ci-windows-x86",
            ignore_failure=False,
        ))

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]

    def add_stage_to_pipeline(
            self,
            pipeline: pipelines.CodePipeline,
            input: pipelines.FileSet,
            role: iam.Role,
            max_retry: int=2,
            env={},
    ):
        stack_names = [stack.stack_name for stack in self.stacks]

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
            timeout=Duration.minutes(180)
            # project_name=f"{self.stage_name}-PrebuildCheck"
        )

        batch_build_jobs = {
            "build-list": [
                {
                    "identifier": options.identifier,
                    "ignore-failure": options.ignore_failure,
                    "env": {
                        "variables": {
                            "PROJECT": options.target,
                            "TIMEOUT": options.timeout,
                            **options.env,
                        }
                    }
                }
                for options in self.build_targets
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
            partial_batch_buildspec=batch_build_jobs,
            env={
                **env,
                "MAX_RETRY": max_retry,
                "NEED_REBUILD": prebuild_check_step.exported_variable("NEED_REBUILD")
            },
        )

        ci_run_step.add_step_dependency(prebuild_check_step)

        # pipeline.add_stage(
        #     self,
        #     post=[
        #         CodeBuildRunStep(
        #             f"{self.stage_name}-BuildStep",
        #             name_prefix=self.stage_name,
        #             input=input,
        #             role=role,
        #             stacks=[stack.stack_name for stack in self.stacks],
        #             build_targets=self.build_targets,
        #             max_retry=max_retry,
        #             env=env,
        #         )
        #     ]
        # )

        pipeline.add_stage(
            self,
            post=[
                prebuild_check_step,
                ci_run_step
            ]
        )




