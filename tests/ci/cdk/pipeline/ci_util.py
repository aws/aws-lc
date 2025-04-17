import typing

from aws_cdk import Environment
from constructs import Construct

from cdk.aws_lc_analytics_stack import AwsLcGitHubAnalyticsStack
from cdk.aws_lc_android_ci_stack import AwsLcAndroidCIStack
from cdk.aws_lc_ec2_test_framework_ci_stack import AwsLcEC2TestingCIStack
from cdk.aws_lc_github_ci_stack import AwsLcGitHubCIStack
from cdk.aws_lc_github_fuzz_ci_stack import AwsLcGitHubFuzzCIStack


# Define CodeBuild Batch jobs for testing code.
def add_ci_stacks(
    scope: Construct,
    env: typing.Union[Environment, typing.Dict[str, typing.Any]],
):
    # define customized settings to run CodeBuild jobs from CodePipeline
    build_options = []

    x86_build_spec_file = "cdk/codebuild/github_ci_linux_x86_omnibus.yaml"
    AwsLcGitHubCIStack(
        scope,
        "aws-lc-ci-linux-x86",
        x86_build_spec_file,
        env=env,
        ignore_failure=False,
        stack_name="aws-lc-ci-linux-x86",
    )

    arm_build_spec_file = "cdk/codebuild/github_ci_linux_arm_omnibus.yaml"
    AwsLcGitHubCIStack(
        scope,
        "aws-lc-ci-linux-arm",
        arm_build_spec_file,
        env=env,
        ignore_failure=False,
        stack_name="aws-lc-ci-linux-arm",
    )

    integration_build_spec_file = "cdk/codebuild/github_ci_integration_omnibus.yaml"
    AwsLcGitHubCIStack(
        scope,
        "aws-lc-ci-integration",
        integration_build_spec_file,
        env=env,
        ignore_failure=True,
        stack_name="aws-lc-ci-integration",
    )

    fuzz_build_spec_file = "cdk/codebuild/github_ci_fuzzing_omnibus.yaml"
    AwsLcGitHubFuzzCIStack(
        scope,
        "aws-lc-ci-fuzzing",
        fuzz_build_spec_file,
        env=env,
        ignore_failure=False,
        stack_name="aws-lc-ci-fuzzing",
    )

    analytics_build_spec_file = "cdk/codebuild/github_ci_analytics_omnibus.yaml"
    AwsLcGitHubAnalyticsStack(
        scope,
        "aws-lc-ci-analytics",
        analytics_build_spec_file,
        env=env,
        ignore_failure=True,
        stack_name="aws-lc-ci-analytics",
    )

    ec2_test_framework_build_spec_file = "cdk/codebuild/ec2_test_framework_omnibus.yaml"
    AwsLcEC2TestingCIStack(
        scope,
        "aws-lc-ci-ec2-test-framework",
        ec2_test_framework_build_spec_file,
        env=env,
        ignore_failure=True,
        stack_name="aws-lc-ci-ec2-test-framework",
    )

    android_build_spec_file = "cdk/codebuild/github_ci_android_omnibus.yaml"
    AwsLcAndroidCIStack(
        scope,
        "aws-lc-ci-devicefarm-android",
        android_build_spec_file,
        env=env,
        ignore_failure=False,
        stack_name="aws-lc-ci-devicefarm-android",
    )

    win_x86_build_spec_file = "cdk/codebuild/github_ci_windows_x86_omnibus.yaml"
    AwsLcGitHubCIStack(
        scope,
        "aws-lc-ci-windows-x86",
        win_x86_build_spec_file,
        env=env,
        ignore_failure=False,
        stack_name="aws-lc-ci-windows-x86",
    )
