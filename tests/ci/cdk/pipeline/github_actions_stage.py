import typing

from aws_cdk import (
    Stage,
    Environment,
    Stack,
    pipelines,
)
from cdk.aws_lc_codebuild_fleets import AwsLcCodeBuildFleets
from cdk.aws_lc_devicefarm_ci_stack import AwsLcDeviceFarmCiStack
from cdk.aws_lc_github_actions_stack import AwsLcGitHubActionsStack
from cdk.aws_lc_github_oidc_stack import AwsLcGitHubOidcStack
from constructs import Construct


class GitHubActionsStage(Stage):
    """Define a stack of IAM role to allow cross-account deployment"""

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

        self.codebuild_fleets = AwsLcCodeBuildFleets(self, "aws-lc-codebuild-fleets",
                                                     env=deploy_environment,
                                                     stack_name="aws-lc-codebuild-fleets", **kwargs)

        self.devicefarm = AwsLcDeviceFarmCiStack(self, "aws-lc-ci-devicefarm",
                                                 env=deploy_environment,
                                                 stack_name="aws-lc-ci-devicefarm", **kwargs)

        self.odic_stack = AwsLcGitHubOidcStack(
            self, "aws-lc-github-oidc", env=deploy_environment, devicefarm=self.devicefarm.props, **kwargs)

        self.actions_stack = AwsLcGitHubActionsStack(
            self,
            "aws-lc-ci-github-actions",
            env=deploy_environment,
            ignore_failure=False,
            stack_name="aws-lc-ci-github-actions",
            **kwargs
        )

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]

    def add_stage_to_wave(self, wave: pipelines.Wave):
        wave.add_stage(self)
