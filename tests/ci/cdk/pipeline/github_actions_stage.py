import typing

from aws_cdk import (
    Stage,
    Environment,
    Stack,
    pipelines,
)
from cdk.aws_lc_github_actions_stack import AwsLcGitHubActionsStack
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

        AwsLcGitHubActionsStack(
            self,
            "aws-lc-ci-github-actions",
            env=deploy_environment,
            ignore_failure=False,
            stack_name="aws-lc-ci-github-actions",
        )

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]
    
    def add_stage_to_wave(self, wave: pipelines.Wave):
        wave.add_stage(self)
