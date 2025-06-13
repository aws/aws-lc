import typing

from aws_cdk import (
    Stage,
    Environment,
    Stack,
    aws_iam as iam,
)
from constructs import Construct


class SetupStage(Stage):
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

        self.setup_stack = SetupStack(
            self,
            "aws-lc-ci-pipeline-setup",
            pipeline_environment=pipeline_environment,
            deploy_environment=deploy_environment,
            stack_name="aws-lc-ci-pipeline-setup",
            **kwargs,
        )

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]


class SetupStack(Stack):
    """Define a stack of IAM role to allow cross-account deployment"""

    def __init__(
        self,
        scope: Construct,
        id: str,
        pipeline_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        deploy_environment: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs,
    ) -> None:
        super().__init__(scope, id, env=deploy_environment, **kwargs)

        cross_account_role = iam.Role(
            self,
            "CrossAccountBuildRole",
            role_name="CrossAccountBuildRole",
            assumed_by=iam.ArnPrincipal(
                f"arn:aws:iam::{pipeline_environment.account}:role/CrossAccountPipelineRole"
            ),
        )

        # Grant access to all CodeBuild projects
        cross_account_role.add_to_policy(
            iam.PolicyStatement(
                effect=iam.Effect.ALLOW,
                actions=["codebuild:*"],
                resources=[
                    f"arn:aws:codebuild:{deploy_environment.region}:{deploy_environment.account}:project/aws-lc-*"
                ],
            )
        )

        cross_account_role.add_to_policy(
            iam.PolicyStatement(
                effect=iam.Effect.ALLOW,
                actions=[
                    "cloudformation:DescribeChangeSet",
                    "cloudformation:DescribeStacks",
                    "ec2:DescribeInstances",
                    "ssm:DescribeInstanceInformation",
                    "ssm:SendCommand",
                    "ssm:ListCommands",
                    "ecr:DescribeImages",
                    "ecr:BatchGetImage",
                    "ecr:PutImage",
                    "ecr:BatchDeleteImage",
                ],
                resources=["*"],
            )
        )
