from aws_cdk import Stage, aws_codebuild as codebuild, Environment, Stack, aws_iam as iam
from constructs import Construct

from cdk.ecr_stack import EcrStack
from cdk.linux_docker_image_batch_build_stack import LinuxDockerImageBatchBuildStack
from cdk.windows_docker_image_build_stack import WindowsDockerImageBuildStack
from util.metadata import LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO, WINDOWS_X86_ECR_REPO, PIPELINE_ACCOUNT


class SetupStage(Stage):
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

        self.setup_stack = SetupStack(
            self,
            "aws-lc-ci-pipeline-setup",
            pipeline_environment=pipeline_environment,
            deploy_environment=deploy_environment,
            stack_name="aws-lc-ci-pipeline-setup",
            **kwargs
        )

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]

class SetupStack(Stack):
    def __init__(
            self,
            scope: Construct,
            id: str,
            pipeline_environment,
            deploy_environment,
            **kwargs) -> None:
        super().__init__(scope, id, env=deploy_environment, **kwargs)

        cross_account_role = iam.Role(
            self,
            'CrossAccountCodeBuildRole',
            role_name='CrossAccountCodeBuildRole',
            assumed_by=iam.ArnPrincipal(f'arn:aws:iam::{pipeline_environment.account}:role/CrossAccountPipelineRole'), #TODO: add a conditional to exclude this in dev env
        )

        # Grant access to all CodeBuild projects
        cross_account_role.add_to_policy(iam.PolicyStatement(
            effect=iam.Effect.ALLOW,
            actions=[
                'codebuild:*'
            ],
            resources=[f'arn:aws:codebuild:{deploy_environment.region}:{deploy_environment.account}:project/aws-lc-*']
        ))

        cross_account_role.add_to_policy(iam.PolicyStatement(
            effect=iam.Effect.ALLOW,
            actions=[
                'cloudformation:DescribeChangeSet',
                'cloudformation:DescribeStacks',
                'ec2:DescribeInstances',
                'ssm:DescribeInstanceInformation',
                'ssm:SendCommand',
                'ssm:ListCommands',
                'ecr:DescribeImages',
                'ecr:BatchGetImage',
                'ecr:PutImage',
                'ecr:BatchDeleteImage'
            ],
            resources=['*']
        ))