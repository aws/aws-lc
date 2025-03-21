from aws_cdk import Stage, aws_codebuild as codebuild, Environment, Stack, aws_iam as iam
from constructs import Construct

from cdk.ecr_stack import EcrStack
from cdk.linux_docker_image_batch_build_stack import LinuxDockerImageBatchBuildStack
from cdk.windows_docker_image_build_stack import WindowsDockerImageBuildStack
from util.metadata import LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO, WINDOWS_X86_ECR_REPO, AWS_ACCOUNT, AWS_REGION, \
    PIPELINE_ACCOUNT


class SetupStage(Stage):
    def __init__(
            self,
            scope: Construct,
            id,
            # pipeline_role_arn: str,
            **kwargs
    ):
        super().__init__(
            scope,
            id,
            **kwargs,
        )

        env=Environment(account=AWS_ACCOUNT, region=AWS_REGION)

        self.setup_stack = SetupStack(
            self,
            "aws-lc-ci-pipeline-setup",
            env=env,
            # pipeline_role_arn=pipeline_role_arn,
            stack_name="aws-lc-ci-pipeline-setup",
        )

    @property
    def stacks(self):
        return [child for child in self.node.children if isinstance(child, Stack)]

class SetupStack(Stack):
    def __init__(
            self,
            scope: Construct,
            id: str,
            # pipeline_role_arn: str,
            **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        cross_account_role = iam.Role(
            self,
            'CrossAccountCodeBuildRole',
            role_name='CrossAccountCodeBuildRole',
            assumed_by=iam.ArnPrincipal(f'arn:aws:iam::{PIPELINE_ACCOUNT}:role/CrossAccountCodeBuildRole'), #TODO: add a conditional to exclude this in dev env
        )

        # Grant access to all CodeBuild projects
        cross_account_role.add_to_policy(iam.PolicyStatement(
            effect=iam.Effect.ALLOW,
            actions=[
                'codebuild:StartBuild',
                'codebuild:StartBuildBatch',
                'codebuild:BatchGetBuilds',
                'codebuild:StopBuild',
                'codebuild:ListProjects',
                'codebuild:BatchGetProjects',
                'codebuild:BatchGetBuildBatches',
                'codebuild:StopBuildBatch',
                'codebuild:RetryBuild',
                'codebuild:RetryBuildBatch'
            ],
            resources=[f'arn:aws:codebuild:{AWS_REGION}:{AWS_ACCOUNT}:project/aws-lc-*']
        ))

        cross_account_role.add_to_policy(iam.PolicyStatement(
            effect=iam.Effect.ALLOW,
            actions=[
                'cloudformation:DescribeChangeSet',
                'cloudformation:DescribeStacks'
            ],
            resources=['*']
        ))

        cross_account_role.add_to_policy(iam.PolicyStatement(
            effect=iam.Effect.ALLOW,
            actions=[
                'ec2:DescribeInstances',
                'ssm:DescribeInstanceInformation',
                'ssm:SendCommand',
                'ssm:ListCommands'
            ],
            resources=['*']
        ))