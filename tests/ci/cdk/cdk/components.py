import pathlib

from aws_cdk import aws_codebuild as codebuild, aws_lambda as lambda_, aws_ecr as ecr, aws_secretsmanager as sm, \
    aws_events as events, aws_events_targets as events_targets, aws_iam as iam, Duration

from constructs import Construct
from util.metadata import AWS_REGION, AWS_ACCOUNT, GITHUB_REPO_OWNER, GITHUB_TOKEN_SECRET_NAME


class PruneStaleGitHubBuilds(Construct):
    def __init__(self, scope: Construct, id: str, *, project: codebuild.IProject, ec2_permissions: bool) -> None:
        super().__init__(scope, id)

        github_token_secret = sm.Secret.from_secret_name_v2(scope=self,
                                                            id="{}-GitHubToken".format(id),
                                                            secret_name=GITHUB_TOKEN_SECRET_NAME)

        lambda_function = lambda_.Function(scope=self,
                                           id="LambdaFunction",
                                           code=lambda_.Code.from_asset_image(
                                               directory=str(pathlib.Path().joinpath("..", "lambda")),
                                               target="purge-stale-builds"),
                                           handler=lambda_.Handler.FROM_IMAGE,
                                           runtime=lambda_.Runtime.FROM_IMAGE,
                                           environment={
                                               "CODEBUILD_PROJECT_NAME": project.project_name,
                                               "GITHUB_REPO_OWNER": GITHUB_REPO_OWNER,
                                               "GITHUB_TOKEN_SECRET_NAME": github_token_secret.secret_name,
                                               "RUST_LOG": "info",
                                           })

        github_token_secret.grant_read(lambda_function)

        lambda_function.add_to_role_policy(
            iam.PolicyStatement(effect=iam.Effect.ALLOW,
                                actions=[
                                    "codebuild:BatchGetBuildBatches",
                                    "codebuild:ListBuildBatchesForProject",
                                    "codebuild:StopBuildBatch"
                                ],
                                resources=[project.project_arn]))

        if ec2_permissions:
            lambda_function.add_to_role_policy(
                iam.PolicyStatement(effect=iam.Effect.ALLOW,
                                actions=[
                                    "ec2:TerminateInstances",
                                ],
                                resources=["arn:aws:ec2:{}:{}:instance/*".format(AWS_REGION, AWS_ACCOUNT)],
                                conditions={
                                    "StringEquals": {
                                        "ec2:ResourceTag/ec2-framework-host": "ec2-framework-host"
                                    }
                                }))
            # ec2:Describe* API actions do not support resource-level permissions.
            lambda_function.add_to_role_policy(
                iam.PolicyStatement(effect=iam.Effect.ALLOW,
                                    actions=[
                                        "ec2:DescribeInstances",
                                    ],
                                    resources=["*"]))


        events.Rule(scope=self, id="PurgeEventRule",
                    description="Purge stale GitHub codebuild jobs and ec2 instances (once per minute)",
                    enabled=True,
                    schedule=events.Schedule.rate(Duration.minutes(1)),
                    targets=[events_targets.LambdaFunction(handler=lambda_function)])
