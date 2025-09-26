# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Duration,
    Stack,
    aws_codebuild as codebuild,
    aws_iam as iam,
    aws_s3_assets,
    aws_logs as logs,
    Environment,
)
from constructs import Construct

from cdk.aws_lc_base_ci_stack import AwsLcBaseCiStack
from cdk.components import PruneStaleGitHubBuilds
from util.iam_policies import (
    code_build_publish_metrics_in_json,
)
from util.metadata import LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO, WINDOWS_X86_ECR_REPO

class AwsLcGitHubActionsStack(AwsLcBaseCiStack):
    """Define a stack used to execute AWS-LC self-hosted GitHub Actions Runners."""

    def __init__(
        self,
        scope: Construct,
        id: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, timeout=180, **kwargs)

        # Define a IAM role for this stack.
        metrics_policy = iam.PolicyDocument.from_json(
            code_build_publish_metrics_in_json(env)
        )

        inline_policies = {
            "metrics_policy": metrics_policy,
            "ecr": iam.PolicyDocument(
                statements=[
                    iam.PolicyStatement(
                        effect=iam.Effect.ALLOW,
                        actions=[
                            "ecr:GetAuthorizationToken",
                        ],
                        resources=["*"],
                    ),
                    iam.PolicyStatement(
                        effect=iam.Effect.ALLOW,
                        actions=[
                            "ecr:BatchGetImage",
                            "ecr:BatchCheckLayerAvailability",
                            "ecr:GetDownloadUrlForLayer",
                        ],
                        resources=[
                            "arn:aws:ecr:{}:{}:repository/{}"
                                .format(env.region, env.account, repo) for repo in [LINUX_X86_ECR_REPO,
                                                                                    LINUX_AARCH_ECR_REPO,
                                                                                    WINDOWS_X86_ECR_REPO]
                        ],
                    ),
                ],
            )
        }
        role = iam.Role(
            scope=self,
            id="{}-role".format(id),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies=inline_policies,
        )

        logging_options = codebuild.LoggingOptions(
            cloud_watch=codebuild.CloudWatchLoggingOptions(log_group=logs.LogGroup(
                self, id="{}-logs".format(id)))
        )

        # Override base class provided configuration
        self.git_hub_source = codebuild.Source.git_hub(
            owner=self.github_repo_owner,
            repo=self.github_repo_name,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.WORKFLOW_JOB_QUEUED
                ),
            ],
        )

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=self.git_hub_source,
            role=role,
            timeout=Duration.minutes(self.timeout),
            logging=logging_options,
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.SMALL,
                privileged=True,
                build_image=codebuild.LinuxBuildImage.STANDARD_7_0,
                environment_variables={
                    "AWS_ACCOUNT_ID": codebuild.BuildEnvironmentVariable(value=env.account),
                    "AWS_ECR_REPO_LINUX_X86": codebuild.BuildEnvironmentVariable(
                        value="{}.dkr.ecr.{}.amazonaws.com/{}".format(env.account, env.region, LINUX_X86_ECR_REPO)
                    ),
                    "AWS_ECR_REPO_LINUX_AARCH": codebuild.BuildEnvironmentVariable(
                        value="{}.dkr.ecr.{}.amazonaws.com/{}".format(env.account, env.region, LINUX_AARCH_ECR_REPO)
                    ),
                    "AWS_ECR_REPO_WINDOWS_X86": codebuild.BuildEnvironmentVariable(
                        value="{}.dkr.ecr.{}.amazonaws.com/{}".format(env.account, env.region, WINDOWS_X86_ECR_REPO)
                    ),
                },
            ),
            build_spec=codebuild.BuildSpec.from_object({
                "version": 0.2,
                "phases": {
                    "pre_build": {
                        "commands": [
                            "mkdir -p /root/.docker",
                            """\
cat <<EOF > /root/.docker/config.json
{
  "credHelpers": {
    "public.ecr.aws": "ecr-login",
    "$AWS_ACCOUNT_ID.dkr.ecr.us-west-2.amazonaws.com": "ecr-login"
  }
}
EOF
"""
                        ]
                    }
                },
            }),
        )

        cfn_project = project.node.default_child
        cfn_project.add_property_override("Triggers.PullRequestBuildPolicy", self.pull_request_policy)
