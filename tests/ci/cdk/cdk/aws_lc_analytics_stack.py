# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Duration,
    Stack,
    aws_codebuild as codebuild,
    aws_iam as iam,
    aws_ec2 as ec2,
    aws_efs as efs,
    Environment,
)
from constructs import Construct

from cdk.aws_lc_base_ci_stack import AwsLcBaseCiStack
from cdk.components import PruneStaleGitHubBuilds
from util.iam_policies import code_build_publish_metrics_in_json
from util.metadata import (
    GITHUB_REPO_OWNER,
    GITHUB_REPO_NAME,
    PRE_PROD_ACCOUNT,
    STAGING_GITHUB_REPO_OWNER,
    STAGING_GITHUB_REPO_NAME,
)
from util.build_spec_loader import BuildSpecLoader


class AwsLcGitHubAnalyticsStack(AwsLcBaseCiStack):
    """Define a stack used to batch execute AWS-LC tests in GitHub."""

    def __init__(
        self,
        scope: Construct,
        id: str,
        spec_file_path: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, timeout=120, **kwargs)

        # Override default CodeBuild resource.
        self.git_hub_source = codebuild.Source.git_hub(
            owner=self.github_repo_owner,
            repo=self.github_repo_name,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(codebuild.EventAction.PUSH)
                # The current FIPS branch does not have the configuration needed to run the analytics, once we update
                # the branch or create a new FIPS branch it should be updated to '(main)|(fips.*)'
                .and_branch_is("main")
            ],
            webhook_triggers_batch_build=True,
        )

        # Define a IAM role for this stack.
        metrics_policy = iam.PolicyDocument.from_json(
            code_build_publish_metrics_in_json(env)
        )
        inline_policies = {"metric_policy": metrics_policy}
        role = iam.Role(
            scope=self,
            id="{}-role".format(id),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies=inline_policies,
        )

        # Define CodeBuild.
        analytics = codebuild.Project(
            scope=self,
            id="AnalyticsCodeBuild",
            project_name=id,
            source=self.git_hub_source,
            role=role,
            timeout=Duration.minutes(120),
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.LARGE,
                privileged=True,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0,
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
        )
        analytics.enable_batch_builds()

        PruneStaleGitHubBuilds(
            scope=self,
            id="PruneStaleGitHubBuilds",
            project=analytics,
            ec2_permissions=False,
            env=env,
        )
