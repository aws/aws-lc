# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Duration,
    Tags,
    aws_codebuild as codebuild,
    aws_iam as iam,
    aws_s3 as s3,
    RemovalPolicy,
    Environment,
)
from constructs import Construct

from util.metadata import (
    GITHUB_REPO_OWNER,
    GITHUB_REPO_NAME
)

from cdk.aws_lc_base_ci_stack import AwsLcBaseCiStack
from cdk.components import PruneStaleGitHubBuilds
from util.iam_policies import (
    bedrock_policy_in_json
)
from util.build_spec_loader import BuildSpecLoader

class AwsLcAiCodeReviewStack(AwsLcBaseCiStack):
    """Define a stack used to batch execute AWS-LC tests in GitHub."""

    def __init__(
            self,
            scope: Construct,
            id: str,
            spec_file_path: str,
            env: typing.Union[Environment, typing.Dict[str, typing.Any]],
            **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, timeout=180, **kwargs)
        
        # Create S3 bucket for AI code review files with versioning
        bucket = s3.Bucket(
            self,
            "aws-lc-ai-code-review-files",
            versioned=True,
            removal_policy=RemovalPolicy.RETAIN,
            block_public_access=s3.BlockPublicAccess.BLOCK_ALL,
        )
        
        # Tag the bucket for easy discovery
        Tags.of(bucket).add("aws-lc", "aws-lc-ai-code-review-files")
        
        self.git_hub_source = codebuild.Source.git_hub(
            owner=self.github_repo_owner,
            repo=self.github_repo_name,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.PULL_REQUEST_CREATED,
                    codebuild.EventAction.PULL_REQUEST_UPDATED,
                    codebuild.EventAction.PULL_REQUEST_REOPENED,
                )
            ],
            webhook_triggers_batch_build=False,
        )

        # Define a IAM role for this stack.
        bedrock_policy = iam.PolicyDocument.from_json(
            bedrock_policy_in_json()
        )

        inline_policies = {
            "bedrock_policy": bedrock_policy,
        }
        role = iam.Role(
            scope=self,
            id="{}-role".format(id),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies=inline_policies,
        )
        
        # Grant CodeBuild read access to the S3 bucket
        bucket.grant_read(role)

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=self.git_hub_source,
            role=role,
            timeout=Duration.minutes(self.timeout),
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.SMALL,
                privileged=False,
                build_image=codebuild.LinuxBuildImage.STANDARD_7_0,
                environment_variables={
                    "GITHUB_REPO_OWNER": codebuild.BuildEnvironmentVariable(
                        type=codebuild.BuildEnvironmentVariableType.PLAINTEXT,
                        value=GITHUB_REPO_OWNER
                    ),
                    "GITHUB_REPO_NAME": codebuild.BuildEnvironmentVariable(
                        type=codebuild.BuildEnvironmentVariableType.PLAINTEXT,
                        value=GITHUB_REPO_NAME
                    ),
                    "AI_CODE_REVIEW_BUCKET": codebuild.BuildEnvironmentVariable(
                        type=codebuild.BuildEnvironmentVariableType.PLAINTEXT,
                        value=bucket.bucket_name
                    )
                }
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env=env),
        )
        
        cfn_project = project.node.default_child
        cfn_project.add_property_override("Triggers.PullRequestBuildPolicy", self.pull_request_policy)

        PruneStaleGitHubBuilds(
            scope=self,
            id="PruneStaleGitHubBuilds",
            project=project,
            ec2_permissions=False,
            env=env,
        )

