# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import Duration, Stack, aws_codebuild as codebuild, aws_iam as iam, aws_s3_assets, aws_logs as logs
from constructs import Construct

from cdk.components import PruneStaleGitHubBuilds
from util.iam_policies import code_build_batch_policy_in_json, code_build_publish_metrics_in_json, code_build_cloudwatch_logs_policy_in_json
from util.metadata import CAN_AUTOLOAD, GITHUB_PUSH_CI_BRANCH_TARGETS, GITHUB_REPO_OWNER, GITHUB_REPO_NAME
from util.build_spec_loader import BuildSpecLoader


class AwsLcGitHubCIStack(Stack):
    """Define a stack used to batch execute AWS-LC tests in GitHub."""

    def __init__(self,
                 scope: Construct,
                 id: str,
                 spec_file_path: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=GITHUB_REPO_OWNER,
            repo=GITHUB_REPO_NAME,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.PULL_REQUEST_CREATED,
                    codebuild.EventAction.PULL_REQUEST_UPDATED,
                    codebuild.EventAction.PULL_REQUEST_REOPENED),
                codebuild.FilterGroup.in_event_of(codebuild.EventAction.PUSH).and_branch_is(
                    GITHUB_PUSH_CI_BRANCH_TARGETS),
            ],
            webhook_triggers_batch_build=True)

        # Define a IAM role for accessing build resources
        log_group = logs.LogGroup(self, id="{}-public-logs".format(id))
        code_build_cloudwatch_logs_policy = iam.PolicyDocument.from_json(
            code_build_cloudwatch_logs_policy_in_json([log_group])
        )
        resource_access_role = iam.Role(scope=self,
                                        id="{}-resource-role".format(id),
                                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                                        inline_policies={
                                            "code_build_cloudwatch_logs_policy": code_build_cloudwatch_logs_policy
                                        })

        # Define a IAM role for this stack.
        code_build_batch_policy = iam.PolicyDocument.from_json(
            code_build_batch_policy_in_json([id])
        )
        metrics_policy = iam.PolicyDocument.from_json(code_build_publish_metrics_in_json())
        inline_policies = {"code_build_batch_policy": code_build_batch_policy,
                           "metrics_policy": metrics_policy,
                           }
        role = iam.Role(scope=self,
                        id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        inline_policies=inline_policies)

        logging_options = codebuild.LoggingOptions(
            cloud_watch=codebuild.CloudWatchLoggingOptions(
                log_group=log_group
            )
        )

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=git_hub_source,
            role=role,
            timeout=Duration.minutes(180),
            logging=logging_options,
            environment=codebuild.BuildEnvironment(compute_type=codebuild.ComputeType.SMALL,
                                                   privileged=False,
                                                   build_image=codebuild.LinuxBuildImage.STANDARD_4_0),
            build_spec=BuildSpecLoader.load(spec_file_path))
        cfn_project = project.node.default_child
        cfn_project.add_property_override("Visibility", "PUBLIC_READ")
        cfn_project.add_property_override("ResourceAccessRole", resource_access_role.role_arn)
        project.enable_batch_builds()

        PruneStaleGitHubBuilds(scope=self, id="PruneStaleGitHubBuilds", project=project, ec2_permissions=False)
