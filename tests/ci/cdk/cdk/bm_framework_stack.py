# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

import subprocess
import boto3

from botocore.exceptions import ClientError
from aws_cdk import Duration, Stack, aws_ec2 as ec2, aws_codebuild as codebuild, aws_iam as iam, aws_logs as logs
from constructs import Construct

from cdk.components import PruneStaleGitHubBuilds
from util.metadata import AWS_ACCOUNT, AWS_REGION, GITHUB_REPO_OWNER, GITHUB_REPO_NAME
from util.iam_policies import code_build_batch_policy_in_json, ec2_bm_framework_policies_in_json, \
                                ssm_bm_framework_policies_in_json, ecr_power_user_policy_in_json
from util.build_spec_loader import BuildSpecLoader

# detailed documentation can be found here: https://docs.aws.amazon.com/cdk/api/latest/docs/aws-ec2-readme.html

class BmFrameworkStack(Stack):
    """Define a stack used to create a CodeBuild instance on which to execute the AWS-LC benchmarking framework"""

    def __init__(self,
                 scope: Construct,
                 id: str,
                 spec_file_path: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define some variables that will be commonly used
        CLOUDWATCH_LOGS = "{}-{}-cw-logs".format(AWS_ACCOUNT, id)

        # Define CodeBuild resource.
        git_hub_source = codebuild.Source.git_hub(
            owner=GITHUB_REPO_OWNER,
            repo=GITHUB_REPO_NAME,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.PULL_REQUEST_CREATED,
                    codebuild.EventAction.PULL_REQUEST_UPDATED,
                    codebuild.EventAction.PULL_REQUEST_REOPENED)
            ],
            webhook_triggers_batch_build=True)

        # Define a IAM role for this stack.
        code_build_batch_policy = iam.PolicyDocument.from_json(code_build_batch_policy_in_json([id]))
        ec2_bm_framework_policy = iam.PolicyDocument.from_json(ec2_bm_framework_policies_in_json())
        ssm_bm_framework_policy = iam.PolicyDocument.from_json(ssm_bm_framework_policies_in_json())
        codebuild_inline_policies = {"code_build_batch_policy": code_build_batch_policy,
                                     "ec2_bm_framework_policy": ec2_bm_framework_policy,
                                     "ssm_bm_framework_policy": ssm_bm_framework_policy}
        codebuild_role = iam.Role(scope=self,
                                  id="{}-codebuild-role".format(id),
                                  assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                                  inline_policies=codebuild_inline_policies,
                                  managed_policies=[
                                      iam.ManagedPolicy.from_aws_managed_policy_name("CloudWatchAgentServerPolicy")
                                  ])

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=git_hub_source,
            role=codebuild_role,
            timeout=Duration.minutes(120),
            environment=codebuild.BuildEnvironment(compute_type=codebuild.ComputeType.SMALL,
                                                   privileged=False,
                                                   build_image=codebuild.LinuxBuildImage.STANDARD_4_0),
            build_spec=BuildSpecLoader.load(spec_file_path))
        project.enable_batch_builds()

        PruneStaleGitHubBuilds(scope=self, id="PruneStaleGitHubBuilds", project=project)

        # use boto3 to determine if a cloudwatch logs group with the name we want exists, and if it doesn't, create it
        logs_client = boto3.client('logs', region_name=AWS_REGION)
        try:
            logs_client.describe_log_groups(logGroupNamePrefix=CLOUDWATCH_LOGS)
        except ClientError:
            # define CloudWatch Logs groups
            logs.LogGroup(self, "{}-cw-logs".format(id),
                          log_group_name=CLOUDWATCH_LOGS)
