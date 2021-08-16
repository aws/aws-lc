# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import subprocess
import boto3

from botocore.exceptions import ClientError
from aws_cdk import core, aws_ec2 as ec2, aws_codebuild as codebuild, aws_iam as iam, aws_s3 as s3, aws_logs as logs
from util.metadata import AWS_ACCOUNT, AWS_REGION, GITHUB_REPO_OWNER, GITHUB_REPO_NAME, LINUX_AARCH_ECR_REPO, \
    LINUX_X86_ECR_REPO
from util.ecr_util import ecr_arn
from util.iam_policies import code_build_batch_policy_in_json, s3_read_write_policy_in_json, \
    ec2_bm_framework_policies_in_json, ssm_bm_framework_policies_in_json, s3_bm_framework_policies_in_json, \
    ecr_power_user_policy_in_json
from util.yml_loader import YmlLoader

# detailed documentation can be found here: https://docs.aws.amazon.com/cdk/api/latest/docs/aws-ec2-readme.html

class BmFrameworkStack(core.Stack):
    """Define a stack used to create a CodeBuild instance on which to execute the AWS-LC benchmarking framework"""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 ecr_repo_name: str,
                 spec_file_path: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define some variables that will be commonly used
        S3_PROD_BUCKET = "{}-{}-prod-bucket".format(AWS_ACCOUNT, id)
        S3_PR_BUCKET = "{}-{}-pr-bucket".format(AWS_ACCOUNT, id)
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
            clone_depth=1)

        # Define a IAM role for this stack.
        code_build_batch_policy = iam.PolicyDocument.from_json(code_build_batch_policy_in_json([id]))
        ec2_bm_framework_policy = iam.PolicyDocument.from_json(ec2_bm_framework_policies_in_json())
        ssm_bm_framework_policy = iam.PolicyDocument.from_json(ssm_bm_framework_policies_in_json())
        s3_bm_framework_policy_prod_bucket = iam.PolicyDocument.from_json(s3_bm_framework_policies_in_json(S3_PROD_BUCKET))
        s3_bm_framework_policy_pr_bucket = iam.PolicyDocument.from_json(s3_bm_framework_policies_in_json(S3_PR_BUCKET))
        codebuild_inline_policies = {"code_build_batch_policy": code_build_batch_policy,
                                     "ec2_bm_framework_policy": ec2_bm_framework_policy,
                                     "ssm_bm_framework_policy": ssm_bm_framework_policy,
                                     "s3_bm_framework_policy_prod_bucket": s3_bm_framework_policy_prod_bucket,
                                     "s3_bm_framework_policy_pr_bucket": s3_bm_framework_policy_pr_bucket}
        codebuild_role = iam.Role(scope=self,
                                  id="{}-codebuild-role".format(id),
                                  assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                                  inline_policies=codebuild_inline_policies,
                                  managed_policies=[
                                      iam.ManagedPolicy.from_aws_managed_policy_name("CloudWatchAgentServerPolicy")
                                  ])

        # Create build spec.
        placeholder_map = {"ECR_REPO_PLACEHOLDER": ecr_arn(ecr_repo_name)}
        build_spec_content = YmlLoader.load(spec_file_path, placeholder_map)

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=git_hub_source,
            role=codebuild_role,
            timeout=core.Duration.minutes(180),
            environment=codebuild.BuildEnvironment(compute_type=codebuild.ComputeType.SMALL,
                                                   privileged=False,
                                                   build_image=codebuild.LinuxBuildImage.STANDARD_4_0),
            build_spec=codebuild.BuildSpec.from_object(build_spec_content))

        # Add 'BuildBatchConfig' property, which is not supported in CDK.
        # CDK raw overrides: https://docs.aws.amazon.com/cdk/latest/guide/cfn_layer.html#cfn_layer_raw
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-resource-codebuild-project.html#aws-resource-codebuild-project-properties
        cfn_build = project.node.default_child
        cfn_build.add_override("Properties.BuildBatchConfig", {
            "ServiceRole": codebuild_role.role_arn,
            "TimeoutInMins": 180
        })

        # create iam for ec2s
        s3_read_write_policy_prod_bucket = iam.PolicyDocument.from_json(s3_read_write_policy_in_json(S3_PROD_BUCKET))
        s3_read_write_policy_pr_bucket = iam.PolicyDocument.from_json(s3_read_write_policy_in_json(S3_PR_BUCKET))
        ecr_power_user_policy = iam.PolicyDocument.from_json(ecr_power_user_policy_in_json([LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO]))
        ec2_inline_policies = {"s3_read_write_policy_prod_bucket": s3_read_write_policy_prod_bucket,
                               "s3_read_write_policy_pr_bucket": s3_read_write_policy_pr_bucket,
                               "ecr_power_user_policy": ecr_power_user_policy}
        ec2_role = iam.Role(scope=self, id="{}-ec2-role".format(id),
                            role_name="{}-ec2-role".format(id),
                            assumed_by=iam.ServicePrincipal("ec2.amazonaws.com"),
                            inline_policies=ec2_inline_policies,
                            managed_policies=[
                                iam.ManagedPolicy.from_aws_managed_policy_name("AmazonSSMManagedInstanceCore"),
                                iam.ManagedPolicy.from_aws_managed_policy_name("CloudWatchAgentServerPolicy")
                            ])
        iam.CfnInstanceProfile(scope=self, id="{}-ec2-profile".format(id),
                               roles=["{}-ec2-role".format(id)],
                               instance_profile_name="{}-ec2-profile".format(id))

        # create vpc for ec2s
        vpc = ec2.Vpc(self, id="{}-ec2-vpc".format(id))

        # create security group with default rules
        ec2.SecurityGroup(self, id="{}-ec2-sg".format(id),
                          allow_all_outbound=True,
                          vpc=vpc,
                          security_group_name='bm_framework_ec2_sg')

        # use boto3 to determine if a bucket with the name that we want exists, and if it doesn't, create it
        s3_res = boto3.resource('s3')
        prod_bucket = s3_res.Bucket(S3_PROD_BUCKET)
        pr_bucket = s3_res.Bucket(S3_PR_BUCKET)
        try:
            s3_res.meta.client.head_bucket(Bucket=prod_bucket.name)
        except ClientError:
            production_results_s3 = s3.Bucket(self, "{}-prod-bucket".format(id),
                                              bucket_name=S3_PROD_BUCKET,
                                              enforce_ssl=True)

            production_results_s3.grant_put(ec2_role)

        try:
            s3_res.meta.client.head_bucket(Bucket=pr_bucket.name)
        except ClientError:
            pr_results_s3 = s3.Bucket(self, "{}-pr-bucket".format(id),
                                      bucket_name=S3_PR_BUCKET,
                                      enforce_ssl=True)

            pr_results_s3.grant_put(ec2_role)

        # use boto3 to determine if a cloudwatch logs group with the name we want exists, and if it doesn't, create it
        logs_client = boto3.client('logs')
        try:
            logs_client.describe_log_groups(logGroupNamePrefix=CLOUDWATCH_LOGS)
        except ClientError:
            # define CloudWatch Logs groups
            logs.LogGroup(self, "{}-cw-logs".format(id),
                          log_group_name=CLOUDWATCH_LOGS)
