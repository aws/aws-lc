# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

import subprocess
import boto3

from botocore.exceptions import ClientError
from aws_cdk import core, aws_ec2 as ec2, aws_codebuild as codebuild, aws_iam as iam, aws_s3 as s3, aws_logs as logs
from util.metadata import AWS_ACCOUNT, AWS_REGION, GITHUB_REPO_OWNER, GITHUB_REPO_NAME
from util.iam_policies import code_build_batch_policy_in_json, ec2_policies_in_json, ssm_policies_in_json, s3_read_write_policy_in_json
from util.build_spec_loader import BuildSpecLoader

# detailed documentation can be found here: https://docs.aws.amazon.com/cdk/api/latest/docs/aws-ec2-readme.html

class AwsLcMacArmCIStack(core.Stack):
    """Define a stack used to create a CodeBuild instance on which to execute the AWS-LC m1 ci ec2 instance"""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 spec_file_path: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define some variables that will be commonly used
        CLOUDWATCH_LOGS = "{}-cw-logs".format(id)

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
        ec2_policy = iam.PolicyDocument.from_json(ec2_policies_in_json())
        ssm_policy = iam.PolicyDocument.from_json(ssm_policies_in_json())
        codebuild_inline_policies = {"code_build_batch_policy": code_build_batch_policy,
                                     "ec2_policy": ec2_policy,
                                     "ssm_policy": ssm_policy}
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
            timeout=core.Duration.minutes(120),
            environment=codebuild.BuildEnvironment(compute_type=codebuild.ComputeType.SMALL,
                                                   privileged=False,
                                                   build_image=codebuild.LinuxBuildImage.STANDARD_4_0),
            build_spec=BuildSpecLoader.load(spec_file_path))
        project.enable_batch_builds()

        # S3 bucket for testing internal fixes.
        s3_read_write_policy = iam.PolicyDocument.from_json(s3_read_write_policy_in_json("aws-lc-codebuild"))
        ec2_inline_policies = {"s3_read_write_policy": s3_read_write_policy}
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
        selection = vpc.select_subnets()

        # create security group with default rules
        security_group = ec2.SecurityGroup(self, id="{}-ec2-sg".format(id),
                          allow_all_outbound=True,
                          vpc=vpc,
                          security_group_name='macos_arm_ec2_sg')

        # Dedicated Hosts are required for Mac ec2 instances.
        cfn_host = ec2.CfnHost(self, id="{}-dedicated-host".format(id),
                                availability_zone="us-west-2a",
                                auto_placement="off",
                                instance_type="mac2.metal")
        core.Tags.of(cfn_host).add("Name", "{}-dedicated-host".format(id))

        # AMI is for M1 MacOS Monterey.
        ami_id="ami-084c6ab9d03ad4d46"
        cfn_instance = ec2.CfnInstance(self, "{}-ec2-instance".format(id),
                        availability_zone="us-west-2a",
                        tenancy="host",
                        host_id=cfn_host.attr_host_id,
                        iam_instance_profile="{}-ec2-profile".format(id),
                        image_id=ami_id,
                        instance_type="mac2.metal",
                        security_group_ids=[security_group.security_group_id],
                        subnet_id=selection.subnet_ids[0],
                        tags=[core.CfnTag(key="Name",value="aws-lc-ci-macos-arm-ec2-instance")])

        # Define logs for SSM.
        logs.LogGroup(self, "{}-cw-logs".format(id), log_group_name=CLOUDWATCH_LOGS)
