# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

import subprocess
import typing

import boto3

from botocore.exceptions import ClientError
from aws_cdk import (
    CfnTag,
    Duration,
    Stack,
    Tags,
    aws_ec2 as ec2,
    aws_codebuild as codebuild,
    aws_iam as iam,
    aws_s3 as s3,
    aws_logs as logs,
    Environment,
)
from constructs import Construct

from cdk.aws_lc_base_ci_stack import AwsLcBaseCiStack
from cdk.components import PruneStaleGitHubBuilds
from util.metadata import (
    GITHUB_PUSH_CI_BRANCH_TARGETS,
    GITHUB_REPO_OWNER,
    GITHUB_REPO_NAME,
    LINUX_AARCH_ECR_REPO,
    LINUX_X86_ECR_REPO,
    PRE_PROD_ACCOUNT,
    STAGING_GITHUB_REPO_OWNER,
    STAGING_GITHUB_REPO_NAME,
)
from util.iam_policies import (
    code_build_batch_policy_in_json,
    ec2_policies_in_json,
    ssm_policies_in_json,
    s3_read_write_policy_in_json,
    ecr_power_user_policy_in_json,
)
from util.build_spec_loader import BuildSpecLoader

# detailed documentation can be found here: https://docs.aws.amazon.com/cdk/api/latest/docs/aws-ec2-readme.html


class AwsLcEC2TestingCIStack(AwsLcBaseCiStack):
    """Define a stack used to create a CodeBuild instance on which to execute the AWS-LC m1 ci ec2 instance"""

    def __init__(
        self,
        scope: Construct,
        id: str,
        spec_file_path: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, timeout=120, **kwargs)

        # S3 bucket for testing internal fixes.
        s3_read_write_policy = iam.PolicyDocument.from_json(
            s3_read_write_policy_in_json("aws-lc-codebuild")
        )
        ecr_power_user_policy = iam.PolicyDocument.from_json(
            ecr_power_user_policy_in_json(
                [LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO], env
            )
        )
        ec2_inline_policies = {
            "s3_read_write_policy": s3_read_write_policy,
            "ecr_power_user_policy": ecr_power_user_policy,
        }
        ec2_role = iam.Role(
            scope=self,
            id="{}-ec2-role".format(id),
            role_name="{}-ec2-role".format(id),
            assumed_by=iam.ServicePrincipal("ec2.amazonaws.com"),
            inline_policies=ec2_inline_policies,
            managed_policies=[
                iam.ManagedPolicy.from_aws_managed_policy_name(
                    "AmazonSSMManagedInstanceCore"
                ),
                iam.ManagedPolicy.from_aws_managed_policy_name(
                    "CloudWatchAgentServerPolicy"
                ),
            ],
        )
        iam.CfnInstanceProfile(
            scope=self,
            id="{}-ec2-profile".format(id),
            roles=[ec2_role.role_name],
            instance_profile_name="{}-ec2-profile".format(id),
        )

        # create vpc for ec2s
        vpc = ec2.Vpc(
            self,
            id="{}-ec2-vpc".format(id),
            nat_gateways=1 # minimize the number of idle NAT gateways and thus elastic IPs
        )

        selected_subnets = vpc.select_subnets(
            subnet_type=ec2.SubnetType.PRIVATE_WITH_EGRESS
        )

        # create security group with default rules
        security_group = ec2.SecurityGroup(
            self,
            id="{}-ec2-sg".format(id),
            allow_all_outbound=True,
            vpc=vpc,
            security_group_name="codebuild_ec2_sg",
        )

        # Define a IAM role for this stack.
        code_build_batch_policy = iam.PolicyDocument.from_json(
            code_build_batch_policy_in_json([id], env)
        )
        ec2_policy = iam.PolicyDocument.from_json(
            ec2_policies_in_json(
                ec2_role.role_name,
                security_group.security_group_id,
                selected_subnets.subnets[0].subnet_id,
                vpc.vpc_id,
                env,
            )
        )
        ssm_policy = iam.PolicyDocument.from_json(ssm_policies_in_json(env))
        codebuild_inline_policies = {
            "code_build_batch_policy": code_build_batch_policy,
            "ec2_policy": ec2_policy,
            "ssm_policy": ssm_policy,
        }
        codebuild_role = iam.Role(
            scope=self,
            id="{}-codebuild-role".format(id),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies=codebuild_inline_policies,
            managed_policies=[
                iam.ManagedPolicy.from_aws_managed_policy_name(
                    "CloudWatchAgentServerPolicy"
                )
            ],
        )

        # Define CodeBuild.
        project = codebuild.Project(
            scope=self,
            id=id,
            project_name=id,
            source=self.git_hub_source,
            role=codebuild_role,
            timeout=Duration.minutes(self.timeout),
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.SMALL,
                privileged=False,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0,
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
            environment_variables={
                "EC2_SECURITY_GROUP_ID": codebuild.BuildEnvironmentVariable(
                    value=security_group.security_group_id
                ),
                "EC2_SUBNET_ID": codebuild.BuildEnvironmentVariable(
                    value=selected_subnets.subnets[0].subnet_id
                ),
                "EC2_VPC_ID": codebuild.BuildEnvironmentVariable(value=vpc.vpc_id),
            },
        )
        project.enable_batch_builds()

        PruneStaleGitHubBuilds(
            scope=self,
            id="PruneStaleGitHubBuilds",
            project=project,
            ec2_permissions=True,
            env=env,
        )

        # Define logs for SSM.
        log_group_name = "{}-cw-logs".format(id)
        log_group = logs.CfnLogGroup(
            self,
            log_group_name,
            log_group_name=log_group_name,
            retention_in_days=365,
        )
