# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Duration,
    Size,
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
from util.iam_policies import (
    code_build_batch_policy_in_json,
    code_build_publish_metrics_in_json,
)
from util.metadata import (
    GITHUB_PUSH_CI_BRANCH_TARGETS,
    GITHUB_REPO_OWNER,
    GITHUB_REPO_NAME,
    PRE_PROD_ACCOUNT,
    STAGING_GITHUB_REPO_OWNER,
    STAGING_GITHUB_REPO_NAME,
)
from util.build_spec_loader import BuildSpecLoader


class AwsLcGitHubFuzzCIStack(AwsLcBaseCiStack):
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

        # Define a IAM role for this stack.
        code_build_batch_policy = iam.PolicyDocument.from_json(
            code_build_batch_policy_in_json([id], env)
        )
        fuzz_policy = iam.PolicyDocument.from_json(
            code_build_publish_metrics_in_json(env)
        )
        inline_policies = {
            "code_build_batch_policy": code_build_batch_policy,
            "fuzz_policy": fuzz_policy,
        }
        role = iam.Role(
            scope=self,
            id="{}-role".format(id),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies=inline_policies,
        )

        # Create the VPC for EFS and CodeBuild
        public_subnet = ec2.SubnetConfiguration(
            name="PublicFuzzingSubnet", subnet_type=ec2.SubnetType.PUBLIC
        )
        private_subnet = ec2.SubnetConfiguration(
            name="PrivateFuzzingSubnet", subnet_type=ec2.SubnetType.PRIVATE_WITH_EGRESS
        )

        # Create a VPC with a single public and private subnet in a single AZ. This is to avoid the elastic IP limit
        # being used up by a bunch of idle NAT gateways
        fuzz_vpc = ec2.Vpc(
            scope=self,
            id="{}-FuzzingVPC".format(id),
            subnet_configuration=[public_subnet, private_subnet],
            max_azs=1,
        )
        build_security_group = ec2.SecurityGroup(
            scope=self, id="{}-FuzzingSecurityGroup".format(id), vpc=fuzz_vpc
        )

        build_security_group.add_ingress_rule(
            peer=build_security_group,
            connection=ec2.Port.all_traffic(),
            description="Allow all traffic inside security group",
        )

        efs_subnet_selection = ec2.SubnetSelection(
            subnet_type=ec2.SubnetType.PRIVATE_WITH_EGRESS
        )

        # Create the EFS to store the corpus and logs. EFS allows new filesystems to burst to 100 MB/s for the first 2
        # TB of data read/written, after that the rate is limited based on the size of the filesystem. As of late
        # 2021 our corpus is less than one GB which results in EFS limiting all reads and writes to the minimum 1 MB/s.
        # To have the fuzzing be able to finish in a reasonable amount of time use the Provisioned capacity option.
        # For now this uses 100 MB/s which matches the performance used for 2021. Looking at EFS metrics in late 2021
        # during fuzz runs EFS sees 4-22 MB/s of transfers thus 100 MB/s gives lots of buffer and allows ~4-5 fuzz runs
        # to start at the same time with no issue.
        # https://docs.aws.amazon.com/efs/latest/ug/performance.html
        fuzz_filesystem = efs.FileSystem(
            scope=self,
            id="{}-FuzzingEFS".format(id),
            file_system_name="AWS-LC-Fuzz-Corpus",
            enable_automatic_backups=True,
            encrypted=True,
            security_group=build_security_group,
            vpc=fuzz_vpc,
            vpc_subnets=efs_subnet_selection,
            performance_mode=efs.PerformanceMode.GENERAL_PURPOSE,
            throughput_mode=efs.ThroughputMode.PROVISIONED,
            provisioned_throughput_per_second=Size.mebibytes(100),
        )

        # Define CodeBuild.
        fuzz_codebuild = codebuild.Project(
            scope=self,
            id="FuzzingCodeBuild",
            project_name=id,
            source=self.git_hub_source,
            role=role,
            timeout=Duration.minutes(self.timeout),
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.LARGE,
                privileged=True,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0,
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
            vpc=fuzz_vpc,
            security_groups=[build_security_group],
        )
        fuzz_codebuild.enable_batch_builds()

        # CDK raw overrides: https://docs.aws.amazon.com/cdk/latest/guide/cfn_layer.html#cfn_layer_raw
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-resource-codebuild-project.html#aws-resource-codebuild-project-properties
        # The EFS identifier needs to match tests/ci/common_fuzz.sh, CodeBuild defines an environment variable named
        # codebuild_$identifier.
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-properties-codebuild-project-projectfilesystemlocation.html
        #
        # TODO: add this to the CDK project above when it supports EfsFileSystemLocation
        cfn_codebuild = fuzz_codebuild.node.default_child
        cfn_codebuild.add_override(
            "Properties.FileSystemLocations",
            [
                {
                    "Identifier": "fuzzing_root",
                    "Location": "%s.efs.%s.amazonaws.com:/"
                    % (fuzz_filesystem.file_system_id, env.region),
                    "MountPoint": "/efs_fuzzing_root",
                    "Type": "EFS",
                }
            ],
        )

        PruneStaleGitHubBuilds(
            scope=self,
            id="PruneStaleGitHubBuilds",
            project=fuzz_codebuild,
            ec2_permissions=False,
            env=env,
        )
