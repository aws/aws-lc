# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Duration,
    Size,
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
from util.metadata import GITHUB_PUSH_CI_BRANCH_TARGETS
from util.build_spec_loader import BuildSpecLoader

NFS_PORT = 2049


class AwsLcGitHubFuzzCIStack(AwsLcBaseCiStack):
    """Batch-execute AWS-LC fuzz tests in GitHub.

    A trusted project (push to main/fips-*) mounts the canonical EFS
    read-write; an untrusted PR project mounts only a read-replica of the
    corpus and has no network path to the canonical filesystem. The trusted
    build syncs the corpus one-way to the replica.
    """

    def __init__(
        self,
        scope: Construct,
        id: str,
        spec_file_path: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, timeout=120, **kwargs)

        trusted_project_name = id
        pr_project_name = "{}-pr".format(id)

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

        trusted_security_group = ec2.SecurityGroup(
            scope=self, id="{}-FuzzingSecurityGroup".format(id), vpc=fuzz_vpc
        )
        trusted_security_group.add_ingress_rule(
            peer=trusted_security_group,
            connection=ec2.Port.all_traffic(),
            description="Allow all traffic inside security group",
        )

        # Deliberately not admitted to the canonical EFS SG.
        pr_security_group = ec2.SecurityGroup(
            scope=self, id="{}-PRFuzzingSecurityGroup".format(id), vpc=fuzz_vpc
        )

        efs_subnet_selection = ec2.SubnetSelection(
            subnet_type=ec2.SubnetType.PRIVATE_WITH_EGRESS
        )

        # Create the canonical EFS to store the corpus and logs. EFS allows new filesystems to burst to 100 MB/s for the
        # first 2 TB of data read/written, after that the rate is limited based on the size of the filesystem. As of
        # late 2021 our corpus is less than one GB which results in EFS limiting all reads and writes to the minimum 1
        # MB/s. To have the fuzzing be able to finish in a reasonable amount of time use the Provisioned capacity
        # option. For now this uses 100 MB/s which matches the performance used for 2021. Looking at EFS metrics in late
        # 2021 during fuzz runs EFS sees 4-22 MB/s of transfers thus 100 MB/s gives lots of buffer and allows ~4-5 fuzz
        # runs to start at the same time with no issue.
        # https://docs.aws.amazon.com/efs/latest/ug/performance.html
        fuzz_filesystem = efs.FileSystem(
            scope=self,
            id="{}-FuzzingEFS".format(id),
            file_system_name="AWS-LC-Fuzz-Corpus",
            enable_automatic_backups=True,
            encrypted=True,
            security_group=trusted_security_group,
            vpc=fuzz_vpc,
            vpc_subnets=efs_subnet_selection,
            performance_mode=efs.PerformanceMode.GENERAL_PURPOSE,
            throughput_mode=efs.ThroughputMode.PROVISIONED,
            provisioned_throughput_per_second=Size.mebibytes(100),
        )

        replica_efs_security_group = ec2.SecurityGroup(
            scope=self, id="{}-ReplicaEFSSecurityGroup".format(id), vpc=fuzz_vpc
        )
        replica_efs_security_group.add_ingress_rule(
            peer=pr_security_group,
            connection=ec2.Port.tcp(NFS_PORT),
            description="Allow PR fuzz builds to read the replica corpus",
        )
        replica_efs_security_group.add_ingress_rule(
            peer=trusted_security_group,
            connection=ec2.Port.tcp(NFS_PORT),
            description="Allow trusted fuzz builds to sync the replica corpus",
        )

        replica_filesystem = efs.FileSystem(
            scope=self,
            id="{}-FuzzingReplicaEFS".format(id),
            file_system_name="AWS-LC-Fuzz-Corpus-PR-Replica",
            enable_automatic_backups=False,
            encrypted=True,
            security_group=replica_efs_security_group,
            vpc=fuzz_vpc,
            vpc_subnets=efs_subnet_selection,
            performance_mode=efs.PerformanceMode.GENERAL_PURPOSE,
            throughput_mode=efs.ThroughputMode.PROVISIONED,
            provisioned_throughput_per_second=Size.mebibytes(100),
        )

        # Trusted project: push to main/fips-*, canonical EFS read-write.
        trusted_source = codebuild.Source.git_hub(
            owner=self.github_repo_owner,
            repo=self.github_repo_name,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.PUSH
                ).and_branch_is(GITHUB_PUSH_CI_BRANCH_TARGETS),
            ],
            webhook_triggers_batch_build=True,
        )

        trusted_role = iam.Role(
            scope=self,
            id="{}-role".format(trusted_project_name),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies={
                "code_build_batch_policy": iam.PolicyDocument.from_json(
                    code_build_batch_policy_in_json([trusted_project_name], env)
                ),
                "fuzz_policy": iam.PolicyDocument.from_json(
                    code_build_publish_metrics_in_json(env)
                ),
            },
        )

        trusted_codebuild = codebuild.Project(
            scope=self,
            id="FuzzingCodeBuild",
            project_name=trusted_project_name,
            source=trusted_source,
            role=trusted_role,
            timeout=Duration.minutes(self.timeout),
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.LARGE,
                privileged=True,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0,
                environment_variables={
                    "FUZZ_CORPUS_WRITABLE": codebuild.BuildEnvironmentVariable(
                        value="true"
                    )
                },
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
            vpc=fuzz_vpc,
            security_groups=[trusted_security_group],
        )
        trusted_codebuild.enable_batch_builds()

        # CDK raw overrides: https://docs.aws.amazon.com/cdk/latest/guide/cfn_layer.html#cfn_layer_raw
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-resource-codebuild-project.html#aws-resource-codebuild-project-properties
        # The EFS identifiers need to match tests/ci/common_fuzz.sh, CodeBuild defines an environment variable named
        # codebuild_$identifier (e.g. fuzzing_root -> CODEBUILD_FUZZING_ROOT).
        # https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-properties-codebuild-project-projectfilesystemlocation.html
        #
        # TODO: add this to the CDK project above when it supports EfsFileSystemLocation
        cfn_trusted_codebuild = trusted_codebuild.node.default_child
        cfn_trusted_codebuild.add_override(
            "Properties.FileSystemLocations",
            [
                {
                    "Identifier": "fuzzing_root",
                    "Location": "%s.efs.%s.amazonaws.com:/"
                    % (fuzz_filesystem.file_system_id, env.region),
                    "MountPoint": "/efs_fuzzing_root",
                    "Type": "EFS",
                },
                {
                    "Identifier": "fuzzing_replica_root",
                    "Location": "%s.efs.%s.amazonaws.com:/"
                    % (replica_filesystem.file_system_id, env.region),
                    "MountPoint": "/efs_fuzzing_replica_root",
                    "Type": "EFS",
                },
            ],
        )

        # Untrusted PR project: replica EFS only, isolated security group.
        pr_source = codebuild.Source.git_hub(
            owner=self.github_repo_owner,
            repo=self.github_repo_name,
            webhook=True,
            webhook_filters=[
                codebuild.FilterGroup.in_event_of(
                    codebuild.EventAction.PULL_REQUEST_CREATED,
                    codebuild.EventAction.PULL_REQUEST_UPDATED,
                    codebuild.EventAction.PULL_REQUEST_REOPENED,
                ),
            ],
            webhook_triggers_batch_build=True,
        )

        pr_role = iam.Role(
            scope=self,
            id="{}-role".format(pr_project_name),
            assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
            inline_policies={
                "code_build_batch_policy": iam.PolicyDocument.from_json(
                    code_build_batch_policy_in_json([pr_project_name], env)
                ),
                "fuzz_policy": iam.PolicyDocument.from_json(
                    code_build_publish_metrics_in_json(env)
                ),
            },
        )

        pr_codebuild = codebuild.Project(
            scope=self,
            id="PRFuzzingCodeBuild",
            project_name=pr_project_name,
            source=pr_source,
            role=pr_role,
            timeout=Duration.minutes(self.timeout),
            environment=codebuild.BuildEnvironment(
                compute_type=codebuild.ComputeType.LARGE,
                privileged=True,
                build_image=codebuild.LinuxBuildImage.STANDARD_4_0,
                environment_variables={
                    "FUZZ_CORPUS_WRITABLE": codebuild.BuildEnvironmentVariable(
                        value="false"
                    )
                },
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
            vpc=fuzz_vpc,
            security_groups=[pr_security_group],
        )
        pr_codebuild.enable_batch_builds()

        cfn_pr_codebuild = pr_codebuild.node.default_child
        cfn_pr_codebuild.add_override(
            "Properties.FileSystemLocations",
            [
                {
                    "Identifier": "fuzzing_root",
                    "Location": "%s.efs.%s.amazonaws.com:/"
                    % (replica_filesystem.file_system_id, env.region),
                    "MountPoint": "/efs_fuzzing_root",
                    "Type": "EFS",
                }
            ],
        )
        cfn_pr_codebuild.add_property_override(
            "Triggers.PullRequestBuildPolicy", self.pull_request_policy
        )

        PruneStaleGitHubBuilds(
            scope=self,
            id="PruneStaleGitHubBuilds",
            project=pr_codebuild,
            ec2_permissions=False,
            env=env,
        )
