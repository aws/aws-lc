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

# NFS port used by EFS mount targets.
NFS_PORT = 2049


class AwsLcGitHubFuzzCIStack(AwsLcBaseCiStack):
    """Define a stack used to batch execute AWS-LC fuzz tests in GitHub.

    Fuzzing is split across two CodeBuild projects so that untrusted fork-PR
    builds cannot read from or write to the canonical fuzzing corpus and the
    crash-artifact store that trusted runs depend on, while still giving PR
    runs a warm seed corpus:

      * a trusted project, triggered only by pushes to the protected CI
        branches (main / fips-*), which mounts the canonical EFS read-write. It
        is the sole reader/writer of the crash-artifact store and the only
        writer of the corpus, and
      * an untrusted project, triggered by pull requests (including forks),
        which mounts only a read-replica EFS that holds a copy of the corpus
        (never the crash-artifact tree). It runs in a dedicated security group
        that the canonical EFS mount target does not admit.

    The corpus is synced one-way (trusted -> replica, corpus subtree only) by
    the trusted build after it merges new inputs back (see
    tests/ci/common_fuzz.sh). Nothing flows replica -> canonical, so a PR that
    scribbles on the replica cannot affect trusted data, and the replica
    self-heals on the next trusted sync.

    Why network isolation rather than a read-only mount or IAM policy:
    CodeBuild does not support IAM authorization for EFS mounts (see
    https://docs.aws.amazon.com/codebuild/latest/userguide/sample-efs-troubleshooting.html),
    and the fuzzing containers run privileged, so neither a per-role read-only
    EFS file-system policy nor an "ro" mount option can be enforced against
    attacker-controlled PR code. The only robust control is denying the PR
    project a network path to the canonical filesystem.
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

        # The trusted (push-triggered) project keeps the stack id as its name;
        # the untrusted (PR-triggered) project is suffixed.
        trusted_project_name = id
        pr_project_name = "{}-pr".format(id)

        # Create the VPC shared by both EFS filesystems and both projects.
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

        # Security group for trusted builds. It is shared with the canonical
        # EFS mount target; the self-referencing ingress rule means only
        # members of this group (i.e. the trusted project) can reach the
        # canonical corpus/crash-artifact filesystem.
        trusted_security_group = ec2.SecurityGroup(
            scope=self, id="{}-FuzzingSecurityGroup".format(id), vpc=fuzz_vpc
        )
        trusted_security_group.add_ingress_rule(
            peer=trusted_security_group,
            connection=ec2.Port.all_traffic(),
            description="Allow all traffic inside security group",
        )

        # Dedicated security group for untrusted PR builds. It is deliberately
        # NOT admitted by the canonical EFS security group, so PR containers
        # have no network path to the canonical filesystem even though they
        # share the VPC and run privileged. They reach only the replica EFS.
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

        # Security group for the replica EFS mount target. It admits the PR
        # project (read path for the warm seed corpus) and the trusted project
        # (one-way sync writer). It does NOT grant the PR project any path to
        # the canonical filesystem above.
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

        # Read-replica EFS: holds a one-way-synced copy of the corpus only
        # (never the crash-artifact tree). No automatic backups: it is derived
        # state that the trusted sync can fully reconstruct.
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

        # ------------------------------------------------------------------
        # Trusted project: triggered only by pushes to main / fips-* (i.e.
        # already-reviewed, merged code). Mounts the canonical EFS read-write
        # and the replica EFS as the one-way sync target.
        # ------------------------------------------------------------------
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
                # Marks this project as the trusted corpus writer. Only builds
                # with this flag set write back to the canonical corpus /
                # crash-artifact store and drive the replica sync (see
                # tests/ci/common_fuzz.sh). This is a project-level variable
                # that PR-authored code cannot change.
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

        # ------------------------------------------------------------------
        # Untrusted project: triggered by pull requests (including forks).
        # Runs unreviewed code, so it mounts ONLY the replica EFS (warm corpus,
        # no crash-artifact tree) and lives in an isolated security group with
        # no path to the canonical filesystem.
        # ------------------------------------------------------------------
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
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
            vpc=fuzz_vpc,
            security_groups=[pr_security_group],
        )
        pr_codebuild.enable_batch_builds()

        # PR builds mount only the replica, at the same identifier the fuzz
        # script reads its corpus from (fuzzing_root -> CODEBUILD_FUZZING_ROOT).
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

        # Prune stale PR builds superseded by newer commits on the same PR.
        PruneStaleGitHubBuilds(
            scope=self,
            id="PruneStaleGitHubBuilds",
            project=pr_codebuild,
            ec2_permissions=False,
            env=env,
        )
