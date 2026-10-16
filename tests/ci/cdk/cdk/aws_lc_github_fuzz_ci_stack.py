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
    aws_s3 as s3,
    Environment,
)
from constructs import Construct

from cdk.aws_lc_base_ci_stack import AwsLcBaseCiStack
from cdk.components import PruneStaleGitHubBuilds
from util.iam_policies import (
    code_build_batch_policy_in_json,
    code_build_publish_metrics_in_json,
    s3_read_write_policy_in_json,
    s3_read_only_policy_in_json,
)
from util.metadata import GITHUB_PUSH_CI_BRANCH_TARGETS
from util.build_spec_loader import BuildSpecLoader


class AwsLcGitHubFuzzCIStack(AwsLcBaseCiStack):
    """Batch-execute AWS-LC fuzz tests in GitHub.

    A trusted project (push to main/fips-*) mounts the canonical EFS
    read-write and uploads the merged corpus to an S3 bucket. An untrusted PR
    project has no EFS mount at all; it downloads the corpus from S3 with an
    IAM-enforced read-only (s3:GetObject) role.

    S3 is used for the PR path rather than a second EFS "replica" on purpose.
    CodeBuild has no IAM authorization for EFS mounts and the containers run
    privileged, so a PR-writable replica cannot be made read-only to the PR
    build. Any shared filesystem the PR build can write and the trusted build
    later reads is exploitable: a PR can plant a symlink and the trusted
    build's own write (running as the trusted principal) follows it back into
    the canonical store. In-band symlink checks are racy because the PR build
    can mutate the replica concurrently. With S3 the read-only grant is
    enforced by IAM outside the container, and the trusted build only ever
    uploads, so it never reads storage that PR code controls.
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

        # The PR project has no path to the canonical EFS: it is in its own
        # security group and mounts no filesystem.
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

        # Corpus distribution bucket for PR builds. The trusted build uploads
        # the merged corpus here; PR builds get s3:GetObject only (enforced by
        # IAM, outside the privileged container), so they can never write it.
        corpus_bucket = s3.Bucket(
            scope=self,
            id="{}-CorpusBucket".format(id),
            block_public_access=s3.BlockPublicAccess.BLOCK_ALL,
            enforce_ssl=True,
            encryption=s3.BucketEncryption.S3_MANAGED,
            versioned=True,
        )
        # Keep storage bounded: the corpus tarball is overwritten on every
        # trusted run, so old versions have no long-term value.
        corpus_bucket.add_lifecycle_rule(
            enabled=True,
            noncurrent_version_expiration=Duration.days(30),
            abort_incomplete_multipart_upload_after=Duration.days(7),
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
                # Upload the merged corpus for PR builds to consume.
                "corpus_s3_policy": iam.PolicyDocument.from_json(
                    s3_read_write_policy_in_json(corpus_bucket.bucket_name)
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
                    ),
                    "FUZZ_CORPUS_BUCKET": codebuild.BuildEnvironmentVariable(
                        value=corpus_bucket.bucket_name
                    ),
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
            ],
        )

        # Untrusted PR project: no EFS mount, corpus pulled read-only from S3.
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
                # Download-only: IAM enforces s3:GetObject with no write action.
                "corpus_s3_policy": iam.PolicyDocument.from_json(
                    s3_read_only_policy_in_json(corpus_bucket.bucket_name)
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
                    ),
                    "FUZZ_CORPUS_BUCKET": codebuild.BuildEnvironmentVariable(
                        value=corpus_bucket.bucket_name
                    ),
                },
            ),
            build_spec=BuildSpecLoader.load(spec_file_path, env),
            vpc=fuzz_vpc,
            security_groups=[pr_security_group],
        )
        pr_codebuild.enable_batch_builds()

        cfn_pr_codebuild = pr_codebuild.node.default_child
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
