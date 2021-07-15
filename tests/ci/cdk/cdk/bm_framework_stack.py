# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
import aws_cdk.core
from aws_cdk import core, aws_ec2 as ec2, aws_codebuild as codebuild, aws_iam as iam, aws_s3 as s3
from util.metadata import AWS_ACCOUNT, AWS_REGION, GITHUB_REPO_OWNER, GITHUB_REPO_NAME
from util.ecr_util import ecr_arn
from util.iam_policies import code_build_batch_policy_in_json, s3_read_write_policy_in_json, ec2_get_put_describe_policy_in_json
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
        ec2_get_put_describe_policy = iam.PolicyDocument.from_json(ec2_get_put_describe_policy_in_json())
        codebuild_inline_policies = {"code_build_batch_policy": code_build_batch_policy,
                                     "ec2_get_put_describe_policy": ec2_get_put_describe_policy}
        codebuild_role = iam.Role(scope=self,
                        id="{}-codebuild-role".format(id),
                        assumed_by=iam.ServicePrincipal("codebuild.amazonaws.com"),
                        inline_policies=codebuild_inline_policies)

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

        # define things needed for ec2 instance below
        S3_PROD_BUCKET = "{}-prod-bucket".format(id)

        # create iam for ec2s
        s3_read_write_policy = iam.PolicyDocument.from_json(s3_read_write_policy_in_json(S3_PROD_BUCKET))
        ec2_inline_policies = {"s3_read_write_policy": s3_read_write_policy}
        ec2_role = iam.Role(scope=self, id="{}-ec2-role".format(id),
                            assumed_by=iam.ServicePrincipal("ec2.amazonaws.com"),
                            inline_policies=ec2_inline_policies)

        # create vpc for ec2s
        vpc = ec2.Vpc(self, id="{}-ec2-vpc".format(id))

        # create security group with default rules
        sec_group = ec2.SecurityGroup(self, id="{}-ec2-sg".format(id),
                                      allow_all_outbound=True,
                                      vpc=vpc,
                                      security_group_name='bm_framework_ec2_sg')

        # We want Ubuntu 20.04 AMI for x86
        ubuntu2004 = ec2.MachineImage.generic_linux({
            "us-west-2": "ami-01773ce53581acf22"
        })

        # Create an EBS block device volume for use by the block_device
        block_device_volume = ec2.BlockDeviceVolume.ebs(volume_size=200, delete_on_termination=True)

        # Create an EBS block device for usage by the ec2 instance
        block_device = ec2.BlockDevice(device_name="/dev/sda1", volume=block_device_volume)

        # commands for the ec2 to run on startup
        command1 = "printf '[Unit]\n" \
                   "  Description=/etc/rc.local Compatibility\n" \
                   "  ConditionPathExists=/etc/rc.local\n" \
                   "[Service]\n" \
                   "  Type=forking\n" \
                   "  ExecStart=/etc/rc.local start\n" \
                   "  TimeoutSec=0\n" \
                   "  StandardOutput=tty\n" \
                   "  RemainAfterExit=yes\n" \
                   "  SysVStartPriority=99\n\n" \
                   "[Install]\n" \
                   "  WantedBy=multi-user.target'" \
                   " | sudo tee -a /etc/systemd/system/rc-local.service"

        command2 = "printf '#!/bin/bash\n" \
                   "echo hi > hi.txt; aws s3 mv hi.txt s3://aws-lc-bm-framework-prod-bucket'" \
                   " | sudo tee -a /etc/rc.local"

        command3 = "sudo chmod +x /etc/rc.local; " \
                   "sudo systemctl enable rc-local.service; " \
                   "sudo systemctl start rc-local.service"

        x86_instance = ec2.Instance(self, id="{}-ec2-x86".format(id),
                                    instance_type=ec2.InstanceType("c5.metal"),
                                    machine_image=ubuntu2004,
                                    vpc=vpc,
                                    security_group=sec_group,
                                    block_devices=[block_device],
                                    role=ec2_role)
        x86_instance.add_user_data(command1)
        x86_instance.add_user_data(command2)
        x86_instance.add_user_data(command3)

        core.Tags.of(x86_instance).add("aws-lc", "{}-ec2-x86-instance".format(id))

        # define s3 buckets below
        production_results_s3 = s3.Bucket(self, "{}-s3-prod".format(id),
                                          bucket_name=S3_PROD_BUCKET,
                                          enforce_ssl=True)

        production_results_s3.grant_put(ec2_role)
