# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import Stack, Tags, aws_ec2 as ec2, aws_s3 as s3, aws_iam as iam, aws_ssm as ssm
from constructs import Construct
from util.iam_policies import ecr_power_user_policy_in_json, s3_read_write_policy_in_json
from util.metadata import AWS_ACCOUNT, AWS_REGION, WINDOWS_X86_ECR_REPO, S3_BUCKET_NAME, GITHUB_REPO_OWNER, WIN_EC2_TAG_KEY, \
    WIN_EC2_TAG_VALUE, SSM_DOCUMENT_NAME, GITHUB_SOURCE_VERSION
from util.yml_loader import YmlLoader


class WindowsDockerImageBuildStack(Stack):
    """Define a temporary stack used to build Windows Docker images. After build, this stack will be destroyed."""

    def __init__(self,
                 scope: Construct,
                 id: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Define SSM command document.
        ecr_repo = "{}.dkr.ecr.{}.amazonaws.com/{}".format(AWS_ACCOUNT, AWS_REGION, WINDOWS_X86_ECR_REPO)
        placeholder_map = {"ECR_PLACEHOLDER": ecr_repo, "GITHUB_OWNER_PLACEHOLDER": GITHUB_REPO_OWNER,
                           "REGION_PLACEHOLDER": AWS_REGION, "GITHUB_SOURCE_VERSION_PLACEHOLDER": GITHUB_SOURCE_VERSION}
        content = YmlLoader.load("./cdk/ssm/windows_docker_build_ssm_document.yaml", placeholder_map)
        ssm.CfnDocument(scope=self,
                        id="{}-ssm-document".format(id),
                        name=SSM_DOCUMENT_NAME,
                        content=content,
                        document_type="Command")

        # Define a S3 bucket to store windows docker files and build scripts.
        s3.Bucket(scope=self,
                  id="{}-s3".format(id),
                  bucket_name=S3_BUCKET_NAME,
                  block_public_access=s3.BlockPublicAccess.BLOCK_ALL)

        # Define a role for EC2.
        ecr_power_user_policy = iam.PolicyDocument.from_json(ecr_power_user_policy_in_json([WINDOWS_X86_ECR_REPO]))
        s3_read_write_policy = iam.PolicyDocument.from_json(s3_read_write_policy_in_json(S3_BUCKET_NAME))
        inline_policies = {"ecr_power_user_policy": ecr_power_user_policy, "s3_read_write_policy": s3_read_write_policy}
        role = iam.Role(scope=self, id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("ec2.amazonaws.com"),
                        inline_policies=inline_policies,
                        managed_policies=[
                            iam.ManagedPolicy.from_aws_managed_policy_name("AmazonSSMManagedInstanceCore")
                        ])

        # Define Windows EC2 instance, where the SSM document will be executed.
        # TODO: This AMI does not have docker installed by default anymore. Find another Windows machine
        #       that has docker by default or update the ssm document to properly install docker.
        machine_image = ec2.MachineImage.latest_windows(
            ec2.WindowsVersion.WINDOWS_SERVER_2019_ENGLISH_FULL_BASE)
        vpc = ec2.Vpc(scope=self, id="{}-vpc".format(id))
        block_device_volume = ec2.BlockDeviceVolume.ebs(volume_size=200, delete_on_termination=True)
        block_device = ec2.BlockDevice(device_name="/dev/sda1", volume=block_device_volume)
        instance = ec2.Instance(scope=self,
                                id="{}-instance".format(id),
                                instance_type=ec2.InstanceType(instance_type_identifier="m5d.xlarge"),
                                vpc=vpc,
                                role=role,
                                block_devices=[block_device],
                                vpc_subnets=ec2.SubnetSelection(subnet_type=ec2.SubnetType.PUBLIC),
                                machine_image=machine_image)

        Tags.of(instance).add(WIN_EC2_TAG_KEY, WIN_EC2_TAG_VALUE)
