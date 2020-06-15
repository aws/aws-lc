# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_ec2 as ec2, aws_iam as iam, aws_s3 as s3, aws_ssm as ssm
import yaml
from util.util import EnvUtil


class WindowsDockerImageBuildStack(core.Stack):
    """Define a stack used to build Windows Docker images."""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 ecr_repo_name: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # Fetch environment variables.
        s3_bucket_name = EnvUtil.get("S3_FOR_WIN_DOCKER_IMG_BUILD", "windows-docker-images")
        win_ec2_tag_key = EnvUtil.get("WIN_EC2_TAG_KEY", "aws-lc")
        win_ec2_tag_value = EnvUtil.get("WIN_EC2_TAG_VALUE", "aws-lc-windows")
        ssm_document_name = EnvUtil.get("WIN_DOCKER_BUILD_SSM_DOCUMENT", "aws-lc-windows-docker-ssm-doc")

        # Define a S3 bucket to store windows docker files and build scripts.
        s3.Bucket(scope=self,
                  id="{}-s3".format(id),
                  bucket_name=s3_bucket_name,
                  block_public_access=s3.BlockPublicAccess.BLOCK_ALL)

        # Define SSM command document.
        aws_account_id = kwargs["env"]["account"]
        aws_region = kwargs["env"]["region"]
        ecr_repo = "{}.dkr.ecr.{}.amazonaws.com/{}".format(aws_account_id, aws_region, ecr_repo_name)
        with open('./cdk/windows_docker_build_ssm_document.yaml') as file:
            file_text = file.read().replace("ECR_PLACEHOLDER", ecr_repo) \
                .replace("S3_BUCKET_PLACEHOLDER", s3_bucket_name) \
                .replace("REGION_PLACEHOLDER", aws_region)
            content = yaml.load(file_text, Loader=yaml.FullLoader)
            ssm.CfnDocument(scope=self,
                            id="{}-ssm-document".format(id),
                            name=ssm_document_name,
                            content=content,
                            document_type="Command")

        # Define a role for EC2.
        role = iam.Role(scope=self, id="{}-role".format(id),
                        assumed_by=iam.ServicePrincipal("ec2.amazonaws.com"),
                        managed_policies=[
                            iam.ManagedPolicy.from_aws_managed_policy_name("AmazonSSMManagedInstanceCore"),
                            iam.ManagedPolicy.from_aws_managed_policy_name("AmazonS3FullAccess"),
                            iam.ManagedPolicy.from_aws_managed_policy_name("AmazonEC2ContainerRegistryPowerUser")
                        ])

        # Define Windows EC2 instance, where the SSM document will be executed.
        machine_image = ec2.MachineImage.latest_windows(ec2.WindowsVersion.WINDOWS_SERVER_2016_ENGLISH_FULL_CONTAINERS)
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

        core.Tag.add(instance, win_ec2_tag_key, win_ec2_tag_value)
