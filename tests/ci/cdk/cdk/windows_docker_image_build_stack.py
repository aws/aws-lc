# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    Stack,
    Tags,
    PhysicalName,
    Environment,
    aws_ec2 as ec2,
    aws_s3 as s3,
    aws_iam as iam,
    aws_ssm as ssm,
)
from constructs import Construct

from util.iam_policies import (
    ecr_power_user_policy_in_json,
    s3_read_write_policy_in_json,
)
from util.metadata import (
    WINDOWS_X86_ECR_REPO,
    GITHUB_REPO_OWNER,
    WIN_EC2_TAG_KEY,
    WIN_EC2_TAG_VALUE,
    SSM_DOCUMENT_NAME,
    GITHUB_SOURCE_VERSION,
    S3_FOR_WIN_DOCKER_IMG_BUILD,
)
from util.yml_loader import YmlLoader


class WindowsDockerImageBuildStack(Stack):
    """Define a temporary stack used to build Windows Docker images."""

    def __init__(
        self,
        scope: Construct,
        id: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs,
    ) -> None:
        super().__init__(scope, id, env=env, **kwargs)

        # Define SSM command document.
        # ecr_uri = ecr_windows_x86.ecr_repo.repository_uri
        ecr_repo = "{}.dkr.ecr.{}.amazonaws.com/{}".format(
            env.account, env.region, WINDOWS_X86_ECR_REPO
        )

        placeholder_map = {
            "ECR_PLACEHOLDER": ecr_repo,
            "GITHUB_OWNER_PLACEHOLDER": GITHUB_REPO_OWNER,
            "REGION_PLACEHOLDER": env.region,
            "GITHUB_SOURCE_VERSION_PLACEHOLDER": GITHUB_SOURCE_VERSION,
        }
        content = YmlLoader.load(
            "./cdk/ssm/windows_docker_build_ssm_document.yaml", placeholder_map
        )

        ssm.CfnDocument(
            scope=self,
            id="{}-ssm-document".format(id),
            name=SSM_DOCUMENT_NAME,
            content=content,
            document_type="Command",
            update_method="NewVersion",
        )

        # Define a S3 bucket to store windows docker files and build scripts.
        bucket = s3.Bucket(
            scope=self,
            id="{}-s3".format(id),
            bucket_name=f"{env.account}-{S3_FOR_WIN_DOCKER_IMG_BUILD}",
            block_public_access=s3.BlockPublicAccess.BLOCK_ALL,
        )

        # Define a role for EC2.
        ecr_power_user_policy = iam.PolicyDocument.from_json(
            ecr_power_user_policy_in_json([WINDOWS_X86_ECR_REPO], env)
        )
        s3_read_write_policy = iam.PolicyDocument.from_json(
            s3_read_write_policy_in_json(bucket.bucket_name)
        )
        inline_policies = {
            "ecr_power_user_policy": ecr_power_user_policy,
            "s3_read_write_policy": s3_read_write_policy,
        }
        role = iam.Role(
            scope=self,
            id="{}-role".format(id),
            assumed_by=iam.ServicePrincipal("ec2.amazonaws.com"),
            inline_policies=inline_policies,
            managed_policies=[
                iam.ManagedPolicy.from_aws_managed_policy_name(
                    "AmazonSSMManagedInstanceCore"
                )
            ],
        )

        # Define Windows EC2 instance, where the SSM document will be executed.
        machine_image = ec2.MachineImage.latest_windows(
            ec2.WindowsVersion.WINDOWS_SERVER_2019_ENGLISH_FULL_BASE
        )
        vpc = ec2.Vpc(
            scope=self,
            id="{}-vpc".format(id),
            nat_gateways=1 # minimize the number of idle NAT gateways and thus elastic IPs
        )
        block_device_volume = ec2.BlockDeviceVolume.ebs(
            volume_size=200, delete_on_termination=True
        )
        block_device = ec2.BlockDevice(
            device_name="/dev/sda1", volume=block_device_volume
        )

        setup_user_data = ec2.UserData.for_windows()
        setup_user_data.add_commands(
            "Install-WindowsFeature -Name Containers -IncludeAllSubFeature -IncludeManagementTools",
            "Set-ExecutionPolicy Bypass -Scope Process -Force; [Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor [Net.SecurityProtocolType]::Tls12; $env:chocolateyUseWindowsCompression = 'true'; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://chocolatey.org/install.ps1')) | Out-Null",
            "choco install docker-cli -y",
            "choco install docker-engine -y",
            "choco install git --version 2.23.0 -y",
            "Set-Service -Name docker -StartupType Automatic",
            "Restart-Computer -Force",
        )

        instance = ec2.Instance(
            scope=self,
            id="{}-instance".format(id),
            instance_type=ec2.InstanceType(instance_type_identifier="m5d.xlarge"),
            vpc=vpc,
            role=role,
            block_devices=[block_device],
            vpc_subnets=ec2.SubnetSelection(subnet_type=ec2.SubnetType.PUBLIC),
            machine_image=machine_image,
            user_data=setup_user_data,
            instance_name="{}-instance".format(id),
        )

        Tags.of(instance).add(WIN_EC2_TAG_KEY, WIN_EC2_TAG_VALUE)

        self.output = {
            "s3_bucket_name": f"{env.account}-{S3_FOR_WIN_DOCKER_IMG_BUILD}",
        }
