# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core, aws_ec2 as ec2
from util.metadata import AWS_ACCOUNT, AWS_REGION, GITHUB_REPO_OWNER, GITHUB_REPO_NAME

# detailed documentation can be found here: https://docs.aws.amazon.com/cdk/api/latest/docs/aws-ec2-readme.html

class BmFrameworkStack(core.Stack):
    """Define a stack used to execute the AWS-LC benchmarking framework"""

    def __init__(self,
                 scope: core.Construct,
                 id: str,
                 **kwargs) -> None:
        super().__init__(scope, id, **kwargs)

        # create vpc for security
        vpc = ec2.Vpc(self, 'VPC')

        # create security group with default rules
        sec_group = ec2.SecurityGroup(self, 'Security Group',
                                    description='temp desc.',
                                    allow_all_outbound=True,
                                    vpc=vpc)

        # We want Ubuntu 20.04 AMI for x86
        ubuntu2004 = ec2.MachineImage.generic_linux({
            "us-west-2": "ami-01773ce53581acf22"
        })

        # commands to run on startup
        startup_commands = 'echo hi'

        # TODO: create vpc endpoint for s3 to connect to ec2s
        x86_ubuntu2004_clang7 = ec2.Instance(self, 'bm_framework_x86_ubuntu-20.04_clang7',
                                             instance_type=ec2.InstanceType("c5.metal"),
                                             machine_image=ubuntu2004,
                                             vpc=vpc,
                                             security_group = sec_group)
        x86_ubuntu2004_clang7.add_user_data(startup_commands)