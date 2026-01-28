# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
import typing

from aws_cdk import (
    aws_iam as iam,
    aws_devicefarm as devicefarm,
    Stack,
    Environment,
)
from dataclasses import dataclass
from constructs import Construct


@dataclass
class DeviceFarmCiProps:
    project_arn: str
    android_pool: str
    android_fips_pool: str


class AwsLcDeviceFarmCiStack(Stack):
    """Define a stack used to execute AWS-LC self-hosted GitHub Actions Runners."""

    def __init__(
        self,
        scope: Construct,
        id: str,
        env: typing.Union[Environment, typing.Dict[str, typing.Any]],
        **kwargs
    ) -> None:
        super().__init__(scope, id, env=env, **kwargs)

        project = devicefarm.CfnProject(self, "DeviceFarmProject",
                                        name='aws-lc-ci')

        android_pool = devicefarm.CfnDevicePool(self, 'AndroidPool',
                                                name='android',
                                                project_arn=project.attr_arn,
                                                description='Android Device Pool',
                                                rules=[{
                                                    "attribute": "PLATFORM",
                                                    "operator": "EQUALS",
                                                    "value": "\"ANDROID\""
                                                },
                                                    {
                                                    "attribute": "OS_VERSION",
                                                    "operator": "GREATER_THAN",
                                                    "value": "\"9\""
                                                },
                                                    {
                                                    "attribute": "AVAILABILITY",
                                                    "operator": "EQUALS",
                                                    "value": "\"HIGHLY_AVAILABLE\""
                                                }],
                                                max_devices=2)

        android_pool_fips = devicefarm.CfnDevicePool(self, 'AndroidPoolFips',
                                                     name='android-fips',
                                                     project_arn=project.attr_arn,
                                                     description='Android Device Pool (FIPS)',
                                                     rules=[
                                                         {
                                                             "attribute": "PLATFORM",
                                                             "operator": "EQUALS",
                                                             "value": "\"ANDROID\""
                                                         },
                                                         {
                                                             "attribute": "OS_VERSION",
                                                             "operator": "GREATER_THAN",
                                                             "value": "\"10\""
                                                         },
                                                         {
                                                             "attribute": "AVAILABILITY",
                                                             "operator": "EQUALS",
                                                             "value": "\"HIGHLY_AVAILABLE\""
                                                         }
                                                     ],
                                                     max_devices=2)
        
        self.props = DeviceFarmCiProps(
            project_arn=project.attr_arn,
            android_pool=android_pool.attr_arn,
            android_fips_pool=android_pool_fips.attr_arn,
        )
