#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from aws_cdk import Environment, App

from cdk.linux_docker_image_batch_build_stack import LinuxDockerImageBatchBuildStack
from pipeline.ci_util import add_ci_stacks
from pipeline.pipeline_stack import AwsLcCiPipeline
from cdk.windows_docker_image_build_stack import WindowsDockerImageBuildStack
from cdk.ecr_stack import EcrStack
from util.metadata import (
    PIPELINE_ACCOUNT,
    PIPELINE_REGION,
)

# Initialize app.
app = App()

AwsLcCiPipeline(
    app,
    "AwsLcCiPipeline",
    env=Environment(account=PIPELINE_ACCOUNT, region=PIPELINE_REGION),
)

app.synth()
