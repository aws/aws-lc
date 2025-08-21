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
    LINUX_X86_ECR_REPO,
    LINUX_AARCH_ECR_REPO,
    WINDOWS_X86_ECR_REPO,
    PIPELINE_ACCOUNT,
    PIPELINE_REGION,
    DEPLOY_ACCOUNT,
    DEPLOY_REGION,
)

# Initialize app.
app = App()

AwsLcCiPipeline(
    app,
    "AwsLcCiPipeline",
    env=Environment(account=PIPELINE_ACCOUNT, region=PIPELINE_REGION),
)

if DEPLOY_ACCOUNT and DEPLOY_REGION:
    # Initialize env.
    env = Environment(account=DEPLOY_ACCOUNT, region=DEPLOY_REGION)

    # Define AWS ECR stacks.
    # ECR holds the docker images, which are pre-built to accelerate the code builds/tests of git pull requests.
    EcrStack(app, "aws-lc-ecr-linux-x86", LINUX_X86_ECR_REPO, env=env)
    EcrStack(app, "aws-lc-ecr-linux-aarch", LINUX_AARCH_ECR_REPO, env=env)
    EcrStack(app, "aws-lc-ecr-windows-x86", WINDOWS_X86_ECR_REPO, env=env)

    # Define CodeBuild Batch job for building Docker images.
    LinuxDockerImageBatchBuildStack(app, "aws-lc-docker-image-build-linux", env=env)

    # AWS CodeBuild cannot build Windows Docker images because DIND (Docker In Docker) is not supported on Windows.
    # Windows Docker images are created by running commands in Windows EC2 instance.
    WindowsDockerImageBuildStack(app, "aws-lc-docker-image-build-windows", env=env)

    add_ci_stacks(app, env=env)

app.synth()
