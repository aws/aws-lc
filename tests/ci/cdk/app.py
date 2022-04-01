#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from aws_cdk import core

from cdk.bm_framework_stack import BmFrameworkStack
from cdk.aws_lc_analytics_stack import  AwsLcGitHubAnalyticsStack
from cdk.aws_lc_github_ci_stack import AwsLcGitHubCIStack
from cdk.aws_lc_github_fuzz_ci_stack import  AwsLcGitHubFuzzCIStack
from cdk.aws_lc_android_ci_stack import AwsLcAndroidCIStack
from cdk.linux_docker_image_batch_build_stack import LinuxDockerImageBatchBuildStack
from cdk.windows_docker_image_build_stack import WindowsDockerImageBuildStack
from cdk.ecr_stack import EcrStack
from util.metadata import AWS_ACCOUNT, AWS_REGION, LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO, WINDOWS_X86_ECR_REPO

# Initialize app.
app = core.App()

# Initialize env.
env = core.Environment(account=AWS_ACCOUNT, region=AWS_REGION)

# Define AWS ECR stacks.
# ECR holds the docker images, which are pre-built to accelerate the code builds/tests of git pull requests.
EcrStack(app, "aws-lc-ecr-linux-x86", LINUX_X86_ECR_REPO, env=env)
EcrStack(app, "aws-lc-ecr-linux-aarch", LINUX_AARCH_ECR_REPO, env=env)
# TODO: re-enable 'aws-lc-ci-windows-x86' when CryptoAlg-826 is fixed.
# EcrStack(app, "aws-lc-ecr-windows-x86", WINDOWS_X86_ECR_REPO, env=env)

# Define CodeBuild Batch job for building Docker images.
LinuxDockerImageBatchBuildStack(app, "aws-lc-docker-image-build-linux", env=env)

# TODO: re-enable 'aws-lc-ci-windows-x86' when CryptoAlg-826 is fixed.
# # AWS CodeBuild cannot build Windows Docker images because DIND (Docker In Docker) is not supported on Windows.
# # Windows Docker images are created by running commands in Windows EC2 instance.
# WindowsDockerImageBuildStack(app, "aws-lc-docker-image-build-windows", env=env)

# Define CodeBuild Batch job for testing code.
x86_build_spec_file = "./cdk/codebuild/github_ci_linux_x86_omnibus.yaml"
AwsLcGitHubCIStack(app, "aws-lc-ci-linux-x86", LINUX_X86_ECR_REPO, x86_build_spec_file, env=env)
arm_build_spec_file = "./cdk/codebuild/github_ci_linux_arm_omnibus.yaml"
AwsLcGitHubCIStack(app, "aws-lc-ci-linux-arm", LINUX_AARCH_ECR_REPO, arm_build_spec_file, env=env)
# TODO: re-enable 'aws-lc-ci-windows-x86' when CryptoAlg-826 is fixed.
# win_x86_build_spec_file = "./cdk/codebuild/github_ci_windows_x86_omnibus.yaml"
# AwsLcGitHubCIStack(app, "aws-lc-ci-windows-x86", WINDOWS_X86_ECR_REPO, win_x86_build_spec_file, env=env)
fuzz_build_spec_file = "cdk/codebuild/github_ci_fuzzing_omnibus.yaml"
AwsLcGitHubFuzzCIStack(app, "aws-lc-ci-fuzzing", LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO, fuzz_build_spec_file, env=env)
analytics_build_spec_file = "cdk/codebuild/github_ci_analytics_omnibus.yaml"
AwsLcGitHubAnalyticsStack(app, "aws-lc-ci-analytics", LINUX_X86_ECR_REPO, LINUX_AARCH_ECR_REPO, analytics_build_spec_file, env=env)
# TODO: re-enable 'aws-lc-ci-bm-framework' when it's ready.
# bm_framework_build_spec_file = "./cdk/codebuild/bm_framework_omnibus.yaml"
# BmFrameworkStack(app, "aws-lc-ci-bm-framework", LINUX_X86_ECR_REPO, bm_framework_build_spec_file, env=env)
android_build_spec_file = "cdk/codebuild/github_ci_android_omnibus.yaml"
AwsLcAndroidCIStack(app, "aws-lc-ci-devicefarm-android", LINUX_X86_ECR_REPO, android_build_spec_file, env=env)

app.synth()
