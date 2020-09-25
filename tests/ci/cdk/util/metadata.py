#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from util.env_util import EnvUtil

# Used when AWS CDK defines AWS resources.
AWS_ACCOUNT = EnvUtil.get("CDK_DEPLOY_ACCOUNT", "654358955777")
AWS_REGION = EnvUtil.get("CDK_DEPLOY_REGION", "us-west-2")

# Used when AWS CDK defines ECR repos.
LINUX_AARCH_ECR_REPO = EnvUtil.get("ECR_LINUX_AARCH_REPO_NAME", "aws-lc-docker-images-linux-aarch")
LINUX_X86_ECR_REPO = EnvUtil.get("ECR_LINUX_X86_REPO_NAME", "aws-lc-docker-images-linux-x86")
WINDOWS_ECR_REPO = EnvUtil.get("ECR_WINDOWS_REPO_NAME", "aws-lc-docker-images-windows")

# Used when AWS CodeBuild needs to create web_hooks.
GITHUB_REPO_OWNER = EnvUtil.get("GITHUB_REPO_OWNER", "bryce-shang")
GITHUB_REPO_NAME = EnvUtil.get("GITHUB_REPO", "aws-lc")

# Used when AWS CDK defines resources for Windows docker image build.
S3_BUCKET_NAME = EnvUtil.get("S3_FOR_WIN_DOCKER_IMG_BUILD", "aws-lc-windows-docker-image-build")
WIN_EC2_TAG_KEY = EnvUtil.get("WIN_EC2_TAG_KEY", "aws-lc")
WIN_EC2_TAG_VALUE = EnvUtil.get("WIN_EC2_TAG_VALUE", "aws-lc-windows-docker-image-build")
SSM_DOCUMENT_NAME = EnvUtil.get("WIN_DOCKER_BUILD_SSM_DOCUMENT", "awslc-ssm-windows-docker-img-build-doc")
