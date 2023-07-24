#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

from util.env_util import EnvUtil

# Used when AWS CDK defines AWS resources.
TEAM_ACCOUNT = "620771051181"
DEFAULT_REGION = "us-west-2"
AWS_ACCOUNT = EnvUtil.get("CDK_DEPLOY_ACCOUNT", TEAM_ACCOUNT)
AWS_REGION = EnvUtil.get("CDK_DEPLOY_REGION", DEFAULT_REGION)
# Indicate if the BuildSpec files can be automatically loaded without manualy deployment.
CAN_AUTOLOAD = (AWS_ACCOUNT == TEAM_ACCOUNT) and (AWS_REGION == DEFAULT_REGION)

# Used when AWS CDK defines ECR repos.
LINUX_AARCH_ECR_REPO = EnvUtil.get("ECR_LINUX_AARCH_REPO_NAME", "aws-lc-docker-images-linux-aarch")
LINUX_X86_ECR_REPO = EnvUtil.get("ECR_LINUX_X86_REPO_NAME", "aws-lc-docker-images-linux-x86")
WINDOWS_X86_ECR_REPO = EnvUtil.get("ECR_WINDOWS_X86_REPO_NAME", "aws-lc-docker-images-windows-x86")

# Used when AWS CodeBuild needs to create web_hooks.
GITHUB_REPO_OWNER = EnvUtil.get("GITHUB_REPO_OWNER", "aws")
GITHUB_REPO_NAME = EnvUtil.get("GITHUB_REPO_NAME", "aws-lc")
GITHUB_SOURCE_VERSION = EnvUtil.get("GITHUB_SOURCE_VERSION", "main")
GITHUB_TOKEN_SECRET_NAME = EnvUtil.get("GITHUB_TOKEN_SECRET_NAME", "aws-lc/ci/github/token")

# Used when AWS CDK defines resources for Windows docker image build.
S3_BUCKET_NAME = EnvUtil.get("S3_FOR_WIN_DOCKER_IMG_BUILD", "aws-lc-windows-docker-image-build")
WIN_EC2_TAG_KEY = EnvUtil.get("WIN_EC2_TAG_KEY", "aws-lc")
WIN_EC2_TAG_VALUE = EnvUtil.get("WIN_EC2_TAG_VALUE", "aws-lc-windows-docker-image-build")
SSM_DOCUMENT_NAME = EnvUtil.get("WIN_DOCKER_BUILD_SSM_DOCUMENT", "windows-ssm-document")

GITHUB_PUSH_CI_BRANCH_TARGETS = r"(main|fips-\d{4}-\d{2}-\d{2}.*)"
