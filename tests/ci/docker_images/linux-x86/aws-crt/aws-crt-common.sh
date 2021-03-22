#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

#################################
# Set up environment variables #
#################################

if [[ -z "${ECS_REPO+x}" || -z "${ECS_REPO}" ]]; then
  export ECS_REPO="620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-linux-x86"
fi

if [[ -z "${GITHUB_REPO_OWNER+x}" || -z "${GITHUB_REPO_OWNER}" ]]; then
  # The owner of the GitHub personal access token. Required when login 'docker.pkg.github.com'.
  export GITHUB_REPO_OWNER='awslabs'
fi

# Environment variables used by AWS-C-CAL
# CI of AWS-C-CAL https://github.com/awslabs/aws-c-cal/blob/905b0fd0ff2ca0d86c7e49b8ef4b636bac4600ea/.github/workflows/ci.yml
# The CI uses Docker images provided by https://github.com/awslabs/aws-crt-builder
BUILDER_VERSION='v0.7.2'
BASE_AWS_CRT_DOCKER_IMG_PREFIX='docker.pkg.github.com/awslabs/aws-crt-builder'
AWS_CRT_MANY_LINUX_SUFFIXES=('aws-crt-manylinux1-x64' 'aws-crt-manylinux1-x86' 'aws-crt-manylinux2014-x64' 'aws-crt-manylinux2014-x86')
AWS_CRT_AL2_X64_SUFFIX='aws-crt-al2-x64'
AWS_CRT_AL2_X64="${BASE_AWS_CRT_DOCKER_IMG_PREFIX}/${AWS_CRT_AL2_X64_SUFFIX}:${BUILDER_VERSION}"
AWS_CRT_UBUNTU_16_X64_SUFFIX='aws-crt-ubuntu-16-x64'
AWS_CRT_UBUNTU_16_X64="${BASE_AWS_CRT_DOCKER_IMG_PREFIX}/${AWS_CRT_UBUNTU_16_X64_SUFFIX}:${BUILDER_VERSION}"

####################################
# Migrate Docker images to AWS ECR #
####################################

function login_github_docker_pkg() {
  if [[ -z "${GITHUB_READ_PKG_ACCESS_TOKEN+x}" || -z "${GITHUB_READ_PKG_ACCESS_TOKEN}" ]]; then
    # GITHUB_READ_PKG_ACCESS_TOKEN is required when pulling images from 'docker.pkg.github.com'.
    # When creating GitHub personal access token, make sure ONLY "read:packages" is granted.
    # https://docs.github.com/en/github/authenticating-to-github/creating-a-personal-access-token
    # https://docs.github.com/en/packages/learn-github-packages/about-github-packages#authenticating-to-github-packages
    echo "GITHUB_READ_PKG_ACCESS_TOKEN is not defined or empty."
    exit 1
  fi
  echo "${GITHUB_READ_PKG_ACCESS_TOKEN}" | docker login docker.pkg.github.com -u "${GITHUB_REPO_OWNER}" --password-stdin
}

function pull_aws_crt_docker_img() {
  # Pull aws-crt-manylinux*:v0.7.2
  for i in "${AWS_CRT_MANY_LINUX_SUFFIXES[@]}"; do
    docker_img="${BASE_AWS_CRT_DOCKER_IMG_PREFIX}/${i}:${BUILDER_VERSION}"
    docker pull "${docker_img}"
  done
  # Pull aws-crt-al2-x64:v0.7.2
  docker pull "${AWS_CRT_AL2_X64}"
  # Pull aws-crt-ubuntu-16-x64:v0.7.2
  docker pull "${AWS_CRT_UBUNTU_16_X64}"
}

function push_aws_crt_docker_img() {
  # Push aws-crt-manylinux*_v0.7.2
  for i in "${AWS_CRT_MANY_LINUX_SUFFIXES[@]}"; do
    source_docker_img="${BASE_AWS_CRT_DOCKER_IMG_PREFIX}/${i}:${BUILDER_VERSION}"
    target_docker_img="${ECS_REPO}:${i}_${BUILDER_VERSION}"
    tag_and_push_img "${source_docker_img}" "${target_docker_img}"
  done
  # Push aws-crt-al2-x64_v0.7.2
  target_aws_art_al2_x64="${ECS_REPO}:${AWS_CRT_AL2_X64_SUFFIX}_${BUILDER_VERSION}"
  tag_and_push_img "${AWS_CRT_AL2_X64}" "${target_aws_art_al2_x64}"
  # Push aws-crt-ubuntu-16-x64_v0.7.2
  target_aws_art_ubuntu_16_x64="${ECS_REPO}:${AWS_CRT_UBUNTU_16_X64_SUFFIX}_${BUILDER_VERSION}"
  tag_and_push_img "${AWS_CRT_UBUNTU_16_X64}" "${target_aws_art_ubuntu_16_x64}"
}
