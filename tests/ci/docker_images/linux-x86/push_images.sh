#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source ./common.sh

if [ -z ${1+x} ]; then
  ECS_REPO="620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-linux-x86"
else
  ECS_REPO=$1
fi

echo "Uploading docker images to ${ECS_REPO}."

$(aws ecr get-login --no-include-email)

# Tag images with date to help find old images, CodeBuild uses the latest tag and gets updated automatically
tag_and_push_img 'ubuntu-16.04:gcc-5x' "${ECS_REPO}:ubuntu-16.04_gcc-5x"
tag_and_push_img 'ubuntu-18.04:gcc-7x' "${ECS_REPO}:ubuntu-18.04_gcc-7x"
tag_and_push_img 'ubuntu-18.04:clang-6x' "${ECS_REPO}:ubuntu-18.04_clang-6x"
tag_and_push_img 'ubuntu-20.04:clang-7x' "${ECS_REPO}:ubuntu-20.04_clang-7x"
tag_and_push_img 'ubuntu-20.04:clang-8x' "${ECS_REPO}:ubuntu-20.04_clang-8x"
tag_and_push_img 'ubuntu-20.04:clang-9x' "${ECS_REPO}:ubuntu-20.04_clang-9x"
tag_and_push_img 'ubuntu-20.04:clang-10x' "${ECS_REPO}:ubuntu-20.04_clang-10x"
tag_and_push_img 'ubuntu-20.04:clang-7x-bm-framework' "${ECS_REPO}:ubuntu-20.04_clang-7x-bm-framework"
tag_and_push_img 'ubuntu-20.04:cryptofuzz' "${ECS_REPO}:ubuntu-20.04_cryptofuzz"
tag_and_push_img 'ubuntu-20.04:clang-10x_formal-verification' "${ECS_REPO}:ubuntu-20.04_clang-10x_formal-verification"
tag_and_push_img 'ubuntu-20.04:gcc-7x' "${ECS_REPO}:ubuntu-20.04_gcc-7x"
tag_and_push_img 'ubuntu-20.04:gcc-8x' "${ECS_REPO}:ubuntu-20.04_gcc-8x"
tag_and_push_img 'centos-7:gcc-4x' "${ECS_REPO}:centos-7_gcc-4x"
tag_and_push_img 'amazonlinux-2:gcc-7x' "${ECS_REPO}:amazonlinux-2_gcc-7x"
tag_and_push_img 'amazonlinux-2:clang-7x' "${ECS_REPO}:amazonlinux-2_clang-7x"
tag_and_push_img 'amazonlinux-2:gcc-7x-intel-sde' "${ECS_REPO}:amazonlinux-2_gcc-7x_intel-sde"
tag_and_push_img 'fedora-31:clang-9x' "${ECS_REPO}:fedora-31_clang-9x"

#################################
# Push images used by aws-c-cal #
#################################
source ./aws-crt/aws-crt-common.sh
push_aws_crt_docker_img
