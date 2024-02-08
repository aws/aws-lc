#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source ./common.sh

if [ -z ${1+x} ]; then
  ECS_REPO="620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-linux-aarch"
else
  ECS_REPO=$1
fi

echo "Uploading docker images to ${ECS_REPO}."

$(aws ecr get-login --no-include-email --region us-west-2)

# Tag images with date to help find old images, CodeBuild uses the latest tag and gets updated automatically
tag_and_push_img 'amazonlinux-2-aarch:gcc-7x' "${ECS_REPO}:amazonlinux-2_gcc-7x"
tag_and_push_img 'amazonlinux-2-aarch:clang-7x' "${ECS_REPO}:amazonlinux-2_clang-7x"
tag_and_push_img 'amazonlinux-2023-aarch:gcc-11x' "${ECS_REPO}:amazonlinux-2023_gcc-11x"
tag_and_push_img 'amazonlinux-2023-aarch:clang-15x' "${ECS_REPO}:amazonlinux-2023_clang-15x"
tag_and_push_img 'amazonlinux-2023-aarch:clang-15x-sanitizer' "${ECS_REPO}:amazonlinux-2023_clang-15x_sanitizer"
tag_and_push_img 'amazonlinux-2023-aarch:cryptofuzz' "${ECS_REPO}:amazonlinux-2023_clang-15x_cryptofuzz"
tag_and_push_img 'ubuntu-20.04-aarch:gcc-7x' "${ECS_REPO}:ubuntu-20.04_gcc-7x"
tag_and_push_img 'ubuntu-20.04-aarch:gcc-8x' "${ECS_REPO}:ubuntu-20.04_gcc-8x"
tag_and_push_img 'ubuntu-20.04-aarch:clang-7x' "${ECS_REPO}:ubuntu-20.04_clang-7x"
tag_and_push_img 'ubuntu-20.04-aarch:clang-8x' "${ECS_REPO}:ubuntu-20.04_clang-8x"
tag_and_push_img 'ubuntu-20.04-aarch:clang-9x' "${ECS_REPO}:ubuntu-20.04_clang-9x"
tag_and_push_img 'ubuntu-20.04-aarch:clang-10x' "${ECS_REPO}:ubuntu-20.04_clang-10x"
tag_and_push_img 'ubuntu-20.04-aarch:clang-7x-bm-framework' "${ECS_REPO}:ubuntu-20.04_clang-7x-bm-framework"
tag_and_push_img 'ubuntu-22.04-aarch:gcc-11x' "${ECS_REPO}:ubuntu-22.04_gcc-11x"
tag_and_push_img 'ubuntu-22.04-aarch:gcc-12x' "${ECS_REPO}:ubuntu-22.04_gcc-12x"
