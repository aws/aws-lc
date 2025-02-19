#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source ./common.sh

if [ -z ${1+x} ]; then
  ECS_REPO="620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-docker-images-linux-x86"
else
  ECS_REPO=$1
fi

echo "Uploading docker images to ${ECS_REPO}."

$(aws ecr get-login --no-include-email --region us-west-2)

# Tag images with date to help find old images, CodeBuild uses the latest tag and gets updated automatically
tag_and_push_img 'ubuntu-16.04:gcc-5x' "${ECS_REPO}:ubuntu-16.04_gcc-5x"
tag_and_push_img 'ubuntu-18.04:gcc-7x' "${ECS_REPO}:ubuntu-18.04_gcc-7x"
tag_and_push_img 'ubuntu-18.04:clang-6x' "${ECS_REPO}:ubuntu-18.04_clang-6x"
tag_and_push_img 'ubuntu-20.04:clang-7x' "${ECS_REPO}:ubuntu-20.04_clang-7x"
tag_and_push_img 'ubuntu-20.04:clang-8x' "${ECS_REPO}:ubuntu-20.04_clang-8x"
tag_and_push_img 'ubuntu-20.04:clang-9x' "${ECS_REPO}:ubuntu-20.04_clang-9x"
tag_and_push_img 'ubuntu-20.04:clang-10x' "${ECS_REPO}:ubuntu-20.04_clang-10x"
tag_and_push_img 'ubuntu-20.04:android' "${ECS_REPO}:ubuntu-20.04_android"
tag_and_push_img 'ubuntu-20.04:clang-7x-bm-framework' "${ECS_REPO}:ubuntu-20.04_clang-7x-bm-framework"
tag_and_push_img 'ubuntu-20.04:clang-10x_formal-verification-saw-x86_64' "${ECS_REPO}:ubuntu-20.04_clang-10x_formal-verification-saw-x86_64"
tag_and_push_img 'ubuntu-20.04:clang-10x_formal-verification-saw-x86_64-aes-gcm' "${ECS_REPO}:ubuntu-20.04_clang-10x_formal-verification-saw-x86_64-aes-gcm"
tag_and_push_img 'ubuntu-20.04:clang-10x_formal-verification-saw-aarch64' "${ECS_REPO}:ubuntu-20.04_clang-10x_formal-verification-saw-aarch64"
tag_and_push_img 'ubuntu-20.04:gcc-7x' "${ECS_REPO}:ubuntu-20.04_gcc-7x"
tag_and_push_img 'ubuntu-20.04:gcc-8x' "${ECS_REPO}:ubuntu-20.04_gcc-8x"
tag_and_push_img 'ubuntu-22.04:clang-14x-sde' "${ECS_REPO}:ubuntu-22.04_clang-14x-sde"
tag_and_push_img 'ubuntu-22.04:gcc-10x' "${ECS_REPO}:ubuntu-22.04_gcc-10x"
tag_and_push_img 'ubuntu-22.04:gcc-11x' "${ECS_REPO}:ubuntu-22.04_gcc-11x"
tag_and_push_img 'ubuntu-22.04:gcc-12x' "${ECS_REPO}:ubuntu-22.04_gcc-12x"
tag_and_push_img 'ubuntu-22.04:gcc-12x_integration' "${ECS_REPO}:ubuntu-22.04_gcc-12x_integration"
tag_and_push_img 'ubuntu-22.04:clang-14x_formal-verification-nsym-aarch64' "${ECS_REPO}:ubuntu-22.04_clang-14x_formal-verification-nsym-aarch64"
tag_and_push_img 'centos-7:gcc-4x' "${ECS_REPO}:centos-7_gcc-4x"
tag_and_push_img 'centos-8:gcc-8x' "${ECS_REPO}:centos-8_gcc-8x"
tag_and_push_img 'amazonlinux-2:gcc-7x' "${ECS_REPO}:amazonlinux-2_gcc-7x"
tag_and_push_img 'amazonlinux-2:gcc-7x-intel-sde' "${ECS_REPO}:amazonlinux-2_gcc-7x_intel-sde"
tag_and_push_img 'amazonlinux-2:clang-7x' "${ECS_REPO}:amazonlinux-2_clang-7x"
tag_and_push_img 'amazonlinux-2023:gcc-11x' "${ECS_REPO}:amazonlinux-2023_gcc-11x"
tag_and_push_img 'amazonlinux-2023:clang-15x' "${ECS_REPO}:amazonlinux-2023_clang-15x"
tag_and_push_img 'amazonlinux-2023:clang-15x-sanitizer' "${ECS_REPO}:amazonlinux-2023_clang-15x_sanitizer"
tag_and_push_img 'amazonlinux-2023:cryptofuzz' "${ECS_REPO}:amazonlinux-2023_clang-15x_cryptofuzz"
tag_and_push_img 'amazonlinux-2023:x509' "${ECS_REPO}:amazonlinux-2023_x509"
tag_and_push_img 'fedora-31:clang-9x' "${ECS_REPO}:fedora-31_clang-9x"
tag_and_push_img 'ubuntu-10.04_gcc-4.1x' "${ECS_REPO}:ubuntu-10.04_gcc-4.1x"
