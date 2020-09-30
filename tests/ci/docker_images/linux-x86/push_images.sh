#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

if [ -z ${1+x} ]; then
  ECS_REPO="620771051181.dkr.ecr.us-west-2.amazonaws.com/aws-lc-test-docker-images-linux-x86"
else
  ECS_REPO=$1
fi

echo "Uploading docker images to ${ECS_REPO}."

$(aws ecr get-login --no-include-email)

# # Tag images with date to help find old images, CodeBuild uses the latest tag and gets updated automatically
docker tag ubuntu-16.04:gcc-5x ${ECS_REPO}:ubuntu-16.04_gcc-5x_`date +%Y-%m-%d`
docker tag ubuntu-16.04:gcc-5x ${ECS_REPO}:ubuntu-16.04_gcc-5x_latest
docker push ${ECS_REPO}:ubuntu-16.04_gcc-5x_latest
docker push ${ECS_REPO}:ubuntu-16.04_gcc-5x_`date +%Y-%m-%d`

docker tag ubuntu-18.04:gcc-7x ${ECS_REPO}:ubuntu-18.04_gcc-7x_`date +%Y-%m-%d`
docker tag ubuntu-18.04:gcc-7x ${ECS_REPO}:ubuntu-18.04_gcc-7x_latest
docker push ${ECS_REPO}:ubuntu-18.04_gcc-7x_latest
docker push ${ECS_REPO}:ubuntu-18.04_gcc-7x_`date +%Y-%m-%d`

docker tag ubuntu-18.04:clang-6x ${ECS_REPO}:ubuntu-18.04_clang-6x_`date +%Y-%m-%d`
docker tag ubuntu-18.04:clang-6x ${ECS_REPO}:ubuntu-18.04_clang-6x_latest
docker push ${ECS_REPO}:ubuntu-18.04_clang-6x_latest
docker push ${ECS_REPO}:ubuntu-18.04_clang-6x_`date +%Y-%m-%d`

docker tag ubuntu-19.04:gcc-8x ${ECS_REPO}:ubuntu-19.04_gcc-8x_`date +%Y-%m-%d`
docker tag ubuntu-19.04:gcc-8x ${ECS_REPO}:ubuntu-19.04_gcc-8x_latest
docker push ${ECS_REPO}:ubuntu-19.04_gcc-8x_latest
docker push ${ECS_REPO}:ubuntu-19.04_gcc-8x_`date +%Y-%m-%d`

docker tag ubuntu-19.04:clang-8x ${ECS_REPO}:ubuntu-19.04_clang-8x_`date +%Y-%m-%d`
docker tag ubuntu-19.04:clang-8x ${ECS_REPO}:ubuntu-19.04_clang-8x_latest
docker push ${ECS_REPO}:ubuntu-19.04_clang-8x_latest
docker push ${ECS_REPO}:ubuntu-19.04_clang-8x_`date +%Y-%m-%d`

docker tag ubuntu-19.10:gcc-9x ${ECS_REPO}:ubuntu-19.10_gcc-9x_`date +%Y-%m-%d`
docker tag ubuntu-19.10:gcc-9x ${ECS_REPO}:ubuntu-19.10_gcc-9x_latest
docker push ${ECS_REPO}:ubuntu-19.10_gcc-9x_latest
docker push ${ECS_REPO}:ubuntu-19.10_gcc-9x_`date +%Y-%m-%d`

docker tag ubuntu-19.10:clang-9x ${ECS_REPO}:ubuntu-19.10_clang-9x_`date +%Y-%m-%d`
docker tag ubuntu-19.10:clang-9x ${ECS_REPO}:ubuntu-19.10_clang-9x_latest
docker push ${ECS_REPO}:ubuntu-19.10_clang-9x_latest
docker push ${ECS_REPO}:ubuntu-19.10_clang-9x_`date +%Y-%m-%d`

docker tag ubuntu-20.04:gcc-9x ${ECS_REPO}:ubuntu-20.04_gcc-9x_`date +%Y-%m-%d`
docker tag ubuntu-20.04:gcc-9x ${ECS_REPO}:ubuntu-20.04_gcc-9x_latest
docker push ${ECS_REPO}:ubuntu-20.04_gcc-9x_latest
docker push ${ECS_REPO}:ubuntu-20.04_gcc-9x_`date +%Y-%m-%d`

docker tag ubuntu-20.04:clang-10x ${ECS_REPO}:ubuntu-20.04_clang-10x_`date +%Y-%m-%d`
docker tag ubuntu-20.04:clang-10x ${ECS_REPO}:ubuntu-20.04_clang-10x_latest
docker push ${ECS_REPO}:ubuntu-20.04_clang-10x_latest
docker push ${ECS_REPO}:ubuntu-20.04_clang-10x_`date +%Y-%m-%d`

docker tag ubuntu-19.10:sanitizer ${ECS_REPO}:ubuntu-19.10_clang-9x_sanitizer_`date +%Y-%m-%d`
docker tag ubuntu-19.10:sanitizer ${ECS_REPO}:ubuntu-19.10_clang-9x_sanitizer_latest
docker push ${ECS_REPO}:ubuntu-19.10_clang-9x_sanitizer_latest
docker push ${ECS_REPO}:ubuntu-19.10_clang-9x_sanitizer_`date +%Y-%m-%d`

docker tag centos-7:gcc-4x ${ECS_REPO}:centos-7_gcc-4x_`date +%Y-%m-%d`
docker tag centos-7:gcc-4x ${ECS_REPO}:centos-7_gcc-4x_latest
docker push ${ECS_REPO}:centos-7_gcc-4x_latest
docker push ${ECS_REPO}:centos-7_gcc-4x_`date +%Y-%m-%d`

docker tag amazonlinux-2:gcc-7x ${ECS_REPO}:amazonlinux-2_gcc-7x_`date +%Y-%m-%d`
docker tag amazonlinux-2:gcc-7x ${ECS_REPO}:amazonlinux-2_gcc-7x_latest
docker push ${ECS_REPO}:amazonlinux-2_gcc-7x_latest
docker push ${ECS_REPO}:amazonlinux-2_gcc-7x_`date +%Y-%m-%d`

docker tag fedora-31:gcc-9x ${ECS_REPO}:fedora-31_gcc-9x_`date +%Y-%m-%d`
docker tag fedora-31:gcc-9x ${ECS_REPO}:fedora-31_gcc-9x_latest
docker push ${ECS_REPO}:fedora-31_gcc-9x_latest
docker push ${ECS_REPO}:fedora-31_gcc-9x_`date +%Y-%m-%d`

docker tag fedora-31:clang-9x ${ECS_REPO}:fedora-31_clang-9x_`date +%Y-%m-%d`
docker tag fedora-31:clang-9x ${ECS_REPO}:fedora-31_clang-9x_latest
docker push ${ECS_REPO}:fedora-31_clang-9x_latest
docker push ${ECS_REPO}:fedora-31_clang-9x_`date +%Y-%m-%d`

docker tag integration:s2n ${ECS_REPO}:s2n_integration_clang-9x_`date +%Y-%m-%d`
docker tag integration:s2n ${ECS_REPO}:s2n_integration_clang-9x_latest
docker push ${ECS_REPO}:s2n_integration_clang-9x_latest
docker push ${ECS_REPO}:s2n_integration_clang-9x_`date +%Y-%m-%d`
