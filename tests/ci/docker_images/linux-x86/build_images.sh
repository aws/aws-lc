#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

########################################
# Build images from AWS-LC GitHub repo #
########################################

# Log Docker hub limit https://docs.docker.com/docker-hub/download-rate-limit/#how-can-i-check-my-current-rate
TOKEN=$(curl "https://auth.docker.io/token?service=registry.docker.io&scope=repository:ratelimitpreview/test:pull" | jq -r .token)
curl --head -H "Authorization: Bearer $TOKEN" https://registry-1.docker.io/v2/ratelimitpreview/test/manifests/latest

# Every "base" image needs to build with the dependencies directory as the context so it has access to the install
# dependencies scripts
docker build -t ubuntu-18.04:base -f ubuntu-18.04_base/Dockerfile ../dependencies
docker build -t ubuntu-18.04:gcc-7x ubuntu-18.04_gcc-7x
docker build -t ubuntu-18.04:clang-6x ubuntu-18.04_clang-6x
docker build -t ubuntu-20.04:base -f ubuntu-20.04_base/Dockerfile ../dependencies
docker build -t ubuntu-20.04:gcc-7x ubuntu-20.04_gcc-7x
docker build -t ubuntu-20.04:gcc-8x ubuntu-20.04_gcc-8x
docker build -t ubuntu-20.04:clang-7x ubuntu-20.04_clang-7x
docker build -t ubuntu-20.04:clang-8x ubuntu-20.04_clang-8x
docker build -t ubuntu-20.04:clang-9x ubuntu-20.04_clang-9x
docker build -t ubuntu-20.04:clang-10x ubuntu-20.04_clang-10x
docker build -t ubuntu-20.04:android -f ubuntu-20.04_android/Dockerfile ../
docker build -t ubuntu-20.04:clang-7x-bm-framework ubuntu-20.04_clang-7x-bm-framework
docker build -t ubuntu-22.04:base -f ubuntu-22.04_base/Dockerfile ../dependencies
docker build -t ubuntu-22.04:clang-14x-sde ubuntu-22.04_clang-14x-sde
docker build -t ubuntu-22.04:gcc-10x ubuntu-22.04_gcc-10x
docker build -t ubuntu-22.04:gcc-11x ubuntu-22.04_gcc-11x
docker build -t ubuntu-22.04:gcc-12x ubuntu-22.04_gcc-12x
docker build -t ubuntu-22.04:gcc-12x_integration ubuntu-22.04_gcc-12x_integration
docker build -t amazonlinux-2:base -f amazonlinux-2_base/Dockerfile ../dependencies
docker build -t amazonlinux-2:gcc-7x amazonlinux-2_gcc-7x
docker build -t amazonlinux-2:gcc-7x-intel-sde amazonlinux-2_gcc-7x-intel-sde
docker build -t amazonlinux-2:clang-7x amazonlinux-2_clang-7x
docker build -t amazonlinux-2023:base -f amazonlinux-2023_base/Dockerfile ../dependencies
docker build -t amazonlinux-2023:gcc-11x amazonlinux-2023_gcc-11x
docker build -t amazonlinux-2023:clang-15x amazonlinux-2023_clang-15x
docker build -t amazonlinux-2023:clang-15x-sanitizer amazonlinux-2023_clang-15x_sanitizer
docker build -t amazonlinux-2023:x509 amazonlinux-2023_x509
docker build -t amazonlinux-2023:cryptofuzz -f amazonlinux-2023_clang-15x_cryptofuzz/Dockerfile ../dependencies
docker build -t ubuntu-16.04:gcc-5x -f ubuntu-16.04_gcc-5x/Dockerfile ../dependencies
docker build -t centos-7:gcc-4x -f centos-7_gcc-4x/Dockerfile ../dependencies
docker build -t centos-8:gcc-8x -f centos-8_gcc-8x/Dockerfile ../dependencies
docker build -t fedora-31:clang-9x -f fedora-31_clang-9x/Dockerfile ../dependencies
###########################################################
# Build images defined in aws-lc-verification GitHub repo #
###########################################################

./ubuntu-20.04_clang-10x_formal-verification-saw-x86_64/create_image.sh ubuntu-20.04:clang-10x_formal-verification-saw-x86_64
./ubuntu-20.04_clang-10x_formal-verification-saw-x86_64-aes-gcm/create_image.sh ubuntu-20.04:clang-10x_formal-verification-saw-x86_64-aes-gcm
./ubuntu-20.04_clang-10x_formal-verification-saw-aarch64/create_image.sh ubuntu-20.04:clang-10x_formal-verification-saw-aarch64
./ubuntu-22.04_clang-14x_formal-verification-nsym-aarch64/create_image.sh ubuntu-22.04:clang-14x_formal-verification-nsym-aarch64

###########################################################
# Build older unofficial docker image that uses gcc 4.1.3 #
###########################################################

./build_legacy_image.sh ubuntu-10.04_gcc-4.1x
