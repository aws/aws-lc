#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

# Log Docker hub limit https://docs.docker.com/docker-hub/download-rate-limit/#how-can-i-check-my-current-rate
TOKEN=$(curl "https://auth.docker.io/token?service=registry.docker.io&scope=repository:ratelimitpreview/test:pull" | jq -r .token)
curl --head -H "Authorization: Bearer $TOKEN" https://registry-1.docker.io/v2/ratelimitpreview/test/manifests/latest

# Every "base" image needs to build with the dependencies directory as the context so it has access to the install
# dependencies scripts
docker build -t amazonlinux-2-aarch:base -f amazonlinux-2_base/Dockerfile ../dependencies
docker build -t amazonlinux-2-aarch:gcc-7x amazonlinux-2_gcc-7x
docker build -t amazonlinux-2-aarch:clang-7x amazonlinux-2_clang-7x
docker build -t amazonlinux-2023-aarch:base -f amazonlinux-2023_base/Dockerfile ../dependencies
docker build -t amazonlinux-2023-aarch:gcc-11x amazonlinux-2023_gcc-11x
docker build -t amazonlinux-2023-aarch:clang-15x amazonlinux-2023_clang-15x
docker build -t amazonlinux-2023-aarch:clang-15x-sanitizer amazonlinux-2023_clang-15x_sanitizer
docker build -t amazonlinux-2023-aarch:cryptofuzz -f amazonlinux-2023_clang-15x_cryptofuzz/Dockerfile ../dependencies
docker build -t ubuntu-20.04-aarch:base -f ubuntu-20.04_base/Dockerfile ../dependencies
docker build -t ubuntu-20.04-aarch:gcc-7x ubuntu-20.04_gcc-7x
docker build -t ubuntu-20.04-aarch:gcc-8x ubuntu-20.04_gcc-8x
docker build -t ubuntu-20.04-aarch:clang-7x ubuntu-20.04_clang-7x
docker build -t ubuntu-20.04-aarch:clang-8x ubuntu-20.04_clang-8x
docker build -t ubuntu-20.04-aarch:clang-9x ubuntu-20.04_clang-9x
docker build -t ubuntu-20.04-aarch:clang-10x ubuntu-20.04_clang-10x
docker build -t ubuntu-20.04-aarch:clang-7x-bm-framework ubuntu-20.04_clang-7x-bm-framework
docker build -t ubuntu-22.04-aarch:base -f ubuntu-22.04_base/Dockerfile ../dependencies
docker build -t ubuntu-22.04-aarch:gcc-11x ubuntu-22.04_gcc-11x
docker build -t ubuntu-22.04-aarch:gcc-12x ubuntu-22.04_gcc-12x
