#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

docker build -t amazonlinux-2-aarch:base amazonlinux-2_base
docker build -t amazonlinux-2-aarch:gcc-7x amazonlinux-2_gcc-7x
docker build -t amazonlinux-2-aarch:clang-7x amazonlinux-2_clang-7x
docker build -t ubuntu-20.04-aarch:base ubuntu-20.04_base
docker build -t ubuntu-20.04-aarch:gcc-7x ubuntu-20.04_gcc-7x
docker build -t ubuntu-20.04-aarch:gcc-8x ubuntu-20.04_gcc-8x
docker build -t ubuntu-20.04-aarch:clang-7x ubuntu-20.04_clang-7x
docker build -t ubuntu-20.04-aarch:clang-8x ubuntu-20.04_clang-8x
docker build -t ubuntu-20.04-aarch:clang-9x ubuntu-20.04_clang-9x
docker build -t ubuntu-20.04-aarch:clang-10x ubuntu-20.04_clang-10x
