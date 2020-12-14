#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

docker build -t amazonlinux-2-aarch:gcc-7x amazonlinux-2_gcc-7x
docker build -t ubuntu-19.10-aarch:clang-9x ubuntu-19.10_clang-9x
docker build -t ubuntu-19.10-aarch:sanitizer ubuntu-19.10_clang-9x_sanitizer
docker build -t ubuntu-20.04-aarch:clang-10x ubuntu-20.04_clang-10x
