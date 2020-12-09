#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

if [ -n "$1" ]; then
  docker_tag="$1"
else
  docker_tag='ubuntu-20.04:clang-10x_formal-verification'
fi
rm -rf aws-lc-verification
git clone https://github.com/awslabs/aws-lc-verification.git
cd aws-lc-verification
docker build -t ${docker_tag} .
cd ..
rm -rf aws-lc-verification
