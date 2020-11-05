#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

if [ -n "$1" ]; then
  docker_tag="$1"
else
  docker_tag='ubuntu-20.04:awslc-saw'
fi
rm -rf aws-lc-verification
# TODO: delete ci-prep branch, and then lock in a specific code commit.
git clone --branch ci-prep https://github.com/awslabs/aws-lc-verification.git
cd aws-lc-verification
docker build -t ${docker_tag} .
cd ..
rm -rf aws-lc-verification
