#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Define aws-lc repo url.
if [ -n "$1" ]; then
  echo "Using forked aws-lc repo -- ${1}"
  aws_lc_repo="$1"
else
  aws_lc_repo='https://github.com/awslabs/aws-lc.git'
fi

# Define the variable of aws-lc branch/specific commit.
if [ -n "$2" ]; then
  echo "Using aws-lc a specific version -- ${2}"
  aws_lc_version="$2"
else
  aws_lc_version='main'
fi

git clone --recurse-submodules https://github.com/awslabs/aws-lc-verification.git
cd aws-lc-verification
# aws-lc-verification stores aws-lc code in src. Below is to support the need of testing in other forked repo.
(rm -rf src && git clone ${aws_lc_repo} src && cd src && git checkout ${aws_lc_version})
# execute the entry to saw scripts.
./SAW/scripts/docker_entrypoint.sh
cd ..
rm -rf aws-lc-verification
