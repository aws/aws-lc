#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

ENTRYPOINT=$1
AWS_LC_DIR=${PWD##*/}
cd ../
ROOT=$(pwd)

rm -rf aws-lc-verification-build
git clone https://github.com/awslabs/aws-lc-verification.git aws-lc-verification-build

cd aws-lc-verification-build
git submodule update --init

# aws-lc-verification has aws-lc as one submodule under 'src' dir.
# Below is to copy code of **target** aws-lc to 'src' dir.
rm -rf ./src/* && cp -r "${ROOT}/${AWS_LC_DIR}/"* ./src
# execute the entry to saw scripts.
./$ENTRYPOINT
cd ..
rm -rf aws-lc-verification-build
