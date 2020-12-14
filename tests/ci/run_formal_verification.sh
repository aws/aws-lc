#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

AWS_LC_DIR=${PWD##*/}
echo "aloha ${AWS_LC_DIR}"
cd ../
ROOT=$(pwd)

rm -rf aws-lc-verification-build
git clone --recurse-submodules https://github.com/awslabs/aws-lc-verification.git aws-lc-verification-build
cd aws-lc-verification-build
# aws-lc-verification has aws-lc as one submodule under 'src' dir.
# Below is to copy code of **target** aws-lc to 'src' dir.
rm -rf ./src/* && cp -r "${ROOT}/${AWS_LC_DIR}/"* ./src
# execute the entry to saw scripts.
./SAW/scripts/docker_entrypoint.sh
cd ..
rm -rf aws-lc-verification-build
