#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

AWS_LC_DIR=${PWD##*/}
cd ../
ROOT=$(pwd)

rm -rf aws-lc-verification-build
git clone https://github.com/awslabs/aws-lc-verification.git aws-lc-verification-build
cd aws-lc-verification-build
# Checkout a version of the formal verification repo that works with this version of AWS-LC
git checkout 7d0a46ac0841d1d9f1c078153d38409af056c482
git submodule update --init
# aws-lc-verification has aws-lc as one submodule under 'src' dir.
# Below is to copy code of **target** aws-lc to 'src' dir.
rm -rf ./src/* && cp -r "${ROOT}/${AWS_LC_DIR}/"* ./src
# execute the entry to saw scripts.
./SAW/scripts/docker_entrypoint.sh
cd ..
rm -rf aws-lc-verification-build
