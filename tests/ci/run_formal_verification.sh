#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

AWS_LC_DIR=${PWD##*/}
cd ../
ROOT=$(pwd)

rm -rf aws-lc-verification-build
git clone https://github.com/awslabs/aws-lc-verification.git aws-lc-verification-build

cd aws-lc-verification-build
# We avoid pulling the saw-script submodule since the repo will take forever to clone.
git submodule update --init
pushd Coq/fiat-crypto; git submodule update --init --recursive; popd

# aws-lc-verification has aws-lc as one submodule under 'src' dir.
# Below is to copy code of **target** aws-lc to 'src' dir.
rm -rf ./src/* && cp -r "${ROOT}/${AWS_LC_DIR}/"* ./src
# execute the entry to saw scripts.
./SAW/scripts/docker_entrypoint.sh
cd ..
rm -rf aws-lc-verification-build
