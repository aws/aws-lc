#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e -x

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
CRATE_DIR="${TMP_DIR}"/aws-lc-sys

###
###
### Test crate on Mac
###
###
if [[ ! "${OSTYPE}" == "darwin"* ]]; then
  echo This scipt must be run on a Mac
  exit 1
fi
"${SCRIPT_DIR}"/_crate_test_build.sh

pushd "${AWS_LC_DIR}"

##
## These docker image can be built from Dockerfiles under: <AWS-LC-DIR>/tests/ci/docker_images/rust
##

## 386 test
docker run -v `pwd`:`pwd` -w `pwd` --rm --platform linux/386 rust:linux-386 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

## x86_64 test
docker run -v `pwd`:`pwd` -w `pwd` --rm --platform linux/amd64 rust:linux-x86_64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

## arm64 test
docker run -v `pwd`:`pwd` -w `pwd` --rm --platform linux/arm64 rust:linux-arm64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

popd
