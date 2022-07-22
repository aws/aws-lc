#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)

echo ARGS: "${@}"

IGNORE_MACOS=0

while getopts "m" option; do
  case ${option} in
  m )
    IGNORE_MACOS=1
    ;;
  * )
    echo "$(basename "${0}")" - Invalid argument: -"${?}"
    echo
    exit 1
    ;;
  esac
done

###
###
### Test crate on Mac
###
###
if [[ ! "${OSTYPE}" == "darwin"* ]]; then
  echo This script is not running on MacOS.
  if [[ ${IGNORE_MACOS} -eq 0 ]]; then
    echo Aborting. Use '-m' to ignore.
    echo
    exit 1
  else
    echo Ignoring non-MacOS. Crate will not be tested for Mac.
    echo
  fi
else
  "${SCRIPT_DIR}"/_crate_test_build.sh
fi

pushd "${AWS_LC_DIR}"

##
## These docker image can be built from Dockerfiles under: <AWS-LC-DIR>/tests/ci/docker_images/rust
##

## 386 test
docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/386 rust:linux-386 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

## x86_64 test
docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/amd64 rust:linux-x86_64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

## arm64 test
docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/arm64 rust:linux-arm64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh

popd
