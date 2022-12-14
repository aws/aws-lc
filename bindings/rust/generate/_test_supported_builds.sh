#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)

if [[ "${GENERATE_FIPS}" -eq 0 ]]; then
  CRATE_NAME="aws-lc-sys"

  ### Test crate on Mac
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
    "${SCRIPT_DIR}"/_crate_test_build.sh ${CRATE_NAME}
  fi

  pushd "${AWS_LC_DIR}"

  ## 386 test
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/386 rust:linux-386 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh ${CRATE_NAME}
  ## x86_64 test
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/amd64 rust:linux-x86_64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh ${CRATE_NAME}
  ## arm64 test
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/arm64 rust:linux-arm64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh ${CRATE_NAME}

  popd
else
  CRATE_NAME="aws-lc-fips-sys"

  pushd "${AWS_LC_DIR}"

  ## x86_64 test
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/amd64 rust:linux-x86_64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh ${CRATE_NAME}
  ## arm64 test
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/arm64 rust:linux-arm64 /bin/bash "${SCRIPT_DIR}"/_crate_test_build.sh ${CRATE_NAME}

  popd
fi
