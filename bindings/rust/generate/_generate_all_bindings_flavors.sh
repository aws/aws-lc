#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)

if [[ "${GENERATE_FIPS}" -eq 0 ]]; then

   ## macos x86_64 bindings
  if [[ ! "${OSTYPE}" == "darwin"* ]]; then
    echo This script is not running on MacOS.
    if [[ ${IGNORE_MACOS} -eq 0 ]]; then
      echo Aborting. Use '-m' to ignore.
      echo
      exit 1
    else
      echo Ignoring non-MacOS. Bindings will not be generated for Mac.
      echo
    fi
  else
    "${SCRIPT_DIR}"/_generate_bindings.sh ${CRATE_NAME}
  fi

  pushd "${AWS_LC_DIR}"

  ## TODO: Find a way to pre-generate bindings for macos-aarch64 on the fly.

  ##
  ## These docker image can be built from Dockerfiles under: <AWS-LC-DIR>/tests/ci/docker_images/rust
  ##

  ## 386 build
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/386 rust:linux-386 /bin/bash "${SCRIPT_DIR}"/_generate_bindings.sh ${CRATE_NAME}
  ## linux x86_64 build
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/amd64 rust:linux-x86_64 /bin/bash "${SCRIPT_DIR}"/_generate_bindings.sh ${CRATE_NAME}
  ## linux aarch64 build
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/arm64 rust:linux-arm64 /bin/bash "${SCRIPT_DIR}"/_generate_bindings.sh ${CRATE_NAME}

  popd
else

  pushd "${AWS_LC_DIR}"

  ## linux x86_64 build
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/amd64 rust:linux-x86_64 /bin/bash "${SCRIPT_DIR}"/_generate_bindings.sh ${CRATE_NAME}
  ## linux aarch64 build
  docker run -v "$(pwd)":"$(pwd)" -w "$(pwd)" --rm --platform linux/arm64 rust:linux-arm64 /bin/bash "${SCRIPT_DIR}"/_generate_bindings.sh ${CRATE_NAME}

  popd
fi


