#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

function usage {
  echo
  echo "Usage: $(basename "${0}") [-d] [-b] [-u] [-m]"
  echo
}

IGNORE_DIRTY=0
IGNORE_BRANCH=0
IGNORE_UPSTREAM=0
IGNORE_MACOS=0

while getopts "dbum" option; do
  case ${option} in
  d )
    IGNORE_DIRTY=1
    ;;
  b )
    IGNORE_BRANCH=1
    ;;
  u )
    IGNORE_UPSTREAM=1
    ;;
  m )
    IGNORE_MACOS=1
    ;;
  * )
    echo Invalid argument: -"${?}"
    usage
    exit 1
    ;;
  esac
done

shift $((OPTIND - 1))

AWS_LC_SYS_VERSION="0.1.0"

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
CRATE_TEMPLATE_DIR="${AWS_LC_DIR}"/bindings/rust/aws-lc-sys-template
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
SYMBOLS_FILE="${TMP_DIR}"/symbols.txt
CRATE_DIR="${TMP_DIR}"/aws-lc-sys
CRATE_AWS_LC_DIR="${CRATE_DIR}"/deps/aws-lc
PREFIX_HEADERS_FILE="${CRATE_AWS_LC_DIR}"/include/boringssl_prefix_symbols.h

if [[ ! -d ${AWS_LC_DIR} ]]; then
  echo "$(basename "${0}")" Sanity Check Failed
  exit 1
fi

pushd "${AWS_LC_DIR}"

if [[ $(git status --porcelain | wc -l) -gt 0 ]]; then
  echo Workspace is dirty.
  if [[ ${IGNORE_DIRTY} -eq 0 ]]; then
    echo Aborting. Use '-d' to ignore.
    echo
    exit 1
  else
    echo Ignoring dirty workspace.
    echo
  fi
fi

CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
if [ "${CURRENT_BRANCH}" != "main" ]
then
  echo Branch is not main.
  if [[ ${IGNORE_BRANCH} -eq 0 ]]; then
    echo Aborting. Use '-b' to ignore.
    echo
    exit 1
  else
    echo Ignoring wrong branch.
    echo
  fi
fi

git fetch
LOCAL_HASH=$(git rev-parse HEAD)
UPSTREAM_HASH=$(git rev-parse "${CURRENT_BRANCH}"'@{upstream}')

if [[ ! "${LOCAL_HASH}" == "${UPSTREAM_HASH}" ]]; then
  echo "${CURRENT_BRANCH}" not up to date with upstream.
  if [[ ${IGNORE_UPSTREAM} -eq 0 ]]; then
    echo Aborting. Use '-u' to ignore.
    echo
    exit 1
  else
    echo Ignoring branch not up to date.
    echo
  fi
fi

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
fi

mkdir -p "${TMP_DIR}"

function create_symbol_file {
  if [[ ! -r "${SYMBOLS_FILE}" ]]; then
    echo Symbol file not found
    echo Performing build for supported platforms.
    "${SCRIPT_DIR}"/_run_supported_symbol_builds.sh
  fi

  if [[ ! -r "${SYMBOLS_FILE}" ]]; then
    echo Symbol file not found after builds performed.
    exit 1
  else
    echo Symbol file generation complete
  fi
}

function create_prefix_headers {
  if [[ ! -r "${PREFIX_HEADERS_FILE}" || "${SYMBOLS_FILE}" -nt "${PREFIX_HEADERS_FILE}" ]]; then
    echo Prefix headers not up to date
    create_symbol_file

    echo Generating prefix headers
    go run "${AWS_LC_DIR}"/util/make_prefix_headers.go -out "${CRATE_AWS_LC_DIR}"/include "${SYMBOLS_FILE}"
  fi

  if [[ ! -r "${PREFIX_HEADERS_FILE}" || "${SYMBOLS_FILE}" -nt "${PREFIX_HEADERS_FILE}" ]]; then
    echo Prefix headers not up to date after generation.
    exit 1
  else
    echo Prefix headers generation complete
  fi
}

function prepare_crate_dir {
  echo Preparing crate directory: "${CRATE_DIR}"
  mkdir -p "${CRATE_DIR}"
  mkdir -p "${CRATE_AWS_LC_DIR}"/

  cp -r "${CRATE_TEMPLATE_DIR}"/* "${CRATE_DIR}"/
  perl -pi -e "s/__AWS_LC_SYS_VERSION__/${AWS_LC_SYS_VERSION}/g" "${CRATE_DIR}"/Cargo.toml

  cp -r "${AWS_LC_DIR}"/crypto  \
        "${AWS_LC_DIR}"/ssl  \
        "${AWS_LC_DIR}"/include \
        "${AWS_LC_DIR}"/tool \
        "${AWS_LC_DIR}"/generated-src \
        "${AWS_LC_DIR}"/CMakeLists.txt \
        "${AWS_LC_DIR}"/LICENSE \
        "${AWS_LC_DIR}"/sources.cmake \
        "${CRATE_AWS_LC_DIR}"/

  cp "${AWS_LC_DIR}"/LICENSE  "${CRATE_AWS_LC_DIR}"/
  cp "${AWS_LC_DIR}"/LICENSE  "${CRATE_DIR}"/

  mkdir -p "${CRATE_AWS_LC_DIR}"/util
  cp -r  "${AWS_LC_DIR}"/util/fipstools "${CRATE_AWS_LC_DIR}"/util

  mkdir -p "${CRATE_AWS_LC_DIR}"/third_party/
  cp -r  "${AWS_LC_DIR}"/third_party/googletest "${AWS_LC_DIR}"/third_party/s2n-bignum "${AWS_LC_DIR}"/third_party/fiat "${CRATE_AWS_LC_DIR}"/third_party/

  mkdir -p  "${CRATE_AWS_LC_DIR}"/tests/compiler_features_tests
  cp "${AWS_LC_DIR}"/tests/compiler_features_tests/*.c "${CRATE_AWS_LC_DIR}"/tests/compiler_features_tests
}

prepare_crate_dir
create_prefix_headers

"${SCRIPT_DIR}"/_test_supported_builds.sh "$( [ ${IGNORE_MACOS} -eq 1 ] && echo '-m' )"
