#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# This script checks out the fips branch for publishing.

set -e

function usage {
  echo
  echo "Usage: $(basename "${0}") [-d] [-b] [-u] [-m] [-s]"
  echo
}

IGNORE_DIRTY=0
IGNORE_BRANCH=0
IGNORE_UPSTREAM=0
IGNORE_MACOS=0
SKIP_TEST=0

while getopts "dbums" option; do
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
  s )
    SKIP_TEST=1
    ;;
  * )
    echo Invalid argument: -"${?}"
    usage
    exit 1
    ;;
  esac
done

shift $((OPTIND - 1))

AWS_LC_FIPS_SYS_VERSION="0.1.0"

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
AWS_LC_FIPS_BRANCH="fips-2022-11-02"
CRATE_TEMPLATE_DIR="${AWS_LC_DIR}"/bindings/rust/aws-lc-fips-sys-template
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
AWS_LC_FIPS_DIR="${TMP_DIR}"/aws-lc
SYMBOLS_FILE="${TMP_DIR}"/symbols.txt
CRATE_DIR="${TMP_DIR}"/aws-lc-fips-sys
COMPLETION_MARKER="${CRATE_DIR}"/.generation_complete
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

mkdir -p "${TMP_DIR}"

# Clone the FIPS branch in local. 
# TODO: This can be optimized to be ran and checked on the FIPS branch when this
# commit is in the latest FIPS branch.
function clone_fips_branch {
  pushd "${TMP_DIR}"
  rm -rf aws-lc
  git clone -b ${AWS_LC_FIPS_BRANCH} --depth 1 --single-branch https://github.com/awslabs/aws-lc.git
  popd
}

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
  # Removes completion marker and any other file remaining from a previous crate generation
  rm -rf "${CRATE_DIR}"

  mkdir -p "${CRATE_DIR}"
  mkdir -p "${CRATE_AWS_LC_DIR}"/

  cp -r "${CRATE_TEMPLATE_DIR}"/* "${CRATE_DIR}"/
  perl -pi -e "s/__AWS_LC_FIPS_SYS_VERSION__/${AWS_LC_FIPS_SYS_VERSION}/g" "${CRATE_DIR}"/Cargo.toml

  cp -r "${AWS_LC_FIPS_DIR}"/crypto  \
        "${AWS_LC_FIPS_DIR}"/ssl  \
        "${AWS_LC_FIPS_DIR}"/include \
        "${AWS_LC_FIPS_DIR}"/tool \
        "${AWS_LC_FIPS_DIR}"/CMakeLists.txt \
        "${AWS_LC_FIPS_DIR}"/LICENSE \
        "${AWS_LC_FIPS_DIR}"/sources.cmake \
        "${AWS_LC_FIPS_DIR}"/go.mod \
        "${CRATE_AWS_LC_DIR}"/

  cp "${AWS_LC_FIPS_DIR}"/LICENSE  "${CRATE_AWS_LC_DIR}"/
  cp "${AWS_LC_FIPS_DIR}"/LICENSE  "${CRATE_DIR}"/

  mkdir -p "${CRATE_AWS_LC_DIR}"/util
  cp -r "${AWS_LC_FIPS_DIR}"/util/fipstools \
        "${AWS_LC_FIPS_DIR}"/util/godeps.go \
        "${AWS_LC_FIPS_DIR}"/util/ar \
        "${CRATE_AWS_LC_DIR}"/util

  mkdir -p "${CRATE_AWS_LC_DIR}"/third_party/
  cp -r  "${AWS_LC_FIPS_DIR}"/third_party/googletest \
          "${AWS_LC_FIPS_DIR}"/third_party/s2n-bignum \
          "${AWS_LC_FIPS_DIR}"/third_party/fiat \
          "${AWS_LC_FIPS_DIR}"/third_party/jitterentropy \
          "${CRATE_AWS_LC_DIR}"/third_party/

  mkdir -p  "${CRATE_AWS_LC_DIR}"/tests/compiler_features_tests
  cp "${AWS_LC_FIPS_DIR}"/tests/compiler_features_tests/*.c "${CRATE_AWS_LC_DIR}"/tests/compiler_features_tests
}

clone_fips_branch
prepare_crate_dir
create_prefix_headers

"${SCRIPT_DIR}"/_generate_all_bindings_flavors.sh

if [[ ${SKIP_TEST} -eq 1 ]]; then
  echo Aborting. Crate generated but not tested.
  exit 1
fi

"${SCRIPT_DIR}"/_test_supported_builds.sh

touch "${COMPLETION_MARKER}"
