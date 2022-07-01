#!/usr/bin/env bash
set -e

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
AWS_LC_SYS_VERSION="0.1.0"

AWS_ACCOUNT_ID="${1}"
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
CRATE_TEMPLATE_DIR="${AWS_LC_DIR}"/bindings/rust/aws-lc-sys-template
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
SYMBOLS_FILE="${TMP_DIR}"/symbols.txt
CRATE_DIR="${TMP_DIR}"/aws-lc-sys
CRATE_AWS_LC_DIR="${CRATE_DIR}"/deps/aws-lc
PREFIX_HEADERS_FILE="${CRATE_AWS_LC_DIR}"/include/boringssl_prefix_symbols.h
BINDINGS_FILE="${CRATE_DIR}"/src/bindings.rs

if [[ ! -d ${AWS_LC_DIR} || ! -d ${TMP_DIR} ]]; then
  echo "$(basename $0)" Sanity Check Failed
  exit 1
fi

function usage {
  echo
  echo "Usage: $(basename $0) [AWS_ACCOUNT_ID]"
  echo
  echo "    AWS_ACCOUNT_ID - The account providing docker images for the build."
  echo
}

# if [ -z "${1}" ]; then
#   usage
#   exit 1
# fi


function create_symbol_file {
  if [[ ! -r "${SYMBOLS_FILE}" ]]; then
    if [[ -z "${AWS_ACCOUNT_ID}" ]]; then
      usage
      exit 1
    fi
    echo Symbol file not found
    echo Performing build for supported platforms.
    ${SCRIPT_DIR}/_run_supported_symbol_builds.sh ${AWS_ACCOUNT_ID}
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

function create_bindings {
  if [[ ! -r "${BINDINGS_FILE}" || "${PREFIX_HEADERS_FILE}" -nt "${BINDINGS_FILE}" ]]; then
    echo Bindings not up to date.
    create_prefix_headers

    echo Generating bindings.
    pushd ${SCRIPT_DIR}
    cargo run -- "${CRATE_DIR}" "${AWS_LC_SYS_VERSION}"
  fi

  if [[ ! -r "${BINDINGS_FILE}" || "${PREFIX_HEADERS_FILE}" -nt "${BINDINGS_FILE}" ]]; then
    echo Bindings not up to date after generation.
    exit 1
  else
    echo Bindings generation complete
  fi
}

function prepare_crate_dir {
  echo Preparing crate directory: ${CRATE_DIR}
  mkdir -p "${CRATE_DIR}"
  mkdir -p "${CRATE_AWS_LC_DIR}"/

  cp -r "${CRATE_TEMPLATE_DIR}"/* "${CRATE_DIR}"/
  perl -pi -e "s/__AWS_LC_SYS_VERSION__/${AWS_LC_SYS_VERSION}/g" "${CRATE_DIR}"/Cargo.toml

  cp -r "${AWS_LC_DIR}"/crypto  \
        "${AWS_LC_DIR}"/ssl  \
        "${AWS_LC_DIR}"/include \
        "${AWS_LC_DIR}"/tool \
        "${AWS_LC_DIR}"/decrepit \
        "${AWS_LC_DIR}"/CMakeLists.txt \
        "${AWS_LC_DIR}"/LICENSE \
        "${AWS_LC_DIR}"/sources.cmake \
        "${CRATE_AWS_LC_DIR}"/

  mkdir -p "${CRATE_AWS_LC_DIR}"/util
  cp -r  "${AWS_LC_DIR}"/util/fipstools "${CRATE_AWS_LC_DIR}"/util

  mkdir -p "${CRATE_AWS_LC_DIR}"/third_party/
  cp -r  "${AWS_LC_DIR}"/third_party/googletest "${AWS_LC_DIR}"/third_party/s2n-bignum "${AWS_LC_DIR}"/third_party/fiat "${CRATE_AWS_LC_DIR}"/third_party/

  mkdir -p  "${CRATE_AWS_LC_DIR}"/tests/compiler_features_tests
  cp "${AWS_LC_DIR}"/tests/compiler_features_tests/*.c "${CRATE_AWS_LC_DIR}"/tests/compiler_features_tests
}

prepare_crate_dir
create_bindings








