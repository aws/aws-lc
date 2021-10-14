# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


if [ -v CODEBUILD_SRC_DIR ]; then
  SRC_ROOT="$CODEBUILD_SRC_DIR"
else
  SRC_ROOT=$(pwd)
fi
echo "$SRC_ROOT"

BUILD_ROOT="${SRC_ROOT}/test_build_dir"
echo "$BUILD_ROOT"

NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)

function run_build {
  local cflags=("$@")
  rm -rf "$BUILD_ROOT"
  mkdir -p "$BUILD_ROOT"
  cd "$BUILD_ROOT" || exit 1

  if [[ "${AWSLC_32BIT}" == "1" ]]; then
    cflags+=("-DCMAKE_TOOLCHAIN_FILE=${SRC_ROOT}/util/32-bit-toolchain.cmake")
  fi

  if [[ -x "$(command -v ninja)" ]]; then
    echo "Using Ninja build system (ninja)."
    BUILD_COMMAND="ninja"
    cflags+=(-GNinja)
  elif [[ -x "$(command -v ninja-build)" ]]; then
    echo "Using Ninja build system (ninja-build)."
    BUILD_COMMAND="ninja-build"
    cflags+=(-GNinja)
  else
    echo "Using Make."
    BUILD_COMMAND="make -j${NUM_CPU_THREADS}"
  fi

  cmake "${cflags[@]}" "$SRC_ROOT"
  $BUILD_COMMAND
  cd "$SRC_ROOT"
}

function run_cmake_custom_target {
  $BUILD_COMMAND -C "$BUILD_ROOT" "$@"
}

function build_and_test {
  run_build "$@"
  run_cmake_custom_target 'run_tests'
}

function fips_build_and_test {
  run_build "$@" -DFIPS=1
  # Upon completion of the build process. The module’s status can be verified by 'tool/bssl isfips'.
  # https://csrc.nist.gov/CSRC/media/projects/cryptographic-module-validation-program/documents/security-policies/140sp3678.pdf
  # FIPS mode is enabled when 'defined(BORINGSSL_FIPS) && !defined(OPENSSL_ASAN)'.
  # https://github.com/awslabs/aws-lc/blob/220e266d4e415cf0101388b89a2bd855e0e4e203/crypto/fipsmodule/is_fips.c#L22
  expect_fips_mode=1
  for build_flag in "$@"
  do
    if [[ "${build_flag}" == '-DASAN=1' ]]; then
      expect_fips_mode=0
      break
    fi
  done
  module_status=$("${BUILD_ROOT}/tool/bssl" isfips)
  [[ "${expect_fips_mode}" == "${module_status}" ]] || { echo >&2 "FIPS Mode validation failed."; exit 1; }
  # Run tests.
  run_cmake_custom_target 'run_tests'
  "${BUILD_ROOT}/util/fipstools/cavp/test_fips"
}

function ensure_file() {
    if [ ! -f "$1" ]; then
        echo "$1 does not exist"
        exit 1
    fi
}

function check_bcm_o_digest {
  # ABS_DIR_TO_STORE_BCM is the absolute directory used to store the built bcm.o.
  if [[ -z "${ABS_DIR_TO_STORE_BCM+x}" || -z "${ABS_DIR_TO_STORE_BCM}" ]]; then
    echo "ABS_DIR_TO_STORE_BCM is not defined or empty."
    exit 1
  fi
  # Check if bcm.o is generated.
  PATH_TO_BUILT_BCM_O="${BUILD_ROOT}/crypto/fipsmodule/bcm.o"
  ensure_file "${PATH_TO_BUILT_BCM_O}"
  # Check if bcm.o is generated.
  PATH_TO_BCM_O_DIGEST="${ABS_DIR_TO_STORE_BCM}/bcm.o.sha256"
  ensure_file "${PATH_TO_BCM_O_DIGEST}"
  # Copy the bcm.o to the target directory.
  cp "${PATH_TO_BUILT_BCM_O}" "${ABS_DIR_TO_STORE_BCM}"
  # Check the digest.
  cd "${ABS_DIR_TO_STORE_BCM}" && (cat "${PATH_TO_BCM_O_DIGEST}" | sha256sum -c) || exit 1
  cd "$SRC_ROOT"
}

function build_and_test_valgrind {
  run_build "$@"
  run_cmake_custom_target 'run_tests_valgrind'
}

function build_and_test_with_sde {
  run_build "$@"
  run_cmake_custom_target 'run_tests_with_sde'
}

function build_and_run_minimal_test {
  run_build "$@"
  run_cmake_custom_target 'run_minimal_tests'
}
