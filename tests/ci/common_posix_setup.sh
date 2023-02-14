# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# If having trouble reaching proxy.golang.org, uncomment the following:
#go env -w GOPROXY=direct

if [ -v CODEBUILD_SRC_DIR ]; then
  SRC_ROOT="$CODEBUILD_SRC_DIR"
else
  SRC_ROOT=$(pwd)
fi
echo "$SRC_ROOT"

BUILD_ROOT="${SRC_ROOT}/test_build_dir"
echo "$BUILD_ROOT"

NUM_CPU_THREADS=''
KERNEL_NAME=$(uname -s)
if [[ "${KERNEL_NAME}" == "Darwin" ]]; then
  # On MacOS, /proc/cpuinfo does not exist.
  NUM_CPU_THREADS=$(sysctl -n hw.ncpu)
else
  # Assume KERNEL_NAME is Linux.
  NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
fi

PLATFORM=$(uname -m)

# Pick cmake3 if possible. We don't know of any OS that installs a cmake3
# executable that is not at least version 3.0.
if [[ -x "$(command -v cmake3)" ]] ; then
  CMAKE_COMMAND="cmake3"
else
  CMAKE_COMMAND="cmake"
fi

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

  ${CMAKE_COMMAND} "${cflags[@]}" "$SRC_ROOT"
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

function generate_symbols_file {
  # read_symbols.go currently only support static libraries
  if [ ! -f  "$BUILD_ROOT"/crypto/libcrypto.a ]; then
    echo "Static library not found: ${BUILD_ROOT}/crypto/libcrypto.a"
    print_system_and_dependency_information
    exit 1
  fi

  go run "$SRC_ROOT"/util/read_symbols.go -out "$BUILD_ROOT"/symbols_crypto.txt "$BUILD_ROOT"/crypto/libcrypto.a
  go run "$SRC_ROOT"/util/read_symbols.go -out "$BUILD_ROOT"/symbols_ssl.txt "$BUILD_ROOT"/ssl/libssl.a

  # The $BUILD_ROOT gets deleted on each run. symbols.txt must be placed elsewhere.
  cat "$BUILD_ROOT"/symbols_crypto.txt  "$BUILD_ROOT"/symbols_ssl.txt >  "$SRC_ROOT"/symbols.txt
}


function verify_symbols_prefixed {
  go run "$SRC_ROOT"/util/read_symbols.go -out "$BUILD_ROOT"/symbols_final_crypto.txt "$BUILD_ROOT"/crypto/libcrypto.a
  go run "$SRC_ROOT"/util/read_symbols.go -out "$BUILD_ROOT"/symbols_final_ssl.txt "$BUILD_ROOT"/ssl/libssl.a
  cat "$BUILD_ROOT"/symbols_final_crypto.txt  "$BUILD_ROOT"/symbols_final_ssl.txt | grep -v -e '^_\?bignum' >  "$SRC_ROOT"/symbols_final.txt
  if [ $(grep -c -v ${CUSTOM_PREFIX}  "$SRC_ROOT"/symbols_final.txt) -ne 0 ]; then
    echo "Symbol(s) missing prefix!"
    exit 1
  fi
}


function build_prefix_and_test {
  CUSTOM_PREFIX=aws_lc_1_1_0
  run_build "$@"
  generate_symbols_file
  run_build "$@" "-DBORINGSSL_PREFIX=${CUSTOM_PREFIX}" "-DBORINGSSL_PREFIX_SYMBOLS=${SRC_ROOT}/symbols.txt"
  verify_symbols_prefixed
  run_cmake_custom_target 'run_tests'
}

function fips_build_and_test {
  run_build "$@" -DFIPS=1
  # Upon completion of the build process. The module’s status can be verified by 'tool/bssl isfips'.
  # https://csrc.nist.gov/CSRC/media/projects/cryptographic-module-validation-program/documents/security-policies/140sp3678.pdf
  # FIPS mode is enabled when 'defined(BORINGSSL_FIPS) && !defined(OPENSSL_ASAN)'.
  # https://github.com/aws/aws-lc/blob/220e266d4e415cf0101388b89a2bd855e0e4e203/crypto/fipsmodule/is_fips.c#L22
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
  "${BUILD_ROOT}/util/fipstools/test_fips"
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

function print_executable_information {
  EXE_NAME=${1}
  EXE_ARGUMENT=${2}
  LABEL=${3}

  echo ""
  echo "${LABEL}:"
  if command -v ${EXE_NAME} &> /dev/null
  then
    ${EXE_NAME} ${EXE_ARGUMENT}
  else
    echo "${EXE_NAME} not found"
  fi
}

function print_system_and_dependency_information {
  print_executable_information "cmake" "--version" "CMake version"
  print_executable_information "cmake3" "--version" "CMake version (cmake3 executable)"
  print_executable_information "go" "version" "Go version"
  print_executable_information "perl" "--version" "Perl version"
  # Ninja executable names are not uniform over operating systems
  print_executable_information "ninja-build" "--version" "Ninja version (ninja-build executable)"
  print_executable_information "ninja" "--version" "Ninja version (ninja executable)"
  print_executable_information "gcc" "--version" "gcc version"
  print_executable_information "g++" "--version" "g++ version"
  print_executable_information "clang" "--version" "clang version"
  print_executable_information "clang++" "--version" "clang++ version"
  print_executable_information "cc" "--version" "cc version"
  print_executable_information "c++" "--version" "c++ version"
  print_executable_information "make" "--version" "Make version"
  print_executable_information "rustup" "show" "Rust toolchain"
  echo ""
  echo "Operating system information:"
  uname -a
  echo ""
  echo "Environment variables"
  env
}
