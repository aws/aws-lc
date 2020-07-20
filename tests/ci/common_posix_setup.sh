# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

function run_build {
  local cflags=("$@")
  rm -rf test_build_dir
  mkdir -p test_build_dir
  cd test_build_dir || exit 1

  if [[ "${AWSLC_32BIT}" == "1" ]]; then
    cflags+=("-DCMAKE_TOOLCHAIN_FILE=../third_party/boringssl/util/32-bit-toolchain.cmake")
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
    BUILD_COMMAND="make"
  fi

  cmake "${cflags[@]}" ../
  $BUILD_COMMAND
  cd ../
}

function run_test {
  $BUILD_COMMAND -C test_build_dir run_tests
}

function build_and_test {
  run_build "$@"
  run_test 
}
