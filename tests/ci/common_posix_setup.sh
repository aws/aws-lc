# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

function run_build {
  local cflags=("$@")
  rm -rf test_build_dir
  mkdir -p test_build_dir
  cd test_build_dir || exit 1

  if [[ "${AWSLC_32BIT}" == "1" ]]; then
    cflags+=("-DCMAKE_TOOLCHAIN_FILE=../util/32-bit-toolchain.cmake")
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

function run_cmake_custom_target {
  $BUILD_COMMAND -C test_build_dir "$@"
}

function build_and_test {
  run_build "$@"
  run_cmake_custom_target 'run_tests'
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
