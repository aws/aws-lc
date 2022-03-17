#!/bin/bash
set -exo pipefail
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

source tests/ci/common_posix_setup.sh

# The build and test time is not meant to be scientific benchmark, just to get a rough sense of changes overtime.
# In case there is a weird change over time this recorded additional information about the host to the logs.
lscpu

function put_metric {
  # This call to publish the metric could fail but we don't want to fail the build +e turns off exit on error
  set +e
  aws cloudwatch put-metric-data \
    --namespace AWS-LC \
    "$@" || echo "Publishing metric failed, continuing with the rest of the build"
  # Turn it back on for the rest of the build
  set -e
}

# Return the size of an object or total for the folder (summarize)
function size {
  du --bytes --apparent-size --summarize "$@" | cut -f1
}

SOURCE_CODE_SIZE=$(size "$SRC_ROOT")
put_metric --metric-name FolderSize --value "$SOURCE_CODE_SIZE" --unit Bytes --dimensions "Folder=root"

for FOLDER_PATH in "$SRC_ROOT"/*/ ; do
    FOLDER_SIZE=$(size "$FOLDER_PATH")
    FOLDER=$(basename "$FOLDER_PATH")
    put_metric --metric-name FolderSize --value "$FOLDER_SIZE" --unit Bytes --dimensions "Folder=${FOLDER}"
done

function run_build_and_collect_metrics {
  if [[ "$small" == "ON" ]]; then
    build_size="Small"
  else
    build_size="Large"
  fi
  if [[ "$no_assembly" == "ON" ]]; then
    assembly="NoAsm"
  else
    assembly="Asm"
  fi
  if [[ "$shared_library" == "ON" ]]; then
    linking="Shared"
  else
    linking="Static"
  fi
  if [[ "$fips" == "ON" ]]; then
    fips_mode="FIPS"
  else
    fips_mode="NotFIPS"
  fi
  common_dimensions="Optimization=Release,BuildSize=${build_size},Assembly=${assembly},CPU=${PLATFORM},Linking=${linking},FIPS=${fips_mode}"

  build_start=$(date +%s)
  run_build -DCMAKE_BUILD_TYPE=Release \
      -DBUILD_SHARED_LIBS="$shared_library" \
      -DOPENSSL_SMALL="$small" \
      -DOPENSSL_NO_ASM="$no_assembly" \
      -DFIPS="$fips"
  build_end=$(date +%s)
  build_time=$((build_end-build_start))
  put_metric --metric-name BuildTime --value "$build_time" --unit Seconds --dimensions "$common_dimensions"

  test_start=$(date +%s)
  run_cmake_custom_target 'run_tests'
  test_end=$(date +%s)
  test_time=$((test_end-test_start))
  put_metric --metric-name TestTime --value "$test_time" --unit Seconds --dimensions "$common_dimensions"

  libcrypto_size=$(du --bytes --apparent-size "${BUILD_ROOT}"/crypto/libcrypto.* | cut -f1)
  libssl_size=$(du --bytes --apparent-size "${BUILD_ROOT}"/ssl/libssl.* | cut -f1)
  put_metric --metric-name LibrarySize --value "$libcrypto_size" --unit Bytes --dimensions "Library=libcrypto,${common_dimensions}"
  put_metric --metric-name LibrarySize --value "$libssl_size" --unit Bytes --dimensions "Library=libssl,${common_dimensions}"
}

fips=OFF
for shared_library in ON OFF; do
  for small in ON OFF; do
    for no_assembly in ON OFF; do
      run_build_and_collect_metrics
    done
  done
done

# We only care about one FIPS dimension
shared_library=ON
small=OFF
no_assembly=OFF
fips=ON
run_build_and_collect_metrics
