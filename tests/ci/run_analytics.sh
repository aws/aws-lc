#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

# The build and test time is not meant to be scientific benchmark, just to get a rough sense of changes overtime.
# In case there is a weird change over time this recorded additional information about the host to the logs.
lscpu

branch=$(echo "$CODEBUILD_WEBHOOK_TRIGGER" | cut -d '/' -f2)
common_dimensions="Branch=${branch}"

commit_timestamp=$(git show -s --format=%ct)

function put_metric {
  # This call to publish the metric could fail but we don't want to fail the build +e turns off exit on error
  set +e
  aws cloudwatch put-metric-data \
    --timestamp "$commit_timestamp" \
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
put_metric --metric-name FolderSize --value "$SOURCE_CODE_SIZE" --unit Bytes --dimensions "Folder=root,${common_dimensions}"

for FOLDER_PATH in "$SRC_ROOT"/*/ ; do
    FOLDER_SIZE=$(size "$FOLDER_PATH")
    FOLDER=$(basename "$FOLDER_PATH")
    put_metric --metric-name FolderSize --value "$FOLDER_SIZE" --unit Bytes --dimensions "Folder=${FOLDER},${common_dimensions}"
done

function run_build_and_collect_metrics {
  cmake_build_flags=("-DCMAKE_BUILD_TYPE=Release")
  if [[ "$small" == "ON" ]]; then
    build_size="Small"
    cmake_build_flags+=("-DOPENSSL_SMALL=1")
  else
    build_size="Large"
  fi
  if [[ "$no_assembly" == "ON" ]]; then
    assembly="NoAsm"
    cmake_build_flags+=("-DOPENSSL_NO_ASM=1")
  else
    assembly="Asm"
  fi

  cmake_build_flags+=("-DBUILD_SHARED_LIBS=${shared_library}")
  if [[ "$shared_library" == "ON" ]]; then
    linking="Shared"
    lib_extension="so"
  else
    linking="Static"
    lib_extension="a"
  fi
  if [[ "$fips" == "ON" ]]; then
    fips_mode="FIPS"
    cmake_build_flags+=("-DFIPS=1")
  else
    fips_mode="NotFIPS"
  fi
  size_common_dimensions="${common_dimensions},Optimization=Release,BuildSize=${build_size},Assembly=${assembly},CPU=${PLATFORM},Linking=${linking},FIPS=${fips_mode}"

  build_start=$(date +%s)
  run_build "${cmake_build_flags[@]}"
  build_end=$(date +%s)
  build_time=$((build_end-build_start))
  put_metric --metric-name BuildTime --value "$build_time" --unit Seconds --dimensions "$size_common_dimensions"

  test_start=$(date +%s)
  run_cmake_custom_target 'run_tests'
  test_end=$(date +%s)
  test_time=$((test_end-test_start))
  put_metric --metric-name TestTime --value "$test_time" --unit Seconds --dimensions "$size_common_dimensions"

  libcrypto_size=$(size "${BUILD_ROOT}/crypto/libcrypto.${lib_extension}")
  libssl_size=$(size "${BUILD_ROOT}/ssl/libssl.${lib_extension}")
  tool_size=$(size "${BUILD_ROOT}/tool/bssl")
  put_metric --metric-name LibCryptoSize --value "$libcrypto_size" --unit Bytes --dimensions "${size_common_dimensions}"
  put_metric --metric-name LibSSLSize --value "$libssl_size" --unit Bytes --dimensions "${size_common_dimensions}"
  put_metric --metric-name ToolSize --value "$tool_size" --unit Bytes --dimensions "${size_common_dimensions}"

  pushd .
  cd "$BUILD_ROOT"
  for file_path in $(find . -type f -name "*.o"); do
    object_size=$(size "${BUILD_ROOT}/${file_path}")
    # Cleanup the file names ./crypto/fipsmodule/CMakeFiles/fipsmodule.dir/bcm.c.o -> crypto/fipsmodule/bcm.c.o
    # sed has there own regex format, [[:alpha:]] matches one Alphabetic character
    file_name=$(sed -e "s/CMakeFiles\///g" -e "s/[[:alpha:]]*\.dir\///g" <<< "$file_path" | cut -c 3-)
    put_metric --metric-name ObjectSize --value "$object_size" --unit Bytes --dimensions "File=${file_name},${size_common_dimensions}"
  done
  popd
}

fips=OFF
for shared_library in ON OFF; do
  for small in ON OFF; do
    for no_assembly in ON OFF; do
      run_build_and_collect_metrics
    done
  done
done

# We only care about two FIPS dimensions
shared_library=ON
small=OFF
no_assembly=OFF
fips=ON
run_build_and_collect_metrics

# The static FIPS build only works on Linux platforms.
if [[ ("$(uname -s)" == 'Linux'*) && (("$(uname -p)" == 'x86_64'*) || ("$(uname -p)" == 'aarch64'*)) ]]; then
  shared_library=OFF
  run_build_and_collect_metrics
fi
