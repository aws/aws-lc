#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# Based on Intel SDE README, SELinux should be turned off to allow pin to work.
# https://software.intel.com/content/www/us/en/develop/articles/intel-software-development-emulator.html#system-configuration
if [[ "$(getenforce)" == 'Disabled' ]]; then
  echo "SELinux is disabled. Disabling SELinux is needed by sde to allow pin work.";
else
  echo "SELinux should be turned off to allow sde pin to work." && exit 1;
fi

echo "Testing AWS-LC in debug mode under Intel's SDE."
build_and_test_with_sde

echo "Testing AWS-LC in release mode under Intel's SDE."
build_and_test_with_sde -DCMAKE_BUILD_TYPE=Release

echo "Testing AWS-LC in RelWithDebInfo mode under Intel's SDE with address sanitizer."
build_and_test_with_sde -DCMAKE_BUILD_TYPE=RelWithDebInfo -DASAN=1
