#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

# Device Farm project to designate Device Farm runs. The two device pools defined below should also belong to this project.
AWSLC_DEVICEFARM_PROJECT_NAME='aws-lc-ci'
# Device pool arn for non-FIPS.
AWSLC_ANDROID_POOL_NAME='android'
# Device pool arn for FIPS.
AWSLC_ANDROID_FIPS_POOL_NAME='android-fips'

###########################
# Main and related helper #
###########################

function script_helper() {
  cat <<EOF
This script helps compile AWSLCAndroidTestRunner and kick off the device farm python script with the arguments needed.

Options:
    --help                          Displays this help menu
    --test-name						          Name of current test.
    --devicefarm-project-arn        The devicefarm project's arn. Default to team account's.
    --devicefarm-device-pool-arn    The device pool's arn.
    --fips                          If we're compiling for FIPS or not. Will always compile for the FIPS, shared, release build.
    --release                       If we're compiling for Release or Debug.
    --shared                        If we're compiling for Shared or Static.
    --action                        Required. The value can be:
	                                   'start-job': kicks off a device farm job.
EOF
}

function export_global_variables() {
  # If these variables are not set or empty, defaults are exported, but the |main-apk| and |test-apk| must be set.
  if [[ -z "${ANDROID_TEST_NAME+x}" || -z "${ANDROID_TEST_NAME}" ]]; then
    export ANDROID_TEST_NAME='AWS-LC Android Test'
  fi
  if [[ -z "${DEVICEFARM_PROJECT_NAME+x}" || -z "${DEVICEFARM_PROJECT_NAME}" ]]; then
    export DEVICEFARM_PROJECT_NAME=$AWSLC_DEVICEFARM_PROJECT_NAME
  fi
  if [[ -z "${FIPS+x}" || -z "${FIPS}" ]]; then
    export FIPS=false
  fi
  if [[ -z "${RELEASE+x}" || -z "${RELEASE}" ]]; then
    export RELEASE=false
  fi
  if [[ -z "${SHARED+x}" || -z "${SHARED}" ]]; then
    export SHARED=false
  fi
  if [[ -z "${DEVICEFARM_DEVICE_POOL_NAME+x}" || -z "${DEVICEFARM_DEVICE_POOL_NAME}" ]]; then
    if [[ "${FIPS}" = true ]]; then
      # Device pool arn for FIPS.
      export DEVICEFARM_DEVICE_POOL_NAME=$AWSLC_ANDROID_FIPS_POOL_NAME
    else
      # Device pool arn for non-FIPS.
      export DEVICEFARM_DEVICE_POOL_NAME=$AWSLC_ANDROID_POOL_NAME
    fi
  fi
  if [[ -z "${AWS_REGION+x}" || -z "${AWS_REGION}" ]]; then
    export AWS_REGION='us-west-2'
  fi
}

function compile_for_android() {
  # |ANDROID_APK| and |ANDROID_TEST_APK| are apk names corresponding to the settings in the test runner gradle file.
  # The working directory of this script should under `tests/ci`. 
  # AWSLCAndroidTestRunner should be at `tests/ci/android/AWSLCAndroidTestRunner`.
  pushd android/AWSLCAndroidTestRunner
  export ANDROID_APK_LOCATION='android/AWSLCAndroidTestRunner/app/build/outputs/apk'
  if [[ "${FIPS}" = true ]]; then
    if [[ "${SHARED}" = true ]]; then
      # FIPS (Release Shared)
      ./gradlew assembleDebug assembleAndroidTest -PFIPS -PShared --offline
    else
      # FIPS (Release Static), go dependencies need to be copied from AWS-LC.
      mkdir app/src/main/cpp/util
      cp -r ../../../../util/godeps.go app/src/main/cpp/util/godeps.go
      cp -r ../../../../go.mod app/src/main/cpp/go.mod
      cp -r ../../../../go.sum app/src/main/cpp/go.sum
      ./gradlew assembleDebug assembleAndroidTest -PFIPS --offline
    fi
    export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_fips.apk"
    export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_fips-androidTest.apk"
  else
    if [[ "${RELEASE}" = true ]]; then
      if [[ "${SHARED}" = true ]]; then
        # Release Shared
        ./gradlew assembleDebug assembleAndroidTest -PRelease -PShared --offline
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_shared_rel.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_shared_rel-androidTest.apk"
      else
        # Release Static
        ./gradlew assembleDebug assembleAndroidTest -PRelease --offline
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_static_rel.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_static_rel-androidTest.apk"
      fi
    else
      if [[ "${SHARED}" = true ]]; then
        # Debug Shared
        ./gradlew assembleDebug assembleAndroidTest -PShared --offline
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_shared_dbg.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_shared_dbg-androidTest.apk"
      else
        # Debug Static
        ./gradlew assembleDebug assembleAndroidTest --offline
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_static_dbg.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_static_dbg-androidTest.apk"
      fi
    fi
  fi
  popd
}

function main() {
  # parse arguments.
  while [[ $# -gt 0 ]]; do
    case ${1} in
    --help)
      script_helper
      exit 0
      ;;
    --test-name)
      export ANDROID_TEST_NAME="${2}"
      shift
      ;;
    --devicefarm-project-arn)
      export DEVICEFARM_PROJECT_NAME="${2}"
      shift
      ;;
    --devicefarm-device-pool-arn)
      export DEVICEFARM_DEVICE_POOL_NAME="${2}"
      shift
      ;;
    --fips)
      export FIPS="${2}"
      shift
      ;;
    --release)
      export RELEASE="${2}"
      shift
      ;;
    --shared)
      export SHARED="${2}"
      shift
      ;;
    --action)
      export ACTION="${2}"
      shift
      ;;
    *)
      echo "${1} is not supported."
      exit 1
      ;;
    esac
    # Check next option -- key/value.
    shift
  done

  # Make sure action is set.
  if [[ -z "${ACTION+x}" || -z "${ACTION}" ]]; then
    echo "${ACTION} is required input."
    exit 1
  fi

  # Export global variables, which provides the contexts needed by ci setup/destroy.
  export_global_variables

  # Execute the action.
  case ${ACTION} in
  start-job)
    compile_for_android
    python3 -u ./devicefarm_job.py
    ;;
  *)
    echo "--action is required. Use '--help' to see allowed actions."
    exit 1
    ;;
  esac
}

# Invoke main
main "$@"