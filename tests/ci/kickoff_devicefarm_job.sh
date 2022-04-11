#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -exuo pipefail

# -e: Exit on any failure
# -x: Print the command before running
# -u: Any variable that is not set will cause an error if used
# -o pipefail: Makes sure to exit a pipeline with a non-zero error code if any command in the pipeline exists with a
#              non-zero error code.

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
  if [[ -z "${DEVICEFARM_PROJECT+x}" || -z "${DEVICEFARM_PROJECT}" ]]; then
    export DEVICEFARM_PROJECT='arn:aws:devicefarm:us-west-2:069218930244:project:e6898943-4414-4ab0-a5d5-b254e33ea53c'
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
  if [[ -z "${DEVICEFARM_DEVICE_POOL+x}" || -z "${DEVICEFARM_DEVICE_POOL}" ]]; then
    if [[ "${FIPS}" = true ]]; then
      # Device pool arn for FIPS.
      export DEVICEFARM_DEVICE_POOL='arn:aws:devicefarm:us-west-2:069218930244:devicepool:e6898943-4414-4ab0-a5d5-b254e33ea53c/ba9f292c-6f3b-4364-9c85-88d9aca371ce'
    else
      # Device pool arn for non-FIPS.
      export DEVICEFARM_DEVICE_POOL='arn:aws:devicefarm:us-west-2:069218930244:devicepool:e6898943-4414-4ab0-a5d5-b254e33ea53c/d62026d5-fb81-45f1-9ef4-2158d654708c'
    fi
  fi
}

function compile_for_android() {
  # |ANDROID_APK| and |ANDROID_TEST_APK| are apk names corresponding to the settings in the test runner gradle file.
  cd android/AWSLCAndroidTestRunner
  export ANDROID_APK_LOCATION='android/AWSLCAndroidTestRunner/app/build/outputs/apk'
  if [[ "${FIPS}" = true ]]; then
    ./gradlew assembleDebug assembleAndroidTest -PFIPS
    export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_fips.apk"
    export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_fips-androidTest.apk"
  else
    if [[ "${RELEASE}" = true ]]; then
      if [[ "${SHARED}" = true ]]; then
        ./gradlew assembleDebug assembleAndroidTest -PRelease -PShared
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_shared_rel.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_shared_rel-androidTest.apk"
      else
        ./gradlew assembleDebug assembleAndroidTest -PRelease
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_static_rel.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_static_rel-androidTest.apk"
      fi
    else
      if [[ "${SHARED}" = true ]]; then
        ./gradlew assembleDebug assembleAndroidTest -PShared
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_shared_dbg.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_shared_dbg-androidTest.apk"
      else
        ./gradlew assembleDebug assembleAndroidTest
        export ANDROID_APK="${ANDROID_APK_LOCATION}/debug/awslc_static_dbg.apk"
        export ANDROID_TEST_APK="${ANDROID_APK_LOCATION}/androidTest/debug/awslc_static_dbg-androidTest.apk"
      fi
    fi
  fi
  cd ../../
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
      export DEVICEFARM_PROJECT="${2}"
      shift
      ;;
    --devicefarm-device-pool-arn)
      export DEVICEFARM_DEVICE_POOL="${2}"
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
    python3 ./devicefarm_job.py
    ;;
  *)
    echo "--action is required. Use '--help' to see allowed actions."
    exit 1
    ;;
  esac
}

# Invoke main
main "$@"