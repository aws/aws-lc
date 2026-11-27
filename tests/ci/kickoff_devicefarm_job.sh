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
    --max-wait-minutes              How long to upload the APKs and wait for the device farm run to finish. Default to 60.
    --resumable                     If the run has not finished after --max-wait-minutes, leave it running and
                                    exit successfully so that 'devicefarm_job.py wait' can resume it later.
    --action                        Required. The value can be:
	                                   'build': compiles the test APKs.
	                                   'run-job': kicks off a device farm job using APKs compiled by 'build'.
	                                   'start-job': compiles the test APKs and kicks off a device farm job.
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
  if [[ -z "${MAX_WAIT_MINUTES+x}" || -z "${MAX_WAIT_MINUTES}" ]]; then
    export MAX_WAIT_MINUTES=60
  fi
  if [[ -z "${RESUMABLE+x}" || -z "${RESUMABLE}" ]]; then
    export RESUMABLE=false
  fi
}

function export_apk_paths() {
  # |ANDROID_APK| and |ANDROID_TEST_APK| are apk names corresponding to the settings in the test runner gradle file.
  local apk_location='android/AWSLCAndroidTestRunner/app/build/outputs/apk'
  local apk_name
  if [[ "${FIPS}" = true ]]; then
    apk_name='awslc_fips'
  elif [[ "${RELEASE}" = true ]]; then
    if [[ "${SHARED}" = true ]]; then
      apk_name='awslc_shared_rel'
    else
      apk_name='awslc_static_rel'
    fi
  else
    if [[ "${SHARED}" = true ]]; then
      apk_name='awslc_shared_dbg'
    else
      apk_name='awslc_static_dbg'
    fi
  fi
  export ANDROID_APK="${apk_location}/debug/${apk_name}.apk"
  export ANDROID_TEST_APK="${apk_location}/androidTest/debug/${apk_name}-androidTest.apk"
}

function compile_for_android() {
  # The working directory of this script should under `tests/ci`. 
  # AWSLCAndroidTestRunner should be at `tests/ci/android/AWSLCAndroidTestRunner`.
  # rust-phase2b CI probe (not for merge): Rust for the test runner's ABIs.
  # android-omnibus.yml runs from main, so the install can't go there.
  ./install_rust.sh aarch64-linux-android armv7-linux-androideabi x86_64-linux-android
  pushd android/AWSLCAndroidTestRunner
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
  else
    if [[ "${RELEASE}" = true ]]; then
      if [[ "${SHARED}" = true ]]; then
        # Release Shared
        ./gradlew assembleDebug assembleAndroidTest -PRelease -PShared --offline
      else
        # Release Static
        ./gradlew assembleDebug assembleAndroidTest -PRelease --offline
      fi
    else
      if [[ "${SHARED}" = true ]]; then
        # Debug Shared
        ./gradlew assembleDebug assembleAndroidTest -PShared --offline
      else
        # Debug Static
        ./gradlew assembleDebug assembleAndroidTest --offline
      fi
    fi
  fi
  popd
}

function run_devicefarm_job() {
  export_apk_paths
  local args=(start --max-wait-minutes "${MAX_WAIT_MINUTES}")
  if [[ "${RESUMABLE}" = true ]]; then
    args+=(--resumable)
  fi
  python3 -u ./devicefarm_job.py "${args[@]}"
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
    --max-wait-minutes)
      export MAX_WAIT_MINUTES="${2}"
      shift
      ;;
    --resumable)
      export RESUMABLE=true
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
  build)
    compile_for_android
    ;;
  run-job)
    run_devicefarm_job
    ;;
  start-job)
    compile_for_android
    run_devicefarm_job
    ;;
  *)
    echo "--action is required. Use '--help' to see allowed actions."
    exit 1
    ;;
  esac
}

# Invoke main
main "$@"