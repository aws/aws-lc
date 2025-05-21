#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exuo pipefail

source util.sh

echo \"Environment variables:\"
env

if [[ -z "${NEED_REBUILD:+x}" || ${NEED_REBUILD} -eq 0 ]]; then
  echo "No rebuild needed"
  exit 0
fi

export COMMIT_HASH=${COMMIT_HASH:-$CODEBUILD_RESOLVED_SOURCE_VERSION}
export CROSS_ACCOUNT_BUILD_ROLE_ARN="arn:aws:iam::${DEPLOY_ACCOUNT}:role/CrossAccountBuildRole"
export CROSS_ACCOUNT_BUILD_SESSION="pipeline-${COMMIT_HASH}"

function build_codebuild_ci_project() {
  local attempt=0
  local project=${1}

  if [[ -z ${project} ]]; then
    echo "No project name provided."
    exit 1
  fi

  if [[ ${DEPLOY_ACCOUNT} == '351119683581' ]]; then
    source_version="main"
  else
    source_version=${COMMIT_HASH}
  fi

  while [[ ${attempt} -le ${MAX_RETRY} ]]; do
      if [[ ${attempt} -eq 0 ]]; then
        echo "Starting CI tests in ${project}"
        start_codebuild_project "${project}" "${source_version}"
      else
        echo "Retrying ${attempt}/${MAX_RETRY}..."
        retry_batch_build
      fi

      echo "Waiting for docker images creation. Building the docker images need to take 1 hour."
      # TODO(CryptoAlg-624): These image build may fail due to the Docker Hub pull limits made on 2020-11-01.
      if codebuild_build_status_check "${TIMEOUT}"; then
        echo "All tests completed successfully"
        exit 0
      fi

      attempt=$((attempt + 1))
    done

  echo "CI tests failed."
  exit 1
}

function build_linux_docker_images() {
  local attempt=0

  while [[ ${attempt} -le ${MAX_RETRY} ]]; do
    if [[ ${attempt} -eq 0 ]]; then
      echo "Activating AWS CodeBuild to build Linux aarch & x86 docker images."
      start_codebuild_project aws-lc-docker-image-build-linux "${COMMIT_HASH}"
    else
      echo "Retrying ${attempt}/${MAX_RETRY}..."
      retry_batch_build
    fi

    echo "Waiting for docker images creation. Building the docker images need to take 1 hour."
    # TODO(CryptoAlg-624): These image build may fail due to the Docker Hub pull limits made on 2020-11-01.
    if codebuild_build_status_check "${TIMEOUT}"; then
      echo "Successfully built Linux docker images"
      exit 0
    fi

    attempt=$((attempt + 1))
  done

  echo "Failed to build Linux docker images"
  exit 1
}

function build_win_docker_images() {
  local attempt=0

  while [[ ${attempt} -le ${MAX_RETRY} ]]; do
    echo "Executing AWS SSM commands to build Windows docker images."
    if ! start_windows_img_build; then
      echo "Failed to start build"
      continue
    fi

    echo "Waiting for docker images creation. Building the docker images need to take 1 hour."
    # TODO(CryptoAlg-624): These image build may fail due to the Docker Hub pull limits made on 2020-11-01.
    if ! win_docker_img_build_status_check "${TIMEOUT}"; then
      echo "Build failed"
      attempt=$((attempt + 1))
      echo "Retrying ${attempt}/${MAX_RETRY}..."
      continue
    fi

    echo "Successfully built Windows docker images"
    exit 0
  done

  echo "Failed to build Windows docker images"
  exit 1
}

while [[ $# -gt 0 ]]; do
  case ${1} in
  --build-type)
    BUILD_TYPE="${2}"
    shift
    ;;
  --platform)
    PLATFORM="${2}"
    shift
    ;;
  --project)
    PROJECT="${2}"
    shift
    ;;
  --max-retry)
    MAX_RETRY="${2}"
    shift
    ;;
  --timeout)
    TIMEOUT="${2}"
    shift
    ;;
  *)
    echo "${1} is not supported."
    exit 1
    ;;
  esac
  shift
done

MAX_RETRY=${MAX_RETRY:-0}
TIMEOUT=${TIMEOUT:-180} # 3 hours F

if [[ -z ${BUILD_TYPE} ]]; then
  echo "No build type provided."
  exit 1
fi

assume_role

if [[ -z "${BUILD_TYPE:+x}" ]]; then
  echo "No build type provided."
  exit 1
fi

if [[ ${BUILD_TYPE} == "docker" ]]; then
  if [[ -z "${PLATFORM:+x}" ]]; then
    echo "When building Docker images, a platform must be specified."
    exit 1
  fi

  if [[ ${PLATFORM} == "linux" ]]; then
    build_linux_docker_images
  elif [[ ${PLATFORM} == "windows" ]]; then
    build_win_docker_images
  fi
  exit 0
fi

if [[ ${BUILD_TYPE} == "ci" ]]; then
  if [[ -z "${PROJECT:+x}" ]]; then
    echo "When building CI tests, a project name must be specified."
    exit 1
  fi

  build_codebuild_ci_project "${PROJECT}"
fi
