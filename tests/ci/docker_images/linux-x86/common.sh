#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

function validate_input() {
  key="${1}"
  value="${2}"
  if [[ -z "${value}" ]]; then
    echo "The value of ${key} is empty."
    exit 1
  fi
}

# Tag images with date to help find old images, CodeBuild uses the latest tag and gets updated automatically.
function tag_and_push_img() {
  source="${1}"
  validate_input 'source' "${source}"
  target="${2}"
  validate_input 'target' "${target}"
  img_push_date=$(date +%Y-%m-%d)
  docker_img_with_latest="${target}_latest"
  docker_img_with_date="${target}_${img_push_date}"
  docker tag "${source}" "${docker_img_with_latest}"
  docker tag "${source}" "${docker_img_with_date}"
  docker push "${docker_img_with_latest}"
  docker push "${docker_img_with_date}"
}
