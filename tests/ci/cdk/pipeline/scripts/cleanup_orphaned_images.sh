#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exuo pipefail

source util.sh

export CROSS_ACCOUNT_BUILD_ROLE_ARN="arn:aws:iam::${DEPLOY_ACCOUNT}:role/CrossAccountBuildRole"
export CROSS_ACCOUNT_BUILD_SESSION="pipeline-${CODEBUILD_RESOLVED_SOURCE_VERSION}"

function remove_pending_images() {
  local repo=${1}

  # List all images in the repository and filter the ones with any tag ending with '_pending'
  image_details=$(aws ecr describe-images --repository-name "$repo" --query 'imageDetails[?length(imageTags) > `0` && imageTags[?ends_with(@, `_pending`)]].{ImageDigest:imageDigest,Tags:imageTags}' --output json)

  if [ -z "$image_details" ]; then
    echo "No images found with tags ending in '_pending'."
    exit 0
  fi

  # Loop through and delete each image by its digest
  for image in $(echo "${image_details}" | jq -c '.[]'); do
    image_digest=$(echo "$image" | jq -r '.ImageDigest')
    tags=$(echo "$image" | jq -r '.Tags[]')

    for tag in $tags; do
      if [[ "$tag" == *"_pending" ]]; then
        new_tag="${tag%_pending}_latest" # Replace '_pending' with '_latest'

        if echo "${tags}" | grep -q "${new_tag}"; then
          echo "Image with digest $image_digest is tagged as latest. Will only be removing pending tag..."
          # Delete the pending tag
          aws ecr batch-delete-image --repository-name "$repo" --image-ids imageTag="$tag"
        else
          echo "Deleting image with digest: $image_digest..."

          # Delete the image by its digest
          aws ecr batch-delete-image --repository-name "$repo" --image-ids imageDigest="$image_digest"
        fi

        if [ $? -eq 0 ]; then
          echo "Image $image_digest with _pending tag removed successfully."
        else
          echo "Failed to cleanup image $image_digest."
        fi
        break
      fi
    done
  done

  echo "Cleanup complete."
}

while [[ $# -gt 0 ]]; do
  case ${1} in
  --repos)
    REPOS="${2}"
    shift
    ;;
  *)
    echo "${1} is not supported."
    exit 1
    ;;
  esac
  shift
done

if [[ -z "${REPOS:+x}" ]]; then
  echo "No build type provided."
  exit 1
fi

assume_role

for repo in ${REPOS}; do
  remove_pending_images "${repo}" &
done

wait
