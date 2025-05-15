#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exuo pipefail

source util.sh

export CROSS_ACCOUNT_BUILD_ROLE_ARN="arn:aws:iam::${DEPLOY_ACCOUNT}:role/CrossAccountBuildRole"
export CROSS_ACCOUNT_BUILD_SESSION="pipeline-${CODEBUILD_RESOLVED_SOURCE_VERSION}"

function promote_pending_tags_to_latest() {
  local repo=${1}

  # Get the list of images with tags ending in "_pending"
  echo "Fetching images from repository '$repo'..."

  # List all images in the repository and filter the ones with any tag ending with '_pending'
  image_details=$(aws ecr describe-images --repository-name "$repo" --query 'imageDetails[?length(imageTags) > `0` && imageTags[?ends_with(@, `_pending`)]].{ImageDigest:imageDigest,Tags:imageTags}' --output json)

  if [ -z "$image_details" ]; then
    echo "No images found with tags ending in '_pending'."
    exit 0
  fi

  # Loop through each image and update the tags
  for image in $(echo "${image_details}" | jq -c '.[]'); do
    image_digest=$(echo "$image" | jq -r '.ImageDigest')
    tags=$(echo "$image" | jq -r '.Tags[]')

    # Check if any tag ends with '_pending'
    for tag in $tags; do
      if [[ "$tag" == *"_pending" ]]; then
        new_tag="${tag%_pending}_latest" # Replace '_pending' with '_latest'

        if echo "${tags}" | grep -q "${new_tag}"; then
          echo "Image with digest $image_digest already has tag '$new_tag' - skipping tag update"
          # Delete the pending tag
          aws ecr batch-delete-image --repository-name "$repo" --image-ids imageTag="$tag"
          break
        else
          echo "Updating tag '$tag' to '$new_tag' for image with digest: $image_digest"

          # Get the image manifest using the image digest
          image_manifest=$(aws ecr batch-get-image --repository-name "$repo" --image-ids imageDigest="$image_digest" --query 'images[0].imageManifest' --output text)

          # Push the new tag using batch-put-image
          aws ecr put-image --repository-name "$repo" --image-manifest "$image_manifest" --image-tag "$new_tag"
          aws ecr batch-delete-image --repository-name "$repo" --image-ids imageTag="$tag"
        fi

        if [ $? -eq 0 ]; then
          echo "Successfully updated tag '$tag' to '$new_tag'."
        else
          echo "Failed to update tag '$tag' to '$new_tag'."
        fi
        break
      fi
    done
  done

  echo "Tag update complete."
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
  promote_pending_tags_to_latest "${repo}" &
done

wait
