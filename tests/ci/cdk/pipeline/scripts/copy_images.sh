#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exuo pipefail

source util.sh

PROD_ACCOUNT="620771051181"
PRE_PROD_ACCOUNT="351119683581"
AWS_REGION="us-west-2"

PROD_ACCOUNT_ARN="arn:aws:iam::${PROD_ACCOUNT}:role/CrossAccountBuildRole"
PRE_PROD_ACCOUNT_ARN="arn:aws:iam::${PRE_PROD_ACCOUNT}:role/CrossAccountBuildRole"

function copy_images() {
  declare -A IMAGES_TO_PUSH

  # First authenticate with pre-prod account
  assume_role "$PRE_PROD_ACCOUNT_ARN"
  PRE_PROD_REGISTRY="${PRE_PROD_ACCOUNT}.dkr.ecr.${AWS_REGION}.amazonaws.com"
  aws ecr get-login-password --region ${AWS_REGION} | docker login --username AWS --password-stdin "$PRE_PROD_REGISTRY"

  # Process each repository and collect all images with _latest tags
  for repo in $REPOS; do
    echo "Processing repo: $repo"

    image_details=$(aws ecr describe-images --repository-name "$repo" --region ${AWS_REGION} \
            --query 'imageDetails[?length(imageTags) > `0` && imageTags[?ends_with(@, `_latest`)]].{ImageNamesWithTag: imageTags[*] | [*].join(`:`, [`'"${repo}"'`, @]), ImageDigest: imageDigest}' \
            --output json)
    
    # Process each image with _latest tag
    for image in $(echo "${image_details}" | jq -c '.[]'); do
      image_digest=$(echo "$image" | jq -r '.ImageDigest')
      image_names_with_tag=$(echo "$image" | jq -r '.ImageNamesWithTag[]')

      echo "Pulling image ${repo}@${image_digest}"
      docker pull "${PRE_PROD_REGISTRY}/${repo}@${image_digest}"

      IMAGES_TO_PUSH["${repo}@${image_digest}"]="${image_names_with_tag}"
    done
  done

  # Switch to prod account
  unset AWS_ACCESS_KEY_ID
  unset AWS_SECRET_ACCESS_KEY
  unset AWS_SESSION_TOKEN
  
  # Authenticate with prod account
  assume_role "$PROD_ACCOUNT_ARN"
  PROD_REGISTRY="${PROD_ACCOUNT}.dkr.ecr.${AWS_REGION}.amazonaws.com"
  aws ecr get-login-password --region ${AWS_REGION} | docker login --username AWS --password-stdin "$PROD_REGISTRY"
  
  # Push all collected images to prod
  # NOTE: New images have a lifecycle policy of 30 days. However, since we're preserving the tag created from the
  # pre-production stage, the date tag on the production images will not match their expiration date
  for image in "${!IMAGES_TO_PUSH[@]}"; do
      image_names_with_tag="${IMAGES_TO_PUSH[$image]}"

      for image_name_with_tag in $image_names_with_tag; do
          echo "Tagging and pushing: $image_name_with_tag"
          docker tag "${PRE_PROD_REGISTRY}/$image" "${PROD_REGISTRY}/$image_name_with_tag"
          docker push "${PROD_REGISTRY}/$image_name_with_tag"
      done
  done

  echo "Successfully copied images from pre-prod to prod"
}

while [[ $# -gt 0 ]]; do
  case ${1} in
  --repos)
    REPOS="${2}"
    shift
    ;;
  --platform)
    PLATFORM="${2}"
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
  echo "No ECR repository provided"
  exit 1
fi

copy_images
