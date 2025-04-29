#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

# Log Docker hub limit https://docs.docker.com/docker-hub/download-rate-limit/#how-can-i-check-my-current-rate
TOKEN=$(curl "https://auth.docker.io/token?service=registry.docker.io&scope=repository:ratelimitpreview/test:pull" | jq -r .token)
curl --head -H "Authorization: Bearer $TOKEN" https://registry-1.docker.io/v2/ratelimitpreview/test/manifests/latest


SCRIPT_DIR=$(dirname "$(readlink -f "${0}")")


BUILDER_NAME=aws-lc-gcc-builder
if ! docker buildx inspect ${BUILDER_NAME}; then
    docker buildx create --name ${BUILDER_NAME} --use
fi

## GCC-4.8
docker buildx build --platform linux/amd64 -t aws-lc:gcc-4.8 "${SCRIPT_DIR}"/4.8 --load

docker buildx rm ${BUILDER_NAME}

