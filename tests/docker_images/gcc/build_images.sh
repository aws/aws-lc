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
curl --output-dir "${SCRIPT_DIR}"/4.8 -LO https://go.dev/dl/go1.18.10.linux-amd64.tar.gz
curl --output-dir "${SCRIPT_DIR}"/4.8 -LO https://github.com/Kitware/CMake/releases/download/v3.6.3/cmake-3.6.3-Linux-x86_64.tar.gz
docker buildx build -t aws-lc:gcc-4.8 "${SCRIPT_DIR}"/4.8 --load
rm "${SCRIPT_DIR}"/4.8/go1.18.10.linux-amd64.tar.gz
rm "${SCRIPT_DIR}"/4.8/cmake-3.6.3-Linux-x86_64.tar.gz

## GCC-7.2
curl --output-dir "${SCRIPT_DIR}"/7.2 -LO https://go.dev/dl/go1.18.10.linux-amd64.tar.gz
curl --output-dir "${SCRIPT_DIR}"/7.2 -LO https://github.com/Kitware/CMake/releases/download/v3.6.3/cmake-3.6.3-Linux-x86_64.tar.gz
docker buildx build -t aws-lc:gcc-7.2 "${SCRIPT_DIR}"/7.2 --load
rm "${SCRIPT_DIR}"/7.2/go1.18.10.linux-amd64.tar.gz
rm "${SCRIPT_DIR}"/7.2/cmake-3.6.3-Linux-x86_64.tar.gz

docker buildx rm ${BUILDER_NAME}

