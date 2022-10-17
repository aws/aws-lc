#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

########################################
# Build images from AWS-LC GitHub repo #
########################################

# Log Docker hub limit https://docs.docker.com/docker-hub/download-rate-limit/#how-can-i-check-my-current-rate
TOKEN=$(curl "https://auth.docker.io/token?service=registry.docker.io&scope=repository:ratelimitpreview/test:pull" | jq -r .token)
curl --head -H "Authorization: Bearer $TOKEN" https://registry-1.docker.io/v2/ratelimitpreview/test/manifests/latest

docker build -t rust:linux-386 linux-386
docker build -t rust:linux-arm64 linux-arm64
docker build -t rust:linux-x86_64 linux-x86_64
