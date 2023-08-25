#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Requires:
# * Install qemu-user-static

# Note:
# On Linux, you can see which architectures that qemu is registered for by looking
# under `/proc/sys/fs/binfmt_misc`.

# If needed, you can clear these entries using the following command:
# `sudo find /proc/sys/fs/binfmt_misc -type f -name 'qemu-*' -exec sh -c 'echo -1 > {}' \;`

# Log Docker hub limit https://docs.docker.com/docker-hub/download-rate-limit/#how-can-i-check-my-current-rate
TOKEN=$(curl "https://auth.docker.io/token?service=registry.docker.io&scope=repository:ratelimitpreview/test:pull" | jq -r .token)
curl --head -H "Authorization: Bearer $TOKEN" https://registry-1.docker.io/v2/ratelimitpreview/test/manifests/latest

SCRIPT_DIR=$(dirname "$(readlink -f "${0}")")

docker run --rm --privileged multiarch/qemu-user-static --reset -p yes

docker buildx create --use
docker buildx build --platform linux/amd64 -t ubuntu-ppc64le:build-tools "${SCRIPT_DIR}"/ubuntu-build-tools --load
