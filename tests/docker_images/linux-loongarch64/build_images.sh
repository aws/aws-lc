#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

# Note:
# After host reboot, qemu registration may need to be performed.
# `docker run --rm --privileged multiarch/qemu-user-static --reset -p yes`

# On Linux, you can see which architectures that qemu is registered for by looking
# under `/proc/sys/fs/binfmt_misc`.

# If needed, you can clear these entries using the following command:
# `sudo find /proc/sys/fs/binfmt_misc -type f -name 'qemu-*' -exec sh -c 'echo -1 > {}' \;`

# Log Docker hub limit https://docs.docker.com/docker-hub/download-rate-limit/#how-can-i-check-my-current-rate
TOKEN=$(curl "https://auth.docker.io/token?service=registry.docker.io&scope=repository:ratelimitpreview/test:pull" | jq -r .token)
curl --head -H "Authorization: Bearer $TOKEN" https://registry-1.docker.io/v2/ratelimitpreview/test/manifests/latest

SCRIPT_DIR=$(dirname "$(readlink -f "${0}")")

docker run --rm --privileged multiarch/qemu-user-static --reset -p yes

ARCH_NAME=loongarch64

X_TOOLS_FILE=${ARCH_NAME}-x-tools
if [ ! -f "./ubuntu-x-tools/${X_TOOLS_FILE}.tar.xz" ]; then
  wget "https://aws-libcrypto.s3.us-west-2.amazonaws.com/cross-compile-toolchains/host-x86_64-pc-linux-gnu/${X_TOOLS_FILE}.tar.xz"
  mv ${X_TOOLS_FILE}.tar.xz ./ubuntu-x-tools/
fi

BUILDER_NAME=${ARCH_NAME}-builder
if ! docker buildx inspect ${BUILDER_NAME}; then
    docker buildx create --name ${BUILDER_NAME} --use
fi

docker buildx build -t ubuntu-${ARCH_NAME}:x-tools "${SCRIPT_DIR}"/ubuntu-x-tools --load

docker buildx rm ${BUILDER_NAME}
