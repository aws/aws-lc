# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2023-aarch:clang-15x

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    dnf -y upgrade --releasever=latest && dnf install -y \
    make \
    automake \
    autoconf \
    libtool \
    boost-devel \
    unzip \
    llvm \
    llvm-devel \
    lld && \
    dnf clean packages && \
    dnf clean metadata && \
    dnf clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/dnf

ENV FUZZ_ROOT=${DEPENDENCIES_DIR}
ENV MODULE_ROOT="${FUZZ_ROOT}/modules"

COPY build_cryptofuzz_modules.sh cryptofuzz_data.zip $FUZZ_ROOT/
RUN set -ex && cd $FUZZ_ROOT && "./build_cryptofuzz_modules.sh"
