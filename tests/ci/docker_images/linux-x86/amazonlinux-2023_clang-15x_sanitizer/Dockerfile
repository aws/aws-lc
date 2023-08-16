# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2023:clang-15x

SHELL ["/bin/bash", "-c"]

ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project

RUN set -ex && \
    dnf -y upgrade --releasever=latest && dnf install -y \
    compiler-rt \
    llvm \
    llvm-devel \
    lld && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-15.0.6  --depth 1 && \
    cd llvm-project && rm -rf $(ls -A | grep -Ev "(libcxx|libcxxabi)") && \
    dnf clean packages && \
    dnf clean metadata && \
    dnf clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/dnf
