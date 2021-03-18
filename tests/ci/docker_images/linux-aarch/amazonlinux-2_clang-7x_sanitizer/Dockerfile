# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM amazonlinux-2-aarch:clang-7x

SHELL ["/bin/bash", "-c"]

ENV DEPENDENCIES_DIR=/home/dependencies
ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project

# llvm, llvm-devel, libcxx, and libcxxabi are needed for the sanitizer tests.
# 11.1.0 is the latest stable release as of 2021-02-16.
# See https://github.com/google/sanitizers/wiki/MemorySanitizerLibcxxHowTo
RUN set -ex && \
    yum -y update && yum install -y \
    llvm-devel \
    llvm && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-11.1.0  --depth 1 && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer
