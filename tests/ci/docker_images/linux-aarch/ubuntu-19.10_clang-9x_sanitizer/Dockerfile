# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu-19.10-aarch:clang-9x

SHELL ["/bin/bash", "-c"]
ENV DEPENDENCIES_DIR=/home/dependencies
ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project

# llvm, llvm-dev, libcxx, and libcxxabi are needed for the sanitizer tests. Git and ca-certificates are needed to get
# the llvm-project, 8.0.1 is the latest stable release as of 2019-12-06.
# See https://github.com/google/sanitizers/wiki/MemorySanitizerLibcxxHowTo
RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends install \
    llvm \
    llvm-dev \
    lld \
    git \
    ca-certificates && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-8.0.1  --depth 1 && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=clang-9
ENV CXX=clang++-9
ENV ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer
