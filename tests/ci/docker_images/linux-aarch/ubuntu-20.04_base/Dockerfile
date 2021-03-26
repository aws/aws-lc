# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM arm64v8/ubuntu:20.04

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive

ENV DEPENDENCIES_DIR=/home/dependencies
ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project

# llvm, llvm-dev, libcxx, and libcxxabi are needed for the sanitizer tests.
# 11.1.0 is the latest stable release as of 2021-02-16.
# See https://github.com/google/sanitizers/wiki/MemorySanitizerLibcxxHowTo

# The awscli is used to publish data to CloudWatch Metrics in some jobs. This requires additional IAM permission
RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    software-properties-common \
    cmake \
    ninja-build \
    perl \
    libunwind-dev \
    pkg-config \
    git \
    ca-certificates \
    wget \
    lld \
    llvm \
    llvm-dev \
    awscli && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-11.1.0  --depth 1 && \
    cd /tmp && \
    wget https://dl.google.com/go/go1.15.2.linux-arm64.tar.gz && \
    tar -xvf go1.15.2.linux-arm64.tar.gz && \
    mv go /usr/local && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
ENV GO111MODULE=on
ENV ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer
