# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM arm64v8/ubuntu:20.04

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive

ENV DEPENDENCIES_DIR=/home/dependencies
ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project
ENV ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"

# llvm, llvm-dev, libcxx, and libcxxabi are needed for the sanitizer tests.
# 11.1.0 is the latest stable release as of 2021-02-16.
# See https://github.com/google/sanitizers/wiki/MemorySanitizerLibcxxHowTo
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
    curl \
    unzip && \
    # Based on https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2-linux.html
    # The awscli is used to publish data to CloudWatch Metrics in some jobs. This requires additional IAM permission
    curl "https://awscli.amazonaws.com/awscli-exe-linux-aarch64.zip" -o "awscliv2.zip" && \
    unzip awscliv2.zip && \
    ./aws/install --bin-dir /usr/bin && \
    rm -rf awscliv2.zip aws/ && \
    # Download a copy of LLVM's libcxx which is required for building and running with Memory Sanitizer
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-11.1.0  --depth 1 && \
    cd llvm-project && rm -rf $(ls -A | grep -Ev "(libcxx|libcxxabi)") && \
    apt-get --purge remove -y curl unzip && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

COPY install_common_dependencies.sh /
RUN set -ex && /install_common_dependencies.sh && rm install_common_dependencies.sh
