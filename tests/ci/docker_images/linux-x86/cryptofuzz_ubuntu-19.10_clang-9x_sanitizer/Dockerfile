# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:19.10

SHELL ["/bin/bash", "-c"]
ENV DEPENDENCIES_DIR=/home/dependencies
ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project

COPY . .

# Install dependencies
RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    clang \
    pkg-config \
    libunwind-dev \
    cmake \
    ninja-build \
    perl \
    golang \
    python2 \
    python \
    curl \
    zip \
    unzip \
    libboost-all-dev \
    wget \
    git \
    ca-certificates \
    mercurial \
    bison \
    flex \
    texinfo && \
    cd /tmp && \
    wget https://dl.google.com/go/go1.13.12.linux-amd64.tar.gz && \
    tar -xvf go1.13.12.linux-amd64.tar.gz && \
    mv go /usr/local && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/* 

# llvm, llvm-dev, libcxx, and libcxxabi are needed for the sanitizer tests. Git and ca-certificates are needed to get
# the llvm-project, 8.0.1 is the latest stable release as of 2019-12-06.
# See https://github.com/google/sanitizers/wiki/MemorySanitizerLibcxxHowTo
RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends install \
    llvm \
    llvm-dev \
    lld \
    libtool && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-8.0.1  --depth 1 && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

# Set environment variables for building
ENV CC=clang-9
ENV CXX=clang++-9
ENV CFLAGS="-fsanitize=address,undefined,fuzzer-no-link -O2 -g"
ENV CXXFLAGS="-fsanitize=address,undefined,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"

RUN source build_configs_install_deps.sh

# Build aws-lc and run cryptofuzz
CMD aws s3 cp s3://${GITHUB_CODE_BUCKET}/${REPO_OWNER}/${REPO_NAME}/${REPO_OWNER}_${REPO_NAME}.zip ./ && \
    unzip ${REPO_OWNER}_${REPO_NAME}.zip -d aws-lc && \
    cd / && \
    ls && \
    cd aws-lc/ && \
    mkdir build/ && \
    cd build/ && \
    cmake -DCMAKE_CXX_FLAGS="$CXXFLAGS" -DCMAKE_C_FLAGS="$CFLAGS" -DBORINGSSL_ALLOW_CXX_RUNTIME=1 .. && \
    make crypto -j$(nproc) && \
    cd / && \
    cd aws-lc-cryptofuzz/modules/openssl/ && \
    make && \
    cd / && \
    chmod +x cryptofuzz.sh && \
    ./cryptofuzz.sh 
