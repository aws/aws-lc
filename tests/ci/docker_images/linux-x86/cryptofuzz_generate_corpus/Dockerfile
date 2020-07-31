# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:19.10

SHELL ["/bin/bash", "-c"]

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
    ca-certificates \
    wget \
    zip \
    unzip \
    curl \
    libboost-all-dev && \
    cd /tmp && \
    wget https://dl.google.com/go/go1.13.12.linux-amd64.tar.gz && \
    tar -xvf go1.13.12.linux-amd64.tar.gz && \
    mv go /usr/local && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV DEPENDENCIES_DIR=/home/dependencies
ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project

RUN set -ex && \
    apt -o APT::Sandbox::User=root update && \
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
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
ENV CFLAGS="-fsanitize=address,undefined,fuzzer-no-link -O2 -g"
ENV CXXFLAGS="-fsanitize=address,undefined,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"
ENV ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer

# Generate some necessary headers for aws-lc-cryptofuzz
RUN cd aws-lc-cryptofuzz/ && \
    python2 gen_repository.py

# Set environment variables so that cryptofuzz can find AWS-LC
ENV CXXFLAGS="$CXXFLAGS -DCRYPTOFUZZ_NO_OPENSSL"

# Set fuzzer in environment variable
ENV LIBFUZZER_LINK="-fsanitize=fuzzer"

# Generate corpus
CMD cd /aws-lc-cryptofuzz/ && \
    make && \
    mkdir /mount/efs/corpus/ && \
    ./generate_corpus /mount/efs/corpus/

