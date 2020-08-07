# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM fedora:31

SHELL ["/bin/bash", "-c"]

COPY . .

# Install dependencies
RUN dnf -y install \
    llvm \
    clang \
    compiler-rt \
    libunwind-devel \
    cmake \
    ninja-build \
    perl \
    golang \
    python2 \
    python \
    curl \
    zip \
    unzip \
    boost-devel \
    git \
    ca-certificates \
    libtool \
    mercurial \
    bison \
    flex \
    texinfo \
    wget \
    quilt \
    --setopt=install_weak_deps=False --best && \
    dnf -y autoremove && \
    dnf clean all && \
    rm -rf /tmp/*

# Set environment variables for building
ENV CC=clang-9
ENV CXX=clang++-9
ENV CFLAGS="-fsanitize=address,undefined,fuzzer-no-link -O2 -g"
ENV CXXFLAGS="-fsanitize=address,undefined,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"

# Build all other crypto libraries to fuzz against
RUN source build_configs_install_deps.sh

# Build aws-lc and run cryptofuzz
CMD source run_aws_lc_cryptofuzz.sh
