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
    --setopt=install_weak_deps=False --best && \
    dnf -y autoremove && \
    dnf clean all && \
    rm -rf /tmp/*

# Set environment variables for building
ENV CC=clang-9
ENV CXX=clang++-9
ENV CFLAGS="-fsanitize=address,undefined,fuzzer-no-link -O2 -g"
ENV CXXFLAGS="-fsanitize=address,undefined,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"

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
