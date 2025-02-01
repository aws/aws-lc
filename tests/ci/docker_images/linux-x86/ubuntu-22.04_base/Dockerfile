# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu:22.04

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive

ENV BOOST_PACKAGE_NAME=boost_1_77_0
ENV BOOST_TARBALL="${BOOST_PACKAGE_NAME}.tar.bz2"
ENV BOOST_SRC_URL="https://d2yr98kym3baw0.cloudfront.net/${BOOST_TARBALL}"
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
    automake \
    check \
    cmake \
    curl \
    make \
    sudo \
    ninja-build \
    patch \
    perl \
    libunwind-dev \
    pkg-config \
    git \
    gnutls-dev \
    ca-certificates \
    wget \
    lld \
    llvm \
    llvm-dev \
    libcryptx-perl \
    libicu-dev \
    libio-socket-ssl-perl \
    libipc-run-perl \
    libjson-perl \
    liblua5.4-dev \
    libnet-dev \
    libnet-ssleay-perl \
    libpam0g-dev \
    libpcap-dev \
    libperl-dev \
    libpcre2-dev \
    libreadline-dev \
    libsqlite3-dev \
    libtool \
    libudev-dev \
    socat \
    zlib1g-dev \
    dpkg-dev \
    flex \
    bison \
    jq \
    unzip && \
    # Based on https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2-linux.html
    # The awscli is used to publish data to CloudWatch Metrics in some jobs. This requires additional IAM permission
    curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip" && \
    unzip awscliv2.zip && \
    ./aws/install --bin-dir /usr/bin && \
    rm -rf awscliv2.zip aws/ && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    # Extract and install Boost 1.77.0. mySQL 8.33 depends on this specific version.
    wget ${BOOST_SRC_URL} && tar xfj ${BOOST_TARBALL} && mv ./${BOOST_PACKAGE_NAME} ./boost && rm ${BOOST_TARBALL} && \
    # Download a copy of LLVM's libcxx which is required for building and running with Memory Sanitizer
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-11.1.0  --depth 1 && \
    cd llvm-project && rm -rf $(ls -A | grep -Ev "(libcxx|libcxxabi)") && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

COPY install_common_dependencies.sh /
RUN set -ex && /install_common_dependencies.sh && rm install_common_dependencies.sh
