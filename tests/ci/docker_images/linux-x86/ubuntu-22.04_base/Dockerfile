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
    autoconf \
    autoconf-archive \
    autogen \
    binutils-dev \
    build-essential \
    check \
    cmake \
    curl \
    make \
    ninja-build \
    patch \
    perl \
    pkg-config \
    git \
    ca-certificates \
    sudo \
    wget \
    clang-format \
    doxygen \
    gcovr \
    gettext \
    gobject-introspection \
    gnupg \
    gnutls-dev \
    gperf \
    groff \
    iproute2 \
    lcov \
    lld \
    llvm \
    llvm-dev \
    libcap-dev \
    libcryptx-perl \
    libcurl4-openssl-dev \
    libevent-dev \
    libfstrm-dev \
    libftdi-dev \
    libglib2.0-dev \
    libgmp-dev \
    libicu-dev \
    libini-config-dev \
    libio-socket-ssl-perl \
    libipc-run-perl \
    libjson-perl \
    liblua5.4-dev \
    libcap-ng-dev \
    libcmocka0 \
    libcmocka-dev \
    libjemalloc-dev \
    libjson-c-dev \
    libltdl-dev \
    liblz4-dev \
    liblzo2-dev \
    libnghttp2-dev \
    libnet-dev \
    libnet-ssleay-perl \
    libnl-3-dev \
    libnl-genl-3-dev \
    libpam-dev \
    libpam0g-dev \
    libpcap-dev \
    libperl-dev \
    libpcre3-dev  \
    libpsl-dev \
    libprotobuf-c-dev \
    libreadline-dev \
    libsqlite3-dev \
    libssl-dev \
    libsystemd-dev \
    libtool \
    libudev-dev \
    libunwind-dev \
    liburcu-dev \
    libusb-1.0-0-dev \
    libuv1-dev \
    libyaml-dev \
    net-tools \
    openjdk-11-jdk \
    openssl \
    pandoc \
    procps \
    protobuf-c-compiler \
    python3 \
    python3-docutils \
    python3-pip \
    python3-pytest \
    python3-six \
    python3-sphinx \
    ruby \
    socat \
    uthash-dev \
    zlib1g-dev \
    dpkg-dev \
    flex \
    bison \
    jq \
    uuid-dev \
    unzip && \
    # Based on https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2-linux.html
    # The awscli is used to publish data to CloudWatch Metrics in some jobs. This requires additional IAM permission
    pip3 install gcovr && \
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