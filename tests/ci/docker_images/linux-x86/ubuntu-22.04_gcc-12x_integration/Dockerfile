# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu-22.04:gcc-12x

SHELL ["/bin/bash", "-c"]

# Define Ruby version (used to build Ruby).
ARG RUBY_VERSION=3.4.3

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    autoconf \
    autoconf-archive \
    autogen \
    binutils-dev \
    build-essential \
    clang-format \
    dnsutils \
    doxygen \
    gcovr \
    gettext \
    gobject-introspection \
    gnupg \
    gperf \
    groff \
    iproute2 \
    lcov \
    ldnsutils \
    libcap-dev \
    libcurl4-openssl-dev \
    libev-dev \
    libevent-dev \
    libexpat1-dev \
    libfstrm-dev \
    libftdi-dev \
    libgcrypt20-dev \
    libglib2.0-dev \
    libgmp-dev \
    libini-config-dev \
    libcap-ng-dev \
    libcmocka0 \
    libcmocka-dev \
    libjemalloc-dev \
    libjson-c-dev \
    libltdl-dev \
    liblz4-dev \
    liblzo2-dev \
    libnghttp2-dev \
    libnl-3-dev \
    libnl-genl-3-dev \
    libpam-dev \
    libpcre3-dev  \
    libprocps-dev \
    libprotobuf-c-dev \
    libpsl-dev \
    libssl-dev \
    libsystemd-dev \
    liburcu-dev \
    libusb-1.0-0-dev \
    libuv1-dev \
    libxml2-dev \
    libyaml-dev \
    meson \
    net-tools \
    netcat-openbsd \
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
    splint \
    uthash-dev \
    uuid-dev \
    vim-common \
    xxd && \
    # Download and install Ruby using the version from ARG
    cd /tmp && \
    wget https://cache.ruby-lang.org/pub/ruby/$(echo ${RUBY_VERSION} | cut -d. -f1-2)/ruby-${RUBY_VERSION}.tar.gz && \
    tar -xzf ruby-${RUBY_VERSION}.tar.gz && \
    cd ruby-${RUBY_VERSION} && \
    ./configure --disable-install-doc && \
    make -j "$(nproc)" && \
    make install && \
    ruby -v && \
    pip3 install gcovr && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

RUN adduser --disabled-password --gecos '' integration && \
    adduser integration sudo && \
    echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers