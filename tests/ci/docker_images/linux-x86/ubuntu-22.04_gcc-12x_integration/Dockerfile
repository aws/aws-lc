# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu-22.04:gcc-12x

SHELL ["/bin/bash", "-c"]

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
    doxygen \
    gcovr \
    gettext \
    gobject-introspection \
    gnupg \
    gperf \
    groff \
    iproute2 \
    lcov \
    libcap-dev \
    libcurl4-openssl-dev \
    libevent-dev \
    libfstrm-dev \
    libftdi-dev \
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
    libpsl-dev \
    libprotobuf-c-dev \
    libssl-dev \
    libsystemd-dev \
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
    uthash-dev \
    uuid-dev && \
    pip3 install gcovr && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

RUN adduser --disabled-password --gecos '' integration && \
    adduser integration sudo && \
    echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers