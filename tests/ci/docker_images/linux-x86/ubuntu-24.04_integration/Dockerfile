# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu-24.04:base

SHELL ["/bin/bash", "-c"]

# Define Ruby version (used to build Ruby).
ARG RUBY_VERSION=3.4.3

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    autoconf \
    binutils-dev \
    build-essential \
    libffi-dev \
    libgmp-dev \
    libssl-dev \
    libyaml-dev \
    zlib1g-dev &&\
    # Download and install Ruby using the version from ARG
    cd /tmp && \
    wget https://cache.ruby-lang.org/pub/ruby/$(echo ${RUBY_VERSION} | cut -d. -f1-2)/ruby-${RUBY_VERSION}.tar.gz && \
    tar -xzf ruby-${RUBY_VERSION}.tar.gz && \
    cd ruby-${RUBY_VERSION} && \
    ./configure --disable-install-doc && \
    make -j "$(nproc)" && \
    make install && \
    ruby -v && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*
