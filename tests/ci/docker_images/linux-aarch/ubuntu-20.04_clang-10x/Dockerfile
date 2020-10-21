# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM arm64v8/ubuntu:20.04

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    clang \
    cmake \
    ninja-build \
    perl \
    libunwind-dev \
    pkg-config \
    ca-certificates \
    wget && \
    cd /tmp && \
    wget https://dl.google.com/go/go1.15.2.linux-arm64.tar.gz && \
    tar -xvf go1.15.2.linux-arm64.tar.gz && \
    mv go /usr/local && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=clang-10
ENV CXX=clang++-10
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
