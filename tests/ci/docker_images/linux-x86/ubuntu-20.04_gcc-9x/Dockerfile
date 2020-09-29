# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:20.04

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    # https://github.com/golang/go/wiki/Ubuntu
    add-apt-repository ppa:longsleep/golang-backports && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-9 \
    g++-9 \
    cmake \
    ninja-build \
    perl \
    quilt \
    libunwind-dev \
    pkg-config \
    golang-go && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=gcc-9
ENV CXX=g++-9
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
