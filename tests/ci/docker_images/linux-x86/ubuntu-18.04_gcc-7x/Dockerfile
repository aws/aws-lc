# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:18.04

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    # https://github.com/golang/go/wiki/Ubuntu
    add-apt-repository ppa:longsleep/golang-backports && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-7 \
    g++-7 \
    cmake \
    ninja-build \
    perl \
    quilt \
    golang-go && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=gcc-7
ENV CXX=g++-7
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
