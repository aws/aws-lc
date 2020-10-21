# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:16.04

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    dpkg --add-architecture i386 && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-5 \
    gcc-5-multilib \
    g++-5 \
    g++-5-multilib \
    linux-libc-dev:i386 \
    cmake \
    ninja-build \
    perl \
    ca-certificates \
    wget && \
    cd /tmp && \
    wget https://dl.google.com/go/go1.13.12.linux-amd64.tar.gz && \
    tar -xvf go1.13.12.linux-amd64.tar.gz && \
    mv go /usr/local && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=gcc-5
ENV CXX=g++-5
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
