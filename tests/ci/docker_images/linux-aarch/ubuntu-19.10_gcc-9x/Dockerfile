# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:19.10

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-9 \
    g++-9 \
    cmake \
    ninja-build \
    perl \
    ca-certificates \
    wget

# Install golang 1.13+, which has GO111MODULE=on by default, and support load crypto/ed25519
RUN cd /tmp && \
    wget https://dl.google.com/go/go1.13.12.linux-amd64.tar.gz && \
    tar -xvf go1.13.12.linux-amd64.tar.gz && \
    mv go /usr/local

RUN apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=gcc-9
ENV CXX=g++-9
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
