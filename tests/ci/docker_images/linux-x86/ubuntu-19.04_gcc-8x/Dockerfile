# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:19.04

SHELL ["/bin/bash", "-c"]

RUN cat /etc/apt/sources.list && \
    sed -i -re 's/([a-z]{2}\.)?archive.ubuntu.com|security.ubuntu.com/old-releases.ubuntu.com/g' /etc/apt/sources.list

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-8 \
    g++-8 \
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

ENV CC=gcc-8
ENV CXX=g++-8
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
