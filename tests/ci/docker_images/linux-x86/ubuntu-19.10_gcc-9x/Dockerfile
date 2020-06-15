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
    libunwind-dev \
    pkg-config \
    golang && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=gcc-9
ENV CXX=g++-9
