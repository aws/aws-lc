# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu-22.04:base

SHELL ["/bin/bash", "-c"]

# gcc-11 is relatively new and not readily available, so we must fetch it from a mirror for now.
RUN set -ex && \
    # echo "deb http://mirrors.kernel.org/ubuntu hirsute main universe" >> /etc/apt/sources.list && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-12 g++-12 && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=gcc-12
ENV CXX=g++-12
