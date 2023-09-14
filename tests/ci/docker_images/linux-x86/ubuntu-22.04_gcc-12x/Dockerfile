# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu-22.04:base

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-12 g++-12 && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

# Create alias to use gcc/cpp-12 preprocessor as default. MySQL relies on cpp being available.
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-12 100 \
                        --slave /usr/bin/g++ g++ /usr/bin/g++-12 \
                        --slave /usr/bin/cpp cpp-bin /usr/bin/cpp-12

# Postgres and NGINXs integration tests cannot be ran as root, so we have to define
# a non-root user here to use in Codebuild.
RUN adduser --disabled-password --gecos '' postgres && \
    adduser postgres sudo && \
    echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers

ENV CC=gcc-12
ENV CXX=g++-12
