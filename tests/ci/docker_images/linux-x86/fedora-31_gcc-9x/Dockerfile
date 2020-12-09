# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM fedora:31

SHELL ["/bin/bash", "-c"]

RUN set -ex

# gcc 9.3.1 is the latest version versions `dnf --showduplicates list gcc`
RUN dnf -y install \
    gcc \
    g++ \
    cmake \
    ninja-build \
    perl \
    git \
    golang \
    --setopt=install_weak_deps=False --best && \
    dnf -y autoremove && \
    dnf clean all && \
    rm -rf /tmp/*

ENV CC=gcc
ENV CXX=g++
