# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM fedora:31

SHELL ["/bin/bash", "-c"]

RUN set -ex

RUN dnf -y install \
    clang \
    cmake \
    ninja-build \
    perl \
    git \
    golang \
    --setopt=install_weak_deps=False --best && \
    dnf -y autoremove && \
    dnf clean all && \
    rm -rf /tmp/*

ENV CC=clang-9
ENV CXX=clang++-9
