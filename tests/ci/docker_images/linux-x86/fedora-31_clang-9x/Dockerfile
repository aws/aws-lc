# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM fedora:31

SHELL ["/bin/bash", "-c"]
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"

RUN set -ex

RUN dnf -y install \
    clang \
    cmake \
    ninja-build \
    perl \
    git \
    wget \
    --setopt=install_weak_deps=False --best && \
    dnf -y autoremove && \
    dnf clean all && \
    rm -rf /tmp/*

ENV CC=clang-9
ENV CXX=clang++-9

COPY install_common_dependencies.sh /
RUN set -ex && /install_common_dependencies.sh && rm install_common_dependencies.sh