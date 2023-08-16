# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2023:base

SHELL ["/bin/bash", "-c"]

# gcc 11.3.1 is the latest version versions `yum --showduplicates list gcc`
RUN set -ex && \
    dnf -y upgrade --releasever=latest && dnf install -y \
    gcc \
    gcc-c++ && \
    dnf clean packages && \
    dnf clean metadata && \
    dnf clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/dnf

ENV CC=gcc
ENV CXX=g++
