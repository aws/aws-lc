# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2023-aarch:base

SHELL ["/bin/bash", "-c"]

# clang 15.0.6 is the latest version versions `yum --showduplicates list clang`
RUN set -ex && \
    dnf -y upgrade --releasever=latest && dnf install -y \
    clang && \
    dnf clean packages && \
    dnf clean metadata && \
    dnf clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/dnf

ENV CC=clang
ENV CXX=clang++
