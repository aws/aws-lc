# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2-aarch:base

SHELL ["/bin/bash", "-c"]

# clang 7.0.1 is the latest version versions `yum --showduplicates list clang`
RUN set -ex && \
    yum -y update && yum install -y \
    clang && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV CC=clang
ENV CXX=clang++
