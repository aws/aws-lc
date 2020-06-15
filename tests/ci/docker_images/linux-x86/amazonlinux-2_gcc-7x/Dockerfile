# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM amazonlinux:2

SHELL ["/bin/bash", "-c"]

# gcc 7.3.1 is the latest version versions `yum --showduplicates list gcc`
RUN set -ex && \
    yum -y update && yum install -y \
    gcc \
    gcc-c++ \
    cmake \
    ninja-build \
    perl \
    golang && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV CC=gcc
ENV CXX=g++
