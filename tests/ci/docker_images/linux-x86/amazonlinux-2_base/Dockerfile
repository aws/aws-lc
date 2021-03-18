# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM amazonlinux:2

SHELL ["/bin/bash", "-c"]

# Install Valgrind for Valgrind test target even though it is not needed for the base test target.
RUN set -ex && \
    yum -y update && yum install -y \
    cmake \
    ninja-build \
    perl \
    golang \
    which \
    git \
    ca-certificates \
    wget \
    valgrind && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV GO111MODULE=on
