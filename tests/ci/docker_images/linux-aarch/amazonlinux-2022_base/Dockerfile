# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM arm64v8/amazonlinux:2022

SHELL ["/bin/bash", "-c"]
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"

ENV DEPENDENCIES_DIR=/home/dependencies

# Install Valgrind for Valgrind test target even though it is not needed for the base test target.
RUN set -ex && \
    yum -y update && yum install -y \
    cmake3 \
    ninja-build \
    perl \
    which \
    git \
    ca-certificates \
    tar \
    wget \
    valgrind \
    unzip && \
    # Based on https://docs.aws.amazon.com/cli/latest/userguide/getting-started-install.html \
    curl "https://awscli.amazonaws.com/awscli-exe-linux-aarch64.zip" -o "awscliv2.zip" && \
    unzip awscliv2.zip && \
    ./aws/install --bin-dir /usr/bin && \
    rm -rf awscliv2.zip aws/ && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

COPY install_common_dependencies.sh /
RUN set -ex && /install_common_dependencies.sh && rm install_common_dependencies.sh
