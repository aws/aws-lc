# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux:2023

SHELL ["/bin/bash", "-c"]
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
ENV ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer

ENV DEPENDENCIES_DIR=/home/dependencies

# AL2023 Upgrade Information https://docs.aws.amazon.com/linux/al2023/ug/deterministic-upgrades-usage.html
# See https://github.com/google/sanitizers/wiki/MemorySanitizerLibcxxHowTo
# Install Valgrind for Valgrind test target even though it is not needed for the base test target.
RUN set -ex && \
    dnf -y upgrade --releasever=latest && dnf install -y \
    cmake \
    ninja-build \
    perl \
    which \
    git \
    ca-certificates \
    tar \
    zlib-devel \
    diffutils \
    make \
    automake \
    autoconf \
    amazon-ssm-agent \
    wget \
    # valgrind is just the application and core resources.
    valgrind \
    # valgrind/memcheck.h is provided by the valgrind-devel package on AL2. see P63119011.
    valgrind-devel \
    unzip && \
    wget https://raw.githubusercontent.com/aws/aws-codebuild-docker-images/master/al/x86_64/standard/5.0/amazon-ssm-agent.json -P /etc/amazon/ssm/ && \
    # Based on https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2-linux.html
    curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip" && \
    unzip awscliv2.zip && \
    ./aws/install --bin-dir /usr/bin && \
    rm -rf awscliv2.zip aws/ && \
    dnf clean packages && \
    dnf clean metadata && \
    dnf clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/dnf

COPY install_common_dependencies.sh /
RUN set -ex && /install_common_dependencies.sh && rm install_common_dependencies.sh
