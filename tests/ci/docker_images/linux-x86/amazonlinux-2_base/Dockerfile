# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux:2

SHELL ["/bin/bash", "-c"]

ENV DEPENDENCIES_DIR=/home/dependencies
ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project
ENV ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"

# llvm, llvm-devel, libcxx, and libcxxabi are needed for the sanitizer tests.
# 11.1.0 is the latest stable release as of 2021-02-16.
# See https://github.com/google/sanitizers/wiki/MemorySanitizerLibcxxHowTo
# Install Valgrind for Valgrind test target even though it is not needed for the base test target.
RUN set -ex && \
    yum -y update && yum install -y \
    cmake \
    cmake3 \
    ninja-build \
    perl \
    which \
    git \
    ca-certificates \
    wget \
    tar \
    llvm \
    llvm-devel \
    # valgrind is just the application and core resources.
    valgrind \
    # valgrind/memcheck.h is provided by the valgrind-devel package on AL2. see P63119011.
    valgrind-devel \
    unzip && \
    # Based on https://docs.aws.amazon.com/cli/latest/userguide/install-cliv2-linux.html
    curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip" && \
    unzip awscliv2.zip && \
    ./aws/install --bin-dir /usr/bin && \
    rm -rf awscliv2.zip aws/ && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-11.1.0  --depth 1 && \
    cd llvm-project && rm -rf $(ls -A | grep -Ev "(libcxx|libcxxabi)") && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

COPY install_common_dependencies.sh /
RUN set -ex && /install_common_dependencies.sh && rm install_common_dependencies.sh
