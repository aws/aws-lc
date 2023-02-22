# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2022-aarch:clang-14x

SHELL ["/bin/bash", "-c"]

ENV LLVM_PROJECT_HOME=${DEPENDENCIES_DIR}/llvm-project

RUN set -ex && \
    yum -y update && yum install -y \
    compiler-rt \
    llvm \
    llvm-devel \
    lld && \
    mkdir -p ${DEPENDENCIES_DIR} && \
    cd ${DEPENDENCIES_DIR} && \
    git clone https://github.com/llvm/llvm-project.git --branch llvmorg-14.0.5  --depth 1 && \
    cd llvm-project && rm -rf $(ls -A | grep -Ev "(libcxx|libcxxabi)") && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

