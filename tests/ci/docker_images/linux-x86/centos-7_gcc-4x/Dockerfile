# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM centos:7

SHELL ["/bin/bash", "-c"]

# We manually install go 1.14.10 because of the version of git
# for CentOS 7 is too old to support the `--unshallow` option
# https://github.com/golang/go/issues/38373
RUN set -ex && \
    yum -y update && \
    yum --enablerepo=extras install epel-release -y && \
    yum -y install \
    gcc \
    libgcc.i686 \
    glibc-devel.x86_64 \
    glibc-devel.i686 \
    gcc-c++ \
    libstdc++-devel.x86_64 \
    libstdc++-devel.i686 \
    cmake \
    ninja-build \
    perl \
    wget && \
    cd /tmp && \
    wget https://golang.org/dl/go1.14.10.linux-amd64.tar.gz && \
    tar -xvf go1.14.10.linux-amd64.tar.gz && \
    mv go /usr/local && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV CC=gcc
ENV CXX=g++
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"