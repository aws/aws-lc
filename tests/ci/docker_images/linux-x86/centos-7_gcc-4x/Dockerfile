# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM centos:7

SHELL ["/bin/bash", "-c"]

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
    quilt \
    golang && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV CC=gcc
ENV CXX=g++
