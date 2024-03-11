# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux:2023

ARG CMAKE_VERSION
ARG CMAKE_DOWNLOAD_URL
ARG CMAKE_SHA256

VOLUME ["/awslc"]

RUN dnf install -y tar ninja-build golang gcc gcc-c++ libcurl-devel libarchive-devel zlib-devel xz-devel

RUN mkdir /cmake

COPY cmake_build.sh /
COPY awslc_build.sh /
COPY entry.sh /

WORKDIR /cmake

RUN curl -L -o source.tar.gz "${CMAKE_DOWNLOAD_URL}"  && \
    echo "${CMAKE_SHA256} source.tar.gz" | sha256sum -c - && \
    mkdir source && \
    tar -x -f source.tar.gz -v --strip-components=1 -C source

WORKDIR /cmake/source

RUN /cmake_build.sh

WORKDIR /

ENTRYPOINT ["/entry.sh"]
