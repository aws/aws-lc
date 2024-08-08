# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM alpine:latest

ARG CC=gcc
ARG CXX=g++

VOLUME ["awslc"]

RUN apk --no-cache add bash  \
                       clang \
                       build-base \
                       cmake \
                       ninja \
                       go \
                       perl \
                       linux-headers

WORKDIR /awslc

ENV CC=${CC}
ENV CXX=${CXX}

COPY entry.sh /

ENTRYPOINT ["/entry.sh"]