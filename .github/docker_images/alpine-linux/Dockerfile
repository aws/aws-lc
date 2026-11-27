# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# TODO(CryptoAlg-2491 & Issue#2010): latest pins to gcc-14, but it's broken with FIPS.
FROM alpine:3.20

ARG CC=gcc
ARG CXX=g++

VOLUME ["awslc"]

RUN apk --no-cache add bash  \
                       curl \
                       clang \
                       build-base \
                       cmake \
                       ninja \
                       go \
                       perl \
                       linux-headers

# rust-phase1 CI probe: Rust for ENABLE_RUST=AUTO.
RUN curl --proto '=https' -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path --profile minimal
ENV PATH="${PATH}:/root/.cargo/bin"

WORKDIR /awslc

ENV CC=${CC}
ENV CXX=${CXX}

ENTRYPOINT ["/bin/bash", "-c"]
