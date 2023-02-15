# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Download exactly what is needed using the sparse registry.
# https://github.com/rust-lang/cargo/issues/10781
# https://blog.rust-lang.org/2022/06/22/sparse-registry-testing.html

FROM --platform=linux/arm64 rust:latest

SHELL ["/bin/bash", "-c"]

RUN apt-get update && \
    apt-get -y install clang cmake && \
    wget https://dl.google.com/go/go1.20.1.linux-amd64.tar.gz && \
    tar -xvf go1.20.1.linux-amd64.tar.gz && \
    mv go /usr/local && \
    rustup update && \
    rustup toolchain install nightly && \
    rustup default nightly && \
    rustup component add rustfmt clippy && \
    cargo +nightly install -Z sparse-registry --debug cargo-ament-build && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CARGO_UNSTABLE_SPARSE_REGISTRY=true

# Static FIPS build only supports clang.
ENV CC=clang
ENV CXX=clang++
