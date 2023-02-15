# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM --platform=linux/386 rust:latest

SHELL ["/bin/bash", "-c"]

RUN apt-get update && \
    apt-get -y install clang cmake && \
    wget https://dl.google.com/go/go1.20.1.linux-amd64.tar.gz && \
    tar -xvf go1.20.1.linux-amd64.tar.gz && \
    mv go /usr/local && \
    rustup update && \
    rustup component add rustfmt clippy && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

