# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM --platform=linux/amd64 rust:latest

SHELL ["/bin/bash", "-c"]
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"

RUN apt-get update && \
    apt-get -y install clang cmake && \
    rustup update && \
    rustup component add rustfmt clippy && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

COPY install_common_dependencies.sh /
RUN set -ex && /install_common_dependencies.sh && rm install_common_dependencies.sh
