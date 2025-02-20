# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2023:clang-15x

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    dnf -y upgrade --releasever=latest && dnf install -y \
    docker \
    openssl-devel \
    patch \
    jq && \
    dnf clean packages && \
    dnf clean metadata && \
    dnf clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/dnf

RUN curl -fsSL https://pyenv.run | bash

ENV PATH="/root/.pyenv/bin:${PATH}"
RUN eval "$(pyenv init -)" && \
    pyenv install 3.13.1

ENV PATH="/root/.pyenv/versions/3.13.1/bin:${PATH}"
ENV CC=clang
ENV CXX=clang++
