# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2023:gcc-11x

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    dnf -y upgrade --releasever=latest && dnf install -y \
    openssl-devel && \
    dnf clean packages && \
    dnf clean metadata && \
    dnf clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/dnf

RUN curl -fsSL https://pyenv.run | bash

ENV PATH="/root/.pyenv/bin:${PATH}"
RUN eval "$(pyenv init -)" && \
    pyenv install 3.13.7

ENV PATH="/root/.pyenv/versions/3.13.7/bin:${PATH}"

RUN git clone https://github.com/C2SP/x509-limbo.git /x509-limbo && \
    cd /x509-limbo && \
    python3 -m venv .venv && \
    source .venv/bin/activate && \
    pip install -e . && \
    deactivate
