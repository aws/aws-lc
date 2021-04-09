# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu-20.04:clang-10x

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    make \
    libboost-all-dev \
    unzip && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV FUZZ_ROOT=${DEPENDENCIES_DIR}
ENV MODULE_ROOT="${FUZZ_ROOT}/modules"

COPY ../build_cryptofuzz_modules.sh ../cryptofuzz_data.zip $FUZZ_ROOT/
RUN set -ex && cd $FUZZ_ROOT && "./build_cryptofuzz_modules.sh"
