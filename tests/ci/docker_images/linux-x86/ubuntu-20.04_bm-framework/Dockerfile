# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu-20.04:base

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    python3.8 && \
    python3-pip && \
    pandas && \
    numpy && \
    boto3 && \
    make && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*
