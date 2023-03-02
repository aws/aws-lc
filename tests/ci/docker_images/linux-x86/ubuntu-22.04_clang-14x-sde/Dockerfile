# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu-22.04:base

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    clang-14 clang++-14 \
    # This provides command `getenforce`, which can tell the current status of SELinux.
    # Based on Interl SDE README, SELinux should be turned off to allow pin to work.
    selinux-basics \
    wget \
    xz-utils \
    tar && \
    # Install Intel® Software Development Emulator
    # This emulator is needed when running BoringSSL/AWS-LC code under Intel's SDE for each supported chip (like ice lake).
    # https://software.intel.com/content/www/us/en/develop/articles/intel-software-development-emulator.html#system-configuration
    wget https://downloadmirror.intel.com/684899/sde-external-9.0.0-2021-11-07-lin.tar.xz && \
    tar -xf sde-external-9.0.0-2021-11-07-lin.tar.xz && \
    rm sde-external-9.0.0-2021-11-07-lin.tar.xz && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=clang-14
ENV CXX=clang++-14
ENV SDEROOT=/sde-external-9.0.0-2021-11-07-lin
ENV PATH="$SDEROOT:$PATH"
