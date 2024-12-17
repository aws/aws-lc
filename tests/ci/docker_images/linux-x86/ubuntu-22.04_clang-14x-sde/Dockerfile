# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu-22.04:base

SHELL ["/bin/bash", "-c"]

ENV SDE_VERSION_TAG=sde-external-9.44.0-2024-08-22-lin
ENV SDE_MIRROR_URL="https://downloadmirror.intel.com/831748/sde-external-9.44.0-2024-08-22-lin.tar.xz"

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
    wget ${SDE_MIRROR_URL} && tar -xf "${SDE_VERSION_TAG}.tar.xz" && rm "${SDE_VERSION_TAG}.tar.xz" && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV CC=clang-14
ENV CXX=clang++-14

# Notes: There are two SDE executables for Linux, sde64 and sde.
#
# Intel SDE supports running applications in their native mode. This means if the application is 64 bit application then SDE
# will run it in 64 bit mode, but if the application is compiled to 32 bits then SDE will run it in 32 bit mode.
# The executable sde64 is available only in Linux because most Linux distributions do not include the 32 bit runtime. It is
# used only when 32 bit applications are not supported on the host system.
ENV SDEROOT="/${SDE_VERSION_TAG}"
ENV PATH="$SDEROOT:$PATH"
