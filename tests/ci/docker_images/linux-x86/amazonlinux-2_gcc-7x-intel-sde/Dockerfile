# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux-2:gcc-7x

SHELL ["/bin/bash", "-c"]

# SDE pins come from .github/docker_images/dependencies.env, passed through as
# --build-arg by build_images.sh. No defaults: builds that do not provide them
# fail fast below rather than drifting from the pinned versions.
ARG SDE_VERSION_TAG
ARG SDE_MIRROR_URL
ARG SDE_SHA256

# Enable the EPEL repository on Amazon Linux 2 before installing packages
# https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/add-repositories.html

# gcc 7.3.1 is the latest version versions `yum --showduplicates list gcc`
# Install Valgrind for Valgrind test target even though it is not needed for the base test target.
RUN set -ex && \
    if [ -z "${SDE_VERSION_TAG}" ] || [ -z "${SDE_MIRROR_URL}" ] || [ -z "${SDE_SHA256}" ]; then \
      echo "Error: SDE build args missing; pass them from .github/docker_images/dependencies.env" >&2; exit 1; \
    fi && \
    yum -y update && yum install -y \
    # Without glibc.i686, running "./sde --help" generates error "bash: ./sde: /lib/ld-linux.so.2: bad ELF interpreter: No such file or directory"
    glibc.i686 \
    # This provides command `getenforce`, which can tell the current status of SELinux.
    # Based on Interl SDE README, SELinux should be turned off to allow pin to work.
    libselinux-utils \
    wget \
    xz \
    tar && \
    # Install Intel® Software Development Emulator
    # This emulator is needed when running BoringSSL/AWS-LC code under Intel's SDE for each supported chip (like ice lake).
    # https://software.intel.com/content/www/us/en/develop/articles/intel-software-development-emulator.html#system-configuration
    wget ${SDE_MIRROR_URL} && \
    echo "${SDE_SHA256}  ${SDE_VERSION_TAG}.tar.xz" | sha256sum -c - && \
    tar -xf "${SDE_VERSION_TAG}.tar.xz" && rm "${SDE_VERSION_TAG}.tar.xz" && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV CC=gcc
ENV CXX=g++
ENV SDEROOT="/${SDE_VERSION_TAG}"
ENV PATH="$SDEROOT:$PATH"
