# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM amazonlinux-2:gcc-7x

SHELL ["/bin/bash", "-c"]

# Enable the EPEL repository on Amazon Linux 2 before installing packages
# https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/add-repositories.html

# gcc 7.3.1 is the latest version versions `yum --showduplicates list gcc`
# Install Valgrind for Valgrind test target even though it is not needed for the base test target.
RUN set -ex && \
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
    wget https://downloadmirror.intel.com/684899/sde-external-9.0.0-2021-11-07-lin.tar.xz && \
    tar -xf sde-external-9.0.0-2021-11-07-lin.tar.xz && \
    rm sde-external-9.0.0-2021-11-07-lin.tar.xz && \
    yum clean packages && \
    yum clean metadata && \
    yum clean all && \
    rm -rf /tmp/* && \
    rm -rf /var/cache/yum

ENV CC=gcc
ENV CXX=g++
ENV SDEROOT=/sde-external-9.0.0-2021-11-07-lin
ENV PATH="$SDEROOT:$PATH"
