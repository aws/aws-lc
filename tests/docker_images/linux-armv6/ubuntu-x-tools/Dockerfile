# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu:22.04

RUN apt-get update && apt-get install -y  \
    git cmake golang gdb gdbserver valgrind \
    libclang1 \
    build-essential \
    ssh \
    rsync \
    tar \
    python3 \
    xz-utils \
    ninja-build

RUN apt-get install -y \
    qemu-system-arm \
    qemu-user \
    qemu-user-binfmt

RUN apt-get clean

COPY armv6-x-tools.tar.xz /
RUN tar Jxvf armv6-x-tools.tar.xz -C / && rm /armv6-x-tools.tar.xz
COPY armv6.cmake /

EXPOSE 1234

ENV GOCACHE=/tmp \
    CMAKE_TOOLCHAIN_FILE=/armv6.cmake \
    CMAKE_SYSTEM_NAME=Linux \
    CMAKE_SYSTEM_PROCESSOR=armv6l \
    PATH="${PATH}:/armv6-unknown-linux-gnueabi/bin/" \
    CMAKE_C_COMPILER=/armv6-unknown-linux-gnueabi/bin/armv6-unknown-linux-gnueabi-gcc \
    CMAKE_CXX_COMPILER=/armv6-unknown-linux-gnueabi/bin/armv6-unknown-linux-gnueabi-g++ \
    CMAKE_SYSROOT=/armv6-unknown-linux-gnueabi/armv6-unknown-linux-gnueabi/sysroot \
    CMAKE_GENERATOR=Ninja

CMD ["/bin/bash"]
