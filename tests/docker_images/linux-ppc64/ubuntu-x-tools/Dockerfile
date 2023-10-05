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
    qemu-system-ppc \
    qemu-user \
    qemu-user-binfmt

RUN apt-get clean

COPY ppc64-x-tools.tar.xz /
RUN tar Jxvf ppc64-x-tools.tar.xz -C / && rm /ppc64-x-tools.tar.xz
COPY ppc64.cmake /

EXPOSE 1234

ENV GOCACHE=/tmp \
    CMAKE_TOOLCHAIN_FILE=/ppc64.cmake \
    CMAKE_SYSTEM_NAME=Linux \
    CMAKE_SYSTEM_PROCESSOR=ppc64 \
    PATH="${PATH}:/powerpc64-linux-gnu/bin/" \
    CMAKE_C_COMPILER=/powerpc64-linux-gnu/bin/powerpc64-unknown-linux-gnu-gcc \
    CMAKE_CXX_COMPILER=/powerpc64-linux-gnu/bin/powerpc64-unknown-linux-gnu-g++ \
    CMAKE_SYSROOT=/powerpc64-linux-gnu/powerpc64-unknown-linux-gnu/sysroot \
    CMAKE_GENERATOR=Ninja

CMD ["/bin/bash"]
