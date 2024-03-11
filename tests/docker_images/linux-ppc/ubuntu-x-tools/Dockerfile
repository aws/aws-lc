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

COPY ppc-x-tools.tar.xz /
RUN tar Jxvf ppc-x-tools.tar.xz -C / && rm /ppc-x-tools.tar.xz
COPY ppc.cmake /

EXPOSE 1234

ENV GOCACHE=/tmp \
    CMAKE_TOOLCHAIN_FILE=/ppc.cmake \
    CMAKE_SYSTEM_NAME=Linux \
    CMAKE_SYSTEM_PROCESSOR=ppc \
    PATH="${PATH}:/powerpc-unknown-linux-gnu/bin/" \
    CMAKE_C_COMPILER=/powerpc-unknown-linux-gnu/bin/powerpc-unknown-linux-gnu-gcc \
    CMAKE_CXX_COMPILER=/powerpc-unknown-linux-gnu/bin/powerpc-unknown-linux-gnu-g++ \
    CMAKE_SYSROOT=/powerpc-unknown-linux-gnu/powerpc-unknown-linux-gnu/sysroot \
    CMAKE_GENERATOR=Ninja

CMD ["/bin/bash"]
