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
    qemu-user \
    qemu-user-binfmt \
    qemu-user-status
# Not yet available
#    qemu-system-loongarch64

RUN apt-get clean

COPY loongarch64-x-tools.tar.xz /
RUN tar Jxvf loongarch64-x-tools.tar.xz -C / && rm /loongarch64-x-tools.tar.xz
COPY loongarch64.cmake /

EXPOSE 1234

ENV GOCACHE=/tmp \
    CMAKE_TOOLCHAIN_FILE=/loongarch64.cmake \
    CMAKE_SYSTEM_NAME=Linux \
    CMAKE_SYSTEM_PROCESSOR=loongarch64 \
    PATH="${PATH}:/loongarch64-unknown-linux-gnu/bin/" \
    CMAKE_C_COMPILER=/loongarch64-unknown-linux-gnu/bin/loongarch64-unknown-linux-gnu-gcc \
    CMAKE_CXX_COMPILER=/loongarch64-unknown-linux-gnu/bin/loongarch64-unknown-linux-gnu-g++ \
    CMAKE_SYSROOT=/loongarch64-unknown-linux-gnu/loongarch64-unknown-linux-gnu/sysroot \
    CMAKE_GENERATOR=Ninja

CMD ["/bin/bash"]
