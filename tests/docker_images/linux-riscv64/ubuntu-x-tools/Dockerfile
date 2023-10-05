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
    qemu-system-misc \
    qemu-user \
    qemu-user-binfmt

RUN apt-get clean

COPY riscv64-x-tools.tar.xz /
RUN tar Jxvf riscv64-x-tools.tar.xz -C / && rm /riscv64-x-tools.tar.xz
COPY riscv64.cmake /

EXPOSE 1234

ENV GOCACHE=/tmp \
    CMAKE_TOOLCHAIN_FILE=/riscv64.cmake \
    CMAKE_SYSTEM_NAME=Linux \
    CMAKE_SYSTEM_PROCESSOR=riscv64 \
    PATH="${PATH}:/riscv64-unknown-linux-gnu/bin/" \
    CMAKE_C_COMPILER=/riscv64-unknown-linux-gnu/bin/riscv64-unknown-linux-gnu-gcc \
    CMAKE_CXX_COMPILER=/riscv64-unknown-linux-gnu/bin/riscv64-unknown-linux-gnu-g++ \
    CMAKE_SYSROOT=/riscv64-unknown-linux-gnu/riscv64-unknown-linux-gnu/sysroot \
    CMAKE_GENERATOR=Ninja

CMD ["/bin/bash"]
