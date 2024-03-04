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
    qemu-system-s390x \
    qemu-user \
    qemu-user-binfmt

RUN apt-get clean

COPY s390x-x-tools.tar.xz /
RUN tar Jxvf s390x-x-tools.tar.xz -C / && rm /s390x-x-tools.tar.xz
COPY s390x.cmake /

EXPOSE 1234

ENV GOCACHE=/tmp \
    CMAKE_TOOLCHAIN_FILE=/s390x.cmake \
    CMAKE_SYSTEM_NAME=Linux \
    CMAKE_SYSTEM_PROCESSOR=s390x \
    PATH="${PATH}:/s390x-ibm-linux-gnu/bin/" \
    CMAKE_C_COMPILER=/s390x-ibm-linux-gnu/bin/s390x-ibm-linux-gnu-gcc \
    CMAKE_CXX_COMPILER=/s390x-ibm-linux-gnu/bin/s390x-ibm-linux-gnu-g++ \
    CMAKE_SYSROOT=/s390x-ibm-linux-gnu/s390x-ibm-linux-gnu/sysroot \
    CMAKE_GENERATOR=Ninja

CMD ["/bin/bash"]
