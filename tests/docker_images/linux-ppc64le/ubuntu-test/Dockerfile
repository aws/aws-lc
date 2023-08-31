# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM --platform=$BUILDPLATFORM ppc64le/ubuntu:latest

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y  \
    git gcc g++ cmake golang gdb gdbserver valgrind \
    libclang-dev clang \
    build-essential \
    ssh \
    rsync \
    tar \
    python3 \
	&& apt-get clean

EXPOSE 7777

ENV GOCACHE=/tmp

CMD ["/bin/bash"]
