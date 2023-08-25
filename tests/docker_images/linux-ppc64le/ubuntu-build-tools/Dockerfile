# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ppc64le/ubuntu:latest

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y  \
    gcc g++ cmake golang gdb valgrind \
    libclang-dev clang \
    build-essential \
    ssh \
    rsync \
    tar \
    python3 \
	&& apt-get clean \
    && mkdir -p /.cache \
    && chmod 777 /.cache

CMD ["/bin/bash"]
