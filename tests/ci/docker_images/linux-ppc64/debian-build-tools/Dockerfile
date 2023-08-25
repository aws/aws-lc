# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM debian-ppc64:base

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y  \
    gcc g++ cmake golang-1.21 gdb valgrind \
    clang libclang1 \
    build-essential \
    ssh \
    rsync \
    tar \
    python3 \
     && apt-get clean

ENV PATH="/usr/lib/go-1.21/bin/:$PATH"

CMD ["/bin/bash"]
