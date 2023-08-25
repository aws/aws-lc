# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM riscv64/ubuntu

SHELL ["/bin/bash", "-c"]

# Note: valgind was not available on this platform
RUN apt-get update && apt-get install -y  \
    gcc g++ cmake golang gdb \
    libclang-dev clang \
    build-essential \
    ssh \
    rsync \
    tar \
    python3 \
     && apt-get clean

CMD ["/bin/bash"]
