# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM --platform=linux/amd64 gcc:7.2

SHELL ["/bin/bash", "-c"]

COPY cmake-3.6.3-Linux-x86_64.tar.gz /
COPY go1.18.10.linux-amd64.tar.gz /
RUN tar -C /usr/local -xzf cmake-3.6.3-Linux-x86_64.tar.gz
RUN rm -rf /usr/local/go && tar -C /usr/local -xzf go1.18.10.linux-amd64.tar.gz
RUN rm cmake-3.6.3-Linux-x86_64.tar.gz
RUN rm go1.18.10.linux-amd64.tar.gz
RUN curl --proto '=https' -sSf https://sh.rustup.rs > ./rust_install.sh && \
    chmod +x ./rust_install.sh && \
    ./rust_install.sh -y
ENV PATH="${PATH}:/usr/local/cmake-3.6.3-Linux-x86_64/bin:/usr/local/go/bin"

CMD ["/bin/bash"]
