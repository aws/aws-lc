# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM scratch

ADD ubuntu-7.10-root.tar.xz /

COPY sources.list /etc/apt/sources.list

CMD ["/bin/bash"]

RUN apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    gcc-4.1 \
    gcc-4.1-multilib \
    g++-4.1 \
    g++-4.1-multilib \
    perl \
    ca-certificates && \
    rm -rf /var/lib/apt/lists/*

ENV CC=gcc-4.1
ENV CXX=g++-4.1

COPY cmake-2.8.12.tar.gz /tmp/cmake-2.8.12.tar.gz
RUN cd /tmp && \
    tar -xvf cmake-2.8.12.tar.gz && \
    cd cmake-2.8.12 && \
    ./configure && make && make install
