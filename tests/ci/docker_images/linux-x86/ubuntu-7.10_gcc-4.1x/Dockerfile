# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu-7.10-gutsy_gcc-4.1x:latest

COPY sources.list /etc/apt/sources.list

CMD ["/bin/bash"]

RUN apt-get update && \
    apt-get -y --no-install-recommends install \
    gcc-4.1 \
    g++-4.1 \
    perl && \
    rm -rf /var/lib/apt/lists/*

ENV CC=gcc-4.1
ENV CXX=g++-4.1

# Pull cmake as an external source since the wget version
# on this image is too old to access the cmake repo.
COPY dependencies/cmake-2.8.12.tar.gz /tmp/cmake-2.8.12.tar.gz
RUN cd /tmp && \
    tar -xvf cmake-2.8.12.tar.gz && \
    cd cmake-2.8.12 && \
    ./configure && make && make install
