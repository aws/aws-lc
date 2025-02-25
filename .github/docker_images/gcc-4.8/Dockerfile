# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM gcc:4.8.5

VOLUME ["/awslc"]

COPY awslc_build.sh /
COPY entry.sh /

WORKDIR /

RUN curl -LOk "https://github.com/Kitware/CMake/releases/download/v3.9.6/cmake-3.9.6-Linux-x86_64.tar.gz"
RUN sha256sum cmake-3.9.6-Linux-x86_64.tar.gz | grep -q "062bf45bee36ce7c2a55ae26b8b5324720f370d420a05cba91b9448c64ffdbea"
RUN tar -C /usr/local -xzf cmake-3.9.6-Linux-x86_64.tar.gz
RUN rm cmake-3.9.6-Linux-x86_64.tar.gz
RUN curl -LOk "https://go.dev/dl/go1.18.10.linux-amd64.tar.gz"
RUN sha256sum go1.18.10.linux-amd64.tar.gz | grep -q "5e05400e4c79ef5394424c0eff5b9141cb782da25f64f79d54c98af0a37f8d49"
RUN rm -rf /usr/local/go && tar -C /usr/local -xzf go1.18.10.linux-amd64.tar.gz
RUN rm go1.18.10.linux-amd64.tar.gz

ENV PATH="${PATH}:/usr/local/cmake-3.9.6-Linux-x86_64/bin:/usr/local/go/bin"

ENTRYPOINT ["/entry.sh"]
