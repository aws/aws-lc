# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM gcc:4.8.5

VOLUME ["/awslc"]

COPY awslc_build.sh /
COPY entry.sh /

WORKDIR /

RUN curl -LOk "https://github.com/Kitware/CMake/releases/download/v3.6.3/cmake-3.6.3-Linux-x86_64.tar.gz"
RUN sha256sum cmake-3.6.3-Linux-x86_64.tar.gz | grep -q "9d915d505c07d84b610e1be6242c7cad68b4b7a4090ce85ecf9cec5effa47c43"
RUN tar -C /usr/local -xzf cmake-3.6.3-Linux-x86_64.tar.gz
RUN rm cmake-3.6.3-Linux-x86_64.tar.gz
RUN curl -LOk "https://go.dev/dl/go1.18.10.linux-amd64.tar.gz"
RUN sha256sum go1.18.10.linux-amd64.tar.gz | grep -q "5e05400e4c79ef5394424c0eff5b9141cb782da25f64f79d54c98af0a37f8d49"
RUN rm -rf /usr/local/go && tar -C /usr/local -xzf go1.18.10.linux-amd64.tar.gz
RUN rm go1.18.10.linux-amd64.tar.gz

ENV PATH="${PATH}:/usr/local/cmake-3.6.3-Linux-x86_64/bin:/usr/local/go/bin"

ENTRYPOINT ["/entry.sh"]
