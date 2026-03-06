# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM ubuntu:18.04

VOLUME ["/awslc"]

# Use kernel.org mirror for more reliable package access
RUN sed -i 's|archive.ubuntu.com|mirrors.edge.kernel.org|g' /etc/apt/sources.list && \
    sed -i 's|security.ubuntu.com|mirrors.edge.kernel.org|g' /etc/apt/sources.list

RUN apt-get update && \
    apt-get install -y \
      ca-certificates \
      cmake \
      curl \
      build-essential \
      gcc-4.8 \
      g++-4.8 && \
    update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-4.8 100 && \
    update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 100 && \
    update-alternatives --install /usr/bin/cc cc /usr/bin/gcc-4.8 100 && \
    apt-get clean

COPY awslc_build.sh /
COPY entry.sh /

WORKDIR /

RUN curl -LOk "https://go.dev/dl/go1.18.10.linux-amd64.tar.gz"
RUN sha256sum go1.18.10.linux-amd64.tar.gz | grep -q "5e05400e4c79ef5394424c0eff5b9141cb782da25f64f79d54c98af0a37f8d49"
RUN rm -rf /usr/local/go && tar -C /usr/local -xzf go1.18.10.linux-amd64.tar.gz
RUN rm go1.18.10.linux-amd64.tar.gz

ENV PATH="${PATH}:/usr/local/go/bin"

ENTRYPOINT ["/entry.sh"]