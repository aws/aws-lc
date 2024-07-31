# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM alpine:latest

VOLUME ["/awslc"]

COPY awslc_build.sh /
COPY entry.sh /

WORKDIR /

RUN apk --no-cache add bash  \
                       curl  \
                       gcc   \
                       build-base \
                       cmake \
                       make  
#https://stackoverflow.com/questions/6329887/how-to-fix-linker-error-cannot-find-crt1-o


# RUN curl -LOk "https://github.com/Kitware/CMake/releases/download/v3.6.3/cmake-3.6.3-Linux-x86_64.tar.gz"
# RUN sha256sum cmake-3.6.3-Linux-x86_64.tar.gz | grep -q "9d915d505c07d84b610e1be6242c7cad68b4b7a4090ce85ecf9cec5effa47c43"
# RUN tar -C /usr/local -xzf cmake-3.6.3-Linux-x86_64.tar.gz
# RUN rm cmake-3.6.3-Linux-x86_64.tar.gz

ENV PATH="${PATH}:/usr/local/cmake-3.6.3-Linux-x86_64/bin"

ENTRYPOINT ["/entry.sh"]