# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu-20.04:clang-10x

SHELL ["/bin/bash", "-c"]

ENV CRYPTOFUZZ_ROOT=${DEPENDENCIES_DIR}/cryptofuzz


RUN set -ex && mkdir $CRYPTOFUZZ_ROOT
COPY build_cryptofuzz_modules.sh $CRYPTOFUZZ_ROOT/.
RUN set -ex && cd $CRYPTOFUZZ_ROOT && ./build_cryptofuzz_modules.sh
ENV CC=clang-10
ENV CXX=clang++-10