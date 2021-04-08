# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu-20.04:clang-10x

SHELL ["/bin/bash", "-c"]

RUN set -ex && \
    apt-get update && \
    apt-get -y --no-install-recommends upgrade && \
    apt-get -y --no-install-recommends install \
    make \
    libboost-all-dev && \
    apt-get autoremove --purge -y && \
    apt-get clean && \
    apt-get autoclean && \
    rm -rf /var/lib/apt/lists/* && \
    rm -rf /tmp/*

ENV FUZZ_ROOT=${DEPENDENCIES_DIR}
ENV MODULE_ROOT="${FUZZ_ROOT}/modules"
#
# # Recommended flags from https://github.com/guidovranken/cryptofuzz/blob/master/docs/building.md
# ENV CFLAGS="-fsanitize=address,undefined,fuzzer-no-link -O2 -g"
# ENV CXXFLAGS="-fsanitize=address,undefined,fuzzer-no-link -D_GLIBCXX_DEBUG -O2 -g"
#
# # Add address sanitizer flags
# ENV CFLAGS="${CFLAGS} -fsanitize=address -fsanitize-address-use-after-scope -fno-omit-frame-pointer"
# ENV CXXFLAGS="${CXXFLAGS} -fsanitize=address -fsanitize-address-use-after-scope -fno-omit-frame-pointer"
#
# # Configure base CryptoFuzz
# RUN git clone --depth 1 https://github.com/guidovranken/cryptofuzz.git && cd cryptofuzz
# ENV CRYPTOFUZZ_ROOT=$(pwd)
# RUN python3 gen_repository.py
#
# RUN mkdir -p $MODULE_ROOT && cd $MODULE_ROOT
#
# # Botan https://github.com/guidovranken/cryptofuzz/blob/master/docs/botan.md
# RUN git clone --depth 1 https://github.com/randombit/botan.git && cd botan

COPY build_cryptofuzz_modules.sh $FUZZ_ROOT/.
RUN set -ex && cd $CRYPTOFUZZ_ROOT && "${FUZZ_ROOT}/build_cryptofuzz_modules.sh"
