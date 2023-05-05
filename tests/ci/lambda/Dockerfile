# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM public.ecr.aws/lambda/provided:al2 as build

ENV CARGO_UNSTABLE_SPARSE_REGISTRY=true

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

RUN yum install -y openssl openssl-devel clang pkgconfig

ENV PATH /root/.cargo/bin:$PATH

ADD . /build

WORKDIR /build

RUN cargo clean && \
    cargo build --release

FROM public.ecr.aws/lambda/provided:al2 as purge-stale-builds

COPY --from=build /build/target/release/purge-stale-builds /

ENTRYPOINT ["/purge-stale-builds"]
