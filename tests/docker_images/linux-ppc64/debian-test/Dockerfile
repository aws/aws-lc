# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM --platform=$BUILDPLATFORM multiarch/qemu-user-static:x86_64-ppc64 AS multiarch

FROM debian:unstable-20230814 AS debian

RUN apt-get update && apt-get install -y debootstrap debian-ports-archive-keyring
RUN mkdir rootfs && debootstrap --keyring=/usr/share/keyrings/debian-ports-archive-keyring.gpg --arch=ppc64 --foreign unstable rootfs http://deb.debian.org/debian-ports/
RUN rm -rf rootfs/proc

FROM scratch
COPY --from=multiarch /usr/bin/qemu-ppc64-static /usr/bin/qemu-ppc64-static
COPY --from=multiarch /usr/bin/qemu-ppc64-static /usr/bin/qemu-ppc64
COPY --from=debian rootfs /

RUN /debootstrap/debootstrap --second-stage

SHELL ["/bin/bash", "-c"]

RUN apt-get update && apt-get install -y  \
    git gcc g++ cmake golang-1.21 gdb gdbserver valgrind \
    clang libclang1 \
    build-essential \
    ssh \
    rsync \
    tar \
    python3 \
     && apt-get clean

EXPOSE 7777

ENV GOCACHE=/tmp
ENV PATH="/usr/lib/go-1.21/bin:$PATH"

CMD ["/bin/bash"]
