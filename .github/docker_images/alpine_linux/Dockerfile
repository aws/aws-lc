# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM alpine:latest

COPY . .

#COPY .github/docker_images/alpine_linux/entry.sh /

WORKDIR /

RUN apk --no-cache add bash  \
                       build-base \
                       cmake \
                       ninja \
                       go \
                       perl \
                       linux-headers

#https://stackoverflow.com/questions/6329887/how-to-fix-linker-error-cannot-find-crt1-o

ENTRYPOINT [".github/docker_images/alpine_linux/entry.sh"]