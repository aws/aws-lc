# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# This release of Ubuntu provides GCC versions 4.8 and 7.5
# * 4.8: /usr/bin/gcc-4.8
# * 7.5: /usr/bin/gcc
FROM ubuntu:18.04

SHELL ["/bin/bash", "-c"]

RUN  apt-get update
RUN  apt-get install -y ca-certificates cmake curl sudo build-essential gcc-4.8 g++-4.8 gdb
RUN  apt-get install -y --no-install-recommends gpg-agent software-properties-common
RUN  apt-add-repository --yes ppa:git-core/ppa
RUN  add-apt-repository --yes ppa:longsleep/golang-backports
RUN  apt-get update
RUN  apt-get install -y git golang-go
RUN  apt-get install -f

ENV GOCACHE /tmp

CMD ["/bin/bash"]
