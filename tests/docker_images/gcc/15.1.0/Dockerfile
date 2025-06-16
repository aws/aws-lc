# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# This release of Ubuntu provides GCC versions 4.8 and 7.5
# * 4.8: /usr/bin/gcc-4.8
# * 7.5: /usr/bin/gcc
FROM gcc:15.1.0

SHELL ["/bin/bash", "-c"]

RUN  apt-get update
RUN  apt-get install -y ca-certificates cmake curl sudo build-essential gdb
RUN  apt-get install -y git golang-go ninja-build
RUN  apt-get install -f

ENV GOCACHE /tmp

CMD ["/bin/bash"]
