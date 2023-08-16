# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux:2023

VOLUME ["/previous", "/next"]

RUN yum install -y libabigail ninja-build cmake golang gcc gcc-c++

COPY build.sh /
COPY diff.sh /

ENTRYPOINT ["/diff.sh"]

CMD ["crypto"]
