# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

FROM amazonlinux:2023

VOLUME ["/previous", "/next", "/workspace"]

# golang:  to run read_public_symbols (baseline mode)
# gcc:     C preprocessor needed by read_public_symbols
# gcc-c++: C++ preprocessor (cc1plus) needed by read_public_symbols for the
#          C++ header pass (e.g. PRIVATE_CXX symbols)
RUN yum install -y golang gcc gcc-c++

COPY check_symbols.sh /

ENTRYPOINT ["/check_symbols.sh"]

CMD ["crypto", "incremental"]
