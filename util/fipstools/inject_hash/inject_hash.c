// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "common.h"

int main(int argc, char *argv[]) {
    if (!inject_hash(argc, argv)) {
        exit(EXIT_FAILURE);
    }
    exit(EXIT_SUCCESS);
}
