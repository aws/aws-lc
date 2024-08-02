// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Simple program that should also be able to compiler, udeful to test different
// compiler flags

#include <stdlib.h>
#include <stdatomic.h>
#if ATOMIC_LONG_LOCK_FREE == 0
#pragma error "ATOMIC_LONG_LOCK_FREE is 0, not enabling C11 atomics"
#endif

int main(int argc, char **argv) {
    return EXIT_SUCCESS;
}
