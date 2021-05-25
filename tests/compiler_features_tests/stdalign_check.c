// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Old versions of GCC don't support __has_include which could be used to check for stdalign.h, try to compile this
// instead

#include <stdalign.h>
#include <stdint.h>

void main() {
    alignas(8) uint8_t test[16];
    int alignment = alignof(test);
}