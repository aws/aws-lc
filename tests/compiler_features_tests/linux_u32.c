// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// This file is to check if <linux/random.h> can be included.
// Currently, I assume the compiler error is caused by '__u32' is not defined.
// Background:
// crypto/fipsmodule/rand/urandom.c includes below Linux header file for FIPS.
// Some old Linux OS does not define '__u32', and then reports below error.
// /usr/include/linux/random.h:38:2: error: unknown type name '__u32'
// __u32 buf[0];
// ^
#include <linux/random.h>

int main() {
    return 0;
}
