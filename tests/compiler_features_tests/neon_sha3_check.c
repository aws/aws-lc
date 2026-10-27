// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Test for NEON SHA3 extension support in the assembler.
int main(void) {
    // Match the implementation's .arch directive even when baseline CFLAGS
    // override the probe's -march flag. Keep one block for Clang's asm validation.
    __asm__(".arch armv8.4-a+sha3\n"
            "eor3 v0.16b, v1.16b, v2.16b, v3.16b\n"
            "bcax v0.16b, v1.16b, v2.16b, v3.16b\n"
            "rax1 v0.2d, v1.2d, v2.2d\n"
            "xar v0.2d, v1.2d, v2.2d, #0x2a\n");
    return 0;
}
