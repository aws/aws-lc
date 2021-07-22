/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ----------------------------------------------------------------------------
// Test bignum for odd-ness
// Input x[k]; output function return
//
//    extern uint64_t bignum_odd (uint64_t k, uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_odd
        .text

bignum_odd:

// Load RAX with the lowest digit for k > 0, else 0

                xor     rax, rax
                test    rdi, rdi
                cmovnz  rax, [rsi]

// Now just return the LSB

                and     rax, 1
                ret
