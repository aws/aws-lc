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
// Count leading zero digits (64-bit words)
// Input x[k]; output function return
//
//    extern uint64_t bignum_cld (uint64_t k, uint64_t *x);
//
// In the case of a zero bignum as input the result is k
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// ----------------------------------------------------------------------------

#define k rdi
#define x rsi
#define i rax
#define a rcx
#define j rdx

.intel_syntax noprefix

                .globl  bignum_cld
                .text

bignum_cld:

// Initialize the index i and also prepare default return value of 0 (i = rax)

                xor     i, i

// If the bignum is zero-length, just return k = 0

                test    k, k
                jz      end

// Run over the words j = 0..i-1, and set i := j + 1 when hitting nonzero a[j]

                xor     j, j
loop:
                mov     a, [x+8*j]
                inc     j
                test    a, a
                cmovnz  i, j
                cmp     j, k
                jnz     loop

                neg     rax
                add     rax, rdi

end:
                ret
