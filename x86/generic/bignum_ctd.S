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
// Count trailing zero digits (64-bit words)
// Input x[k]; output function return
//
//    extern uint64_t bignum_ctd (uint64_t k, uint64_t *x);
//
// In the case of a zero bignum as input the result is k
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_ctd
        .text

#define k rdi
#define x rsi
#define i rdx
#define a rax



bignum_ctd:

// If the bignum is zero-length, just return 0

                xor     rax, rax
                test    k, k
                jz      end

// Record in i that the lowest nonzero word is i - 1, where i = k + 1 means
// that the bignum was entirely zero

                mov     i, k
                inc     i
loop:
                mov     a, [x+8*k-8]
                test    a, a
                cmovne  i, k
                dec     k
                jnz     loop

// We now want to return i - 1

                dec     i
                mov     rax, i
end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
