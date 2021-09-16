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


        .globl  bignum_cld
        .text

#define k %rdi
#define x %rsi
#define i %rax
#define a %rcx
#define j %rdx



bignum_cld:

// Initialize the index i and also prepare default return value of 0 (i = %rax)

                xorq    i, i

// If the bignum is zero-length, just return k = 0

                testq   k, k
                jz      end

// Run over the words j = 0..i-1, and set i := j + 1 when hitting nonzero a[j]

                xorq    j, j
loop:
                movq    (x,j,8), a
                incq    j
                testq   a, a
                cmovnzq j, i
                cmpq    k, j
                jnz     loop

                negq    %rax
                addq    %rdi, %rax

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
