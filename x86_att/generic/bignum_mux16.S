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
// Select element from 16-element table, z := xs[k*i]
// Inputs xs[16*k], i; output z[k]
//
//    extern void bignum_mux16
//     (uint64_t k, uint64_t *z, uint64_t *xs, uint64_t i);
//
// It is assumed that all numbers xs[16] and the target z have the same size k
// The pointer xs is to a contiguous array of size 16, elements size-k bignums
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = xs, RCX = i
// ----------------------------------------------------------------------------


        .globl  bignum_mux16
        .text

#define k %rdi
#define z %rsi

// These get moved from original registers

#define x %rcx
#define i %rax

// Other registers

#define a %rdx
#define b %r8
#define j %r9
#define n %r10



bignum_mux16:


// Copy size into decrementable counter, or skip everything if k = 0

                testq   k, k
                jz      end                     // If length = 0 do nothing
                movq    k, n

// Multiply i by k so we can compare pointer offsets directly with it

                movq    %rcx, %rax
                movq    %rdx, %rcx
                mulq    k

// Main loop

loop:
                movq    (x), a
                movq    k, j
.rep 15
                movq    (x,j,8), b
                cmpq    i, j
                cmoveq  b, a
                addq    k, j
.endr
                movq    a, (z)
                addq    $8, z
                addq    $8, x
                decq    n
                jnz     loop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
