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
// Test bignums for equality, x = y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_eq
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_eq
        .text

#define m %rdi
#define x %rsi
#define n %rdx
#define y %rcx
#define c %rax
// We can re-use n for this, not needed when d appears
#define d %rdx

bignum_eq:

// Initialize the accumulated OR of differences to zero

                xorq    c, c

// If m >= n jump into the m > n loop at the final equality test
// This will drop through for m = n

                cmpq    n, m
                jnc     mtest

// Toploop for the case n > m

nloop:
                decq    n
                orq     (y,n,8), c
                cmpq    n, m
                jnz     nloop
                jmp     mmain

// Toploop for the case m > n (or n = m which enters at "mtest")

mloop:
                decq    m
                orq     (x,m,8), c
                cmpq    n, m
mtest:
                jnz     mloop

// Combined main loop for the min(m,n) lower words

mmain:
                testq   m, m
                jz      end

loop:
                movq    -8(x,m,8), d
                xorq    -8(y,m,8), d
                orq     d, c
                decq    m
                jnz     loop

// Set a standard C condition based on whether c is nonzero

end:
                negq    c
                sbbq    c, c
                incq    c
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
