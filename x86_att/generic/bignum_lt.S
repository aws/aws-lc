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
// Compare bignums, x < y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_lt
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_lt
        .text

#define m %rdi
#define x %rsi
#define n %rdx
#define y %rcx
#define i %r8
#define a %rax

#define ashort %eax



bignum_lt:

// Zero the main index counter for both branches

                xorq    i, i

// Speculatively form m := m - n and do case split

                subq    n, m
                jc      ylonger

// The case where x is longer or of the same size (m >= n)

                incq    m
                testq   n, n
                jz      xtest
xmainloop:
                movq    (x,i,8), a
                sbbq    (y,i,8), a
                incq    i
                decq    n
                jnz     xmainloop
                jmp     xtest
xtoploop:
                movq    (x,i,8), a
                sbbq    $0, a
                incq    i
xtest:
                decq    m
                jnz     xtoploop
                sbbq    a, a
                negq    a
                ret

// The case where y is longer (n > m)

ylonger:
                addq    n, m
                subq    m, n
                testq   m, m
                jz      ytoploop
ymainloop:
                movq    (x,i,8), a
                sbbq    (y,i,8), a
                incq    i
                decq    m
                jnz     ymainloop
ytoploop:
                movl    $0, ashort
                sbbq    (y,i,8), a
                incq    i
                decq    n
                jnz     ytoploop

                sbbq    a, a
                negq    a
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
