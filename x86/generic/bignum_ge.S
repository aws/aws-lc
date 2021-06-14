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
// Compare bignums, x >= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_ge
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// ----------------------------------------------------------------------------

#define m rdi
#define x rsi
#define n rdx
#define y rcx
#define i r8
#define a rax

#define ashort eax

.intel_syntax noprefix

                .globl  bignum_ge
                .text

bignum_ge:

// Zero the main index counter for both branches

                xor     i, i

// Speculatively form m := m - n and do case split

                sub     m, n
                jc      ylonger

// The case where x is longer or of the same size (m >= n)

                inc     m
                test    n, n
                jz      xtest
xmainloop:
                mov     a, [x+8*i]
                sbb     a, [y+8*i]
                inc     i
                dec     n
                jnz     xmainloop
                jmp     xtest
xtoploop:
                mov     a, [x+8*i]
                sbb     a, 0
                inc     i
xtest:
                dec     m
                jnz     xtoploop
                sbb     a, a
                inc     a
                ret

// The case where y is longer (n > m)

ylonger:
                add     m, n
                sub     n, m
                test    m, m
                jz      ytoploop
ymainloop:
                mov     a, [x+8*i]
                sbb     a, [y+8*i]
                inc     i
                dec     m
                jnz     ymainloop
ytoploop:
                mov     ashort, 0
                sbb     a, [y+8*i]
                inc     i
                dec     n
                jnz     ytoploop

                sbb     a, a
                inc     a
                ret
