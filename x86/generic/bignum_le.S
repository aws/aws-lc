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
// Compare bignums, x <= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_le
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_le
        .text

#define m rdi
#define x rsi
#define n rdx
#define y rcx
#define i r8
#define a rax

#define ashort eax



bignum_le:

// Zero the main index counter for both branches

                xor     i, i

// Speculatively form n := n - m and do case split

                sub     n, m
                jc      ylonger

// The case where y is longer or of the same size (n >= m)

                inc     n
                test    m, m
                jz      xtest
xmainloop:
                mov     a, [y+8*i]
                sbb     a, [x+8*i]
                inc     i
                dec     m
                jnz     xmainloop
                jmp     xtest
xtoploop:
                mov     a, [y+8*i]
                sbb     a, 0
                inc     i
xtest:
                dec     n
                jnz     xtoploop
                sbb     a, a
                inc     a
                ret

// The case where x is longer (m > n)

ylonger:
                add     n, m
                sub     m, n
                test    n, n
                jz      ytoploop
ymainloop:
                mov     a, [y+8*i]
                sbb     a, [x+8*i]
                inc     i
                dec     n
                jnz     ymainloop
ytoploop:
                mov     ashort, 0
                sbb     a, [x+8*i]
                inc     i
                dec     m
                jnz     ytoploop

                sbb     a, a
                inc     a
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
