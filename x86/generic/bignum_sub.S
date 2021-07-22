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
// Subtract, z := x - y
// Inputs x[m], y[n]; outputs function return (carry-out) and z[p]
//
//    extern uint64_t bignum_sub
//     (uint64_t p, uint64_t *z,
//      uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Does the z := x - y operation, truncating modulo p words in general and
// returning a top borrow (0 or 1) in the p'th place, only subtracting input
// words below p (as well as m and n respectively) to get the diff and borrow.
//
// Standard x86-64 ABI: RDI = p, RSI = z, RDX = m, RCX = x, R8 = n, R9 = y,
// returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_sub
        .text

#define p rdi
#define z rsi
#define m rdx
#define x rcx
#define n r8
#define y r9
#define i r10
#define a rax

#define ashort eax



bignum_sub:

// Zero the main index counter for both branches

                xor     i, i

// First clamp the two input sizes m := min(p,m) and n := min(p,n) since
// we'll never need words past the p'th. Can now assume m <= p and n <= p.
// Then compare the modified m and n and branch accordingly

                cmp     p, m
                cmovc   m, p
                cmp     p, n
                cmovc   n, p
                cmp     m, n
                jc      ylonger

// The case where x is longer or of the same size (p >= m >= n)

                sub     p, m
                sub     m, n
                inc     m
                test    n, n
                jz      xtest
xmainloop:
                mov     a, [x+8*i]
                sbb     a, [y+8*i]
                mov     [z+8*i],a
                inc     i
                dec     n
                jnz     xmainloop
                jmp     xtest
xtoploop:
                mov     a, [x+8*i]
                sbb     a, 0
                mov     [z+8*i],a
                inc     i
xtest:
                dec     m
                jnz     xtoploop
                sbb     a, a
                test    p, p
                jz      tailskip
tailloop:
                mov     [z+8*i],a
                inc     i
                dec     p
                jnz     tailloop
tailskip:
                neg     a
                ret

// The case where y is longer (p >= n > m)

ylonger:

                sub     p, n
                sub     n, m
                test    m, m
                jz      ytoploop
ymainloop:
                mov     a, [x+8*i]
                sbb     a, [y+8*i]
                mov     [z+8*i],a
                inc     i
                dec     m
                jnz     ymainloop
ytoploop:
                mov     ashort, 0
                sbb     a, [y+8*i]
                mov     [z+8*i],a
                inc     i
                dec     n
                jnz     ytoploop
                sbb     a, a
                test    p, p
                jnz     tailloop
                neg     a
                ret
