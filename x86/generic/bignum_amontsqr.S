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
// Almost-Montgomery square, z :== (x^2 / 2^{64k}) (congruent mod m)
// Inputs x[k], y[k]; output z[k]
//
//    extern void bignum_amontsqr
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y);
//
// Does z :== (x^2 / 2^{64k}) mod m, meaning that the result, in the native
// size k, is congruent modulo m, but might not be fully reduced mod m. This
// is why it is called *almost* Montgomery squaring.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = y
// ----------------------------------------------------------------------------

#define k rdi
#define z rsi
#define x r9            // We copy x here but it comes in in rdx originally
#define m rcx

#define a rax           // General temp, low part of product and mul input
#define b rdx           // General temp, High part of product

#define w r8            // Negated modular inverse
#define j rbx           // Inner loop counter
#define d rbp           // Home for i'th digit or Montgomery multiplier
#define h r10
#define e r11
#define n r12
#define i r13
#define c0 r14
#define c1 r15

// A temp reg in the initial word-level negmodinv.

#define t2 rdx

#define ashort eax
#define jshort ebx

.intel_syntax noprefix

                .globl  bignum_amontsqr
                .text

bignum_amontsqr:

// Save registers

                push    rbx
                push    rbp
                push    r12
                push    r13
                push    r14
                push    r15

// If k = 0 the whole operation is trivial

                test    k, k
                jz      end

// Move x input into its permanent home, since we need rdx for multiplications

                mov     x, rdx

// Compute word-level negated modular inverse w for m == m[0].

                mov     a, [m]

                mov     t2, a
                mov     w, a
                shl     t2, 2
                sub     w, t2
                xor     w, 2

                mov     t2, w
                imul    t2, a
                mov     ashort, 2
                add     a, t2
                add     t2, 1

                imul    w, a

                imul    t2, t2
                mov     ashort, 1
                add     a, t2
                imul    w, a

                imul    t2, t2
                mov     ashort, 1
                add     a, t2
                imul    w, a

                imul    t2, t2
                mov     ashort, 1
                add     a, t2
                imul    w, a

// Initialize the output c0::z to zero so we can then consistently add rows.
// It would be a bit more efficient to special-case the zeroth row, but
// this keeps the code slightly simpler.

                xor     i, i            // Also initializes i for main loop
                xor     j, j
zoop:
                mov     [z+8*j], i
                inc     j
                cmp     j, k
                jc      zoop

                xor     c0, c0

// Outer loop pulling down digits d=x[i], multiplying by x and reducing

outerloop:

// Multiply-add loop where we always have CF + previous high part h to add in.
// Note that in general we do need yet one more carry in this phase and hence
// initialize c1 with the top carry.

                mov     d, [x+8*i]
                xor     j, j
                xor     h, h
                xor     c1, c1
                mov     n, k

maddloop:
                adc     h, [z+8*j]
                sbb     e, e
                mov     a, [x+8*j]
                mul     d
                sub     rdx, e
                add     a, h
                mov     [z+8*j], a
                mov     h, rdx
                inc     j
                dec     n
                jnz     maddloop
                adc     c0, h
                adc     c1, c1

// Montgomery reduction loop, similar but offsetting writebacks

                mov     e, [z]
                mov     d, w
                imul    d, e
                mov     a, [m]
                mul     d
                add     a, e            // Will be zero but want the carry
                mov     h, rdx
                mov     jshort, 1
                mov     n, k
                dec     n
                jz      montend

montloop:
                adc     h, [z+8*j]
                sbb     e, e
                mov     a, [m+8*j]
                mul     d
                sub     rdx, e
                add     a, h
                mov     [z+8*j-8], a
                mov     h, rdx
                inc     j
                dec     n
                jnz     montloop

montend:
                adc     h, c0
                adc     c1, 0
                mov     c0, c1
                mov     [z+8*j-8], h

// End of outer loop.

                inc     i
                cmp     i, k
                jc      outerloop

// Now convert carry word, which is always in {0,1}, into a mask "d"
// and do a masked subtraction of m for the final almost-Montgomery result.

                xor     d, d
                sub     d, c0
                xor     e, e
                xor     j, j
corrloop:
                mov     a, [m+8*j]
                and     a, d
                neg     e
                sbb     [z+8*j], a
                sbb     e, e
                inc     j
                cmp     j, k
                jc      corrloop

end:
                pop     r15
                pop     r14
                pop     r13
                pop     r12
                pop     rbp
                pop     rbx

                ret
