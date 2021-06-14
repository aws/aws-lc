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
// Convert from (almost-)Montgomery form z := (x / 2^{64k}) mod m
// Inputs x[k], m[k]; output z[k]
//
//    extern void bignum_demont
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *m);
//
// Does z := (x / 2^{64k}) mod m, hence mapping out of Montgomery domain.
// In other words, this is a k-fold Montgomery reduction with same-size input.
// This can handle almost-Montgomery inputs, i.e. any k-digit bignum.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = m
// ----------------------------------------------------------------------------

#define k rdi
#define z rsi
#define x rdx
#define m rcx

#define a rax           // General temp, low part of product and mul input
#define b rdx           // General temp, high part of product (no longer x)

#define w r8            // Negated modular inverse
#define i r9            // Outer loop counter
#define j rbx           // Inner loop counter
#define d rbp           // Home for Montgomery multiplier
#define h r10
#define e r11
#define n r12

// A temp reg in the initial word-level negmodinv, same as j

#define t rbx

#define ashort eax
#define jshort ebx

.intel_syntax noprefix

                .globl  bignum_demont
                .text

bignum_demont:

// Save registers

                push    rbx
                push    rbp
                push    r12

// If k = 0 the whole operation is trivial

                test    k, k
                jz      end

// Compute word-level negated modular inverse w for m == m[0].

                mov     a, [m]

                mov     t, a
                mov     w, a
                shl     t, 2
                sub     w, t
                xor     w, 2

                mov     t, w
                imul    t, a
                mov     ashort, 2
                add     a, t
                add     t, 1

                imul    w, a

                imul    t, t
                mov     ashort, 1
                add     a, t
                imul    w, a

                imul    t, t
                mov     ashort, 1
                add     a, t
                imul    w, a

                imul    t, t
                mov     ashort, 1
                add     a, t
                imul    w, a

// Initially just copy the input to the output. It would be a little more
// efficient but somewhat fiddlier to tweak the zeroth iteration below instead.
// After this we never use x again and can safely recycle RDX for muls

                xor     j, j
iloop:
                mov     a, [x+8*j]
                mov     [z+8*j], a
                inc     j
                cmp     j, k
                jc      iloop

// Outer loop, just doing a standard Montgomery reduction on z

                xor     i, i

outerloop:
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
                adc     h, 0
                mov     [z+8*j-8], h

// End of outer loop.

                inc     i
                cmp     i, k
                jc      outerloop

// Now do a comparison of z with m to set a final correction mask
// indicating that z >= m and so we need to subtract m.

                xor     j, j
                mov     n, k
cmploop:
                mov     a, [z+8*j]
                sbb     a, [m+8*j]
                inc     j
                dec     n
                jnz     cmploop
                sbb     d, d
                not     d

// Now do a masked subtraction of m for the final reduced result.

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
                pop     r12
                pop     rbp
                pop     rbx

                ret
