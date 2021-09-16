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


        .globl  bignum_demont
        .text

#define k %rdi
#define z %rsi
#define x %rdx
#define m %rcx

// General temp, low part of product and mul input
#define a %rax
// General temp, high part of product (no longer x)
#define b %rdx
// Negated modular inverse
#define w %r8
// Outer loop counter
#define i %r9
// Inner loop counter
#define j %rbx
// Home for Montgomery multiplier
#define d %rbp
#define h %r10
#define e %r11
#define n %r12

// A temp reg in the initial word-level negmodinv, same as j

#define t %rbx

#define ashort %eax
#define jshort %ebx


bignum_demont:

// Save registers

                pushq   %rbx
                pushq   %rbp
                pushq   %r12

// If k = 0 the whole operation is trivial

                testq   k, k
                jz      end

// Compute word-level negated modular inverse w for m == m[0].

                movq    (m), a

                movq    a, t
                movq    a, w
                shlq    $2, t
                subq    t, w
                xorq    $2, w

                movq    w, t
                imulq   a, t
                movl    $2, ashort
                addq    t, a
                addq    $1, t

                imulq   a, w

                imulq   t, t
                movl    $1, ashort
                addq    t, a
                imulq   a, w

                imulq   t, t
                movl    $1, ashort
                addq    t, a
                imulq   a, w

                imulq   t, t
                movl    $1, ashort
                addq    t, a
                imulq   a, w

// Initially just copy the input to the output. It would be a little more
// efficient but somewhat fiddlier to tweak the zeroth iteration below instead.
// After this we never use x again and can safely recycle RDX for muls

                xorq    j, j
iloop:
                movq    (x,j,8), a
                movq    a, (z,j,8)
                incq    j
                cmpq    k, j
                jc      iloop

// Outer loop, just doing a standard Montgomery reduction on z

                xorq    i, i

outerloop:
                movq    (z), e
                movq    w, d
                imulq   e, d
                movq    (m), a
                mulq    d
                addq    e, a // Will be zero but want the carry
                movq    %rdx, h
                movl    $1, jshort
                movq    k, n
                decq    n
                jz      montend

montloop:
                adcq    (z,j,8), h
                sbbq    e, e
                movq    (m,j,8), a
                mulq    d
                subq    e, %rdx
                addq    h, a
                movq    a, -8(z,j,8)
                movq    %rdx, h
                incq    j
                decq    n
                jnz     montloop

montend:
                adcq    $0, h
                movq    h, -8(z,j,8)

// End of outer loop.

                incq    i
                cmpq    k, i
                jc      outerloop

// Now do a comparison of z with m to set a final correction mask
// indicating that z >= m and so we need to subtract m.

                xorq    j, j
                movq    k, n
cmploop:
                movq    (z,j,8), a
                sbbq    (m,j,8), a
                incq    j
                decq    n
                jnz     cmploop
                sbbq    d, d
                notq    d

// Now do a masked subtraction of m for the final reduced result.

                xorq    e, e
                xorq    j, j
corrloop:
                movq    (m,j,8), a
                andq    d, a
                negq    e
                sbbq    a, (z,j,8)
                sbbq    e, e
                incq    j
                cmpq    k, j
                jc      corrloop

end:
                popq    %r12
                popq    %rbp
                popq    %rbx

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
