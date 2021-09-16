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
// Shift bignum right by c < 64 bits z := floor(x / 2^c)
// Inputs x[n], c; outputs function return (bits shifted out) and z[k]
//
//    extern uint64_t bignum_shr_small
//     (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t c);
//
// Does the "z := x >> c" operation where x is n digits, result z is p.
// The shift count c is masked to 6 bits so it actually uses c' = c mod 64.
// The return value is the inout mod 2^c'.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = c, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_shr_small
        .text

#define p %rdi
#define z %rsi
#define n %rdx

// These get moved from their initial positions

#define c %rcx
#define x %r9

// Other variables

#define b %rax
#define t %r8
#define a %r10

#define ashort %r10d



bignum_shr_small:

// Reshuffle registers to put the shift count into CL

                movq    %rcx, x
                movq    %r8, c

// Set default carry-in word to 0, useful for other things too

                xorq    b, b

// First, if p > n then pad output on the left with p-n zeros

                cmpq    p, n
                jnc     nopad
padloop:
                decq    p
                movq    b, (z,p,8)
                cmpq    p, n
                jc      padloop
nopad:

// We now know that p <= n. If in fact p < n let carry word = x[p] instead of 0

                jz      shiftstart
                movq    (x,p,8), b
shiftstart:
                testq   p, p
                jz      trivial

// Now the main loop

loop:
                movq    -8(x,p,8), a
                movq    a, t
                shrdq   %cl, b, a
                movq    a, -8(z,p,8)
                movq    t, b
                decq    p
                jnz     loop

// Mask the carry word and return with that as RAX = b

trivial:
                movl    $1, ashort
                shlq    %cl, a
                decq    a
                andq    a, b

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
