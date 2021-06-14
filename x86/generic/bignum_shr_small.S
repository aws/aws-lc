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

#define p rdi
#define z rsi
#define n rdx

// These get moved from their initial positions

#define c rcx
#define x r9

// Other variables

#define b rax
#define t r8
#define a r10

#define ashort r10d

.intel_syntax noprefix

                .globl  bignum_shr_small
                .text

bignum_shr_small:

// Reshuffle registers to put the shift count into CL

                mov     x, rcx
                mov     c, r8

// Set default carry-in word to 0, useful for other things too

                xor     b, b

// First, if p > n then pad output on the left with p-n zeros

                cmp     n, p
                jnc     nopad
padloop:
                dec     p
                mov     [z+8*p],b
                cmp     n, p
                jc      padloop
nopad:

// We now know that p <= n. If in fact p < n let carry word = x[p] instead of 0

                jz      shiftstart
                mov     b,[x+8*p]
shiftstart:
                test    p, p
                jz      trivial

// Now the main loop

loop:
                mov     a, [x+8*p-8]
                mov     t, a
                shrd    a, b, cl
                mov     [z+8*p-8],a
                mov     b, t
                dec     p
                jnz     loop

// Mask the carry word and return with that as RAX = b

trivial:
                mov     ashort, 1
                shl     a, cl
                dec     a
                and     b, a

end:
                ret
