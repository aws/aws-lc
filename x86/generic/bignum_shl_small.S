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
// Shift bignum left by c < 64 bits z := x * 2^c
// Inputs x[n], c; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_shl_small
//     (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t c);
//
// Does the "z := x << c" operation where x is n digits, result z is p.
// The shift count c is masked to 6 bits so it actually uses c' = c mod 64.
// The return value is the "next word" of a p+1 bit result, if n <= p.
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
#define i r11

.intel_syntax noprefix

                .globl  bignum_shl_small
                .text

bignum_shl_small:

// First clamp the input size n := min(p,n) since we can never need to read
// past the p'th term of the input to generate p-digit output.

                cmp     p, n
                cmovc   n, p

// Initialize "previous word" carry b to zero and main index i also to zero.
// Then just skip the main loop if n = 0

                xor     b, b
                xor     i, i

                test    n, n
                jz      tail

// Reshuffle registers to put the shift count into CL

                mov     x, rcx
                mov     c, r8

// Now the main loop

loop:
                mov     a, [x+8*i]
                mov     t, a
                shld    a, b, cl
                mov     [z+8*i],a
                mov     b, t
                inc     i
                cmp     i, n
                jc      loop

// Shift the top word correspondingly. Using shld one more time is easier
// than carefully producing a complementary shift with care over the zero case

                xor     a, a
                shld    a, b, cl
                mov     b, a

// If we are at the end, finish, otherwise write carry word then zeros

tail:
                cmp     i, p
                jnc     end
                mov     [z+8*i],b
                xor     b, b
                inc     i
                cmp     i, p
                jnc     end

tloop:
                mov     [z+8*i],b
                inc     i
                cmp     i, p
                jc      tloop

// Return, with RAX = b as the top word

end:
                ret
