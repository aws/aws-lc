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


        .globl  bignum_shl_small
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
#define i %r11



bignum_shl_small:

// First clamp the input size n := min(p,n) since we can never need to read
// past the p'th term of the input to generate p-digit output.

                cmpq    n, p
                cmovcq  p, n

// Initialize "previous word" carry b to zero and main index i also to zero.
// Then just skip the main loop if n = 0

                xorq    b, b
                xorq    i, i

                testq   n, n
                jz      tail

// Reshuffle registers to put the shift count into CL

                movq    %rcx, x
                movq    %r8, c

// Now the main loop

loop:
                movq    (x,i,8), a
                movq    a, t
                shldq   %cl, b, a
                movq    a, (z,i,8)
                movq    t, b
                incq    i
                cmpq    n, i
                jc      loop

// Shift the top word correspondingly. Using shld one more time is easier
// than carefully producing a complementary shift with care over the zero case

                xorq    a, a
                shldq   %cl, b, a
                movq    a, b

// If we are at the end, finish, otherwise write carry word then zeros

tail:
                cmpq    p, i
                jnc     end
                movq    b, (z,i,8)
                xorq    b, b
                incq    i
                cmpq    p, i
                jnc     end

tloop:
                movq    b, (z,i,8)
                incq    i
                cmpq    p, i
                jc      tloop

// Return, with RAX = b as the top word

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
