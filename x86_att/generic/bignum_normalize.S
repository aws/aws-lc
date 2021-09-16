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
// Normalize bignum in-place by shifting left till top bit is 1
// Input z[k]; outputs function return (bits shifted left) and z[k]
//
//    extern uint64_t bignum_normalize (uint64_t k, uint64_t *z);
//
// Given a k-digit bignum z, this function shifts it left by its number of
// leading zero bits, to give result with top bit 1, unless the input number
// was 0. The return is the same as the output of bignum_clz, i.e. the number
// of bits shifted (nominally 64 * k in the case of zero input).
//
// Standard x86-64 ABI: RDI = k, RSI = z, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_normalize
        .text

#define k %rdi
#define z %rsi

// Return value, which we put in %rax to save a move or two

#define r %rax

// Other variables
// Matters that c is RCX as CL=lo(c) is assumed in shifts

#define b %r9
#define c %rcx
#define d %rdx
#define i %r8
#define j %r10

#define dshort %edx


bignum_normalize:

// Initialize shift count r = 0 and i = k - 1 but return immediately if k = 0.
// Otherwise load top digit c, but then if k = 1 skip the digitwise part

                xorq    r, r
                movq    k, i
                subq    $1, i
                jc      end
                movq    (z,i,8), c
                jz      bitpart

// Do d rather stupid but constant-time digit normalization, conditionally
// shifting left (k-1) times based on whether the top word is zero.
// With careful binary striding this could be O(k*log(k)) instead of O(k^2)
// while still retaining the constant-time style.

normloop:
                xorq    j, j
                movq    k, b
                movq    r, d
                incq    r
                negq    c
                cmovneq d, r
                movl    $0, dshort
shufloop:
                movq    d, c
                movq    (z,j,8), d
                cmovcq  d, c
                movq    c, (z,j,8)
                incq    j
                decq    b
                jnz     shufloop
                decq    i
                jnz     normloop

// We now have the top digit nonzero, assuming the input was nonzero,
// and as per the invariant of the loop above, c holds that digit. So
// now just count c's leading zeros and shift z bitwise that many bits.
// We need to patch the bsr result for the undefined case of zero input

bitpart:
                movl    $127, dshort
                bsrq    c, c
                cmovzq  d, c
                xorq    $63, c

                shlq    $6, r
                addq    c, r

                xorq    b, b
                xorq    i, i
bitloop:
                movq    (z,i,8), d
                movq    d, j
                shldq   %cl, b, d
                movq    d, (z,i,8)
                movq    j, b
                incq    i
                cmpq    k, i
                jc      bitloop

 end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
