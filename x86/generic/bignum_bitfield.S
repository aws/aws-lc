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
// Select bitfield starting at bit n with length l <= 64
// Inputs x[k], n, l; output function return
//
//    extern uint64_t bignum_bitfield
//     (uint64_t k, uint64_t *x, uint64_t n, uint64_t l);
//
// One-word bitfield from a k-digit (digit=64 bits) bignum, in constant-time
// style. Bitfield starts at bit n and has length l, indexing from 0 (=LSB).
// Digits above the top are treated uniformly as zero, as usual. Since the
// result is returned in a single word, effectively we use l' = min(64,l)
// for the length.
//
// Standard x86-64 ABI: RDI = k, RSI = x, RDX = n, RCX = l, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_bitfield
        .text

#define k rdi
#define x rsi
#define n rdx
#define l rcx

#define d r8
#define e rax
#define i r9
#define a r10
#define m r11

#define mshort r11d



bignum_bitfield:

// Initialize second of digit pair to zero and if length is zero finish
// immediately; the digit e is also the return value in RAX

                xor     e, e
                test    k, k
                jz      end

// Decompose the index into n = 64 * n + m, then increment n for next part

                mov     mshort, 63
                and     m, n
                shr     n, 6
                inc     n

// Run over the digits setting d = n'th and e = (n+1)'th

                xor     i, i
loop:
                mov     a, [x+8*i]
                cmp     i, n
                cmovc   d, a
                cmovz   e, a
                inc     i
                cmp     i, k
                jc      loop

// Put zero in a register, for several purposes

                xor     a, a

// Override d with 0 if we ran off the end (e will retain original 0).

                cmp     i, n
                cmovc   d, a

// Override e if we have m = 0 (i.e. original n was divisible by 64)
// This is because then we want to shift it right by 64 below.

                test    m, m
                cmovz   e, a

// Create a size-l bitmask first (while the shift is conveniently in CL)

                cmp     l, 64
                adc     a, a
                shl     a, cl
                dec     a

// Combine shifted digits to get the bitfield(n,64)

                mov     l, m
                shr     d, cl
                neg     rcx
                shl     e, cl
                or      e, d

// Now mask it down to get bitfield (n,l)

                and     e, a

end:
                ret
