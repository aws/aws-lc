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
// Optionally negate, z := -x (if p nonzero) or z := x (if p zero)
// Inputs p, x[k]; outputs function return (nonzero input) and z[k]
//
//    extern uint64_t bignum_optneg
//     (uint64_t k, uint64_t *z, uint64_t p, uint64_t *x);
//
// It is assumed that both numbers x and z have the same size k digits.
// Returns a carry, which is equivalent to "x is nonzero".
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = p, RCX = x, returns RAX
// ----------------------------------------------------------------------------

.intel_syntax noprefix

                .globl  bignum_optneg
                .text

#define k rdi
#define z rsi
#define p rdx
#define x rcx

#define c rax
#define a r8
#define i r9

#define cshort eax

bignum_optneg:

// If k = 0 do nothing, but need to set zero return for the carry (c = rax)

                xor     c, c
                test    k, k
                jz      end

// Convert p into a strict bitmask and set initial carry-in in c

                neg     p
                sbb     p, p
                sub     c, p

// Main loop

                xor     i, i
loop:

                mov     a, [x+8*i]
                xor     a, p
                add     a, c
                mov     cshort, 0
                mov     [z+8*i], a
                adc     c, 0
                inc     i
                cmp     i, k
                jc      loop

// Return carry flag, fixing up inversion for negative case

                xor     rax, p
                and     rax, 1

end:
                ret
