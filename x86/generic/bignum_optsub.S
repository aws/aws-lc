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
// Optionally subtract, z := x - y (if p nonzero) or z := x (if p zero)
// Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_optsub
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y);
//
// It is assumed that all numbers x, y and z have the same size k digits.
// Returns carry-out as per usual subtraction, always 0 if p was zero.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = p, R8 = y, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_optsub
        .text

#define k rdi
#define z rsi
#define x rdx
#define p rcx
#define y r8

#define i r9
#define b r10
#define c rax
#define a r11


bignum_optsub:

// Initialize top carry to zero in all cases (also return value)

                xor     c, c

// If k = 0 do nothing

                test    k, k
                jz      end

// Convert the nonzero/zero status of p into an all-1s or all-0s mask

                neg     p
                sbb     p, p

// Now go round the loop for i=0...k-1, saving the carry in c each iteration

                xor     i, i
loop:
                mov     a, [x+8*i]
                mov     b, [y+8*i]
                and     b, p
                neg     c
                sbb     a, b
                sbb     c, c
                mov     [z+8*i], a
                inc     i
                cmp     i, k
                jc      loop

// Return top carry

                neg     rax

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
