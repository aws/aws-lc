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
// Multiply bignum by 10 and add word: z := 10 * z + d
// Inputs z[k], d; outputs function return (carry) and z[k]
//
//    extern uint64_t bignum_muladd10 (uint64_t k, uint64_t *z, uint64_t d);
//
// Although typically the input d < 10, this is not actually required.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = d, returns X0
// ----------------------------------------------------------------------------

        .globl  bignum_muladd10
        .text
        .balign 4

#define k x0
#define z x1
#define d x2

#define i x3
#define h x4

#define a x5
#define l x5

bignum_muladd10:

// If k = 0 just return the input d as the carry (out of zero digits)

                cbz     k, end

// Simple loop

                mov     i, xzr
loop:
                ldr     a, [z, i, lsl #3]
                lsr     h, a, #61
                add     l, a, a
                add     h, h, h, lsr #2
                adds    l, l, l, lsl #2
                adc     h, h, xzr
                adds    a, l, d
                str     a, [z, i, lsl #3]
                adc     d, h, xzr
                add     i, i, 1
                cmp     i, k
                bcc     loop

// Return the final carry

end:
                mov     x0, d
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
