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
// Double modulo p_521, z := (2 * x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_double_p521
//     (uint64_t z[static 9], uint64_t x[static 9]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_double_p521
        .globl  _bignum_double_p521
        .text
        .balign 4

#define z x0
#define x x1

#define c x2
#define h x3
#define l x4

bignum_double_p521:
_bignum_double_p521:

// We can decide whether 2 * x >= p_521 just by 2 * x >= 2^521, which
// amounts to whether the top word is >= 256

                ldr     c, [x, #64]
                subs    xzr, c, #256

// Now if 2 * x >= p_521 we want 2 * x - p_521 = (2 * x + 1) - 2^521
// and otherwise just 2 * x. Feed in the condition as the carry bit
// to get 2 * x + [2 * x >= p_521] then just mask it off to 521 bits.

                ldp     l, h, [x]
                adcs    l, l, l
                adcs    h, h, h
                stp     l, h, [z]

                ldp     l, h, [x, #16]
                adcs    l, l, l
                adcs    h, h, h
                stp     l, h, [z, #16]

                ldp     l, h, [x, #32]
                adcs    l, l, l
                adcs    h, h, h
                stp     l, h, [z, #32]

                ldp     l, h, [x, #48]
                adcs    l, l, l
                adcs    h, h, h
                stp     l, h, [z, #48]

                adc     c, c, c
                and     c, c, #0x1FF
                str     c, [z, #64]

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
