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
// Convert 4-digit (256-bit) bignum to/from little-endian form
// Input x[4]; output z[4]
//
//    extern void bignum_littleendian_4
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_fromlebytes_4
//     (uint64_t z[static 4], uint8_t x[static 32]);
//
//    extern void bignum_tolebytes_4
//     (uint8_t z[static 32], uint64_t x[static 4]);
//
// The implementation works by loading in bytes and storing in words (i.e.
// stylistically it is "fromlebytes"); in the more common little-endian
// usage of ARM, this is just copying.
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------

        .globl  bignum_littleendian_4
        .globl  bignum_fromlebytes_4
        .globl  bignum_tolebytes_4
        .text
        .balign 4

#define z x0
#define x x1

#define d x2
#define dshort w2
#define a x3

bignum_littleendian_4:
bignum_fromlebytes_4:
bignum_tolebytes_4:

// word 0

                ldrb    dshort, [x]
                extr    a, d, xzr, #8
                ldrb    dshort, [x, #1]
                extr    a, d, a, #8
                ldrb    dshort, [x, #2]
                extr    a, d, a, #8
                ldrb    dshort, [x, #3]
                extr    a, d, a, #8
                ldrb    dshort, [x, #4]
                extr    a, d, a, #8
                ldrb    dshort, [x, #5]
                extr    a, d, a, #8
                ldrb    dshort, [x, #6]
                extr    a, d, a, #8
                ldrb    dshort, [x, #7]
                extr    a, d, a, #8
                str     a, [z]

// word 1

                ldrb    dshort, [x, #8]
                extr    a, d, xzr, #8
                ldrb    dshort, [x, #9]
                extr    a, d, a, #8
                ldrb    dshort, [x, #10]
                extr    a, d, a, #8
                ldrb    dshort, [x, #11]
                extr    a, d, a, #8
                ldrb    dshort, [x, #12]
                extr    a, d, a, #8
                ldrb    dshort, [x, #13]
                extr    a, d, a, #8
                ldrb    dshort, [x, #14]
                extr    a, d, a, #8
                ldrb    dshort, [x, #15]
                extr    a, d, a, #8
                str     a, [z, #8]

// word 2

                ldrb    dshort, [x, #16]
                extr    a, d, xzr, #8
                ldrb    dshort, [x, #17]
                extr    a, d, a, #8
                ldrb    dshort, [x, #18]
                extr    a, d, a, #8
                ldrb    dshort, [x, #19]
                extr    a, d, a, #8
                ldrb    dshort, [x, #20]
                extr    a, d, a, #8
                ldrb    dshort, [x, #21]
                extr    a, d, a, #8
                ldrb    dshort, [x, #22]
                extr    a, d, a, #8
                ldrb    dshort, [x, #23]
                extr    a, d, a, #8
                str     a, [z, #16]

// word 3

                ldrb    dshort, [x, #24]
                extr    a, d, xzr, #8
                ldrb    dshort, [x, #25]
                extr    a, d, a, #8
                ldrb    dshort, [x, #26]
                extr    a, d, a, #8
                ldrb    dshort, [x, #27]
                extr    a, d, a, #8
                ldrb    dshort, [x, #28]
                extr    a, d, a, #8
                ldrb    dshort, [x, #29]
                extr    a, d, a, #8
                ldrb    dshort, [x, #30]
                extr    a, d, a, #8
                ldrb    dshort, [x, #31]
                extr    a, d, a, #8
                str     a, [z, #24]

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
