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
// Convert 6-digit (384-bit) bignum to/from little-endian form
// Input x[6]; output z[6]
//
//    extern void bignum_littleendian_6
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_fromlebytes_6
//     (uint64_t z[static 6], uint8_t x[static 48]);
//
//    extern void bignum_tolebytes_6
//     (uint8_t z[static 48], uint64_t x[static 6]);
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_littleendian_6
        .globl  bignum_fromlebytes_6
        .globl  bignum_tolebytes_6
        .text

#define z rdi
#define x rsi
#define a rax

bignum_littleendian_6:
bignum_fromlebytes_6:
bignum_tolebytes_6:

                mov     a, [x]
                mov     [z], a

                mov     a, [x+8]
                mov     [z+8], a

                mov     a, [x+16]
                mov     [z+16], a

                mov     a, [x+24]
                mov     [z+24], a

                mov     a, [x+32]
                mov     [z+32], a

                mov     a, [x+40]
                mov     [z+40], a

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
