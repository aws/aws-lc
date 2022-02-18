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
// Optionally negate modulo p_384, z := (-x) mod p_384 (if p nonzero) or
// z := x (if p zero), assuming x reduced
// Inputs p, x[6]; output z[6]
//
//    extern void bignum_optneg_p384
//      (uint64_t z[static 6], uint64_t p, uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = p, RDX = x
// ----------------------------------------------------------------------------


        .globl  bignum_optneg_p384
        .globl  _bignum_optneg_p384
        .text

#define z %rdi
#define q %rsi
#define x %rdx

#define n0 %rax
#define n1 %rcx
#define n2 %r8
#define n3 %r9
#define n4 %r10
#define n5 %r11

#define n0short %eax

bignum_optneg_p384:
_bignum_optneg_p384:

// Adjust q by zeroing it if the input is zero (to avoid giving -0 = p_384,
// which is not strictly reduced even though it's correct modulo p_384).
// This step is redundant if we know a priori that the input is nonzero, which
// is the case for the y coordinate of points on the P-384 curve, for example.

                movq    (x), n0
                orq     8(x), n0
                movq    16(x), n1
                orq     24(x), n1
                movq    32(x), n2
                orq     40(x), n2
                orq     n1, n0
                orq     n2, n0
                negq    n0
                sbbq    n0, n0
                andq    n0, q

// Turn q into a bitmask, all 1s for q=false, all 0s for q=true

                negq    q
                sbbq    q, q
                notq    q

// Let [n5;n4;n3;n2;n1] = if q then p_384 else -1

                movl    $0x00000000ffffffff, n0short
                orq     q, n0
                movq    $0xffffffff00000000, n1
                orq     q, n1
                movq    $0xfffffffffffffffe, n2
                orq     q, n2
                movq    $0xffffffffffffffff, n3
                movq    n3, n4
                movq    n3, n5

// Subtract so [n5;n4;n3;n2;n1;n0] = if q then p_384 - x else -1 - x

                subq    (x), n0
                sbbq    8(x), n1
                sbbq    16(x), n2
                sbbq    24(x), n3
                sbbq    32(x), n4
                sbbq    40(x), n5

// XOR the words with the bitmask, which in the case q = false has the
// effect of restoring ~(-1 - x) = -(-1 - x) - 1 = 1 + x - 1 = x
// and write back the digits to the output

                xorq    q, n0
                movq    n0, (z)
                xorq    q, n1
                movq    n1, 8(z)
                xorq    q, n2
                movq    n2, 16(z)
                xorq    q, n3
                movq    n3, 24(z)
                xorq    q, n4
                movq    n4, 32(z)
                xorq    q, n5
                movq    n5, 40(z)

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
