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
// 384-bit multiplex/select z := x (if p nonzero) or z := y (if p zero)
// Inputs p, x[6], y[6]; output z[6]
//
//    extern void bignum_mux_6
//     (uint64_t p, uint64_t z[static 6],
//      uint64_t x[static 6], uint64_t y[static 6]);
//
// It is assumed that all numbers x, y and z have the same size 6 digits.
//
// Standard x86-64 ABI: RDI = p, RSI = z, RDX = x, RCX = y
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_mux_6
        .text

#define p rdi
#define z rsi
#define x rdx
#define y rcx
#define a rax
#define b r8


bignum_mux_6:
                test    p, p

                .set    I, 0
                .rep    6
                mov     a, [x+8*I]
                mov     b, [y+8*I]
                cmovz   a, b
                mov     [z+8*I], a
                .set    I, (I+1)
                .endr

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
