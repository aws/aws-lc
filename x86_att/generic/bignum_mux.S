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
// Multiplex/select z := x (if p nonzero) or z := y (if p zero)
// Inputs p, x[k], y[k]; output z[k]
//
//    extern void bignum_mux
//     (uint64_t p, uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y);
//
// It is assumed that all numbers x, y and z have the same size k digits.
//
// Standard x86-64 ABI: RDI = p, RSI = k, RDX = z, RCX = x, R8 = y
// ----------------------------------------------------------------------------


        .globl  bignum_mux
        .text

#define b %rdi
#define k %rsi
#define z %rdx
#define x %rcx
#define y %r8
#define i %r9
#define a %rax



bignum_mux:
                testq   k, k
                jz      end                     // If length = 0 do nothing

                xorq    i, i
                negq    b                       // CF <=> (b != 0)
loop:
                movq    (x,i,8), a
                movq    (y,i,8), b
                cmovncq b, a // CF ? a : b
                movq    a, (z,i,8)
                incq    i
                decq    k
                jnz     loop
end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
