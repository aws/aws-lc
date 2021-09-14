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
// Subtract modulo m, z := (x - y) mod m, assuming x and y reduced
// Inputs x[k], y[k], m[k]; output z[k]
//
//    extern void bignum_modsub
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = x, X3 = y, X4 = m
// ----------------------------------------------------------------------------

        .globl  bignum_modsub
        .text
        .balign 4

#define k x0
#define z x1
#define x x2
#define y x3
#define m x4
#define i x5
#define j x6
#define a x7
#define b x8
#define c x9


bignum_modsub:

                adds    j, k, xzr               // j = k and ZF = (k = 0)
                beq     end                     // if k = 0 do nothing
                subs    i, xzr, xzr             // i = 0 and CF = 1

// Subtract z := x - y and record a mask for the carry x - y < 0

subloop:
                ldr     a, [x, i]
                ldr     b, [y, i]
                sbcs    a, a, b
                str     a, [z, i]
                add     i, i, #8
                sub     j, j, #1
                cbnz    j, subloop
                csetm   c, cc

// Now do a masked addition z := z + [c] * m

                mov     j, k
                adds    i, xzr, xzr
addloop:
                ldr     a, [z, i]
                ldr     b, [m, i]
                and     b, b, c
                adcs    a, a, b
                str     a, [z, i]
                add     i, i, #8
                sub     j, j, #1
                cbnz    j, addloop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
