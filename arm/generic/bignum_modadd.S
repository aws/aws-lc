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
// Add modulo m, z := (x + y) mod m, assuming x and y reduced
// Inputs x[k], y[k], m[k]; output z[k]
//
//    extern void bignum_modadd
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = x, X3 = y, X4 = m
// ----------------------------------------------------------------------------

        .globl  bignum_modadd
        .text

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


bignum_modadd:

                adds    j, k, xzr               // j = k and ZF = (k = 0)
                beq     end                     // if k = 0 do nothing
                adds    i, xzr, xzr             // i = 0 and CF = 0

// First just add (c::z) := x + y

addloop:
                ldr     a, [x, i]
                ldr     b, [y, i]
                adcs    a, a, b
                str     a, [z, i]
                add     i, i, #8
                sub     j, j, #1
                cbnz    j, addloop
                cset    c, cs

// Now do a comparison subtraction (c::z) - m, recording mask for (c::z) >= m

                mov     j, k
                subs    i, xzr, xzr
cmploop:
                ldr     a, [z, i]
                ldr     b, [m, i]
                sbcs    xzr, a, b
                add     i, i, #8
                sub     j, j, #1
                cbnz    j, cmploop
                sbcs    c, c, xzr
                mvn     c, c

// Now do a masked subtraction z := z - [c] * m

                mov     j, k
                subs    i, xzr, xzr
subloop:
                ldr     a, [z, i]
                ldr     b, [m, i]
                and     b, b, c
                sbcs    a, a, b
                str     a, [z, i]
                add     i, i, #8
                sub     j, j, #1
                cbnz    j, subloop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
