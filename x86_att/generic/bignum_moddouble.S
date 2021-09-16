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
// Double modulo m, z := (2 * x) mod m, assuming x reduced
// Inputs x[k], m[k]; output z[k]
//
//    extern void bignum_moddouble
//      (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *m);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = m
// ----------------------------------------------------------------------------


        .globl  bignum_moddouble
        .text

#define k %rdi
#define z %rsi
#define x %rdx
#define m %rcx
#define i %r8
#define a %r9
#define c %rax
#define b %r10

bignum_moddouble:

// If k = 0 do nothing

                testq   k, k
                jz      end

// Do (_::z) = 2 * x - m and generate a mask in c for 2 * x < m

                xorq    c, c
                xorq    i, i
                xorq    b, b

dubloop:
                movq    (x,i,8), a
                shrdq   $63, a, c
                negq    b
                sbbq    (m,i,8), c
                sbbq    b, b
                movq    c, (z,i,8)
                movq    a, c
                incq    i
                cmpq    k, i
                jc      dubloop
                shrq    $63, c

                addq    b, c

// Now do a corrective masked addition z := z + [c] * m

                xorq    i, i
                xorq    b, b
corrloop:
                movq    (m,i,8), a
                andq    c, a
                negq    b
                adcq    (z,i,8), a
                sbbq    b, b
                movq    a, (z,i,8)
                incq    i
                cmpq    k, i
                jc      corrloop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
