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
// Optionally negate, z := -x (if p nonzero) or z := x (if p zero)
// Inputs p, x[k]; outputs function return (nonzero input) and z[k]
//
//    extern uint64_t bignum_optneg
//     (uint64_t k, uint64_t *z, uint64_t p, uint64_t *x);
//
// It is assumed that both numbers x and z have the same size k digits.
// Returns a carry, which is equivalent to "x is nonzero".
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = p, RCX = x, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_optneg
        .text

#define k %rdi
#define z %rsi
#define p %rdx
#define x %rcx

#define c %rax
#define a %r8
#define i %r9

#define cshort %eax

bignum_optneg:

// If k = 0 do nothing, but need to set zero return for the carry (c = %rax)

                xorq    c, c
                testq   k, k
                jz      end

// Convert p into a strict bitmask and set initial carry-in in c

                negq    p
                sbbq    p, p
                subq    p, c

// Main loop

                xorq    i, i
loop:

                movq    (x,i,8), a
                xorq    p, a
                addq    c, a
                movl    $0, cshort
                movq    a, (z,i,8)
                adcq    $0, c
                incq    i
                cmpq    k, i
                jc      loop

// Return carry flag, fixing up inversion for negative case

                xorq    p, %rax
                andq    $1, %rax

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
