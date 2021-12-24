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
// Square, z := x^2
// Input x[4]; output z[8]
//
//    extern void bignum_sqr_4_8_alt
//     (uint64_t z[static 8], uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_sqr_4_8_alt
        .text

// Input arguments

#define z %rdi
#define x %rsi

// Other variables used as a rotating 3-word window to add terms to

#define t0 %rcx
#define t1 %r8
#define t2 %r9

// Macro for the key "multiply and add to (c,h,l)" step, for square term

#define combadd1(c,h,l,I)                       \
        movq    8*I(x), %rax ;                   \
        mulq    %rax;                            \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    $0, c

// A short form for the very last term where we don't expect a top carry

#define combads(c,h,l,I)                        \
        movq    8*I(x), %rax ;                   \
        mulq    %rax;                            \
        addq    %rax, l ;                         \
        adcq    %rdx, h

// A version doubling before adding, for non-square terms

#define combadd2(c,h,l,I,J)                     \
        movq    8*I(x), %rax ;                   \
        mulq     8*J(x);              \
        addq    %rax, %rax ;                       \
        adcq    %rdx, %rdx ;                       \
        adcq    $0, c ;                           \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    $0, c

// Stash the result

#define stash(c,h,l,I)                          \
        movq    l, 8*I(z)

bignum_sqr_4_8_alt:

// Result term 0

        movq    (x), %rax
        mulq    %rax

        movq    %rax, (z)
        movq    %rdx, t0
        xorq    t1, t1

// Result term 1

       xorq    t2, t2
       combadd2(t2,t1,t0,0,1)
       stash(t2,t1,t0,1)

// Result term 2

        xorq    t0, t0
        combadd1(t0,t2,t1,1)
        combadd2(t0,t2,t1,0,2)
        stash(t0,t2,t1,2)

// Result term 3

        xorq    t1, t1
        combadd2(t1,t0,t2,0,3)
        combadd2(t1,t0,t2,1,2)
        stash(t1,t0,t2,3)

// Result term 4

        xorq    t2, t2
        combadd2(t2,t1,t0,1,3)
        combadd1(t2,t1,t0,2)
        stash(t2,t1,t0,4)

// Result term 5

        xorq    t0, t0
        combadd2(t0,t2,t1,2,3)
        stash(t0,t2,t1,5)

// Result term 6

        xorq    t1, t1
        combads(t1,t0,t2,3)
        stash(t1,t0,t2,6)

// Result term 7

        stash(t2,t1,t0,7)

// Return

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
