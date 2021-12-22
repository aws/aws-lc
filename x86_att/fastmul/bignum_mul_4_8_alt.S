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
// Multiply z := x * y
// Inputs x[4], y[4]; output z[8]
//
//    extern void bignum_mul_4_8_alt
//      (uint64_t z[static 8], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------


        .globl  bignum_mul_4_8_alt
        .text

// These are actually right

#define z %rdi
#define x %rsi

// This is moved from %rdx to free it for muls

#define y %rcx

// Other variables used as a rotating 3-word window to add terms to

#define t0 %r8
#define t1 %r9
#define t2 %r10

// Macro for the key "multiply and add to (c,h,l)" step

#define combadd(c,h,l,I,J)                      \
        movq    8*I(x), %rax ;                   \
        mulq     8*J(y);              \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    $0, c

// A minutely shorter form for the very first term where c = 0 initially

#define combadz(c,h,l,I,J)                      \
        movq    8*I(x), %rax ;                   \
        mulq     8*J(y);              \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    c, c

// A short form for the very last term where we don't expect a top carry

#define combads(c,h,l,I,J)                      \
        movq    8*I(x), %rax ;                   \
        mulq     8*J(y);              \
        addq    %rax, l ;                         \
        adcq    %rdx, h

// Stash the result

#define stash(c,h,l,I)                          \
        movq    l, 8*I(z)

bignum_mul_4_8_alt:

// Copy y into a safe register to start with

        movq    %rdx, y

// Result term 0

        movq    (x), %rax
        mulq     (y)

        movq    %rax, (z)
        movq    %rdx, t0
        xorq    t1, t1

// Result term 1

       xorq    t2, t2
       combadz(t2,t1,t0,0,1)
       combadd(t2,t1,t0,1,0)
       stash(t2,t1,t0,1)

// Result term 2

        xorq    t0, t0
        combadd(t0,t2,t1,0,2)
        combadd(t0,t2,t1,1,1)
        combadd(t0,t2,t1,2,0)
        stash(t0,t2,t1,2)

// Result term 3

        xorq    t1, t1
        combadd(t1,t0,t2,0,3)
        combadd(t1,t0,t2,1,2)
        combadd(t1,t0,t2,2,1)
        combadd(t1,t0,t2,3,0)
        stash(t1,t0,t2,3)

// Result term 4

        xorq    t2, t2
        combadd(t2,t1,t0,1,3)
        combadd(t2,t1,t0,2,2)
        combadd(t2,t1,t0,3,1)
        stash(t2,t1,t0,4)

// Result term 5

        xorq    t0, t0
        combadd(t0,t2,t1,2,3)
        combadd(t0,t2,t1,3,2)
        stash(t0,t2,t1,5)

// Result term 6

        xorq    t1, t1
        combads(t1,t0,t2,3,3)
        stash(t1,t0,t2,6)

// Result term 7

        stash(t2,t1,t0,7)

// Return

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
