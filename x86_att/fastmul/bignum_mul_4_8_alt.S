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

#define combadd(c,h,l,numa,numb)                \
        movq    numa, %rax ;                      \
        mulq     numb;                 \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    $0, c

// A minutely shorter form for when c = 0 initially

#define combadz(c,h,l,numa,numb)                \
        movq    numa, %rax ;                      \
        mulq     numb;                 \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    c, c

// A short form where we don't expect a top carry

#define combads(h,l,numa,numb)                  \
        movq    numa, %rax ;                      \
        mulq     numb;                 \
        addq    %rax, l ;                         \
        adcq    %rdx, h

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
        combads(t1,t0,(x),8(y))
        combadz(t2,t1,t0,8(x),(y))
        movq    t0, 8(z)

// Result term 2

        xorq    t0, t0
        combadz(t0,t2,t1,(x),16(y))
        combadd(t0,t2,t1,8(x),8(y))
        combadd(t0,t2,t1,16(x),(y))
        movq    t1, 16(z)

// Result term 3

        xorq    t1, t1
        combadz(t1,t0,t2,(x),24(y))
        combadd(t1,t0,t2,8(x),16(y))
        combadd(t1,t0,t2,16(x),8(y))
        combadd(t1,t0,t2,24(x),(y))
        movq    t2, 24(z)

// Result term 4

        xorq    t2, t2
        combadz(t2,t1,t0,8(x),24(y))
        combadd(t2,t1,t0,16(x),16(y))
        combadd(t2,t1,t0,24(x),8(y))
        movq    t0, 32(z)

// Result term 5

        xorq    t0, t0
        combadz(t0,t2,t1,16(x),24(y))
        combadd(t0,t2,t1,24(x),16(y))
        movq    t1, 40(z)

// Result term 6

        xorq    t1, t1
        combads(t0,t2,24(x),24(y))
        movq    t2, 48(z)

// Result term 7

        movq    t0, 56(z)

// Return

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
