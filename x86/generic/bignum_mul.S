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
// Inputs x[m], y[n]; output z[k]
//
//    extern void bignum_mul
//     (uint64_t k, uint64_t *z,
//      uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Does the "z := x * y" operation where x is m digits, y is n, result z is k.
// Truncates the result in general unless k >= m + n
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = m, RCX = x, R8 = n, R9 = y
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_mul
        .text

// These are actually right

#define p rdi
#define z rsi
#define n r8

// These are not

#define c r15
#define h r14
#define l r13
#define x r12
#define y r11
#define i rbx
#define k r10
#define m rbp

// These are always local scratch since multiplier result is in these

#define a rax
#define d rdx



bignum_mul:

// We use too many registers, and also we need rax:rdx for multiplications

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        mov     m, rdx

// If the result size is zero, do nothing
// Note that even if either or both inputs has size zero, we can't
// just give up because we at least need to zero the output array
// If we did a multiply-add variant, however, then we could

        test    p, p
        jz      end

// Set initial 2-part sum to zero (we zero c inside the body)

        xor     h,h
        xor     l,l

// Otherwise do outer loop k = 0 ... k = p - 1

        xor     k, k

outerloop:

// Zero our carry term first; we eventually want it and a zero is useful now
// Set a =  max 0 (k + 1 - n), i = min (k + 1) m
// This defines the range a <= j < i for the inner summation
// Note that since k < p < 2^64 we can assume k + 1 doesn't overflow
// And since we want to increment it anyway, we might as well do it now

        xor     c, c            // c = 0
        inc     k               // k = k + 1

        mov     a, k            // a = k + 1
        sub     a, n            // a = k + 1 - n
        cmovc   a, c            // a = max 0 (k + 1 - n)

        mov     i, m            // i = m
        cmp     k, m            // CF <=> k + 1 < m
        cmovc   i, k            // i = min (k + 1) m

// Turn i into a loop count, and skip things if it's <= 0
// Otherwise set up initial pointers x -> x0[a] and y -> y0[k - a]
// and then launch into the main inner loop, postdecrementing i

        mov     d, k
        sub     d, i
        sub     i, a
        jbe     innerend
        lea     x,[rcx+8*a]
        lea     y,[r9+8*d-8]

innerloop:
        mov     rax, [y+8*i]
        mul     QWORD PTR  [x]
        add     x, 8
        add     l, rax
        adc     h, rdx
        adc     c, 0
        dec     i
        jnz     innerloop

innerend:

        mov     [z], l
        mov     l, h
        mov     h, c
        add     z, 8

        cmp     k, p
        jc      outerloop

end:
        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
