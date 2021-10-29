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
// Square z := x^2
// Input x[n]; output z[k]
//
//    extern void bignum_sqr
//     (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x);
//
// Does the "z := x^2" operation where x is n digits and result z is k.
// Truncates the result in general unless k >= 2 * n
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_sqr
        .text

// First three are where arguments come in, but n is moved.

#define p rdi
#define z rsi
#define x rcx
#define n r8

// These are always local scratch since multiplier result is in these

#define a rax
#define d rdx

// Other variables

#define i rbx
#define ll rbp
#define hh r9
#define k r10
#define y r11
#define htop r12
#define l r13
#define h r14
#define c r15

// Short versions

#define llshort ebp

bignum_sqr:

// We use too many registers, and also we need rax:rdx for multiplications

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        mov     n, rdx

// If p = 0 the result is trivial and nothing needs doing

        test    p, p
        jz      end

// initialize (hh,ll) = 0

        xor     llshort, llshort
        xor     hh, hh

// Iterate outer loop from k = 0 ... k = p - 1 producing result digits

        xor     k, k

outerloop:

// First let bot = MAX 0 (k + 1 - n) and top = MIN (k + 1) n
// We want to accumulate all x[i] * x[k - i] for bot <= i < top
// For the optimization of squaring we avoid duplication and do
// 2 * x[i] * x[k - i] for i < htop, where htop = MIN ((k+1)/2) n
// Initialize i = bot; in fact just compute bot as i directly.

        xor     c, c
        lea     i, [k+1]
        mov     htop, i
        shr     htop, 1
        sub     i, n
        cmovc   i, c
        cmp     htop, n
        cmovnc  htop, n

// Initialize the three-part local sum (c,h,l); c was already done above

        xor     l, l
        xor     h, h

// If htop <= bot then main doubled part of the sum is empty

        cmp     i, htop
        jnc     nosumming

// Use a moving pointer for [y] = x[k-i] for the cofactor

        mov     a, k
        sub     a, i
        lea     y, [x+8*a]

// Do the main part of the sum x[i] * x[k - i] for 2 * i < k

innerloop:
        mov     a, [x+8*i]
        mul     QWORD PTR [y]
        add     l, a
        adc     h, d
        adc     c, 0
        sub     y, 8
        inc     i
        cmp     i, htop
        jc      innerloop

// Now double it

        add     l, l
        adc     h, h
        adc     c, c

// If k is even (which means 2 * i = k) and i < n add the extra x[i]^2 term

nosumming:
        test    k, 1
        jnz     innerend
        cmp     i, n
        jnc     innerend

        mov     a, [x+8*i]
        mul     a
        add     l, a
        adc     h, d
        adc     c, 0

// Now add the local sum into the global sum, store and shift

innerend:
        add     l, ll
        mov     [z+8*k], l
        adc     h, hh
        mov     ll, h
        adc     c, 0
        mov     hh, c

        inc     k
        cmp     k, p
        jc      outerloop

// Rextore registers and return

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
