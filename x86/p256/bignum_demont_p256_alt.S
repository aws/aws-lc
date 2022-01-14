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
// Convert from Montgomery form z := (x / 2^256) mod p_256, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_demont_p256_alt
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// This assumes the input is < p_256 for correctness. If this is not the case,
// use the variant "bignum_deamont_p256" instead.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_demont_p256_alt
        .text

#define z rdi
#define x rsi

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rcx as temporaries

#define mulpado(high,low,m)             \
        mulx    rcx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rcx

// Add rcx * m into a register-pair (high,low) maintaining consistent
// carry-catching with carry (negated, as bitmask) and using rax and rdx
// as temporaries

#define mulpadd(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rcx;                    \
        sub     rdx, carry;             \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// Initial version assuming no carry-in

#define mulpadi(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rcx;                    \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// Version with no carry in or out

#define mulpadn(high,low,m)             \
        mov     rax, m;                 \
        mul     rcx;                    \
        add     low, rax;               \
        adc     high, rdx

bignum_demont_p256_alt:

// Set up an initial 4-word window [r11,r10,r9,r8] = x

        mov     r8, [x]
        mov     r9, [x+8]
        mov     r10, [x+16]
        mov     r11, [x+24]

// Load constant 2^32; rcx toggles between this and (1 - rcx) below

        mov     rcx, 0x0000000100000000

// Montgomery reduce windows 0 and 1 together as [r8;rsi;r11;r10]

        mulpadi(rsi,r10,r9,r8)
        mulpadd(rsi,r11,r10,r9)
        neg     rcx
        neg     rsi
        inc     rcx
        mulpadi(r8,rsi,r11,r8)
        neg     r8
        mulpadn(r8,rsi,r9)

// Montgomery reduce windows 2 and 3 together as [r10;r9;r8;rsi]

        neg     rcx
        inc     rcx
        mulpadi(r9,rsi,r11,r10)
        mulpadd(r9,r8,rsi,r11)
        neg     rcx
        neg     r9
        inc     rcx
        mulpadi(r10,r9,r8,r10)
        neg     r10
        mulpadn(r10,r9,r11)

// Since the input was assumed reduced modulo, i.e. < p, we actually know that
// 2^256 * [carries; r10;r9;r8;rsi] is <= (p - 1) + (2^256 - 1) p
// and hence [carries; r10;r9;r8;rsi] < p. This means in fact carries = 0
// and [r10;r9;r8;rsi] is already our answer, without further correction.
// Write that back.

        mov     [z], rsi
        mov     [z+8], r8
        mov     [z+16], r9
        mov     [z+24], r10

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
