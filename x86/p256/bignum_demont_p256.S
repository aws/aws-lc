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
//    extern void bignum_demont_p256
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// This assumes the input is < p_256 for correctness. If this is not the case,
// use the variant "bignum_deamont_p256" instead.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_demont_p256
        .text

#define z rdi
#define x rsi

// Macro "mulpadd i x" adds rdx * x to the (i,i+1) position of
// the rotating register window rsi,rbx,r11,r10,r9,r8 maintaining consistent
// double-carrying using ADCX and ADOX and using rcx/rax as temps

.macro mulpadd arg1,arg2
        mulx    rcx, rax, \arg2
.if (\arg1 % 6 == 0)
        adcx    r8, rax
        adox    r9, rcx
.elseif (\arg1 % 6 == 1)
        adcx    r9, rax
        adox    r10, rcx
.elseif (\arg1 % 6 == 2)
        adcx    r10, rax
        adox    r11, rcx
.elseif (\arg1 % 6 == 3)
        adcx    r11, rax
        adox    rbx, rcx
.elseif (\arg1 % 6 == 4)
        adcx    rbx, rax
        adox    rsi, rcx
.elseif (\arg1 % 6 == 5)
        adcx    rsi, rax
        adox    r8, rcx
.endif

.endm



bignum_demont_p256:

// Save one more register to play with

        push    rbx

// Set up an initial 4-word window [r11,r10,r9,r8] = x

        mov     r8, [x+8*0]
        mov     r9, [x+8*1]
        mov     r10, [x+8*2]
        mov     r11, [x+8*3]

// Fill in two zeros to the left

        xor     rbx, rbx
        xor     rsi, rsi

// Montgomery reduce windows 0 and 1 together

        mov     rdx, 0x0000000100000000
        mulpadd 1, r8
        mulpadd 2, r9
        mov     rdx, 0xffffffff00000001
        mulpadd 3, r8
        mulpadd 4, r9
        mov     r8d, 0
        adcx    rsi, r8

// Append just one more leading zero (by the above r8 = 0 already).

        xor     r9, r9

// Montgomery reduce windows 2 and 3 together

        mov     rdx, 0x0000000100000000
        mulpadd 3, r10
        mulpadd 4, r11
        mov     rdx, 0xffffffff00000001
        mulpadd 5, r10
        mulpadd 6, r11
        mov     r10d, 0
        adcx    r9, r10

// Since the input was assumed reduced modulo, i.e. < p, we actually know that
// 2^256 * [carries; r9;r8;rsi;rbx] is <= (p - 1) + (2^256 - 1) p
// and hence [carries; r9;r8;rsi;rbx] < p. This means in fact carries = 0
// and [r9;r8;rsi;rbx] is already our answer, without further correction.
// Write that back.

        mov     [z+8*0], rbx
        mov     [z+8*1], rsi
        mov     [z+8*2], r8
        mov     [z+8*3], r9

// Restore saved register and return

        pop     rbx

        ret
