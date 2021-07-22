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
// Montgomery square, z := (x^2 / 2^256) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_montsqr_p256
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Does z := (x^2 / 2^256) mod p_256, assuming x^2 <= 2^256 * p_256, which is
// guaranteed in particular if x < p_256 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_montsqr_p256
        .text

#define z rdi
#define x rsi

// Use this fairly consistently for a zero

#define zero rbp
#define zeroe ebp

// Macro "mulpadd i x" adds rdx * x to the (i,i+1) position of
// the rotating register window r15,...,r8 maintaining consistent
// double-carrying using ADCX and ADOX and using rbx/rax as temps

.macro mulpadd arg1,arg2
        mulx    rbx, rax, \arg2
.if (\arg1 % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif (\arg1 % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif (\arg1 % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif (\arg1 % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
.elseif (\arg1 % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
.elseif (\arg1 % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
.elseif (\arg1 % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
.elseif (\arg1 % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
.endif

.endm



bignum_montsqr_p256:

// Save more registers to play with

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

// Compute [r15;r8] = [00] which we use later, but mainly
// set up an initial window [r14;...;r9] = [23;03;01]

        mov     rdx, [x]
        mulx    r15, r8, rdx
        mulx    r10, r9, [x+8*1]
        mulx    r12, r11, [x+8*3]
        mov     rdx, [x+8*2]
        mulx    r14, r13, [x+8*3]

// Clear our zero register, and also initialize the flags for the carry chain

        xor     zeroe, zeroe

// Chain in the addition of 02 + 12 + 13 to that window (no carry-out possible)
// This gives all the "heterogeneous" terms of the squaring ready to double

        mulpadd 2, [x]
        mulpadd 3, [x+8*1]
        mov     rdx, [x+8*3]
        mulpadd 4, [x+8*1]
        adcx    r13, zero
        adox    r14, zero
        adc     r14, zero

// Double and add to the 00 + 11 + 22 + 33 terms

        xor     zeroe, zeroe
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [x+8*1]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [x+8*2]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [x+8*3]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, zero
        adox    r15, zero

// First two waves of Montgomery reduction. Consolidate the double carries
// in r9 and propagate up to the top in r8, which is no longer needed otherwise.

        xor     zeroe, zeroe
        mov     rdx, 0x0000000100000000
        mulpadd 1, r8
        mulpadd 2, r9
        mov     rdx, 0xffffffff00000001
        mulpadd 3, r8
        mulpadd 4, r9
        adcx    r13, zero
        mov     r9d, zeroe
        adox    r9, zero
        adcx    r9, zero
        add     r14, r9
        adc     r15, zero
        mov     r8d, zeroe
        adc     r8, zero

// Now two more steps of Montgomery reduction, again with r8 = top carry

        xor     zeroe, zeroe
        mov     rdx, 0x0000000100000000
        mulpadd 3, r10
        mulpadd 4, r11
        mov     rdx, 0xffffffff00000001
        mulpadd 5, r10
        mulpadd 6, r11
        adcx    r15, zero
        adox    r8, zero
        adc     r8, zero

// Load [rax;r11;rbp;rdx;rcx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [rax;r11;rbp;rdx;rcx] = [r8;r15;r14;r13;r12] + (2^320 - p_256)

        mov     ecx, 1
        add     rcx, r12
        lea     rdx, [rdx-1]
        adc     rdx, r13
        lea     rbp, [rbp-1]
        mov     rax, rbp
        adc     rbp, r14
        mov     r11d,  0x00000000fffffffe
        adc     r11, r15
        adc     rax, r8

// Now carry is set if r + (2^320 - p_256) >= 2^320, i.e. r >= p_256
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovc   r12, rcx
        cmovc   r13, rdx
        cmovc   r14, rbp
        cmovc   r15, r11

// Write back reduced value

        mov     [z], r12
        mov     [z+8*1], r13
        mov     [z+8*2], r14
        mov     [z+8*3], r15

// Restore saved registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

        ret
