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
// Almost-Montgomery square, z :== (x^2 / 2^256) (congruent mod p_256)
// Input x[4]; output z[4]
//
//    extern void bignum_amontsqr_p256
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// "Almost" means the 4-digit result is correct mod p_256 but might not be
// fully reduced, i.e. it might be >= p_256. Use "bignum_montsqr_p256" instead
// where full reduction to a result < p_256 is desired/needed.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

#define z rdi
#define x rsi

// Use this fairly consistently for a zero

#define zero rbp

// Some temp registers for the last correction stage

#define d rax
#define u rdx
#define v rcx

#define ushort edx

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

.intel_syntax noprefix

                .globl  bignum_amontsqr_p256
                .text

bignum_amontsqr_p256:

// Save more registers to play with

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

// Set up an initial window [r14;...;r9] = [23;03;01]

        mov     rdx, [x]
        mulx    r10, r9, [x+8*1]
        mulx    r12, r11, [x+8*3]
        mov     rdx, [x+8*2]
        mulx    r14, r13, [x+8*3]

// Clear our zero register, and also initialize the flags for the carry chain

        xor     zero, zero

// Chain in the addition of 02 + 12 + 13 to that window (no carry-out possible)
// This gives all the "heterogeneous" terms of the squaring ready to double

        mulpadd 2, [x]
        mulpadd 3, [x+8*1]
        mov     rdx, [x+8*3]
        mulpadd 4, [x+8*1]
        adcx    r13, zero
        adox    r14, zero
        adcx    r14, zero

// Double and add to the 00 + 11 + 22 + 33 terms

        xor     zero, zero
        mov     rdx, [x]
        mulx    rdx, r8, rdx
        adcx    r9, r9
        adox    r9, rdx
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

// First two waves of Montgomery reduction.
// Catch the carry at the 6 position (r14) in r9, which is no longer needed

        xor     zero, zero
        mov     rdx, 0x0000000100000000
        mulpadd 1, r8
        mulpadd 2, r9
        mov     rdx, 0xffffffff00000001
        mulpadd 3, r8
        mulpadd 4, r9
        adcx    r13, zero
        mov     r9, zero
        adox    r9, zero
        adcx    r9, zero

// Now two more steps of Montgomery reduction.
// Catch the carry at the 8 position (r14) in r8

        xor     zero, zero
        mov     rdx, 0x0000000100000000
        mulpadd 3, r10
        mulpadd 4, r11
        mov     rdx, 0xffffffff00000001
        mulpadd 5, r10
        mulpadd 6, r11
        adcx    r15, zero
        mov     rax, zero
        adox    rax, zero
        adcx    rax, zero

// Finally add in the skipped carry to give a pre-reduced 5-word form
// in the window [rax; r15;r14;r13;r12]

        add     r14, r9
        adc     r15, 0
        adc     rax, 0

// Load non-trivial digits of p_256 = [v; 0; u; -1] masked using rax.
// Note that this only gives *almost* Montgomery reduction

        neg     d
        mov     ushort, 0x00000000ffffffff
        and     u, d
        mov     v, 0xffffffff00000001
        and     v, d

// Do a masked subtraction of p_256 and write back

        sub     r12, d
        sbb     r13, u
        sbb     r14, 0
        sbb     r15, v

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
