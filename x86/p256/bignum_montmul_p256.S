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
// Montgomery multiply, z := (x * y / 2^256) mod p_256
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_montmul_p256
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Does z := (2^{-256} * x * y) mod p_256, assuming that the inputs x and y
// satisfy x * y <= 2^256 * p_256 (in particular this is true if we are in
// the "usual" case x < p_256 and y < p_256).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_montmul_p256
        .text

#define z rdi
#define x rsi

// We move the y argument here so we can use rdx for multipliers

#define y rcx

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



bignum_montmul_p256:

// Save more registers to play with

        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15

// Copy y into a safe register to start with

        mov     y, rdx

// Do row 0 computation, which is a bit different:
// set up initial window [r12,r11,r10,r9,r8] = y[0] * x
// Unlike later, we only need a single carry chain

        xor     r13d, r13d
        mov     rdx, [y+8*0]
        mulx    r9, r8, [x+8*0]
        mulx    r10, rbx, [x+8*1]
        adc     r9, rbx
        mulx    r11, rbx, [x+8*2]
        adc     r10, rbx
        mulx    r12, rbx, [x+8*3]
        adc     r11, rbx
        adc     r12, r13

// Add row 1

        mov     rdx, [y+8*1]
        xor     r14d, r14d
        mulpadd 1, [x]
        mulpadd 2, [x+8*1]
        mulpadd 3, [x+8*2]
        mulpadd 4, [x+8*3]
        adc    r13, r14

// Montgomery reduce windows 0 and 1 together

        xor     r15d, r15d
        mov     rdx, 0x0000000100000000
        mulpadd 1, r8
        mulpadd 2, r9
        not     rdx
        lea     rdx, [rdx+2]
        mulpadd 3, r8
        mulpadd 4, r9
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15

// Add row 2

        mov     rdx, [y+8*2]
        xor     r8d, r8d
        mulpadd 2, [x]
        mulpadd 3, [x+8*1]
        mulpadd 4, [x+8*2]
        adox    r14, r8
        mulx    rbx, rax, [x+8*3]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8

// Add row 3

        mov     rdx, [y+8*3]
        xor     r9d, r9d
        mulpadd 3, [x]
        mulpadd 4, [x+8*1]
        mulpadd 5, [x+8*2]
        adox    r15, r9
        mulx    rbx, rax, [x+8*3]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9

// Montgomery reduce windows 2 and 3 together

        xor     r9d, r9d
        mov     rdx, 0x0000000100000000
        mulpadd 3, r10
        mulpadd 4, r11
        not     rdx
        lea     rdx, [rdx+2]
        mulpadd 5, r10
        mulpadd 6, r11
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9

// We now have a pre-reduced 5-word form [r8; r15;r14;r13;r12]
// Load [rax;r11;rbx;rdx;rcx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [rax;r11;rbx;rdx;rcx] = [r8;r15;r14;r13;r12] + (2^320 - p_256)

        mov     ecx, 1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0x00000000fffffffe
        adc     r11, r15
        adc     rax, r8

// Now carry is set if r + (2^320 - p_256) >= 2^320, i.e. r >= p_256
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovc   r12, rcx
        cmovc   r13, rdx
        cmovc   r14, r9
        cmovc   r15, r11

// Write back reduced value

        mov     [z+8*0], r12
        mov     [z+8*1], r13
        mov     [z+8*2], r14
        mov     [z+8*3], r15

// Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx

        ret
