 ; * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 ; *
 ; * Licensed under the Apache License, Version 2.0 (the "License").
 ; * You may not use this file except in compliance with the License.
 ; * A copy of the License is located at
 ; *
 ; *  http://aws.amazon.com/apache2.0
 ; *
 ; * or in the "LICENSE" file accompanying this file. This file is distributed
 ; * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 ; * express or implied. See the License for the specific language governing
 ; * permissions and limitations under the License.

; ----------------------------------------------------------------------------
; Almost-Montgomery multiply, z :== (x * y / 2^384) (congruent mod p_384)
; Inputs x[6], y[6]; output z[6]
;
;    extern void bignum_amontmul_p384
;     (uint64_t z[static 6], uint64_t x[static 6], uint64_t y[static 6]);
;
; Does z :== (x * y / 2^384) mod p_384, meaning that the result, in the native
; size 6, is congruent modulo p_384, but might not be fully reduced mod p_384.
; This is why it is called *almost* Montgomery multiplication.
;
; Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
; ----------------------------------------------------------------------------

%define z rdi
%define x rsi

; We move the y argument here so we can use rdx for multipliers

%define y rcx

; Fairly consistently used as a zero register

%define zero rbp

; Some temp registers for the last correction stage

%define d rax
%define u rdx
%define v rcx
%define w rbx

; Macro "mulpadd i x" adds rdx * x to the (i,i+1) position of
; the rotating register window r15,...,r8 maintaining consistent
; double-carrying using ADCX and ADOX and using rbx/rax as temps

%macro mulpadd 2
        mulx    rbx, rax, %2
%if (%1 % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
%elif (%1 % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
%elif (%1 % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
%elif (%1 % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
%elif (%1 % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
%elif (%1 % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
%elif (%1 % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
%elif (%1 % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
%endif

%endm

; Core one-step Montgomery reduction macro. Takes input in
; [d7;d6;d5;d4;d3;d2;d1;d0] and returns result in [d7;d6;d5;d4;d3;d2;d1],
; adding to the existing contents, re-using d0 as a temporary internally
;
; We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
; where w = [d0 + (d0<<32)] mod 2^64
;
;       montredc d7,d6,d5,d4,d3,d2,d1,d0, t3,t2,t1
;
; This particular variant, with its mix of addition and subtraction
; at the top, is not intended to maintain a coherent carry or borrow out.
; It is assumed the final result would fit in [d7;d6;d5;d4;d3;d2;d1].
; which is always the case here as the top word is even always in {0,1}

%macro montredc 8
; Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64
                mov     rdx, %8
                shl     rdx, 32
                add     rdx, %8
; Construct [rbp;rbx;rax;-] = (2^384 - p_384) * w
; We know the lowest word will cancel so we can re-use %8 as a temp
                xor     rbp, rbp
                mov     rax, 0xffffffff00000001
                mulx    rax, rbx, rax
                mov     rbx, 0x00000000ffffffff
                mulx    rbx, %8, rbx
                adc     rax, %8
                adc     rbx, rdx
                adc     rbp, 0
; Now subtract that and add 2^384 * w
                sub     %7, rax
                sbb     %6, rbx
                sbb     %5, rbp
                sbb     %4, 0
                sbb     %3, 0
                sbb     rdx, 0
                add     %2, rdx
                adc     %1, 0
%endm

                global  bignum_amontmul_p384
                section .text

bignum_amontmul_p384:

; Save more registers to play with

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

; Copy y into a safe register to start with

        mov     y, rdx

; Do row 0 computation, which is a bit different:
; set up initial window [r14,r13,r12,r11,r10,r9,r8] = y[0] * x
; Unlike later, we only need a single carry chain

        mov     rdx, [y+8*0]
        mulx    r9, r8, [x+8*0]
        mulx    r10, rbx, [x+8*1]
        add     r9, rbx
        mulx    r11, rbx, [x+8*2]
        adc     r10, rbx
        mulx    r12, rbx, [x+8*3]
        adc     r11, rbx
        mulx    r13, rbx, [x+8*4]
        adc     r12, rbx
        mulx    r14, rbx, [x+8*5]
        adc     r13, rbx
        adc     r14, 0

; Montgomery reduce the zeroth window

        xor     r15, r15
        montredc r15, r14,r13,r12,r11,r10,r9,r8

; Add row 1

        xor     zero, zero
        mov     rdx, [y+8*1]
        xor     r8, r8
        mulpadd 1, [x]
        mulpadd 2, [x+8*1]
        mulpadd 3, [x+8*2]
        mulpadd 4, [x+8*3]
        mulpadd 5, [x+8*4]
        mulpadd 6, [x+8*5]
        adcx    r15, zero
        adox    r8, zero
        adcx    r8, zero

; Montgomery reduce window 1

        montredc r8, r15,r14,r13,r12,r11,r10,r9

; Add row 2

        xor     zero, zero
        mov     rdx, [y+8*2]
        xor     r9, r9
        mulpadd 2, [x]
        mulpadd 3, [x+8*1]
        mulpadd 4, [x+8*2]
        mulpadd 5, [x+8*3]
        mulpadd 6, [x+8*4]
        mulpadd 7, [x+8*5]
        adcx    r8, zero
        adox    r9, zero
        adcx    r9, zero

; Montgomery reduce window 2

        montredc r9, r8,r15,r14,r13,r12,r11,r10

; Add row 3

        xor     zero, zero
        mov     rdx, [y+8*3]
        xor     r10, r10
        mulpadd 3, [x]
        mulpadd 4, [x+8*1]
        mulpadd 5, [x+8*2]
        mulpadd 6, [x+8*3]
        mulpadd 7, [x+8*4]
        mulpadd 8, [x+8*5]
        adcx    r9, zero
        adox    r10, zero
        adcx    r10, zero

; Montgomery reduce window 3

        montredc r10, r9,r8,r15,r14,r13,r12,r11

; Add row 4

        xor     zero, zero
        mov     rdx, [y+8*4]
        xor     r11, r11
        mulpadd 4, [x]
        mulpadd 5, [x+8*1]
        mulpadd 6, [x+8*2]
        mulpadd 7, [x+8*3]
        mulpadd 8, [x+8*4]
        mulpadd 9, [x+8*5]
        adcx    r10, zero
        adox    r11, zero
        adcx    r11, zero

; Montgomery reduce window 4

        montredc r11, r10,r9,r8,r15,r14,r13,r12

; Add row 5

        xor     zero, zero
        mov     rdx, [y+8*5]
        xor     r12, r12
        mulpadd 5, [x]
        mulpadd 6, [x+8*1]
        mulpadd 7, [x+8*2]
        mulpadd 8, [x+8*3]
        mulpadd 9, [x+8*4]
        mulpadd 10, [x+8*5]
        adcx    r11, zero
        adox    r12, zero
        adcx    r12, zero

; Montgomery reduce window 5

        montredc r12, r11,r10,r9,r8,r15,r14,r13

; We now have a pre-reduced 7-word form [r12;r11;r10;r9;r8;r15;r14]
; Load non-trivial digits of 2^384 - p_384 = [0; 0; 0; w; v; u] masked with r12
; Note that this only gives *almost* Montgomery reduction

        neg     r12
        mov     u, 0xffffffff00000001
        and     u, r12
        mov     v, 0x00000000ffffffff
        and     v, r12
        mov     w, 0x0000000000000001
        and     w, r12

; Masked addition of 2^384 - p_384, hence subtraction of p_384

        add    r14, u
        adc    r15, v
        adc    r8, w
        adc    r9, 0
        adc    r10, 0
        adc    r11, 0

; Write back the result

        mov     [z], r14
        mov     [z+8*1], r15
        mov     [z+8*2], r8
        mov     [z+8*3], r9
        mov     [z+8*4], r10
        mov     [z+8*5], r11

; Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

        ret
