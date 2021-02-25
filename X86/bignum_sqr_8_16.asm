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
; Square, z := x^2
; Input x[8]; output z[16]
;
;    extern void bignum_sqr_8_16 (uint64_t z[static 16], uint64_t x[static 8]);
;
; Standard x86-64 ABI: RDI = z, RSI = x
; ----------------------------------------------------------------------------

; These are actually right

%define z rdi
%define x rsi

; A zero register

%define zero rbp

; mulpadd i, j adds rdx * x[i] into the window  at the i+j point

%macro mulpadd 2
        mulx    rbx, rax, [x+8*%1]
%if ((%1 + %2) % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
%elif ((%1 + %2) % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
%elif ((%1 + %2) % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
%elif ((%1 + %2) % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
%elif ((%1 + %2) % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
%elif ((%1 + %2) % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
%elif ((%1 + %2) % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
%elif ((%1 + %2) % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
%endif

%endm

%macro diagonals 0

        xor     zero, zero

; Set initial window [r8..r10] + 2 wb = 10 + 20 + 30 + 40 + 50 + 60 + 70

        mov     rdx, [x+8*0]
        mulx    rax, r9, [x+8*1]
        mov     [z+8*1], r9
        mov     r9, zero
        mulx    rbx, r10, [x+8*2]
        adcx    r10, rax
        mov     [z+8*2], r10
        mov     r10, zero
        mulx    rax, r11, [x+8*3]
        adcx    r11, rbx
        mulx    rbx, r12, [x+8*4]
        adcx    r12, rax
        mulx    rax, r13, [x+8*5]
        adcx    r13, rbx
        mulx    rbx, r14, [x+8*6]
        adcx    r14, rax
        mulx    r8, r15, [x+8*7]
        adcx    r15, rbx
        adcx    r8, zero

; Add in the next diagonal = 21 + 31 + 41 + 51 + 61 + 71 + 54

        xor     zero, zero
        mov     rdx, [x+8*1]
        mulpadd 2, 1
        mov     [z+8*3], r11
        mulpadd 3, 1
        mov     [z+8*4], r12
        mulpadd 4, 1
        mulpadd 5, 1
        mulpadd 6, 1
        mov     r11, zero
        mulpadd 7, 1
        mov     r12, zero
        mov     rdx, [x+8*4]
        mulpadd 5, 4
        adcx    r10, zero

; And the next one = 32 + 42 + 52 + 62 + 72 + 64 + 65

        xor     zero, zero
        mov     rdx, [x+8*2]
        mulpadd 3, 2
        mov     [z+8*5], r13
        mulpadd 4, 2
        mov     [z+8*6], r14
        mulpadd 5, 2
        mulpadd 6, 2
        mulpadd 7, 2
        mov     rdx, [x+8*6]
        mov     r13, zero
        mulpadd 4, 6
        mov     r14, zero
        mulpadd 5, 6
        adcx    r12, zero

; And the final one = 43 + 53 + 63 + 73 + 74 + 75 + 76

        xor     zero, zero
        mov     rdx, [x+8*3]
        mulpadd 4, 3
        mov     [z+8*7], r15
        mulpadd 5, 3
        mov     [z+8*8], r8
        mulpadd 6, 3
        mulpadd 7, 3
        mov     rdx, [x+8*7]
        mulpadd 4, 7
        mov     r15, zero
        mulpadd 5, 7
        mov     r8, zero
        mulpadd 6, 7
        adcx    r14, zero

; Double and add things; use z[1]..z[8] and thereafter the registers
; r9..r15 which haven't been written back yet

        xor     zero, zero
        mov     rdx, [x+8*0]
        mulx    rbx, rax, rdx
        mov     [z+8*0], rax
        mov     rax, [z+8*1]
        adcx    rax, rax
        adox    rax, rbx
        mov     [z+8*1], rax

        mov     rax, [z+8*2]
        mov     rdx, [x+8*1]
        mulx    rbx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [z+8*2], rax
        mov     rax, [z+8*3]
        adcx    rax, rax
        adox    rax, rbx
        mov     [z+8*3], rax

        mov     rax, [z+8*4]
        mov     rdx, [x+8*2]
        mulx    rbx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [z+8*4], rax
        mov     rax, [z+8*5]
        adcx    rax, rax
        adox    rax, rbx
        mov     [z+8*5], rax

        mov     rax, [z+8*6]
        mov     rdx, [x+8*3]
        mulx    rbx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [z+8*6], rax
        mov     rax, [z+8*7]
        adcx    rax, rax
        adox    rax, rbx
        mov     [z+8*7], rax

        mov     rax, [z+8*8]
        mov     rdx, [x+8*4]
        mulx    rbx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [z+8*8], rax
        adcx    r9, r9
        adox    r9, rbx
        mov     [z+8*9], r9

        mov     rdx, [x+8*5]
        mulx    rbx, rdx, rdx
        adcx    r10, r10
        adox    r10, rdx
        mov     [z+8*10], r10
        adcx    r11, r11
        adox    r11, rbx
        mov     [z+8*11], r11

        mov     rdx, [x+8*6]
        mulx    rbx, rdx, rdx
        adcx    r12, r12
        adox    r12, rdx
        mov     [z+8*12], r12
        adcx    r13, r13
        adox    r13, rbx
        mov     [z+8*13], r13

        mov     rdx, [x+8*7]
        mulx    rbx, rdx, rdx
        adcx    r14, r14
        adox    r14, rdx
        mov     [z+8*14], r14
        adcx    r15, r15
        adox    r15, rbx
        mov     [z+8*15], r15

%endm

                global  bignum_sqr_8_16
                section .text

bignum_sqr_8_16:

; Save more registers to play with

        push    rbp
        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15

; Do the multiplication

         diagonals

; Real epilog

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx
        pop     rbp

        ret
