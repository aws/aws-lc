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
; Input x[16]; output z[32]; temporary buffer t[>=24]
;
;    extern void bignum_ksqr_16_32
;     (uint64_t z[static 32], uint64_t x[static 16], uint64_t t[static 24]);
;
; In this x86 code the final temporary space argument t is unused, but
; it is retained in the prototype above for API consistency with ARM.
;
; Standard x86-64 ABI: RDI = z, RSI = x, RDX = t
; ----------------------------------------------------------------------------

%define z rdi
%define x rsi

; A zero register

%define zero rbp

; ------------------------------------------------------------------------
; mulpadd i, j adds x[i] * rdx (now assumed = x[j]) into the window at i+j
; ------------------------------------------------------------------------

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


; ------------------------------------------------------------------------
; addrow i,j adds z[i+j] + x[i..i+7] * x[j] into the window
; ------------------------------------------------------------------------

%macro addrow 2
        mov     rdx, [x+8*%2]
        xor     zero, zero      ; Get a known flag state and give a zero reg

%if ((%1 + %2) % 8 == 0)
        adox    r8, [z+8*(%1+%2)]
%elif ((%1 + %2) % 8 == 1)
        adox    r9, [z+8*(%1+%2)]
%elif ((%1 + %2) % 8 == 2)
        adox    r10, [z+8*(%1+%2)]
%elif ((%1 + %2) % 8 == 3)
        adox    r11, [z+8*(%1+%2)]
%elif ((%1 + %2) % 8 == 4)
        adox    r12, [z+8*(%1+%2)]
%elif ((%1 + %2) % 8 == 5)
        adox    r13, [z+8*(%1+%2)]
%elif ((%1 + %2) % 8 == 6)
        adox    r14, [z+8*(%1+%2)]
%elif ((%1 + %2) % 8 == 7)
        adox    r15, [z+8*(%1+%2)]
%endif

        mulpadd %1, %2

%if ((%1 + %2) % 8 == 0)
        mov     [z+8*(%1+%2)], r8
        mov     r8, zero
%elif ((%1 + %2) % 8 == 1)
        mov     [z+8*(%1+%2)], r9
        mov     r9, zero
%elif ((%1 + %2) % 8 == 2)
        mov     [z+8*(%1+%2)], r10
        mov     r10, zero
%elif ((%1 + %2) % 8 == 3)
        mov     [z+8*(%1+%2)], r11
        mov     r11, zero
%elif ((%1 + %2) % 8 == 4)
        mov     [z+8*(%1+%2)], r12
        mov     r12, zero
%elif ((%1 + %2) % 8 == 5)
        mov     [z+8*(%1+%2)], r13
        mov     r13, zero
%elif ((%1 + %2) % 8 == 6)
        mov     [z+8*(%1+%2)], r14
        mov     r14, zero
%elif ((%1 + %2) % 8 == 7)
        mov     [z+8*(%1+%2)], r15
        mov     r15, zero
%endif

        mulpadd (%1+1), %2
        mulpadd (%1+2), %2
        mulpadd (%1+3), %2
        mulpadd (%1+4), %2
        mulpadd (%1+5), %2
        mulpadd (%1+6), %2
        mulpadd (%1+7), %2

%if ((%1 + %2) % 8 == 0)
        adcx    r8, zero
%elif ((%1 + %2) % 8 == 1)
        adcx    r9, zero
%elif ((%1 + %2) % 8 == 2)
        adcx    r10, zero
%elif ((%1 + %2) % 8 == 3)
        adcx    r11, zero
%elif ((%1 + %2) % 8 == 4)
        adcx    r12, zero
%elif ((%1 + %2) % 8 == 5)
        adcx    r13, zero
%elif ((%1 + %2) % 8 == 6)
        adcx    r14, zero
%elif ((%1 + %2) % 8 == 7)
        adcx    r15, zero
%endif


%endm


; ------------------------------------------------------------------------
; Adds off-diagonal part of x[i..i+7]^2 into the window, writes 0..7 back
; ------------------------------------------------------------------------

%macro sqr 1

        xor     zero, zero

; Set up the initial window

        mov     r9, [z+16*%1+8*1]
        mov     r10, [z+16*%1+8*2]
        mov     r11, [z+16*%1+8*3]
        mov     r12, [z+16*%1+8*4]
        mov     r13, [z+16*%1+8*5]
        mov     r14, [z+16*%1+8*6]
        mov     r15, [z+16*%1+8*7]
        mov     r8, zero

; Add in the first diagonal [r8..r10] + 2 wb = 10 + 20 + 30 + 40 + 50 + 60 + 70

        mov     rdx, [x+8*%1+8*0]
        mulpadd (%1+1), (%1+0)
        mov     [z+16*%1+8*1],r9
        mulpadd (%1+2), (%1+0)
        mov     [z+16*%1+8*2],r10
        mulpadd (%1+3), (%1+0)
        mulpadd (%1+4), (%1+0)
        mov     r9, zero
        mulpadd (%1+5), (%1+0)
        mov     r10, zero
        mulpadd (%1+6), (%1+0)
        mulpadd (%1+7), (%1+0)
        adcx    r8, zero

; Add in the next diagonal = 21 + 31 + 41 + 51 + 61 + 71 + 54

        xor     zero, zero
        mov     rdx, [x+8*%1+8*1]
        mulpadd (%1+2), (%1+1)
        mov     [z+16*%1+8*3], r11
        mulpadd (%1+3), (%1+1)
        mov     [z+16*%1+8*4], r12
        mulpadd (%1+4), (%1+1)
        mulpadd (%1+5), (%1+1)
        mulpadd (%1+6), (%1+1)
        mov     r11, zero
        mulpadd (%1+7), (%1+1)
        mov     r12, zero
        mov     rdx, [x+8*%1+8*4]
        mulpadd (%1+5), (%1+4)
        adcx    r10, zero

; And the next one = 32 + 42 + 52 + 62 + 72 + 64 + 65

        xor     zero, zero
        mov     rdx, [x+8*%1+8*2]
        mulpadd (%1+3), (%1+2)
        mov     [z+16*%1+8*5], r13
        mulpadd (%1+4), (%1+2)
        mov     [z+16*%1+8*6], r14
        mulpadd (%1+5), (%1+2)
        mulpadd (%1+6), (%1+2)
        mulpadd (%1+7), (%1+2)
        mov     rdx, [x+8*%1+8*6]
        mov     r13, zero
        mulpadd (%1+4), (%1+6)
        mov     r14, zero
        mulpadd (%1+5), (%1+6)
        adcx    r12, zero

; And the final one = 43 + 53 + 63 + 73 + 74 + 75 + 76

        xor     zero, zero
        mov     rdx, [x+8*%1+8*3]
        mulpadd (%1+4), (%1+3)
        mov     [z+16*%1+8*7], r15
        mulpadd (%1+5), (%1+3)
        mulpadd (%1+6), (%1+3)
        mulpadd (%1+7), (%1+3)
        mov     rdx, [x+8*%1+8*7]
        mulpadd (%1+4), (%1+7)
        mulpadd (%1+5), (%1+7)
        mulpadd (%1+6), (%1+7)
        adcx    r14, zero
        mov     r15, zero
%endm

; ------------------------------------------------------------------------
; Multiply-add: z := z + x[i...i+7] * x
; ------------------------------------------------------------------------

%macro addrows 1

        sqr %1

        %assign i (%1+8)
%rep (8-%1)
        addrow %1, i
        %assign i (i+1)
%endrep

        mov     [z+8*(16+%1)], r8
        mov     [z+8*(17+%1)], r9
        mov     [z+8*(18+%1)], r10
        mov     [z+8*(19+%1)], r11
        mov     [z+8*(20+%1)], r12
        mov     [z+8*(21+%1)], r13
        mov     [z+8*(22+%1)], r14
        mov     [z+8*(23+%1)], r15
%endm


; ------------------------------------------------------------------------
; mulrow i,j adds x[i..i+7] * x[j] into the window
; just like addrow but no addition of z[i+j]
; ------------------------------------------------------------------------

%macro mulrow 2
        mov     rdx, [x+8*%2]
        xor     zero, zero      ; Get a known flag state and give a zero reg

        mulpadd %1, %2

%if ((%1 + %2) % 8 == 0)
        mov     [z+8*(%1+%2)], r8
        mov     r8, zero
%elif ((%1 + %2) % 8 == 1)
        mov     [z+8*(%1+%2)], r9
        mov     r9, zero
%elif ((%1 + %2) % 8 == 2)
        mov     [z+8*(%1+%2)], r10
        mov     r10, zero
%elif ((%1 + %2) % 8 == 3)
        mov     [z+8*(%1+%2)], r11
        mov     r11, zero
%elif ((%1 + %2) % 8 == 4)
        mov     [z+8*(%1+%2)], r12
        mov     r12, zero
%elif ((%1 + %2) % 8 == 5)
        mov     [z+8*(%1+%2)], r13
        mov     r13, zero
%elif ((%1 + %2) % 8 == 6)
        mov     [z+8*(%1+%2)], r14
        mov     r14, zero
%elif ((%1 + %2) % 8 == 7)
        mov     [z+8*(%1+%2)], r15
        mov     r15, zero
%endif

        mulpadd (%1+1), %2
        mulpadd (%1+2), %2
        mulpadd (%1+3), %2
        mulpadd (%1+4), %2
        mulpadd (%1+5), %2
        mulpadd (%1+6), %2
        mulpadd (%1+7), %2

%if ((%1 + %2) % 8 == 0)
        adcx    r8, zero
%elif ((%1 + %2) % 8 == 1)
        adcx    r9, zero
%elif ((%1 + %2) % 8 == 2)
        adcx    r10, zero
%elif ((%1 + %2) % 8 == 3)
        adcx    r11, zero
%elif ((%1 + %2) % 8 == 4)
        adcx    r12, zero
%elif ((%1 + %2) % 8 == 5)
        adcx    r13, zero
%elif ((%1 + %2) % 8 == 6)
        adcx    r14, zero
%elif ((%1 + %2) % 8 == 7)
        adcx    r15, zero
%endif


%endm

; ------------------------------------------------------------------------
; Compute off-diagonal part of x[0..7]^2, write back 1..7 elements and
; set up the high part in the standard register window. DOES NOT WRITE z[0]!
; ------------------------------------------------------------------------

%macro sqrz 0

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
        mulpadd 6, 3
        mulpadd 7, 3
        mov     rdx, [x+8*7]
        mulpadd 4, 7
        mulpadd 5, 7
        mulpadd 6, 7
        adcx    r14, zero
        mov     r15, zero
%endm

; ------------------------------------------------------------------------
; Multiply-add: z := x[0...7] * x off-diagonal elements
; ------------------------------------------------------------------------

%macro mulrows 0
        sqrz

        %assign i 8
%rep 8
        mulrow 0, i
        %assign i (i+1)
%endrep

        mov     [z+8*16], r8
        mov     [z+8*17], r9
        mov     [z+8*18], r10
        mov     [z+8*19], r11
        mov     [z+8*20], r12
        mov     [z+8*21], r13
        mov     [z+8*22], r14
        mov     [z+8*23], r15
%endm

; ------------------------------------------------------------------------
; The actual code
; ------------------------------------------------------------------------

                global  bignum_ksqr_16_32

                section .text

bignum_ksqr_16_32:

; Save more registers to play with

        push    rbp
        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15

; Now just systematically add in the rows to get all off-diagonal elements

        mulrows
        addrows 8

; Double and add the diagonal elements. Note that z[0] was never written above

        xor     rax, rax
        mov     rdx, [x+8*0]
        mulx    rbx, rax, rdx
        mov     [z+8*0], rax

        mov     rdx, [z+8*1]
        adcx    rdx, rdx
        adox    rdx, rbx
        mov     [z+8*1], rdx

        %assign i 1
%rep 15
        mov     rdx, [x+8*i]
        mulx    rbx, rax, rdx

        mov     rdx, [z+8*(2*i)]
        adcx    rdx, rdx
        adox    rdx, rax
        mov     [z+8*(2*i)], rdx

        mov     rdx, [z+8*(2*i+1)]
        adcx    rdx, rdx
        adox    rdx, rbx
        mov     [z+8*(2*i+1)], rdx
        %assign i (i+1)

%endrep

; Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx
        pop     rbp

        ret
