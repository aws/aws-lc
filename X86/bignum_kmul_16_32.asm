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
; Multiply z := x * y
; Inputs x[16], y[16]; output z[32]; temporary buffer t[>=32]
;
;    extern void bignum_kmul_16_32
;     (uint64_t z[static 32], uint64_t x[static 16], uint64_t y[static 16],
;      uint64_t t[static 32])
;
; In this x86 code the final temporary space argument t is unused, but
; it is retained in the prototype above for API consistency with ARM.
;
; Standard x86-64 ABI: RDI = z, RSI = x, RDX = y, RCX = t
; ----------------------------------------------------------------------------

; These parameters are kept where they come in

%define z rdi
%define x rsi

; This one gets moved to free up rdx for muls

%define y rcx

; Often used for zero

%define zero rbp

; Inner loop count

; mulpadd i, j adds x[i] * rdx (now assumed = y[j]) into the window at i+j

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



; addrow i adds z[i] + x[0..7] * y[i] into the window

%macro addrow 1
        mov     rdx, [y+8*%1]
        xor     zero, zero

%if (%1 % 8 == 0)
        adox    r8, [z+8*%1]
%elif (%1 % 8 == 1)
        adox    r9, [z+8*%1]
%elif (%1 % 8 == 2)
        adox    r10, [z+8*%1]
%elif (%1 % 8 == 3)
        adox    r11, [z+8*%1]
%elif (%1 % 8 == 4)
        adox    r12, [z+8*%1]
%elif (%1 % 8 == 5)
        adox    r13, [z+8*%1]
%elif (%1 % 8 == 6)
        adox    r14, [z+8*%1]
%elif (%1 % 8 == 7)
        adox    r15, [z+8*%1]
%endif

        mulpadd 0, %1

%if (%1 % 8 == 0)
        mov     [z+8*%1], r8
        mov     r8, zero
%elif (%1 % 8 == 1)
        mov     [z+8*%1], r9
        mov     r9, zero
%elif (%1 % 8 == 2)
        mov     [z+8*%1], r10
        mov     r10, zero
%elif (%1 % 8 == 3)
        mov     [z+8*%1], r11
        mov     r11, zero
%elif (%1 % 8 == 4)
        mov     [z+8*%1], r12
        mov     r12, zero
%elif (%1 % 8 == 5)
        mov     [z+8*%1], r13
        mov     r13, zero
%elif (%1 % 8 == 6)
        mov     [z+8*%1], r14
        mov     r14, zero
%elif (%1 % 8 == 7)
        mov     [z+8*%1], r15
        mov     r15, zero
%endif

        mulpadd 1, %1
        mulpadd 2, %1
        mulpadd 3, %1
        mulpadd 4, %1
        mulpadd 5, %1
        mulpadd 6, %1
        mulpadd 7, %1

%if (%1 % 8 == 0)
        adc     r8, zero
%elif (%1 % 8 == 1)
        adc     r9, zero
%elif (%1 % 8 == 2)
        adc     r10, zero
%elif (%1 % 8 == 3)
        adc     r11, zero
%elif (%1 % 8 == 4)
        adc     r12, zero
%elif (%1 % 8 == 5)
        adc     r13, zero
%elif (%1 % 8 == 6)
        adc     r14, zero
%elif (%1 % 8 == 7)
        adc     r15, zero
%endif

%endm

; Special zero version of addrow, setting up the window from scratch

%macro addrowz 0
        mov     rdx, [y]
        xor     zero, zero

        mulx    r9, rax, [x]
        adc     [z], rax

        mulx    r10, rax, [x+8*1]
        adc     r9, rax

        mulx    r11, rax, [x+8*2]
        adc     r10, rax

        mulx    r12, rax, [x+8*3]
        adc     r11, rax

        mulx    r13, rax, [x+8*4]
        adc     r12, rax

        mulx    r14, rax, [x+8*5]
        adc     r13, rax

        mulx    r15, rax, [x+8*6]
        adc     r14, rax

        mulx    r8, rax, [x+8*7]
        adc     r15, rax

        adc     r8, zero
%endm

; This is a variant where we add the initial z[0..7] at the outset.
; This makes the initialization process a bit less wasteful. By doing
; a block of 8 we get the same effect except that we add z[0..7]
;
; adurow i adds 2^{7*64} * z[i+7] + x[0..7] * y[i] into the window

%macro adurow 1
        mov     rdx, [y+8*%1]
        xor     zero, zero

        mulpadd 0, %1

%if (%1 % 8 == 0)
        mov     [z+8*%1],r8
%elif (%1 % 8 == 1)
        mov     [z+8*%1],r9
%elif (%1 % 8 == 2)
        mov     [z+8*%1],r10
%elif (%1 % 8 == 3)
        mov     [z+8*%1],r11
%elif (%1 % 8 == 4)
        mov     [z+8*%1],r12
%elif (%1 % 8 == 5)
        mov     [z+8*%1],r13
%elif (%1 % 8 == 6)
        mov     [z+8*%1],r14
%elif (%1 % 8 == 7)
        mov     [z+8*%1],r15
%endif

        mulpadd 1, %1
        mulpadd 2, %1
        mulpadd 3, %1
        mulpadd 4, %1
        mulpadd 5, %1
        mulpadd 6, %1

%if (%1 % 8 == 0)
        mulx    r8, rax, [x+8*7]
        adcx    r15, rax
        adox    r8, zero
        adcx    r8, zero
%elif (%1 % 8 == 1)
        mulx    r9, rax, [x+8*7]
        adcx    r8, rax
        adox    r9, zero
        adcx    r9, zero
%elif (%1 % 8 == 2)
        mulx    r10, rax, [x+8*7]
        adcx    r9, rax
        adox    r10, zero
        adcx    r10, zero
%elif (%1 % 8 == 3)
        mulx    r11, rax, [x+8*7]
        adcx    r10, rax
        adox    r11, zero
        adcx    r11, zero
%elif (%1 % 8 == 4)
        mulx    r12, rax, [x+8*7]
        adcx    r11, rax
        adox    r12, zero
        adcx    r12, zero
%elif (%1 % 8 == 5)
        mulx    r13, rax, [x+8*7]
        adcx    r12, rax
        adox    r13, zero
        adcx    r13, zero
%elif (%1 % 8 == 6)
        mulx    r14, rax, [x+8*7]
        adcx    r13, rax
        adox    r14, zero
        adcx    r14, zero
%elif (%1 % 8 == 7)
        mulx    r15, rax, [x+8*7]
        adcx    r14, rax
        adox    r15, zero
        adcx    r15, zero
%endif

%endm

; Special "adurow 0" case to do first stage

%macro adurowz 0
        mov     rdx, [y]
        xor     zero, zero

        mov     r8, [z]
        mov     r9, [z+8*1]

        mulpadd 0, 0
        mov     [z],r8

        mov     r10, [z+8*2]
        mulpadd 1, 0
        mov     r11, [z+8*3]
        mulpadd 2, 0
        mov     r12, [z+8*4]
        mulpadd 3, 0
        mov     r13, [z+8*5]
        mulpadd 4, 0
        mov     r14, [z+8*6]
        mulpadd 5, 0
        mov     r15, [z+8*7]
        mulpadd 6, 0

        mulx    r8, rax, [x+8*7]
        adcx    r15, rax
        mov     rax, 0
        adox    r8, rax
        adcx    r8, rax
%endm

; Multiply-add: z := z + x[0..7] * y

%macro addrows 0
        adurowz
        adurow  1
        adurow  2
        adurow  3
        adurow  4
        adurow  5
        adurow  6
        adurow  7
        addrow  8
        addrow  9
        addrow  10
        addrow  11
        addrow  12
        addrow  13
        addrow  14
        addrow  15

        mov     [z+8*16], r8
        mov     [z+8*17], r9
        mov     [z+8*18], r10
        mov     [z+8*19], r11
        mov     [z+8*20], r12
        mov     [z+8*21], r13
        mov     [z+8*22], r14
        mov     [z+8*23], r15

%endm

; mulrow i adds x[0..7] * y[i] into the window
; just like addrow but no addition of z[i]

%macro mulrow 1
        mov     rdx, [y+8*%1]
        xor     zero, zero

        mulpadd 0, %1

%if (%1 % 8 == 0)
        mov     [z+8*%1], r8
        mov     r8, zero
%elif (%1 % 8 == 1)
        mov     [z+8*%1], r9
        mov     r9, zero
%elif (%1 % 8 == 2)
        mov     [z+8*%1], r10
        mov     r10, zero
%elif (%1 % 8 == 3)
        mov     [z+8*%1], r11
        mov     r11, zero
%elif (%1 % 8 == 4)
        mov     [z+8*%1], r12
        mov     r12, zero
%elif (%1 % 8 == 5)
        mov     [z+8*%1], r13
        mov     r13, zero
%elif (%1 % 8 == 6)
        mov     [z+8*%1], r14
        mov     r14, zero
%elif (%1 % 8 == 7)
        mov     [z+8*%1], r15
        mov     r15, zero
%endif

        mulpadd 1, %1
        mulpadd 2, %1
        mulpadd 3, %1
        mulpadd 4, %1
        mulpadd 5, %1
        mulpadd 6, %1
        mulpadd 7, %1

%if (%1 % 8 == 0)
        adc     r8, zero
%elif (%1 % 8 == 1)
        adc     r9, zero
%elif (%1 % 8 == 2)
        adc     r10, zero
%elif (%1 % 8 == 3)
        adc     r11, zero
%elif (%1 % 8 == 4)
        adc     r12, zero
%elif (%1 % 8 == 5)
        adc     r13, zero
%elif (%1 % 8 == 6)
        adc     r14, zero
%elif (%1 % 8 == 7)
        adc     r15, zero
%endif


%endm

; Special zero version of mulrow, setting up the window from scratch

%macro mulrowz 0
        mov     rdx, [y]
        xor     zero, zero

        mulx    r9, rax, [x]
        mov     [z], rax

        mulx    r10, rax, [x+8*1]
        adcx     r9, rax

        mulx    r11, rax, [x+8*2]
        adcx    r10, rax

        mulx    r12, rax, [x+8*3]
        adcx    r11, rax

        mulx    r13, rax, [x+8*4]
        adcx    r12, rax

        mulx    r14, rax, [x+8*5]
        adcx    r13, rax

        mulx    r15, rax, [x+8*6]
        adcx    r14, rax

        mulx    r8, rax, [x+8*7]
        adcx    r15, rax

        adc     r8, zero
%endm

; Multiply-add: z := x[0..7] * y plus window

%macro mulrows 0
        mulrowz
        mulrow  1
        mulrow  2
        mulrow  3
        mulrow  4
        mulrow  5
        mulrow  6
        mulrow  7
        mulrow  8
        mulrow  9
        mulrow  10
        mulrow  11
        mulrow  12
        mulrow  13
        mulrow  14
        mulrow  15
        mov     [z+8*16], r8
        mov     [z+8*17], r9
        mov     [z+8*18], r10
        mov     [z+8*19], r11
        mov     [z+8*20], r12
        mov     [z+8*21], r13
        mov     [z+8*22], r14
        mov     [z+8*23], r15
%endm

                global  bignum_kmul_16_32
                section .text

bignum_kmul_16_32:

; Save more registers to play with

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

; Move y into its permanent home, freeing up rdx for its special role in muls

        mov     y, rdx

; Do the zeroth row as a pure product then the next as multiply-add

        mulrows
        add     z, 64
        add     x, 64
        addrows

; Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

        ret
