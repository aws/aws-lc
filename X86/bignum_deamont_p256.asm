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
; Convert from almost-Montgomery form, z := (x / 2^256) mod p_256
; Input x[4]; output z[4]
;
;    extern void bignum_deamont_p256
;     (uint64_t z[static 4], uint64_t x[static 4]);
;
; Convert a 4-digit bignum x out of its (optionally almost) Montgomery form,
; "almost" meaning any 4-digit input will work, with no range restriction.
;
; Standard x86-64 ABI: RDI = z, RSI = x
; ----------------------------------------------------------------------------

%define z rdi
%define x rsi

; Re-use these as temporaries in the correction phase

%define d rdx
%define u r10
%define v r11

; Macro "mulpadd i x" adds rdx * x to the (i,i+1) position of
; the rotating register window rsi,rbx,r11,r10,r9,r8 maintaining consistent
; double-carrying using ADCX and ADOX and using rcx/rax as temps

%macro mulpadd 2
        mulx    rcx, rax, %2
%if (%1 % 6 == 0)
        adcx    r8, rax
        adox    r9, rcx
%elif (%1 % 6 == 1)
        adcx    r9, rax
        adox    r10, rcx
%elif (%1 % 6 == 2)
        adcx    r10, rax
        adox    r11, rcx
%elif (%1 % 6 == 3)
        adcx    r11, rax
        adox    rbx, rcx
%elif (%1 % 6 == 4)
        adcx    rbx, rax
        adox    rsi, rcx
%elif (%1 % 6 == 5)
        adcx    rsi, rax
        adox    r8, rcx
%endif

%endm

                global  bignum_deamont_p256
                section .text

bignum_deamont_p256:

; Save one more register to play with

        push    rbx

; Set up an initial 4-word window [r11,r10,r9,r8] = x

        mov     r8, [x+8*0]
        mov     r9, [x+8*1]
        mov     r10, [x+8*2]
        mov     r11, [x+8*3]

; Fill in two zeros to the left

        xor     rbx, rbx
        xor     rsi, rsi

; Montgomery reduce windows 0 and 1 together

        mov     rdx, 0x0000000100000000
        mulpadd 1, r8
        mulpadd 2, r9
        mov     rdx, 0xffffffff00000001
        mulpadd 3, r8
        mulpadd 4, r9
        mov     r8, 0
        adcx    rsi, r8

; Append just one more leading zero (by the above r8 = 0 already).

        xor     r9, r9

; Montgomery reduce windows 2 and 3 together

        mov     rdx, 0x0000000100000000
        mulpadd 3, r10
        mulpadd 4, r11
        mov     rdx, 0xffffffff00000001
        mulpadd 5, r10
        mulpadd 6, r11
        mov     r10, 0
        adcx    r9, r10

; We now have a pre-reduced dd = [r9;r8;rsi;rbx]. Load non-trivial digits
; of p_256 = [v; 0; u; -1]

        mov     u, 0x00000000ffffffff
        mov     v, 0xffffffff00000001

; Now do the subtraction (p_256-1) - (r9;r8;rsi;rbx) to get the carry

        mov     d, -2
        sub     d, rbx
        mov     d, u
        sbb     d, rsi
        mov     d, 0
        sbb     d, r8
        mov     d, v
        sbb     d, r9

; Convert the carry CF <=> dd >= p_256 to a bitmask and do a masked subtraction

        sbb     d, d
        and     u, d
        and     v, d

        sub     rbx, d
        sbb     rsi, u
        sbb     r8, 0
        sbb     r9, v

; Write back

        mov     [z+8*0], rbx
        mov     [z+8*1], rsi
        mov     [z+8*2], r8
        mov     [z+8*3], r9

; Restore saved register and return

        pop     rbx

        ret
