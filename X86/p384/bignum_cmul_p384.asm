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
; Multiply by a single word modulo p_384, z := (c * x) mod p_384, assuming
; x reduced
; Inputs c, x[6]; output z[6]
;
;    extern void bignum_cmul_p384
;     (uint64_t z[static 6], uint64_t c, uint64_t x[static 6]);
;
; Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
; ----------------------------------------------------------------------------

%define z rdi

%define x rcx   ; Temporarily moved here for initial multiply
%define m rdx   ; Likewise this is thrown away after initial multiply

%define a rax
%define c rcx

%define d0 rsi
%define d1 r8
%define d2 r9
%define d3 r10
%define d4 r11
%define d5 r12

%define q rdx   ; Multiplier again for second stage

        section .text
        global  bignum_cmul_p384

bignum_cmul_p384:

; We seem to need (just!) one extra register, which we need to save and restore

                push    r12

; Shuffle inputs (since we want multiplier in rdx)

                mov     x, rdx
                mov     m, rsi

; Multiply, accumulating the result as 2^384 * h + [d5;d4;d3;d2;d1;d0]
; but actually immediately producing q = h + 1, our quotient approximation,
; by adding 1 to it. Note that by hypothesis x is reduced mod p_384, so our
; product is <= (2^64 - 1) * (p_384 - 1) and hence  h <= 2^64 - 2, meaning
; there is no danger this addition of 1 could wrap.

                mulx    d1, d0, [x]
                mulx    d2, a, [x+8]
                add     d1, a
                mulx    d3,a, [x+16]
                adc     d2, a
                mulx    d4,a, [x+24]
                adc     d3, a
                mulx    d5,a, [x+32]
                adc     d4, a
                mulx    q,a, [x+40]
                adc     d5, a
                adc     q, 1

; It's easy to see -p_384 <= z - q * p_384 < p_384, so we just need to
; subtract q * p_384 and then correct if that is negative by adding p_384.
;
; Write p_384 = 2^384 - r where r = 2^128 + 2^96 - 2^32 + 1
;
; We want z - q * (2^384 - r)
;       = (2^384 * h + l) - q * (2^384 - r)
;       = 2^384 * (h - q) + (l + q * r)
;       = 2^384 * (-1) + (l + q * r)

                xor     c, c
                mov     a, 0xffffffff00000001
                mulx    c, a, a
                adcx    d0, a
                adox    d1, c
                mov     a, 0x00000000ffffffff
                mulx    c, a, a
                adcx    d1, a
                adox    d2, c
                adcx    d2, q
                mov     a, 0
                mov     c, 0
                adox    a, a
                adc     d3, a
                adc     d4, c
                adc     d5, c
                adc     c, c
                sub     c, 1

; The net c value is now the top word of the 7-word answer, hence will
; be -1 if we need a corrective addition, 0 otherwise, usable as a mask.
; Now use that mask for a masked addition of p_384, which again is in
; fact done by a masked subtraction of 2^384 - p_384, so that we only
; have three nonzero digits and so can avoid using another register.

                mov     q, 0x00000000ffffffff
                xor     a, a
                and     q, c
                sub     a, q
                and     c, 1

                sub     d0, a
                mov     [z], d0
                sbb     d1, q
                mov     [z+8], d1
                sbb     d2, c
                mov     [z+16], d2
                sbb     d3, 0
                mov     [z+24], d3
                sbb     d4, 0
                mov     [z+32], d4
                sbb     d5, 0
                mov     [z+40], d5

; Return

                pop     r12
                ret
