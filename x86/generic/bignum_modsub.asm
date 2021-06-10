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
; Subtract modulo m, z := (x - y) mod m, assuming x and y reduced
; Inputs x[k], y[k], m[k]; output z[k]
;
;    extern void bignum_modsub
;     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);
;
; Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = y, R8 = m
; ----------------------------------------------------------------------------

                global  bignum_modsub
                section .text


%define k rdi
%define z rsi
%define x rdx
%define y rcx
%define m r8
%define i r9
%define j r10
%define a rax
%define c r11

bignum_modsub:

; If k = 0 do nothing

                test    k, k
                jz      end

; Subtract z := x - y and record a mask for the carry x - y < 0

                xor     c, c
                mov     j, k
                xor     i, i
subloop:
                mov     a, [x+8*i]
                sbb     a, [y+8*i]
                mov     [z+8*i], a
                inc     i
                dec     j
                jnz     subloop
                sbb     c, c

; Now do a masked addition z := z + [c] * m

                xor     i, i
addloop:
                mov     a, [m+8*i]
                and     a, c
                neg     j
                adc     [z+8*i], a
                sbb     j, j
                inc     i
                cmp     i, k
                jc      addloop

end:
                ret
