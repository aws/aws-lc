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
; Double modulo m, z := (2 * x) mod m, assuming x reduced
; Inputs x[k], m[k]; output z[k]
;
;    extern void bignum_moddouble
;      (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *m);
;
; Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = m
; ----------------------------------------------------------------------------

                global  bignum_moddouble
                section .text

%define k rdi
%define z rsi
%define x rdx
%define m rcx
%define i r8
%define a r9
%define c rax
%define b r10

bignum_moddouble:

; If k = 0 do nothing

                test    k, k
                jz      end

; Do (_::z) = 2 * x - m and generate a mask in c for 2 * x < m

                xor     c, c
                xor     i, i
                xor     b, b

dubloop:
                mov     a, [x+8*i]
                shrd    c, a, 63
                neg     b
                sbb     c, [m+8*i]
                sbb     b, b
                mov     [z+8*i],c
                mov     c, a
                inc     i
                cmp     i, k
                jc      dubloop
                shr     c, 63

                add     c, b

; Now do a corrective masked addition z := z + [c] * m

                xor     i, i
                xor     b, b
corrloop:
                mov     a, [m+8*i]
                and     a, c
                neg     b
                adc     a, [z+8*i]
                sbb     b, b
                mov     [z+8*i], a
                inc     i
                cmp     i, k
                jc      corrloop

end:
                ret
