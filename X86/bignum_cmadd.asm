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
; Multiply-add with single-word multiplier, z := z + c * y
; Inputs c, y[n]; outputs function return (carry-out) and z[k]
;
;    extern uint64_t bignum_cmadd
;     (uint64_t k, uint64_t *z, uint64_t c, uint64_t n, uint64_t *y);
;
; Does the "z := z + c * y" operation where y is n digits, result z is p.
; Truncates the result in general.
;
; The return value is a high/carry word that is meaningful when p = n + 1, or
; more generally when n <= p and the result fits in p + 1 digits. In these
; cases it gives the top digit of the (p + 1)-digit result.
;
; Standard x86-64 ABI: RDI = k, RSI = z, RDX = c, RCX = n, R8 = y, returns RAX
; ----------------------------------------------------------------------------

%define p rdi
%define z rsi
%define c r9
%define n rcx
%define x r8

%define i r10
%define h r11

%define r rbx

                global  bignum_cmadd
                section .text

bignum_cmadd:

; Seems hard to avoid one more register

                push    rbx

; First clamp the input size n := min(p,n) since we can never need to read
; past the p'th term of the input to generate p-digit output.
; Subtract p := p - min(n,p) so it holds the size of the extra tail needed

                cmp     p, n
                cmovc   n, p
                sub     p, n

; Initialize high part h = 0; if n = 0 do nothing but return that zero

                xor     h, h
                test    n, n
                jz      end

; Move c into a safer register as multiplies overwrite rdx

                mov     c, rdx

; Initialization of the loop: 2^64 * CF + [h,z_0'] = z_0 + c * x_0

                mov     rax, [x]
                mul     c
                add     [z], rax
                mov     h, rdx
                mov     i, 1
                dec     n
                jz      hightail

; Main loop, where we always have CF + previous high part h to add in

loop:
                adc     h, [z+8*i]
                sbb     r, r
                mov     rax, [x+8*i]
                mul     c
                sub     rdx, r
                add     rax, h
                mov     [z+8*i], rax
                mov     h, rdx
                inc     i
                dec     n
                jnz     loop

hightail:
                adc     h, 0

; Propagate the carry all the way to the end with h as extra carry word

tail:
                test    p, p
                jz      end

                add     [z+8*i], h
                mov     h, 0
                inc     i
                dec     p
                jz      highend

tloop:
                adc     [z+8*i], h
                inc     i
                dec     p
                jnz     tloop

highend:

                adc     h, 0

; Return the high/carry word

end:
                mov     rax, h

                pop     rbx
                ret
