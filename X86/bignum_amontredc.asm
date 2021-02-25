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
; Almost-Montgomery reduce, z :== (x' / 2^{64p}) (congruent mod m)
; Inputs x[n], m[k], p; output z[k]
;
;    extern void bignum_amontredc
;     (uint64_t k, uint64_t *z,
;      uint64_t n, uint64_t *x, uint64_t *m, uint64_t p);
;
; Does a :== (x' / 2^{64p}) mod m where x' = x if n <= p + k and in general
; is the lowest (p+k) digits of x. That is, p-fold almost-Montgomery reduction
; w.r.t. a k-digit modulus m giving a k-digit answer.
;
; Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = m, R9 = p
; ----------------------------------------------------------------------------

%define k rdi
%define z rsi
%define n r10            ; We copy x here but it comes in in rdx originally
%define x rcx
%define m r8
%define p r9

%define a rax           ; General temp, low part of product and mul input
%define b rdx           ; General temp, High part of product

%define w QWORD[rsp]    ; Negated modular inverse
%define j rbx           ; Inner loop counter
%define d rbp           ; Home for i'th digit or Montgomery multiplier
%define h r11
%define e r12
%define t r13
%define i r14
%define c r15

; Some more intuitive names for temp regs in initial word-level negmodinv.

%define t1 rbx
%define t2 r14

                global  bignum_amontredc
                section .text

bignum_amontredc:

; Save registers and allocate space on stack for non-register variable w

                push    rbx
                push    rbp
                push    r12
                push    r13
                push    r14
                push    r15
                sub     rsp, 8

; If k = 0 the whole operation is trivial

                test    k, k
                jz      end

; Move n input into its permanent home, since we need rdx for multiplications

                mov     n, rdx

; Compute word-level negated modular inverse w for m == m[0].

                mov     a, [m]

                mov     t2, a
                mov     t1, a
                shl     t2, 2
                sub     t1, t2
                xor     t1, 2

                mov     t2, t1
                imul    t2, a
                mov     a, 2
                add     a, t2
                add     t2, 1

                imul    t1, a

                imul    t2, t2
                mov     a, 1
                add     a, t2
                imul    t1, a

                imul    t2, t2
                mov     a, 1
                add     a, t2
                imul    t1, a

                imul    t2, t2
                mov     a, 1
                add     a, t2
                imul    t1, a

                mov     w, t1

; Initialize z to the lowest k digits of the input, zero-padding if n < k.

                mov     j, k
                cmp     n, k
                cmovc   j, n
                xor     i, i
                test    j, j
                jz      padloop
copyloop:
                mov     a, [x+8*i]
                mov     [z+8*i], a
                inc     i
                cmp     i, j
                jc      copyloop

                cmp     i, k
                jnc     initialized

                xor     j, j
padloop:
                mov     [z+8*i], j
                inc     i
                cmp     i, k
                jc      padloop

initialized:
                xor     c, c

; Now if p = 0 that's the end of the operation

                test    p, p
                jz      end

; Outer loop, just doing a standard Montgomery reduction on z

                xor     i, i
outerloop:
                mov     e, [z]
                mov     d, w
                imul    d, e
                mov     a, [m]
                mul     d
                add     a, e            ; Will be zero but want the carry
                mov     h, rdx
                mov     j, 1
                mov     t, k
                dec     t
                jz      montend

montloop:
                adc     h, [z+8*j]
                sbb     e, e
                mov     a, [m+8*j]
                mul     d
                sub     rdx, e
                add     a, h
                mov     [z+8*j-8], a
                mov     h, rdx
                inc     j
                dec     t
                jnz     montloop

montend:
                adc     h, c
                mov     c, 0
                adc     c, 0

                add     j, i
                cmp     j, n
                jnc     offtheend
                mov     a, [x+8*j]
                add     h, a
                adc     c, 0
offtheend:
                mov     [z+8*k-8], h

; End of outer loop.

                inc     i
                cmp     i, p
                jc      outerloop

; Now convert carry word, which is always in {0,1}, into a mask "d"
; and do a masked subtraction of m for the final almost-Montgomery result.

                xor     d, d
                sub     d, c
                xor     e, e
                xor     j, j
corrloop:
                mov     a, [m+8*j]
                and     a, d
                neg     e
                sbb     [z+8*j], a
                sbb     e, e
                inc     j
                cmp     j, k
                jc      corrloop

end:
                add     rsp, 8
                pop     r15
                pop     r14
                pop     r13
                pop     r12
                pop     rbp
                pop     rbx

                ret
