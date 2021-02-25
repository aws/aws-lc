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
; Negated modular inverse, z := (-1/x) mod 2^{64k}
; Input x[k]; output z[k]; temporary buffer t[>=k]
;
;    extern void bignum_negmodinv
;     (uint64_t k, uint64_t *z, uint64_t *t, uint64_t *x);
;
; The output is z with t (at least k words) used as a temporary buffer.
; Assuming x is odd (otherwise nothing makes sense) the result satisfies
;
;       x * z + 1 == 0 (mod 2^{64 * k})
;
; Standard x86-64 ABI: RDI = k, RSI = z, RDX = t, RCX = x
; ----------------------------------------------------------------------------

                global bignum_negmodinv
                extern wordnegmodinv
                extern bignum_mul
                extern bignum_mulc

                section .text

%define b       rbx
%define b2      rbp
%define k       r12
%define x       r13
%define y       r14
%define a       r15

bignum_negmodinv:
                push    rbx
                push    rbp
                push    r12
                push    r13
                push    r14
                push    r15

start:

; If length = 0 do nothing else (could even skip push/pops)

                cmp     rdi, 0
                jz      end

; So now we can assume k >= 1.
; Preserve the main parameters we need

                mov     k, rdi
                mov     x, rsi
                mov     y, rdx
                mov     a, rcx

; Initially set up a 1-word modular inverse in x as our starting-point

                mov     rdi, [a]
                call    wordnegmodinv
                mov     [x], rax

; If in fact we only have k = 1 then that's already the final answer

                mov     rax, k
                sub     rax, 1
                jz      end

; We can now assume k >= 2; set b = 1 to indicate 1-word accuracy

                mov     b, 1

; Now the start of the main loop; part of our loop invariant is that b < k

mainloop:

; Set b2 = min(2 * b,k)
; Note that we don't need to consider overflow in 2 * b
; Besides being a crazy number, we must then violate nonoverlapping
; since the numbers would be >= 2^63 words and so > 2^64 bytes long

                lea     b2, [2*b]
                cmp     k, b2
                cmovc   b2, k

; Set y = a * x + 1
; Actually because of the optimization below we could add
; any constant >= 1, since the high part would be the same.
; Could even use register b maybe, though it seems crazy
; We know it's nonzero and might possibly be more efficient(?!?)

                mov     QWORD [y], 1
                mov     rdi, b2
                mov     rsi, y
                mov     rdx, b2
                mov     rcx, a
                mov     r8, b
                mov     r9, x
                call    bignum_mulc

; Set x' = x * y + x = x * (y + 1) = x * (a * x + 2)
; There is a nice optimization here: the low b of x
; are already correct, by the inductive hypothesis.
; And the bottom b of y = a * x + 1 is zero too.
; Hence to get x + x * y we can do x * y_hi and store
; it in the high part of x. Remember that in general
; b2 - b < b, and we need to allow for sizes that
; are not exactly a power of 2, hence the b2 - b to
; get the size of the top "half".

                mov     rdi, b2
                sub     rdi, b
                lea     rsi, [x+8*b]
                mov     rdx, b
                mov     rcx, x
                mov     r8, rdi
                lea     r9, [y+8*b]
                call    bignum_mul

; Set b = b2 and loop if it's not the whole bignum

                mov     b, b2
                cmp     b, k
                jc      mainloop

end:
                pop     r15
                pop     r14
                pop     r13
                pop     r12
                pop     rbp
                pop     rbx

                ret
