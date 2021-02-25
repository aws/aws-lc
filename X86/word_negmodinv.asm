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
; Single-word negated modular inverse (-1/a) mod 2^64
; Input a; output function return
;
;    extern uint64_t word_negmodinv (uint64_t a);
;
; A 64-bit function that returns a negated multiplicative inverse mod 2^64
; of its input, assuming that input is odd. Given odd input a, the result z
; will satisfy a * z + 1 == 0 (mod 2^64), i.e. a 64-bit word multiplication
; a * z will give -1.
;
; Standard x86-64 ABI: RDI = a, returns RAX
; ----------------------------------------------------------------------------

        global  word_negmodinv
        section .text

word_negmodinv:

; Initial magical 5-bit approximation x = (a - a<<2) xor 2

                mov     rcx, rdi
                mov     rax, rdi
                shl     rcx, 2
                sub     rax, rcx
                xor     rax, 2

; Now refine to 64-bit congruence

                mov     rcx, rax    ; rcx = x
                imul    rcx, rdi    ; rcx = a * x
                mov     rdx, 2
                add     rdx, rcx    ; rdx = 1 + e = 2 + a * x
                add     rcx, 1      ; rcx = e = a * x + 1

                imul    rax, rdx    ; rax = x * (1 + e)

                imul    rcx, rcx    ; rcx = e^2
                mov     rdx, 1
                add     rdx, rcx
                imul    rax, rdx    ; rax = x * (1 + e) * (1 + e^2)

                imul    rcx, rcx    ; rcx = e^4
                mov     rdx, 1
                add     rdx, rcx
                imul    rax, rdx    ; rax = x * (1 + e) * (1 + e^2) * (1 + e^4)

                imul    rcx, rcx    ; rcx = e^8
                mov     rdx, 1
                add     rdx, rcx
                imul    rax, rdx    ; rax = x * (1 + e) * ... * * (1 + e^8)

                ret
