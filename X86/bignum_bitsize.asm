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
; Return size of bignum in bits
; Input x[k]; output function return
;
;    extern uint64_t bignum_bitsize (uint64_t k, uint64_t *x);
;
; In the case of a zero bignum as input the result is 0
;
; In principle this has a precondition k < 2^58, but obviously that
; is always true in practice because of address space limitations.
;
; Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
; ----------------------------------------------------------------------------

%define k rdi
%define x rsi
%define i rax
%define w rdx
%define a rcx
%define j r8

                global  bignum_bitsize
                section .text

bignum_bitsize:

; Initialize the index i and also prepare default return value of 0 (i = rax)

                xor     i, i

; If the bignum is zero-length, just return 0

                test    k, k
                jz      end

; Use w = a[i-1] to store nonzero words in a bottom-up sweep
; Set the initial default to be as if we had a 11...11 word directly below

                mov     w, -1
                xor     j, j
loop:
                mov     a, [x+8*j]
                inc     j
                test    a, a
                cmovnz  i, j
                cmovnz  w, a
                cmp     j, k
                jnz     loop

; Now w = a[i-1] is the highest nonzero word, or in the zero case the
; default of the "extra" 11...11 = a[0-1]. We now want 64* i - clz(w) =
; 64 * i - (63 - bsr(w)) = (64 * i - 63) + bsr(w). Note that this code
; does not rely on the behavior of the bsr instruction for zero inputs,
; which is undefined.

                shl     i, 6
                sub     i, 63
                bsr     w, w
                add     rax, w

end:
                ret
