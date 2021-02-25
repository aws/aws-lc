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
; Halve modulo p_256, z := (x / 2) mod p_256, assuming x reduced
; Input x[4]; output z[4]
;
;    extern void bignum_half_p256
;     (uint64_t z[static 4], uint64_t x[static 4]);
;
; Standard x86-64 ABI: RDI = z, RSI = x
; ----------------------------------------------------------------------------

%define z rdi
%define x rsi

%define a rax
%define d0 rcx
%define d1 rdx
%define d2 r8
%define d3 r9

        global bignum_half_p256
        section .text

bignum_half_p256:

; Load lowest digit and get a mask for its lowest bit in d0

                mov     a, [x]
                mov     d0, 1
                and     d0, a
                neg     d0

; Create a masked version of p_256

                mov     d1, 0x00000000ffffffff
                xor     d3, d3
                and     d1, d0
                sub     d3, d1
                xor     d2, d2

; Perform addition with masked p_256. Catch the carry in a, as a bitmask
; for convenience though we only use its LSB below with SHRD

                add     d0, a
                adc     d1, [x+8]
                adc     d2, [x+16]
                adc     d3, [x+24]
                sbb     a, a

; Shift right, pushing the carry back down, and store back

                shrd    d0, d1, 1
                mov     [z], d0
                shrd    d1, d2, 1
                mov     [z+8], d1
                shrd    d2, d3, 1
                mov     [z+16], d2
                shrd    d3, a, 1
                mov     [z+24], d3

; Return

                ret
