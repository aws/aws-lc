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
; Montgomery square, z := (x^2 / 2^384) mod p_384
; Input x[6]; output z[6]
;
;    extern void bignum_montsqr_p384
;     (uint64_t z[static 6], uint64_t x[static 6]);
;
; Does z := (x^2 / 2^384) mod p_384, assuming x^2 <= 2^384 * p_384, which is
; guaranteed in particular if x < p_384 initially (the "intended" case).
;
; Standard x86-64 ABI: RDI = z, RSI = x
; ----------------------------------------------------------------------------

%define z rdi
%define x rsi

; Some temp registers for the last correction stage

%define d rax
%define u rdx
%define v r10
%define w r11

; A zero register, very often

%define zero rbp

; Macro "mulpadd i x" adds rdx * x to the (i,i+1) position of the
; rotating register window r15,...,r8 maintaining consistent
; double-carrying using ADCX and ADOX and using rbx/rax as temps

%macro mulpadd 2
        mulx    rbx, rax, %2
%if (%1 % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
%elif (%1 % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
%elif (%1 % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
%elif (%1 % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
%elif (%1 % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
%elif (%1 % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
%elif (%1 % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
%elif (%1 % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
%endif

%endm

; Core one-step "short" Montgomery reduction macro. Takes input in
; [d5;d4;d3;d2;d1;d0] and returns result in [d6;d5;d4;d3;d2;d1],
; adding to the existing [d5;d4;d3;d2;d1] and re-using d0 as a
; temporary internally, as well as rdx, rax and the temporary t.
; It is OK for d6 and d0 to be the same register (they often are)
;
; We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
; where w = [d0 + (d0<<32)] mod 2^64
;
;       montreds d6,d5,d4,d3,d2,d1,d0, t

%macro montreds 8
; Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64
                mov     rdx, %7
                shl     rdx, 32
                add     rdx, %7
; Construct [%8;%7;rax;-] = (2^384 - p_384) * w
; We know the lowest word will cancel so we can re-use %7 as a temp, and %8
                mov     rax, 0xffffffff00000001
                mulx    rax, %7, rax
                mov     %8, 0x00000000ffffffff
                mulx    %7, %8, %8
                add     rax, %8
                adc     %7, rdx
                mov     %8, 0
                adc     %8, %8
; Now subtract that and add 2^384 * w
                sub     %6, rax
                sbb     %5, %7
                sbb     %4, %8
                sbb     %3, 0
                sbb     %2, 0
                mov     %1, rdx
                sbb     %1, 0
%endm

                global  bignum_montsqr_p384

bignum_montsqr_p384:

; Save more registers to play with

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

; Set up an initial window [rcx;r15;...r9] = [34;05;03;01]
; Note that we are using rcx as the first step past the rotating window

        mov     rdx, [x]
        mulx    r10, r9, [x+8*1]
        mulx    r12, r11, [x+8*3]
        mulx    r14, r13, [x+8*5]
        mov     rdx, [x+8*3]
        mulx    rcx, r15, [x+8*4]

; Clear our zero register, and also initialize the flags for the carry chain

        xor     zero, zero

; Chain in the addition of 02 + 12 + 13 + 14 + 15 to that window
; (no carry-out possible)

        mov     rdx, [x+8*2]
        mulpadd 2,[x]
        mulpadd 3, [x+8*1]
        mov     rdx, [x+8*1]
        mulpadd 4, [x+8*3]
        mulpadd 5, [x+8*4]
        mulpadd 6, [x+8*5]
        adcx    r15, zero
        adox    rcx, zero
        adcx    rcx, zero

; Again zero out the flags. Actually they are already cleared but it may
; help decouple these in the OOO engine not to wait for the chain above

        xor     zero, zero

; Now chain in the 04 + 23 + 24 + 25 + 35 + 45 terms
; We are running out of registers in our rotating window, so we start
; using rbx (and hence need care with using mulpadd after this). Thus
; our result so far is in [rbp;rbx;rcx;r15;...r9]

        mov     rdx, [x+8*4]
        mulpadd 4, [x]
        mov     rdx, [x+8*2]
        mulpadd 5, [x+8*3]
        mulpadd 6, [x+8*4]
        mulx    rdx, rax, [x+8*5]
        adcx    r15, rax
        adox    rcx, rdx

; First set up the last couple of spots in our window, [rbp;rbx] = 45
; then add the last other term 35

        mov     rdx, [x+8*5]
        mulx    rbp, rbx, [x+8*4]
        mulx    rdx, rax, [x+8*3]
        adcx    rcx, rax
        adox    rbx, rdx
        mov     rax, 0
        adcx    rbx, rax
        adox    rbp, rax
        adcx    rbp, rax

; Just for a clear fresh start for the flags; we don't use the zero

        xor     rax, rax

; Double and add to the 00 + 11 + 22 + 33 + 44 + 55 terms
; For one glorious moment the entire squaring result is all in the
; register file as [rsi;rbp;rbx;rcx;r15;...;r8]
; (since we've now finished with x we can re-use rsi)

        mov     rdx, [x]
        mulx    rax, r8, [x]
        adcx    r9, r9
        adox    r9, rax
        mov     rdx, [x+8*1]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [x+8*2]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [x+8*3]
        mulx    rdx, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, r15
        adox    r15, rdx
        mov     rdx, [x+8*4]
        mulx    rdx, rax, rdx
        adcx    rcx, rcx
        adox    rcx, rax
        adcx    rbx, rbx
        adox    rbx, rdx
        mov     rdx, [x+8*5]
        mulx    rsi, rax, rdx
        adcx    rbp, rbp
        adox    rbp, rax
        mov     rax, 0
        adcx    rsi, rax
        adox    rsi, rax

; We need just *one* more register as a temp for the Montgomery steps.
; Since we are writing to the z buffer anyway, make use of that to shash rbx.

        mov     [z], rbx

; Montgomery reduce the r13,...,r8 window 6 times

        montreds r8,r13,r12,r11,r10,r9,r8, rbx
        montreds r9,r8,r13,r12,r11,r10,r9, rbx
        montreds r10,r9,r8,r13,r12,r11,r10, rbx
        montreds r11,r10,r9,r8,r13,r12,r11, rbx
        montreds r12,r11,r10,r9,r8,r13,r12, rbx
        montreds r13,r12,r11,r10,r9,r8,r13, rbx

; Now we can safely restore rbx before accumulating

        mov     rbx, [z]

        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rsi, r13
        mov     r8, 0
        adc     r8, 0

; We now have a pre-reduced 7-word form [r8;rsi;rbp;rbx;rcx;r15;r14]

; We know, writing B = 2^{6*64} that the full implicit result is
; B^2 c <= z + (B - 1) * p < B * p + (B - 1) * p < 2 * B * p,
; so the top half is certainly < 2 * p. If c = 1 already, we know
; subtracting p will give the reduced modulus. But now we do a
; comparison to catch cases where the residue is >= p.
; First set [0;0;0;w;v;u] = 2^384 - p_384

        mov     u, 0xffffffff00000001
        mov     v, 0x00000000ffffffff
        mov     w, 0x0000000000000001

; Let dd = [rsi;rbp;rbx;rcx;r15;r14] be the topless 6-word intermediate result.
; Set CF if the addition dd + (2^384 - p_384) >= 2^384, hence iff dd >= p_384.

        mov     d, r14
        add     d, u
        mov     d, r15
        adc     d, v
        mov     d, rcx
        adc     d, w
        mov     d, rbx
        adc     d, 0
        mov     d, rbp
        adc     d, 0
        mov     d, rsi
        adc     d, 0

; Now just add this new carry into the existing r8. It's easy to see they
; can't both be 1 by our range assumptions, so this gives us a {0,1} flag

        adc     r8, 0

; Now convert it into a bitmask

        neg     r8

; Masked addition of 2^384 - p_384, hence subtraction of p_384

        and     u, r8
        and     v, r8
        and     w, r8

        add    r14, u
        adc    r15, v
        adc    rcx, w
        adc    rbx, 0
        adc    rbp, 0
        adc    rsi, 0

; Write back the result

        mov     [z], r14
        mov     [z+8*1], r15
        mov     [z+8*2], rcx
        mov     [z+8*3], rbx
        mov     [z+8*4], rbp
        mov     [z+8*5], rsi

; Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        ret
