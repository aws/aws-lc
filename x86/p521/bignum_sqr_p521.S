/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ----------------------------------------------------------------------------
// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_sqr_p521 (uint64_t z[static 9], uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_sqr_p521
        .text

#define z rdi
#define x rsi

// A zero register

#define zero rbp
#define zeroe ebp

// mulpadd (high,low,i) adds rdx * x[i] to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rcx as temporaries.

#define mulpadd(high,low,i)             \
        mulx    rcx, rax, [x+8*i];      \
        adcx    low, rax;               \
        adox    high, rcx

// mulpade (hight,low,i) adds rdx * x[i] to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax as a temporary, assuming high created from scratch
// and that zero has value zero.

#define mulpade(high,low,i)             \
        mulx    high, rax, [x+8*i];     \
        adcx    low, rax;               \
        adox    high, zero

bignum_sqr_p521:

// Save more registers to play with

        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

// Do a basic 8x8 squaring writing back z[0..7] but keeping the
// top half in the usual rotating register window r15,...,r8. Except
// for the lack of full writeback this is the same as bignum_sqr_8_16.

        xor     zeroe, zeroe

        mov     rdx, [x+8*0]
        mulx    rax, r9, [x+8*1]
        mov     [z+8*1], r9
        mulx    rcx, r10, [x+8*2]
        adcx    r10, rax
        mov     [z+8*2], r10
        mulx    rax, r11, [x+8*3]
        adcx    r11, rcx
        mulx    rcx, r12, [x+8*4]
        adcx    r12, rax
        mulx    rax, r13, [x+8*5]
        adcx    r13, rcx
        mulx    rcx, r14, [x+8*6]
        adcx    r14, rax
        mulx    r8, r15, [x+8*7]
        adcx    r15, rcx
        adcx    r8, zero

        xor     zeroe, zeroe
        mov     rdx, [x+8*1]
        mulpadd(r12,r11,2)
        mov     [z+8*3], r11
        mulpadd(r13,r12,3)
        mov     [z+8*4], r12
        mulpadd(r14,r13,4)
        mulpadd(r15,r14,5)
        mulpadd(r8,r15,6)
        mulpade(r9,r8,7)
        mov     rdx, [x+8*4]
        mulpade(r10,r9,5)
        adcx    r10, zero

        xor     zeroe, zeroe
        mov     rdx, [x+8*2]
        mulpadd(r14,r13,3)
        mov     [z+8*5], r13
        mulpadd(r15,r14,4)
        mov     [z+8*6], r14
        mulpadd(r8,r15,5)
        mulpadd(r9,r8,6)
        mulpadd(r10,r9,7)
        mov     rdx, [x+8*6]
        mulpade(r11,r10,4)
        mulpade(r12,r11,5)
        adcx    r12, zero

        xor     zeroe, zeroe
        mov     rdx, [x+8*3]
        mulpadd(r8,r15,4)
        mov     [z+8*7], r15
        mulpadd(r9,r8,5)
        mulpadd(r10,r9,6)
        mulpadd(r11,r10,7)
        mov     rdx, [x+8*7]
        mulpadd(r12,r11,4)
        mulpade(r13,r12,5)
        mulpade(r14,r13,6)
        adcx    r14, zero

        xor     zeroe, zeroe
        mov     rdx, [x+8*0]
        mulx    rcx, rax, rdx
        mov     [z+8*0], rax
        mov     rax, [z+8*1]
        adcx    rax, rax
        adox    rax, rcx
        mov     [z+8*1], rax

        mov     rax, [z+8*2]
        mov     rdx, [x+8*1]
        mulx    rcx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [z+8*2], rax
        mov     rax, [z+8*3]
        adcx    rax, rax
        adox    rax, rcx
        mov     [z+8*3], rax

        mov     rax, [z+8*4]
        mov     rdx, [x+8*2]
        mulx    rcx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [z+8*4], rax
        mov     rax, [z+8*5]
        adcx    rax, rax
        adox    rax, rcx
        mov     [z+8*5], rax

        mov     rax, [z+8*6]
        mov     rdx, [x+8*3]
        mulx    rcx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [z+8*6], rax
        mov     rax, [z+8*7]
        adcx    rax, rax
        adox    rax, rcx
        mov     [z+8*7], rax

        mov     rdx, [x+8*4]
        mulx    rcx, rdx, rdx
        adcx    r8, r8
        adox    r8, rdx
        adcx    r9, r9
        adox    r9, rcx

        mov     rdx, [x+8*5]
        mulx    rcx, rdx, rdx
        adcx    r10, r10
        adox    r10, rdx
        adcx    r11, r11
        adox    r11, rcx

        mov     rdx, [x+8*6]
        mulx    rcx, rdx, rdx
        adcx    r12, r12
        adox    r12, rdx
        adcx    r13, r13
        adox    r13, rcx

        mov     rdx, [x+8*7]
        mulx    r15, rdx, rdx
        adcx    r14, r14
        adox    r14, rdx
        adcx    r15, zero
        adox    r15, zero

// Augment the high part with the contribution from the top little word C.
// If we write the input as 2^512 * C + x then we are otherwise just doing
// x^2, so we need to add to the high part 2^512 * C^2 + (2 * C) * x.
// The initial doubling add of C also clears the CF and OF flags as desired.
// We extend the window now to the 9-element rbp,r15,r14,...,r8.

        mov     rdx, [x+8*8]
        mov     rbp, rdx
        imul    rbp, rbp
        add     rdx, rdx
        mulpadd(r9,r8,0)
        mulpadd(r10,r9,1)
        mulpadd(r11,r10,2)
        mulpadd(r12,r11,3)
        mulpadd(r13,r12,4)
        mulpadd(r14,r13,5)
        mulpadd(r15,r14,6)
        mulx   rcx, rax, [x+8*7]
        adcx   r15, rax
        adox   rbp, rcx
        adc    rbp, 0

// Rotate the upper portion right 9 bits since 2^512 == 2^-9 (mod p_521)
// Let rotated result rbp,r15,r14,...,r8 be h (high) and z[0..7] be l (low)

        mov     rax, r8
        and     rax, 0x1FF
        shrd    r8, r9, 9
        shrd    r9, r10, 9
        shrd    r10, r11, 9
        shrd    r11, r12, 9
        shrd    r12, r13, 9
        shrd    r13, r14, 9
        shrd    r14, r15, 9
        shrd    r15, rbp, 9
        shr     rbp, 9
        add     rbp, rax

// Force carry-in then add to get s = h + l + 1
// but actually add all 1s in the top 53 bits to get simple carry out

        stc
        adc     r8, [z+8*0]
        adc     r9, [z+8*1]
        adc     r10,[z+8*2]
        adc     r11,[z+8*3]
        adc     r12,[z+8*4]
        adc     r13,[z+8*5]
        adc     r14,[z+8*6]
        adc     r15,[z+8*7]
        adc     rbp, ~0x1FF

// Now CF is set <=> h + l + 1 >= 2^521 <=> h + l >= p_521,
// in which case the lower 521 bits are already right. Otherwise if
// CF is clear, we want to subtract 1. Hence suntract the complement
// of the carry flag then mask the top word, which scrubs the
// padding in either case. Write digits back as they are created.

        cmc
        sbb     r8, 0
        mov     [z], r8
        sbb     r9, 0
        mov     [z+8],  r9
        sbb     r10, 0
        mov     [z+16], r10
        sbb     r11, 0
        mov     [z+24], r11
        sbb     r12, 0
        mov     [z+32], r12
        sbb     r13, 0
        mov     [z+40], r13
        sbb     r14, 0
        mov     [z+48], r14
        sbb     r15, 0
        mov     [z+56], r15
        sbb     rbp, 0
        and     rbp, 0x1FF
        mov     [z+64], rbp

// Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
