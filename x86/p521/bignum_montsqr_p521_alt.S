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
// Montgomery square, z := (x^2 / 2^576) mod p_521
// Input x[9]; output z[9]
//
//    extern void bignum_montsqr_p521_alt
//     (uint64_t z[static 9], uint64_t x[static 9]);
//
// Does z := (x^2 / 2^576) mod p_521, assuming x < p_521. This means the
// Montgomery base is the "native size" 2^{9*64} = 2^576; since p_521 is
// a Mersenne prime the basic modular squaring bignum_sqr_p521 can be
// considered a Montgomery operation to base 2^521.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_montsqr_p521_alt
        .text

// Input arguments

#define z rdi
#define x rsi

// Macro for the key "multiply and add to (c,h,l)" step

#define combadd(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

// Set up initial window (c,h,l) = numa * numb

#define combaddz(c,h,l,numa,numb)               \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        xor     c, c;                           \
        mov     l, rax;                         \
        mov     h, rdx

// Doubling step (c,h,l) = 2 * (c,hh,ll) + (0,h,l)

#define doubladd(c,h,l,hh,ll)                   \
        add     ll, ll;                         \
        adc     hh, hh;                         \
        adc     c, c;                           \
        add     l, ll;                          \
        adc     h, hh;                          \
        adc     c, 0

// Square term incorporation (c,h,l) += numba^2

#define combadd1(c,h,l,numa)                    \
        mov     rax, numa;                      \
        mul     rax;                            \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

// A short form where we don't expect a top carry

#define combads(h,l,numa)                       \
        mov     rax, numa;                      \
        mul     rax;                            \
        add     l, rax;                         \
        adc     h, rdx

// A version doubling directly before adding, for single non-square terms

#define combadd2(c,h,l,numa,numb)               \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     c, 0;                           \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

bignum_montsqr_p521_alt:

// Make more registers available

        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15

// Start doing a conventional columnwise squaring,
// temporarily storing the lower 9 digits to the output buffer.
// Start with result term 0

        mov     rax, [x]
        mul     rax

        mov     [z], rax
        mov     r9, rdx
        xor     r10, r10

// Result term 1

        xor     r11, r11
        combadd2(r11,r10,r9,[x],[x+8])
        mov     [z+8], r9

// Result term 2

        xor     r12, r12
        combadd1(r12,r11,r10,[x+8])
        combadd2(r12,r11,r10,[x],[x+16])
        mov     [z+16], r10

// Result term 3

        combaddz(r13,rcx,rbx,[x],[x+24])
        combadd(r13,rcx,rbx,[x+8],[x+16])
        doubladd(r13,r12,r11,rcx,rbx)
        mov     [z+24], r11

// Result term 4

        combaddz(r14,rcx,rbx,[x],[x+32])
        combadd(r14,rcx,rbx,[x+8],[x+24])
        doubladd(r14,r13,r12,rcx,rbx)
        combadd1(r14,r13,r12,[x+16])
        mov     [z+32], r12

// Result term 5

        combaddz(r15,rcx,rbx,[x],[x+40])
        combadd(r15,rcx,rbx,[x+8],[x+32])
        combadd(r15,rcx,rbx,[x+16],[x+24])
        doubladd(r15,r14,r13,rcx,rbx)
        mov     [z+40], r13

// Result term 6

        combaddz(r8,rcx,rbx,[x],[x+48])
        combadd(r8,rcx,rbx,[x+8],[x+40])
        combadd(r8,rcx,rbx,[x+16],[x+32])
        doubladd(r8,r15,r14,rcx,rbx)
        combadd1(r8,r15,r14,[x+24])
        mov     [z+48], r14

// Result term 7

        combaddz(r9,rcx,rbx,[x],[x+56])
        combadd(r9,rcx,rbx,[x+8],[x+48])
        combadd(r9,rcx,rbx,[x+16],[x+40])
        combadd(r9,rcx,rbx,[x+24],[x+32])
        doubladd(r9,r8,r15,rcx,rbx)
        mov     [z+56], r15

// Result term 8

        combaddz(r10,rcx,rbx,[x],[x+64])
        combadd(r10,rcx,rbx,[x+8],[x+56])
        combadd(r10,rcx,rbx,[x+16],[x+48])
        combadd(r10,rcx,rbx,[x+24],[x+40])
        doubladd(r10,r9,r8,rcx,rbx)
        combadd1(r10,r9,r8,[x+32])
        mov     [z+64], r8

// We now stop writing back and keep remaining results in a register window.
// Continue with result term 9

        combaddz(r11,rcx,rbx,[x+8],[x+64])
        combadd(r11,rcx,rbx,[x+16],[x+56])
        combadd(r11,rcx,rbx,[x+24],[x+48])
        combadd(r11,rcx,rbx,[x+32],[x+40])
        doubladd(r11,r10,r9,rcx,rbx)

// Result term 10

        combaddz(r12,rcx,rbx,[x+16],[x+64])
        combadd(r12,rcx,rbx,[x+24],[x+56])
        combadd(r12,rcx,rbx,[x+32],[x+48])
        doubladd(r12,r11,r10,rcx,rbx)
        combadd1(r12,r11,r10,[x+40])

// Result term 11

        combaddz(r13,rcx,rbx,[x+24],[x+64])
        combadd(r13,rcx,rbx,[x+32],[x+56])
        combadd(r13,rcx,rbx,[x+40],[x+48])
        doubladd(r13,r12,r11,rcx,rbx)

// Result term 12

        combaddz(r14,rcx,rbx,[x+32],[x+64])
        combadd(r14,rcx,rbx,[x+40],[x+56])
        doubladd(r14,r13,r12,rcx,rbx)
        combadd1(r14,r13,r12,[x+48])

// Result term 13

        combaddz(r15,rcx,rbx,[x+40],[x+64])
        combadd(r15,rcx,rbx,[x+48],[x+56])
        doubladd(r15,r14,r13,rcx,rbx);

// Result term 14

        xor     r8, r8
        combadd1(r8,r15,r14,[x+56])
        combadd2(r8,r15,r14,[x+48],[x+64])

// Result term 15

        mov     rax, [x+56]
        mul     QWORD PTR [x+64]
        add     rax, rax
        adc     rdx, rdx
        add     r15, rax
        adc     r8, rdx

// Result term 16

        mov     rax, [x+64]
        imul    rax, rax
        add     rax, r8

// Now the upper portion is [rax;r15;r14;r13;r12;r11;r10;r9;[z+64]].
// Rotate the upper portion right 9 bits since 2^512 == 2^-9 (mod p_521)
// Let rotated result rdx,r15,r14,...,r8 be h (high) and z[0..7] be l (low)

        mov     r8, [z+64]
        mov     rdx, r8
        and     rdx, 0x1FF
        shrd    r8, r9, 9
        shrd    r9, r10, 9
        shrd    r10, r11, 9
        shrd    r11, r12, 9
        shrd    r12, r13, 9
        shrd    r13, r14, 9
        shrd    r14, r15, 9
        shrd    r15, rax, 9
        shr     rax, 9
        add     rdx, rax

// Force carry-in then add to get s = h + l + 1
// but actually add all 1s in the top 53 bits to get simple carry out

        stc
        adc     r8, [z]
        adc     r9, [z+8]
        adc     r10,[z+16]
        adc     r11,[z+24]
        adc     r12,[z+32]
        adc     r13,[z+40]
        adc     r14,[z+48]
        adc     r15,[z+56]
        adc     rdx, ~0x1FF

// Now CF is set <=> h + l + 1 >= 2^521 <=> h + l >= p_521,
// in which case the lower 521 bits are already right. Otherwise if
// CF is clear, we want to subtract 1. Hence subtract the complement
// of the carry flag then mask the top word, which scrubs the
// padding in either case.

        cmc
        sbb     r8, 0
        sbb     r9, 0
        sbb     r10, 0
        sbb     r11, 0
        sbb     r12, 0
        sbb     r13, 0
        sbb     r14, 0
        sbb     r15, 0
        sbb     rdx, 0
        and     rdx, 0x1FF

// So far, this has been the same as a pure modular squaring.
// Now finally the Montgomery ingredient, which is just a 521-bit
// rotation by 9*64 - 521 = 55 bits right. Write digits back as
// they are created.

        mov     rax, r8
        shrd    r8, r9, 55
        mov     [z], r8
        shrd    r9, r10, 55
        mov     [z+8],  r9
        shrd    r10, r11, 55
        shl     rax, 9
        mov     [z+16], r10
        shrd    r11, r12, 55
        mov     [z+24], r11
        shrd    r12, r13, 55
        mov     [z+32], r12
        or      rdx, rax
        shrd    r13, r14, 55
        mov     [z+40], r13
        shrd    r14, r15, 55
        mov     [z+48], r14
        shrd    r15, rdx, 55
        mov     [z+56], r15
        shr     rdx, 55
        mov     [z+64], rdx

// Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
