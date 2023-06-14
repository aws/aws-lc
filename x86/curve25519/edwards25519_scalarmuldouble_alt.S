// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Double scalar multiplication for edwards25519, fresh and base point
// Input scalar[4], point[8], bscalar[4]; output res[8]
//
// extern void edwards25519_scalarmuldouble_alt
//   (uint64_t res[static 8],uint64_t scalar[static 4],
//    uint64_t point[static 8],uint64_t bscalar[static 4]);
//
// Given scalar = n, point = P and bscalar = m, returns in res
// the point (X,Y) = n * P + m * B where B = (...,4/5) is
// the standard basepoint for the edwards25519 (Ed25519) curve.
//
// Both 256-bit coordinates of the input point P are implicitly
// reduced modulo 2^255-19 if they are not already in reduced form,
// but the conventional usage is that they *are* already reduced.
// The scalars can be arbitrary 256-bit numbers but may also be
// considered as implicitly reduced modulo the group order.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point, RCX = bscalar
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point, R9 = bscalar
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(edwards25519_scalarmuldouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(edwards25519_scalarmuldouble_alt)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for result and temporaries on stack with some aliasing.
// Both "resx" and "resy" assume the "res" pointer has been preloaded into rbp.

#define resx rbp+(0*NUMSIZE)
#define resy rbp+(1*NUMSIZE)

#define scalar rsp+(0*NUMSIZE)
#define bscalar rsp+(1*NUMSIZE)

#define acc rsp+(3*NUMSIZE)

#define tabent rsp+(7*NUMSIZE)
#define btabent rsp+(11*NUMSIZE)

#define tab rsp+(14*NUMSIZE)

// Additional variables kept on the stack

#define bf QWORD PTR [rsp+2*NUMSIZE]
#define cf QWORD PTR [rsp+2*NUMSIZE+8]
#define i QWORD PTR [rsp+2*NUMSIZE+16]
#define res QWORD PTR [rsp+2*NUMSIZE+24]

// Total size to reserve on the stack (excluding local subroutines)

#define NSPACE (46*NUMSIZE)

// Sub-references used in local subroutines with local stack

#define x_0 rdi+0
#define y_0 rdi+NUMSIZE
#define z_0 rdi+(2*NUMSIZE)
#define w_0 rdi+(3*NUMSIZE)

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)
#define w_1 rsi+(3*NUMSIZE)

#define x_2 rbp+0
#define y_2 rbp+NUMSIZE
#define z_2 rbp+(2*NUMSIZE)
#define w_2 rbp+(3*NUMSIZE)

#define t0 rsp+(0*NUMSIZE)
#define t1 rsp+(1*NUMSIZE)
#define t2 rsp+(2*NUMSIZE)
#define t3 rsp+(3*NUMSIZE)
#define t4 rsp+(4*NUMSIZE)
#define t5 rsp+(5*NUMSIZE)

// Macro wrapping up the basic field multiplication, only trivially
// different from a pure function call to bignum_mul_p25519_alt.

#define mul_p25519(P0,P1,P2)                    \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        xor     r10,r10;                        \
        xor     r11,r11;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x8];             \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2];                 \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,0x0;                        \
        xor     r12,r12;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x10];            \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,r12;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x8];             \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2];                 \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        xor     r13,r13;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x18];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,r13;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x10];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2];                 \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        xor     r14,r14;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x18];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,r14;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        xor     r15,r15;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,r15;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r14,rax;                        \
        adc     r15,rdx;                        \
        mov     esi,0x26;                       \
        mov     rax,r12;                        \
        mul     rsi;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rsi;                            \
        sub     rdx,rcx;                        \
        xor     rcx,rcx;                        \
        add     r11,rax;                        \
        mov     r12,rdx;                        \
        adc     r12,rcx;                        \
        shld    r12,r11,0x1;                    \
        lea     rax,[r12+0x1];                  \
        mov     esi,0x13;                       \
        bts     r11,63;                         \
        imul    rax,rsi;                        \
        add     r8,rax;                         \
        adc     r9,rcx;                         \
        adc     r10,rcx;                        \
        adc     r11,rcx;                        \
        sbb     rax,rax;                        \
        not     rax;                            \
        and     rax,rsi;                        \
        sub     r8,rax;                         \
        sbb     r9,rcx;                         \
        sbb     r10,rcx;                        \
        sbb     r11,rcx;                        \
        btr     r11,63;                         \
        mov     [P0],r8;                        \
        mov     [P0+0x8],r9;                    \
        mov     [P0+0x10],r10;                  \
        mov     [P0+0x18],r11

// A version of multiplication that only guarantees output < 2 * p_25519.
// This basically skips the +1 and final correction in quotient estimation.

#define mul_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2];                 \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        xor     r10,r10;                        \
        xor     r11,r11;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x8];             \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2];                 \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,0x0;                        \
        xor     r12,r12;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x10];            \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,r12;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x8];             \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2];                 \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        xor     r13,r13;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P2+0x18];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,r13;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x10];            \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2];                 \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        xor     r14,r14;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P2+0x18];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,r14;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x8];             \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        xor     r15,r15;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,r15;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x10];            \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     QWORD PTR [P2+0x18];            \
        add     r14,rax;                        \
        adc     r15,rdx;                        \
        mov     ebx,0x26;                       \
        mov     rax,r12;                        \
        mul     rbx;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        xor     rcx,rcx;                        \
        add     r11,rax;                        \
        mov     r12,rdx;                        \
        adc     r12,rcx;                        \
        shld    r12,r11,0x1;                    \
        btr     r11, 0x3f;                      \
        mov     edx, 0x13;                      \
        imul    rdx, r12;                       \
        add     r8, rdx;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        mov     rax, [P1];                      \
        mul     rax;                            \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        xor     r10,r10;                        \
        xor     r11,r11;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x8];             \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r11,0x0;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        adc     r11,0x0;                        \
        xor     r12,r12;                        \
        mov     rax, [P1+0x8];                  \
        mul     rax;                            \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x10];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r12,0x0;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        adc     r12,0x0;                        \
        xor     r13,r13;                        \
        mov     rax, [P1];                      \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r13,0x0;                        \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x10];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r13,0x0;                        \
        add     r11,rax;                        \
        adc     r12,rdx;                        \
        adc     r13,0x0;                        \
        xor     r14,r14;                        \
        mov     rax, [P1+0x8];                  \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r14,0x0;                        \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        add     r12,rax;                        \
        adc     r13,rdx;                        \
        adc     r14,0x0;                        \
        xor     r15,r15;                        \
        mov     rax, [P1+0x10];                 \
        mul     QWORD PTR [P1+0x18];            \
        add     rax,rax;                        \
        adc     rdx,rdx;                        \
        adc     r15,0x0;                        \
        add     r13,rax;                        \
        adc     r14,rdx;                        \
        adc     r15,0x0;                        \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        add     r14,rax;                        \
        adc     r15,rdx;                        \
        mov     ebx,0x26;                       \
        mov     rax,r12;                        \
        mul     rbx;                            \
        add     r8,rax;                         \
        adc     r9,rdx;                         \
        sbb     rcx,rcx;                        \
        mov     rax,r13;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r14;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        add     r10,rax;                        \
        adc     r11,rdx;                        \
        sbb     rcx,rcx;                        \
        mov     rax,r15;                        \
        mul     rbx;                            \
        sub     rdx,rcx;                        \
        xor     rcx,rcx;                        \
        add     r11,rax;                        \
        mov     r12,rdx;                        \
        adc     r12,rcx;                        \
        shld    r12, r11, 0x1;                  \
        btr     r11, 0x3f;                      \
        mov     edx, 0x13;                      \
        imul    rdx, r12;                       \
        add     r8, rdx;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(P0,P1,P2)                    \
        mov     r8, [P1];                       \
        xor     ebx, ebx;                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     ecx, 38;                        \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     rax, [P1+24];                   \
        sbb     rax, [P2+24];                   \
        cmovnc  rcx, rbx;                       \
        sub     r8, rcx;                        \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     rax, rbx;                       \
        mov     [P0], r8;                       \
        mov     [P0+8], r9;                     \
        mov     [P0+16], r10;                   \
        mov     [P0+24], rax

// Modular addition and doubling with double modulus 2 * p_25519 = 2^256 - 38.
// This only ensures that the result fits in 4 digits, not that it is reduced
// even w.r.t. double modulus. The result is always correct modulo provided
// the sum of the inputs is < 2^256 + 2^256 - 38, so in particular provided
// at least one of them is reduced double modulo.

#define add_twice4(P0,P1,P2)                    \
        mov     r8, [P1];                       \
        xor     ecx, ecx;                       \
        add     r8, [P2];                       \
        mov     r9, [P1+0x8];                   \
        adc     r9, [P2+0x8];                   \
        mov     r10, [P1+0x10];                 \
        adc     r10, [P2+0x10];                 \
        mov     r11, [P1+0x18];                 \
        adc     r11, [P2+0x18];                 \
        mov     eax, 38;                        \
        cmovnc  rax, rcx;                       \
        add     r8, rax;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

#define double_twice4(P0,P1)                    \
        mov     r8, [P1];                       \
        xor     ecx, ecx;                       \
        add     r8, r8;                         \
        mov     r9, [P1+0x8];                   \
        adc     r9, r9;                         \
        mov     r10, [P1+0x10];                 \
        adc     r10, r10;                       \
        mov     r11, [P1+0x18];                 \
        adc     r11, r11;                       \
        mov     eax, 38;                        \
        cmovnc  rax, rcx;                       \
        add     r8, rax;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Load the constant k_25519 = 2 * d_25519 using immediate operations

#define load_k25519(P0)                         \
        mov     rax, 0xebd69b9426b2f159;        \
        mov     [P0], rax;                      \
        mov     rax, 0x00e0149a8283b156;        \
        mov     [P0+8], rax;                    \
        mov     rax, 0x198e80f2eef3d130;        \
        mov     [P0+16], rax;                   \
        mov     rax, 0x2406d9dc56dffce7;        \
        mov     [P0+24], rax

S2N_BN_SYMBOL(edwards25519_scalarmuldouble_alt):

// In this case the Windows form literally makes a subroutine call.
// This avoids hassle arising from keeping code and data together.

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        call    edwards25519_scalarmuldouble_alt_standard
        pop     rsi
        pop     rdi
        ret

edwards25519_scalarmuldouble_alt_standard:
#endif

// Save registers, make room for temps, preserve input arguments.

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        sub     rsp, NSPACE

// Move the output pointer to a stable place

        mov     res, rdi

// Copy scalars while recoding all 4-bit nybbles except the top
// one (bits 252..255) into signed 4-bit digits. This is essentially
// done just by adding the recoding constant 0x0888..888, after
// which all digits except the first have an implicit bias of -8,
// so 0 -> -8, 1 -> -7, ... 7 -> -1, 8 -> 0, 9 -> 1, ... 15 -> 7.
// (We could literally create 2s complement signed nybbles by
// XORing with the same constant 0x0888..888 afterwards, but it
// doesn't seem to make the end usage any simpler.)
//
// In order to ensure that the unrecoded top nybble (bits 252..255)
// does not become > 8 as a result of carries lower down from the
// recoding, we first (conceptually) subtract the group order iff
// the top digit of the scalar is > 2^63. In the implementation the
// reduction and recoding are combined by optionally using the
// modified recoding constant 0x0888...888 + (2^256 - group_order).

        mov     r8, [rcx]
        mov     r9, [rcx+8]
        mov     r10, [rcx+16]
        mov     r11, [rcx+24]
        mov     r12, 0xc7f56fb5a0d9e920
        mov     r13, 0xe190b99370cba1d5
        mov     r14, 0x8888888888888887
        mov     r15, 0x8888888888888888
        mov     rax, 0x8000000000000000
        mov     rbx, 0x0888888888888888
        cmp     rax, r11
        cmovnc  r12, r15
        cmovnc  r13, r15
        cmovnc  r14, r15
        cmovnc  r15, rbx
        add     r8, r12
        adc     r9, r13
        adc     r10, r14
        adc     r11, r15
        mov     [rsp+32], r8
        mov     [rsp+40], r9
        mov     [rsp+48], r10
        mov     [rsp+56], r11

        mov     r8, [rsi]
        mov     r9, [rsi+8]
        mov     r10, [rsi+16]
        mov     r11, [rsi+24]
        mov     r12, 0xc7f56fb5a0d9e920
        mov     r13, 0xe190b99370cba1d5
        mov     r14, 0x8888888888888887
        mov     r15, 0x8888888888888888
        mov     rax, 0x8000000000000000
        mov     rbx, 0x0888888888888888
        cmp     rax, r11
        cmovnc  r12, r15
        cmovnc  r13, r15
        cmovnc  r14, r15
        cmovnc  r15, rbx
        add     r8, r12
        adc     r9, r13
        adc     r10, r14
        adc     r11, r15
        mov     [rsp], r8
        mov     [rsp+8], r9
        mov     [rsp+16], r10
        mov     [rsp+24], r11

// Create table of multiples 1..8 of the general input point at "tab".
// Reduce the input coordinates x and y modulo 2^256 - 38 first, for the
// sake of definiteness; this is the reduction that will be maintained.
// We could slightly optimize the additions because we know the input
// point is affine (so Z = 1), but it doesn't seem worth the complication.

        mov     eax, 38
        mov     r8, [rdx]
        xor     ebx, ebx
        mov     r9, [rdx+8]
        xor     ecx, ecx
        mov     r10, [rdx+16]
        xor     esi, esi
        mov     r11, [rdx+24]
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rsi, r11
        cmovnc  rax, r8
        mov     [rsp+448], rax
        cmovnc  rbx, r9
        mov     [rsp+456], rbx
        cmovnc  rcx, r10
        mov     [rsp+464], rcx
        cmovnc  rsi, r11
        mov     [rsp+472], rsi

        mov     eax, 38
        mov     r8, [rdx+32]
        xor     ebx, ebx
        mov     r9, [rdx+40]
        xor     ecx, ecx
        mov     r10, [rdx+48]
        xor     esi, esi
        mov     r11, [rdx+56]
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rsi, r11
        cmovnc  rax, r8
        mov     [rsp+480], rax
        cmovnc  rbx, r9
        mov     [rsp+488], rbx
        cmovnc  rcx, r10
        mov     [rsp+496], rcx
        cmovnc  rsi, r11
        mov     [rsp+504], rsi

        mov     eax, 1
        mov     [rsp+512], rax
        xor     eax, eax
        mov     [rsp+520], rax
        mov     [rsp+528], rax
        mov     [rsp+536], rax

        lea     rdi, [rsp+544]
        lea     rsi, [rsp+448]
        lea     rbp, [rsp+480]
        mul_4(x_0,x_1,x_2)

// Multiple 2

        lea     rdi, [rsp+576]
        lea     rsi, [rsp+448]
        call    edwards25519_scalarmuldouble_alt_epdouble

// Multiple 3

        lea     rdi, [rsp+704]
        lea     rsi, [rsp+448]
        lea     rbp, [rsp+576]
        call    edwards25519_scalarmuldouble_alt_epadd

// Multiple 4

        lea     rdi, [rsp+832]
        lea     rsi, [rsp+576]
        call    edwards25519_scalarmuldouble_alt_epdouble

// Multiple 5

        lea     rdi, [rsp+960]
        lea     rsi, [rsp+448]
        lea     rbp, [rsp+832]
        call    edwards25519_scalarmuldouble_alt_epadd

// Multiple 6

        lea     rdi, [rsp+1088]
        lea     rsi, [rsp+704]
        call    edwards25519_scalarmuldouble_alt_epdouble

// Multiple 7

        lea     rdi, [rsp+1216]
        lea     rsi, [rsp+448]
        lea     rbp, [rsp+1088]
        call    edwards25519_scalarmuldouble_alt_epadd

// Multiple 8

        lea     rdi, [rsp+1344]
        lea     rsi, [rsp+832]
        call    edwards25519_scalarmuldouble_alt_epdouble

// Handle the initialization, starting the loop counter at i = 252
// and initializing acc to the sum of the table entries for the
// top nybbles of the scalars (the ones with no implicit -8 bias).

        mov     rax, 252
        mov     i, rax

// Index for btable entry...

        mov     rax, [rsp+56]
        shr     rax, 60
        mov     bf, rax

// ...and constant-time indexing based on that index

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

        lea     rbp, [rip+edwards25519_scalarmuldouble_alt_table]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi

        mov     [rsp+352], rax
        mov     [rsp+360], rbx
        mov     [rsp+368], rcx
        mov     [rsp+376], rdx
        mov     [rsp+384], r8
        mov     [rsp+392], r9
        mov     [rsp+400], r10
        mov     [rsp+408], r11
        mov     [rsp+416], r12
        mov     [rsp+424], r13
        mov     [rsp+432], r14
        mov     [rsp+440], r15

// Index for table entry...

        mov     rax, [rsp+24]
        shr     rax, 60
        mov     bf, rax

// ...and constant-time indexing based on that index.
// Do the Y and Z fields first, to save on registers...

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        lea     rbp, [rsp+480]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi

        mov     [rsp+256], rax
        mov     [rsp+264], rbx
        mov     [rsp+272], rcx
        mov     [rsp+280], rdx
        mov     [rsp+288], r8
        mov     [rsp+296], r9
        mov     [rsp+304], r10
        mov     [rsp+312], r11

// ...followed by the X and W fields

        lea     rbp, [rsp+448]

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi

        mov     [rsp+224], rax
        mov     [rsp+232], rbx
        mov     [rsp+240], rcx
        mov     [rsp+248], rdx
        mov     [rsp+320], r8
        mov     [rsp+328], r9
        mov     [rsp+336], r10
        mov     [rsp+344], r11

// Add those elements to initialize the accumulator for bit position 252

        lea     rdi, [rsp+96]
        lea     rsi, [rsp+224]
        lea     rbp, [rsp+352]
        call    edwards25519_scalarmuldouble_alt_pepadd

// Main loop with acc = [scalar/2^i] * point + [bscalar/2^i] * basepoint
// Start with i = 252 for bits 248..251 and go down four at a time to 3..0

edwards25519_scalarmuldouble_alt_loop:

        mov     rax, i
        sub     rax, 4
        mov     i, rax

// Double to acc' = 2 * acc

        lea     rdi, [rsp+96]
        lea     rsi, [rsp+96]
        call    edwards25519_scalarmuldouble_alt_pdouble

// Get btable entry, first getting the adjusted bitfield...

        mov     rax, i
        mov     rcx, rax
        shr     rax, 6
        mov     rax, [rsp+8*rax+32]
        shr     rax, cl
        and     rax, 15

        sub     rax, 8
        sbb     rcx, rcx
        xor     rax, rcx
        sub     rax, rcx
        mov     cf, rcx
        mov     bf, rax

// ... then doing constant-time lookup with the appropriate index...

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

        lea     rbp, [rip+edwards25519_scalarmuldouble_alt_table]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi

// ... then optionally negating before storing. The table entry
// is in precomputed form and we currently have
//
//      [rdx;rcx;rbx;rax] = y - x
//      [r11;r10;r9;r8] = x + y
//      [r15;r14;r13;r12] = 2 * d * x * y
//
// Negation for Edwards curves is -(x,y) = (-x,y), which in this modified
// form amounts to swapping the first two fields and negating the third.
// The negation does not always fully reduce even mod 2^256-38 in the zero
// case, instead giving -0 = 2^256-38. But that is fine since the result is
// always fed to a multipliction inside the "pepadd" function below that
// handles any 256-bit input.

        mov     rdi, cf
        test    rdi, rdi

        mov     rsi, rax
        cmovnz  rsi, r8
        cmovnz  r8, rax
        mov     [rsp+352], rsi
        mov     [rsp+384], r8

        mov     rsi, rbx
        cmovnz  rsi, r9
        cmovnz  r9, rbx
        mov     [rsp+360], rsi
        mov     [rsp+392], r9

        mov     rsi, rcx
        cmovnz  rsi, r10
        cmovnz  r10, rcx
        mov     [rsp+368], rsi
        mov     [rsp+400], r10

        mov     rsi, rdx
        cmovnz  rsi, r11
        cmovnz  r11, rdx
        mov     [rsp+376], rsi
        mov     [rsp+408], r11

        xor     r12, rdi
        xor     r13, rdi
        xor     r14, rdi
        xor     r15, rdi
        and     rdi, 37
        sub     r12, rdi
        sbb     r13, 0
        sbb     r14, 0
        sbb     r15, 0
        mov     [rsp+416], r12
        mov     [rsp+424], r13
        mov     [rsp+432], r14
        mov     [rsp+440], r15

// Get table entry, first getting the adjusted bitfield...

        mov     rax, i
        mov     rcx, rax
        shr     rax, 6
        mov     rax, [rsp+8*rax]
        shr     rax, cl
        and     rax, 15

        sub     rax, 8
        sbb     rcx, rcx
        xor     rax, rcx
        sub     rax, rcx
        mov     cf, rcx
        mov     bf, rax

// ...and constant-time indexing based on that index
// Do the Y and Z fields first, to save on registers
// and store them back (they don't need any modification)

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        lea     rbp, [rsp+480]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi

        mov     [rsp+256], rax
        mov     [rsp+264], rbx
        mov     [rsp+272], rcx
        mov     [rsp+280], rdx
        mov     [rsp+288], r8
        mov     [rsp+296], r9
        mov     [rsp+304], r10
        mov     [rsp+312], r11

// Now do the X and W fields...

        lea     rbp, [rsp+448]

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi

// ... then optionally negate before storing the X and W fields. This
// time the table entry is extended-projective, and is here:
//
//      [rdx;rcx;rbx;rax] = X
//      [tabent+32] = Y
//      [tabent+64] = Z
//      [r11;r10;r9;r8] = W
//
// This time we just need to negate the X and the W fields.
// The crude way negation is done can result in values of X or W
// (when initially zero before negation) being exactly equal to
// 2^256-38, but the "pepadd" function handles that correctly.

        mov     rdi, cf

        xor     rax, rdi
        xor     rbx, rdi
        xor     rcx, rdi
        xor     rdx, rdi

        xor     r8, rdi
        xor     r9, rdi
        xor     r10, rdi
        xor     r11, rdi

        and     rdi, 37

        sub     rax, rdi
        sbb     rbx, 0
        sbb     rcx, 0
        sbb     rdx, 0

        mov     [rsp+224], rax
        mov     [rsp+232], rbx
        mov     [rsp+240], rcx
        mov     [rsp+248], rdx

        sub     r8, rdi
        sbb     r9, 0
        sbb     r10, 0
        sbb     r11, 0

        mov     [rsp+320], r8
        mov     [rsp+328], r9
        mov     [rsp+336], r10
        mov     [rsp+344], r11

// Double to acc' = 4 * acc

        lea     rdi, [rsp+96]
        lea     rsi, [rsp+96]
        call    edwards25519_scalarmuldouble_alt_pdouble

// Add tabent := tabent + btabent

        lea     rdi, [rsp+224]
        lea     rsi, [rsp+224]
        lea     rbp, [rsp+352]
        call    edwards25519_scalarmuldouble_alt_pepadd

// Double to acc' = 8 * acc

        lea     rdi, [rsp+96]
        lea     rsi, [rsp+96]
        call    edwards25519_scalarmuldouble_alt_pdouble

// Double to acc' = 16 * acc

        lea     rdi, [rsp+96]
        lea     rsi, [rsp+96]
        call    edwards25519_scalarmuldouble_alt_epdouble

// Add table entry, acc := acc + tabent

        lea     rdi, [rsp+96]
        lea     rsi, [rsp+96]
        lea     rbp, [rsp+224]
        call    edwards25519_scalarmuldouble_alt_epadd

// Loop down

        mov     rax, i
        test    rax, rax
        jnz     edwards25519_scalarmuldouble_alt_loop

// Modular inverse setup

        mov     rdi, 4
        lea     rsi, [rsp+224]
        lea     rdx, [rsp+160]
        lea     rcx, [rip+edwards25519_scalarmuldouble_alt_p25519]
        lea     r8, [rsp+352]

// Inline copy of bignum_modinv, identical except for stripping out the
// prologue and epilogue saving and restoring registers and the initial
// test for k = 0 (which is trivially false here since k = 4). For more
// details and explanations see "x86/generic/bignum_modinv.S". Note
// that the stack it uses for its own temporaries is 80 bytes so it
// only overwrites local variables that are no longer needed.

        mov     [rsp+0x40], rsi
        mov     [rsp+0x38], r8
        mov     [rsp+0x48], rcx
        lea     r10, [r8+8*rdi]
        mov     [rsp+0x30], r10
        lea     r15, [r10+8*rdi]
        xor     r11, r11
        xor     r9, r9
edwards25519_scalarmuldouble_alt_copyloop:
        mov     rax, [rdx+8*r9]
        mov     rbx, [rcx+8*r9]
        mov     [r10+8*r9], rax
        mov     [r15+8*r9], rbx
        mov     [r8+8*r9], rbx
        mov     [rsi+8*r9], r11
        inc     r9
        cmp     r9, rdi
        jb      edwards25519_scalarmuldouble_alt_copyloop
        mov     rax, [r8]
        mov     rbx, rax
        dec     rbx
        mov     [r8], rbx
        mov     rbp, rax
        mov     r12, rax
        shl     rbp, 0x2
        sub     r12, rbp
        xor     r12, 0x2
        mov     rbp, r12
        imul    rbp, rax
        mov     eax, 0x2
        add     rax, rbp
        add     rbp, 0x1
        imul    r12, rax
        imul    rbp, rbp
        mov     eax, 0x1
        add     rax, rbp
        imul    r12, rax
        imul    rbp, rbp
        mov     eax, 0x1
        add     rax, rbp
        imul    r12, rax
        imul    rbp, rbp
        mov     eax, 0x1
        add     rax, rbp
        imul    r12, rax
        mov     [rsp+0x28], r12
        mov     rax, rdi
        shl     rax, 0x7
        mov     [rsp+0x20], rax
edwards25519_scalarmuldouble_alt_outerloop:
        mov     r13, [rsp+0x20]
        add     r13, 0x3f
        shr     r13, 0x6
        cmp     r13, rdi
        cmovae  r13, rdi
        xor     r12, r12
        xor     r14, r14
        xor     rbp, rbp
        xor     rsi, rsi
        xor     r11, r11
        mov     r8, [rsp+0x30]
        lea     r15, [r8+8*rdi]
        xor     r9, r9
edwards25519_scalarmuldouble_alt_toploop:
        mov     rbx, [r8+8*r9]
        mov     rcx, [r15+8*r9]
        mov     r10, r11
        and     r10, r12
        and     r11, rbp
        mov     rax, rbx
        or      rax, rcx
        neg     rax
        cmovb   r14, r10
        cmovb   rsi, r11
        cmovb   r12, rbx
        cmovb   rbp, rcx
        sbb     r11, r11
        inc     r9
        cmp     r9, r13
        jb      edwards25519_scalarmuldouble_alt_toploop
        mov     rax, r12
        or      rax, rbp
        bsr     rcx, rax
        xor     rcx, 0x3f
        shld    r12, r14, cl
        shld    rbp, rsi, cl
        mov     rax, [r8]
        mov     r14, rax
        mov     rax, [r15]
        mov     rsi, rax
        mov     r10d, 0x1
        mov     r11d, 0x0
        mov     ecx, 0x0
        mov     edx, 0x1
        mov     r9d, 0x3a
        mov     [rsp+0x8], rdi
        mov     [rsp+0x10], r13
        mov     [rsp], r8
        mov     [rsp+0x18], r15
edwards25519_scalarmuldouble_alt_innerloop:
        xor     eax, eax
        xor     ebx, ebx
        xor     r8, r8
        xor     r15, r15
        bt      r14, 0x0
        cmovb   rax, rbp
        cmovb   rbx, rsi
        cmovb   r8, rcx
        cmovb   r15, rdx
        mov     r13, r14
        sub     r14, rbx
        sub     rbx, r13
        mov     rdi, r12
        sub     rdi, rax
        cmovb   rbp, r12
        lea     r12, [rdi-0x1]
        cmovb   r14, rbx
        cmovb   rsi, r13
        not     r12
        cmovb   rcx, r10
        cmovb   rdx, r11
        cmovae  r12, rdi
        shr     r14, 1
        add     r10, r8
        add     r11, r15
        shr     r12, 1
        add     rcx, rcx
        add     rdx, rdx
        dec     r9
        jne     edwards25519_scalarmuldouble_alt_innerloop
        mov     rdi, [rsp+0x8]
        mov     r13, [rsp+0x10]
        mov     r8, [rsp]
        mov     r15, [rsp+0x18]
        mov     [rsp], r10
        mov     [rsp+0x8], r11
        mov     [rsp+0x10], rcx
        mov     [rsp+0x18], rdx
        mov     r8, [rsp+0x38]
        mov     r15, [rsp+0x40]
        xor     r14, r14
        xor     rsi, rsi
        xor     r10, r10
        xor     r11, r11
        xor     r9, r9
edwards25519_scalarmuldouble_alt_congloop:
        mov     rcx, [r8+8*r9]
        mov     rax, [rsp]
        mul     rcx
        add     r14, rax
        adc     rdx, 0x0
        mov     r12, rdx
        mov     rax, [rsp+0x10]
        mul     rcx
        add     rsi, rax
        adc     rdx, 0x0
        mov     rbp, rdx
        mov     rcx, [r15+8*r9]
        mov     rax, [rsp+0x8]
        mul     rcx
        add     r14, rax
        adc     r12, rdx
        shrd    r10, r14, 0x3a
        mov     [r8+8*r9], r10
        mov     r10, r14
        mov     r14, r12
        mov     rax, [rsp+0x18]
        mul     rcx
        add     rsi, rax
        adc     rbp, rdx
        shrd    r11, rsi, 0x3a
        mov     [r15+8*r9], r11
        mov     r11, rsi
        mov     rsi, rbp
        inc     r9
        cmp     r9, rdi
        jb      edwards25519_scalarmuldouble_alt_congloop
        shld    r14, r10, 0x6
        shld    rsi, r11, 0x6
        mov     r15, [rsp+0x48]
        mov     rbx, [r8]
        mov     r12, [rsp+0x28]
        imul    r12, rbx
        mov     rax, [r15]
        mul     r12
        add     rax, rbx
        mov     r10, rdx
        mov     r9d, 0x1
        mov     rcx, rdi
        dec     rcx
        je      edwards25519_scalarmuldouble_alt_wmontend
edwards25519_scalarmuldouble_alt_wmontloop:
        adc     r10, [r8+8*r9]
        sbb     rbx, rbx
        mov     rax, [r15+8*r9]
        mul     r12
        sub     rdx, rbx
        add     rax, r10
        mov     [r8+8*r9-0x8], rax
        mov     r10, rdx
        inc     r9
        dec     rcx
        jne     edwards25519_scalarmuldouble_alt_wmontloop
edwards25519_scalarmuldouble_alt_wmontend:
        adc     r10, r14
        mov     [r8+8*rdi-0x8], r10
        sbb     r10, r10
        neg     r10
        mov     rcx, rdi
        xor     r9, r9
edwards25519_scalarmuldouble_alt_wcmploop:
        mov     rax, [r8+8*r9]
        sbb     rax, [r15+8*r9]
        inc     r9
        dec     rcx
        jne     edwards25519_scalarmuldouble_alt_wcmploop
        sbb     r10, 0x0
        sbb     r10, r10
        not     r10
        xor     rcx, rcx
        xor     r9, r9
edwards25519_scalarmuldouble_alt_wcorrloop:
        mov     rax, [r8+8*r9]
        mov     rbx, [r15+8*r9]
        and     rbx, r10
        neg     rcx
        sbb     rax, rbx
        sbb     rcx, rcx
        mov     [r8+8*r9], rax
        inc     r9
        cmp     r9, rdi
        jb      edwards25519_scalarmuldouble_alt_wcorrloop
        mov     r8, [rsp+0x40]
        mov     rbx, [r8]
        mov     rbp, [rsp+0x28]
        imul    rbp, rbx
        mov     rax, [r15]
        mul     rbp
        add     rax, rbx
        mov     r11, rdx
        mov     r9d, 0x1
        mov     rcx, rdi
        dec     rcx
        je      edwards25519_scalarmuldouble_alt_zmontend
edwards25519_scalarmuldouble_alt_zmontloop:
        adc     r11, [r8+8*r9]
        sbb     rbx, rbx
        mov     rax, [r15+8*r9]
        mul     rbp
        sub     rdx, rbx
        add     rax, r11
        mov     [r8+8*r9-0x8], rax
        mov     r11, rdx
        inc     r9
        dec     rcx
        jne     edwards25519_scalarmuldouble_alt_zmontloop
edwards25519_scalarmuldouble_alt_zmontend:
        adc     r11, rsi
        mov     [r8+8*rdi-0x8], r11
        sbb     r11, r11
        neg     r11
        mov     rcx, rdi
        xor     r9, r9
edwards25519_scalarmuldouble_alt_zcmploop:
        mov     rax, [r8+8*r9]
        sbb     rax, [r15+8*r9]
        inc     r9
        dec     rcx
        jne     edwards25519_scalarmuldouble_alt_zcmploop
        sbb     r11, 0x0
        sbb     r11, r11
        not     r11
        xor     rcx, rcx
        xor     r9, r9
edwards25519_scalarmuldouble_alt_zcorrloop:
        mov     rax, [r8+8*r9]
        mov     rbx, [r15+8*r9]
        and     rbx, r11
        neg     rcx
        sbb     rax, rbx
        sbb     rcx, rcx
        mov     [r8+8*r9], rax
        inc     r9
        cmp     r9, rdi
        jb      edwards25519_scalarmuldouble_alt_zcorrloop
        mov     r8, [rsp+0x30]
        lea     r15, [r8+8*rdi]
        xor     r9, r9
        xor     r12, r12
        xor     r14, r14
        xor     rbp, rbp
        xor     rsi, rsi
edwards25519_scalarmuldouble_alt_crossloop:
        mov     rcx, [r8+8*r9]
        mov     rax, [rsp]
        mul     rcx
        add     r14, rax
        adc     rdx, 0x0
        mov     r10, rdx
        mov     rax, [rsp+0x10]
        mul     rcx
        add     rsi, rax
        adc     rdx, 0x0
        mov     r11, rdx
        mov     rcx, [r15+8*r9]
        mov     rax, [rsp+0x8]
        mul     rcx
        sub     rdx, r12
        sub     r14, rax
        sbb     r10, rdx
        sbb     r12, r12
        mov     [r8+8*r9], r14
        mov     r14, r10
        mov     rax, [rsp+0x18]
        mul     rcx
        sub     rdx, rbp
        sub     rsi, rax
        sbb     r11, rdx
        sbb     rbp, rbp
        mov     [r15+8*r9], rsi
        mov     rsi, r11
        inc     r9
        cmp     r9, r13
        jb      edwards25519_scalarmuldouble_alt_crossloop
        xor     r9, r9
        mov     r10, r12
        mov     r11, rbp
        xor     r14, r12
        xor     rsi, rbp
edwards25519_scalarmuldouble_alt_optnegloop:
        mov     rax, [r8+8*r9]
        xor     rax, r12
        neg     r10
        adc     rax, 0x0
        sbb     r10, r10
        mov     [r8+8*r9], rax
        mov     rax, [r15+8*r9]
        xor     rax, rbp
        neg     r11
        adc     rax, 0x0
        sbb     r11, r11
        mov     [r15+8*r9], rax
        inc     r9
        cmp     r9, r13
        jb      edwards25519_scalarmuldouble_alt_optnegloop
        sub     r14, r10
        sub     rsi, r11
        mov     r9, r13
edwards25519_scalarmuldouble_alt_shiftloop:
        mov     rax, [r8+8*r9-0x8]
        mov     r10, rax
        shrd    rax, r14, 0x3a
        mov     [r8+8*r9-0x8], rax
        mov     r14, r10
        mov     rax, [r15+8*r9-0x8]
        mov     r11, rax
        shrd    rax, rsi, 0x3a
        mov     [r15+8*r9-0x8], rax
        mov     rsi, r11
        dec     r9
        jne     edwards25519_scalarmuldouble_alt_shiftloop
        not     rbp
        mov     rcx, [rsp+0x48]
        mov     r8, [rsp+0x38]
        mov     r15, [rsp+0x40]
        mov     r10, r12
        mov     r11, rbp
        xor     r9, r9
edwards25519_scalarmuldouble_alt_fliploop:
        mov     rdx, rbp
        mov     rax, [rcx+8*r9]
        and     rdx, rax
        and     rax, r12
        mov     rbx, [r8+8*r9]
        xor     rbx, r12
        neg     r10
        adc     rax, rbx
        sbb     r10, r10
        mov     [r8+8*r9], rax
        mov     rbx, [r15+8*r9]
        xor     rbx, rbp
        neg     r11
        adc     rdx, rbx
        sbb     r11, r11
        mov     [r15+8*r9], rdx
        inc     r9
        cmp     r9, rdi
        jb      edwards25519_scalarmuldouble_alt_fliploop
        sub     QWORD PTR [rsp+0x20], 0x3a
        ja      edwards25519_scalarmuldouble_alt_outerloop

// Store result

        mov     rdi, res
        lea     rsi, [rsp+96]
        lea     rbp, [rsp+224]
        mul_p25519(x_0,x_1,x_2)

        mov     rdi, res
        add     rdi, 32
        lea     rsi, [rsp+128]
        lea     rbp, [rsp+224]
        mul_p25519(x_0,x_1,x_2)

// Restore stack and registers

        add     rsp, NSPACE

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        ret

// ****************************************************************************
// Localized versions of subroutines.
// These are close to the standalone functions "edwards25519_epdouble" etc.,
// but are only maintaining reduction modulo 2^256 - 38, not 2^255 - 19.
// ****************************************************************************

edwards25519_scalarmuldouble_alt_epdouble:
        sub rsp, (5*NUMSIZE)
        add_twice4(t0,x_1,y_1)
        sqr_4(t1,z_1)
        sqr_4(t2,x_1)
        sqr_4(t3,y_1)
        double_twice4(t1,t1)
        sqr_4(t0,t0)
        add_twice4(t4,t2,t3)
        sub_twice4(t2,t2,t3)
        add_twice4(t3,t1,t2)
        sub_twice4(t1,t4,t0)
        mul_4(y_0,t2,t4)
        mul_4(z_0,t3,t2)
        mul_4(w_0,t1,t4)
        mul_4(x_0,t1,t3)
        add rsp, (5*NUMSIZE)
        ret

edwards25519_scalarmuldouble_alt_pdouble:
        sub rsp, (5*NUMSIZE)
        add_twice4(t0,x_1,y_1)
        sqr_4(t1,z_1)
        sqr_4(t2,x_1)
        sqr_4(t3,y_1)
        double_twice4(t1,t1)
        sqr_4(t0,t0)
        add_twice4(t4,t2,t3)
        sub_twice4(t2,t2,t3)
        add_twice4(t3,t1,t2)
        sub_twice4(t1,t4,t0)
        mul_4(y_0,t2,t4)
        mul_4(z_0,t3,t2)
        mul_4(x_0,t1,t3)
        add rsp, (5*NUMSIZE)
        ret

edwards25519_scalarmuldouble_alt_epadd:
        sub rsp, (6*NUMSIZE)
        mul_4(t0,w_1,w_2)
        sub_twice4(t1,y_1,x_1)
        sub_twice4(t2,y_2,x_2)
        add_twice4(t3,y_1,x_1)
        add_twice4(t4,y_2,x_2)
        double_twice4(t5,z_2)
        mul_4(t1,t1,t2)
        mul_4(t3,t3,t4)
        load_k25519(t2)
        mul_4(t2,t2,t0)
        mul_4(t4,z_1,t5)
        sub_twice4(t0,t3,t1)
        add_twice4(t5,t3,t1)
        sub_twice4(t1,t4,t2)
        add_twice4(t3,t4,t2)
        mul_4(w_0,t0,t5)
        mul_4(x_0,t0,t1)
        mul_4(y_0,t3,t5)
        mul_4(z_0,t1,t3)
        add rsp, (6*NUMSIZE)
        ret

edwards25519_scalarmuldouble_alt_pepadd:
        sub rsp, (6*NUMSIZE)
        double_twice4(t0,z_1);
        sub_twice4(t1,y_1,x_1);
        add_twice4(t2,y_1,x_1);
        mul_4(t3,w_1,z_2);
        mul_4(t1,t1,x_2);
        mul_4(t2,t2,y_2);
        sub_twice4(t4,t0,t3);
        add_twice4(t0,t0,t3);
        sub_twice4(t5,t2,t1);
        add_twice4(t1,t2,t1);
        mul_4(z_0,t4,t0);
        mul_4(x_0,t5,t4);
        mul_4(y_0,t0,t1);
        mul_4(w_0,t5,t1);
        add rsp, (6*NUMSIZE)
        ret

// ****************************************************************************
// The precomputed data (all read-only). This is currently part of the same
// text section, which gives position-independent code with simple PC-relative
// addressing. However it could be put in a separate section via something like
//
// .section .rodata
// ****************************************************************************

// The modulus p_25519 = 2^255 - 19, for the modular inverse

edwards25519_scalarmuldouble_alt_p25519:
        .quad   0xffffffffffffffed
        .quad   0xffffffffffffffff
        .quad   0xffffffffffffffff
        .quad   0x7fffffffffffffff

// Precomputed table of multiples of generator for edwards25519
// all in precomputed extended-projective (y-x,x+y,2*d*x*y) triples.

edwards25519_scalarmuldouble_alt_table:

        // 1 * G

        .quad   0x9d103905d740913e
        .quad   0xfd399f05d140beb3
        .quad   0xa5c18434688f8a09
        .quad   0x44fd2f9298f81267
        .quad   0x2fbc93c6f58c3b85
        .quad   0xcf932dc6fb8c0e19
        .quad   0x270b4898643d42c2
        .quad   0x07cf9d3a33d4ba65
        .quad   0xabc91205877aaa68
        .quad   0x26d9e823ccaac49e
        .quad   0x5a1b7dcbdd43598c
        .quad   0x6f117b689f0c65a8

        // 2 * G

        .quad   0x8a99a56042b4d5a8
        .quad   0x8f2b810c4e60acf6
        .quad   0xe09e236bb16e37aa
        .quad   0x6bb595a669c92555
        .quad   0x9224e7fc933c71d7
        .quad   0x9f469d967a0ff5b5
        .quad   0x5aa69a65e1d60702
        .quad   0x590c063fa87d2e2e
        .quad   0x43faa8b3a59b7a5f
        .quad   0x36c16bdd5d9acf78
        .quad   0x500fa0840b3d6a31
        .quad   0x701af5b13ea50b73

        // 3 * G

        .quad   0x56611fe8a4fcd265
        .quad   0x3bd353fde5c1ba7d
        .quad   0x8131f31a214bd6bd
        .quad   0x2ab91587555bda62
        .quad   0xaf25b0a84cee9730
        .quad   0x025a8430e8864b8a
        .quad   0xc11b50029f016732
        .quad   0x7a164e1b9a80f8f4
        .quad   0x14ae933f0dd0d889
        .quad   0x589423221c35da62
        .quad   0xd170e5458cf2db4c
        .quad   0x5a2826af12b9b4c6

        // 4 * G

        .quad   0x95fe050a056818bf
        .quad   0x327e89715660faa9
        .quad   0xc3e8e3cd06a05073
        .quad   0x27933f4c7445a49a
        .quad   0x287351b98efc099f
        .quad   0x6765c6f47dfd2538
        .quad   0xca348d3dfb0a9265
        .quad   0x680e910321e58727
        .quad   0x5a13fbe9c476ff09
        .quad   0x6e9e39457b5cc172
        .quad   0x5ddbdcf9102b4494
        .quad   0x7f9d0cbf63553e2b

        // 5 * G

        .quad   0x7f9182c3a447d6ba
        .quad   0xd50014d14b2729b7
        .quad   0xe33cf11cb864a087
        .quad   0x154a7e73eb1b55f3
        .quad   0xa212bc4408a5bb33
        .quad   0x8d5048c3c75eed02
        .quad   0xdd1beb0c5abfec44
        .quad   0x2945ccf146e206eb
        .quad   0xbcbbdbf1812a8285
        .quad   0x270e0807d0bdd1fc
        .quad   0xb41b670b1bbda72d
        .quad   0x43aabe696b3bb69a

        // 6 * G

        .quad   0x499806b67b7d8ca4
        .quad   0x575be28427d22739
        .quad   0xbb085ce7204553b9
        .quad   0x38b64c41ae417884
        .quad   0x3a0ceeeb77157131
        .quad   0x9b27158900c8af88
        .quad   0x8065b668da59a736
        .quad   0x51e57bb6a2cc38bd
        .quad   0x85ac326702ea4b71
        .quad   0xbe70e00341a1bb01
        .quad   0x53e4a24b083bc144
        .quad   0x10b8e91a9f0d61e3

        // 7 * G

        .quad   0xba6f2c9aaa3221b1
        .quad   0x6ca021533bba23a7
        .quad   0x9dea764f92192c3a
        .quad   0x1d6edd5d2e5317e0
        .quad   0x6b1a5cd0944ea3bf
        .quad   0x7470353ab39dc0d2
        .quad   0x71b2528228542e49
        .quad   0x461bea69283c927e
        .quad   0xf1836dc801b8b3a2
        .quad   0xb3035f47053ea49a
        .quad   0x529c41ba5877adf3
        .quad   0x7a9fbb1c6a0f90a7

        // 8 * G

        .quad   0xe2a75dedf39234d9
        .quad   0x963d7680e1b558f9
        .quad   0x2c2741ac6e3c23fb
        .quad   0x3a9024a1320e01c3
        .quad   0x59b7596604dd3e8f
        .quad   0x6cb30377e288702c
        .quad   0xb1339c665ed9c323
        .quad   0x0915e76061bce52f
        .quad   0xe7c1f5d9c9a2911a
        .quad   0xb8a371788bcca7d7
        .quad   0x636412190eb62a32
        .quad   0x26907c5c2ecc4e95

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
