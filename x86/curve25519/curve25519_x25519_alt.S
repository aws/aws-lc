// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// The x25519 function for curve25519
// Inputs scalar[4], point[4]; output res[4]
//
// extern void curve25519_x25519_alt
//   (uint64_t res[static 4],uint64_t scalar[static 4],uint64_t point[static 4])
//
// The function has a second prototype considering the arguments as arrays
// of bytes rather than 64-bit words. The underlying code is the same, since
// the x86 platform is little-endian.
//
// extern void curve25519_x25519_byte_alt
//   (uint8_t res[static 32],uint8_t scalar[static 32],uint8_t point[static 32])
//
// Given a scalar n and the X coordinate of an input point P = (X,Y) on
// curve25519 (Y can live in any extension field of characteristic 2^255-19),
// this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the
// point at infinity. Both n and X inputs are first slightly modified/mangled
// as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748);
// in particular the lower three bits of n are set to zero. Does not implement
// the zero-check specified in Section 6.1.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519_alt)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519_byte_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519_byte_alt)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for the input result argument during the whole body
// and other variables that are only needed prior to the modular inverse.

#define res QWORD PTR [rsp+12*NUMSIZE]
#define i QWORD PTR [rsp+12*NUMSIZE+8]
#define swap QWORD PTR [rsp+12*NUMSIZE+16]

// Pointers to result x coord to be written, assuming the base "res"
// has been loaded into rbp

#define resx rbp+0

// Pointer-offset pairs for temporaries on stack with some aliasing.
// Both dmsn and dnsm need space for >= 5 digits, and we allocate 8

#define scalar rsp+(0*NUMSIZE)

#define pointx rsp+(1*NUMSIZE)

#define dm rsp+(2*NUMSIZE)

#define zm rsp+(3*NUMSIZE)
#define sm rsp+(3*NUMSIZE)
#define dpro rsp+(3*NUMSIZE)

#define sn rsp+(4*NUMSIZE)

#define zn rsp+(5*NUMSIZE)
#define dn rsp+(5*NUMSIZE)
#define e rsp+(5*NUMSIZE)

#define dmsn rsp+(6*NUMSIZE)
#define p rsp+(6*NUMSIZE)

#define xm rsp+(8*NUMSIZE)
#define dnsm rsp+(8*NUMSIZE)
#define spro rsp+(8*NUMSIZE)

#define xn rsp+(10*NUMSIZE)
#define s rsp+(10*NUMSIZE)

#define d rsp+(11*NUMSIZE)

// Total size to reserve on the stack
// This includes space for the 3 other variables above
// and rounds up to a multiple of 32

#define NSPACE (13*NUMSIZE)

// Macro wrapping up the basic field operation bignum_mul_p25519_alt, only
// trivially different from a pure function call to that subroutine.

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

// Multiplication just giving a 5-digit result (actually < 39 * p_25519)
// by not doing anything beyond the first stage of reduction

#define mul_5(P0,P1,P2)                         \
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
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11;                 \
        mov     [P0+0x20], r12

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

// Add 5-digit inputs and normalize to 4 digits

#define add5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        add     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        adc     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        adc     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        adc     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        adc     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
        shld   r12, r11, 0x1;                   \
        btr    r11, 0x3f;                       \
        mov    edx, 0x13;                       \
        imul   rdx, r12;                        \
        add    r8, rdx;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Modular addition with double modulus 2 * p_25519 = 2^256 - 38.
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

// 5-digit subtraction with upward bias to make it positive, adding
// 1000 * (2^255 - 19) = 2^256 * 500 - 19000, then normalizing to 4 digits

#define sub5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        sbb     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        sbb     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
        sub     r8, 19000;                      \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     r11, rbx;                       \
        sbb     r12, rbx;                       \
        add     r12, 500;                       \
        shld    r12, r11, 0x1;                  \
        btr     r11, 0x3f;                      \
        mov     edx, 0x13;                      \
        imul    rdx, r12;                       \
        add     r8, rdx;                        \
        adc     r9, rbx;                        \
        adc     r10, rbx;                       \
        adc     r11, rbx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Combined z = c * x + y with reduction only < 2 * p_25519
// It is assumed that 19 * (c * x + y) < 2^60 * 2^256 so we
// don't need a high mul in the final part.

#define cmadd_4(P0,C1,P2,P3)                    \
        mov     rsi,C1;                         \
        mov     rax,[P2];                       \
        mul     rsi;                            \
        mov     r8,rax;                         \
        mov     r9,rdx;                         \
        mov     rax,[P2+0x8];                   \
        xor     r10,r10;                        \
        mul     rsi;                            \
        add     r9,rax;                         \
        adc     r10,rdx;                        \
        mov     rax,[P2+0x10];                  \
        mul     rsi;                            \
        add     r10,rax;                        \
        adc     rdx,0x0;                        \
        mov     rax,[P2+0x18];                  \
        mov     r11,rdx;                        \
        mul     rsi;                            \
        xor     esi,esi;                        \
        add     r11,rax;                        \
        adc     rdx,rsi;                        \
        add     r8,[P3];                        \
        adc     r9,[P3+0x8];                    \
        adc     r10,[P3+0x10];                  \
        adc     r11,[P3+0x18];                  \
        adc     rdx,rsi;                        \
        shld    rdx, r11, 0x1;                  \
        btr     r11, 63;                        \
        mov     ebx, 0x13;                      \
        imul    rdx, rbx;                       \
        add     r8, rdx;                        \
        adc     r9, rsi;                        \
        adc     r10, rsi;                       \
        adc     r11, rsi;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Multiplex: z := if NZ then x else y

#define mux_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        mov     rcx, [P2];                      \
        cmovz   rax, rcx;                       \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        mov     rcx, [P2+8];                    \
        cmovz   rax, rcx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        mov     rcx, [P2+16];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        mov     rcx, [P2+24];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+24], rax

S2N_BN_SYMBOL(curve25519_x25519_alt):
S2N_BN_SYMBOL(curve25519_x25519_byte_alt):

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
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

// Copy the inputs to the local variables with minimal mangling:
//
//  - The scalar is in principle turned into 01xxx...xxx000 but
//    in the structure below the special handling of these bits is
//    explicit in the main computation; the scalar is just copied.
//
//  - The point x coord is reduced mod 2^255 by masking off the
//    top bit. In the main loop we only need reduction < 2 * p_25519.

        mov     rax, [rsi]
        mov     [rsp], rax
        mov     rax, [rsi+8]
        mov     [rsp+8], rax
        mov     rax, [rsi+16]
        mov     [rsp+16], rax
        mov     rax, [rsi+24]
        mov     [rsp+24], rax

        mov     r8, [rdx]
        mov     r9, [rdx+8]
        mov     r10, [rdx+16]
        mov     r11, [rdx+24]
        btr     r11, 63
        mov     [rsp+32], r8
        mov     [rsp+40], r9
        mov     [rsp+48], r10
        mov     [rsp+56], r11

// Initialize with explicit doubling in order to handle set bit 254.
// Set swap = 1 and (xm,zm) = (x,1) then double as (xn,zn) = 2 * (x,1).
// We use the fact that the point x coordinate is still in registers.
// Since zm = 1 we could do the doubling with an operation count of
// 2 * S + M instead of 2 * S + 2 * M, but it doesn't seem worth
// the slight complication arising from a different linear combination.

        mov     eax, 1
        mov     swap, rax
        mov     [rsp+256], r8
        mov     [rsp+96], rax
        xor     eax, eax
        mov     [rsp+264], r9
        mov     [rsp+104], rax
        mov     [rsp+272], r10
        mov     [rsp+112], rax
        mov     [rsp+280], r11
        mov     [rsp+120], rax

        sub_twice4(d,xm,zm)
        add_twice4(s,xm,zm)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

// The main loop over unmodified bits from i = 253, ..., i = 3 (inclusive).
// This is a classic Montgomery ladder, with the main coordinates only
// reduced mod 2 * p_25519, some intermediate results even more loosely.

        mov     eax, 253
        mov     i, rax

curve25519_x25519_alt_scalarloop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn

        sub_twice4(dm,xm,zm)
        add_twice4(sn,xn,zn)
        sub_twice4(dn,xn,zn)
        add_twice4(sm,xm,zm)

// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mov     rdx, i
        mov     rcx, rdx
        shr     rdx, 6
        mov     rdx, [rsp+8*rdx]
        shr     rdx, cl
        and     rdx, 1
        cmp     rdx, swap
        mov     swap, rdx
        mux_4(d,dm,dn)
        mux_4(s,sm,sn)

// ADDING: dmsn = dm * sn; dnsm = sm * dn

        mul_5(dnsm,sm,dn)
        mul_5(dmsn,sn,dm)

// DOUBLING: d = (xt - zt)^2

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2

        sub5_4(dpro,dmsn,dnsm)
        add5_4(spro,dmsn,dnsm)
        sqr_4(s,s)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: xm' = (dmsn + dnsm)^2

        sqr_4(xm,spro)

// DOUBLING: e = 121666 * p + d

        cmadd_4(e,0x1db42,p,d)

// DOUBLING: xn' = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_4(xn,s,d)

// DOUBLING: zn' = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//               = p * (d + 121666 * p)

        mul_4(zn,p,e)

// ADDING: zm' = x * (dmsn - dnsm)^2

        mul_4(zm,dpro,pointx)

// Loop down as far as 3 (inclusive)

        mov     rax, i
        sub     rax, 1
        mov     i, rax
        cmp     rax, 3
        jnc     curve25519_x25519_alt_scalarloop

// Multiplex directly into (xn,zn) then do three pure doubling steps;
// this accounts for the implicit zeroing of the three lowest bits
// of the scalar. On the very last doubling we *fully* reduce zn mod
// p_25519 to ease checking for degeneracy below.

        mov     rdx, swap
        test    rdx, rdx
        mux_4(xn,xm,xn)
        mux_4(zn,zm,zn)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_p25519(zn,p,e)

// The projective result of the scalar multiplication is now (xn,zn).
// First set up the constant sn = 2^255 - 19 for the modular inverse.

        mov     rax, -19
        mov     rcx, -1
        mov     rdx, 0x7fffffffffffffff
        mov     [rsp+128], rax
        mov     [rsp+136], rcx
        mov     [rsp+144], rcx
        mov     [rsp+152], rdx

// Prepare to call the modular inverse function to get zm = 1/zn

        mov     rdi, 4
        lea     rsi, [rsp+96]
        lea     rdx, [rsp+160]
        lea     rcx, [rsp+128]
        lea     r8, [rsp+192]

// Inline copy of bignum_modinv, identical except for stripping out the
// prologue and epilogue saving and restoring registers and the initial
// test for k = 0 (which is trivially false here since k = 4). For more
// details and explanations see "x86/generic/bignum_modinv.S". Note
// that the stack it uses for its own temporaries is 80 bytes so it
// only overwrites pointx, scalar and dm, which are no longer needed.

        mov     [rsp+0x40], rsi
        mov     [rsp+0x38], r8
        mov     [rsp+0x48], rcx
        lea     r10, [r8+8*rdi]
        mov     [rsp+0x30], r10
        lea     r15, [r10+8*rdi]
        xor     r11, r11
        xor     r9, r9
curve25519_x25519_alt_copyloop:
        mov     rax, [rdx+8*r9]
        mov     rbx, [rcx+8*r9]
        mov     [r10+8*r9], rax
        mov     [r15+8*r9], rbx
        mov     [r8+8*r9], rbx
        mov     [rsi+8*r9], r11
        inc     r9
        cmp     r9, rdi
        jb      curve25519_x25519_alt_copyloop
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
curve25519_x25519_alt_outerloop:
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
curve25519_x25519_alt_toploop:
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
        jb      curve25519_x25519_alt_toploop
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
curve25519_x25519_alt_innerloop:
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
        jne     curve25519_x25519_alt_innerloop
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
curve25519_x25519_alt_congloop:
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
        jb      curve25519_x25519_alt_congloop
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
        je      curve25519_x25519_alt_wmontend
curve25519_x25519_alt_wmontloop:
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
        jne     curve25519_x25519_alt_wmontloop
curve25519_x25519_alt_wmontend:
        adc     r10, r14
        mov     [r8+8*rdi-0x8], r10
        sbb     r10, r10
        neg     r10
        mov     rcx, rdi
        xor     r9, r9
curve25519_x25519_alt_wcmploop:
        mov     rax, [r8+8*r9]
        sbb     rax, [r15+8*r9]
        inc     r9
        dec     rcx
        jne     curve25519_x25519_alt_wcmploop
        sbb     r10, 0x0
        sbb     r10, r10
        not     r10
        xor     rcx, rcx
        xor     r9, r9
curve25519_x25519_alt_wcorrloop:
        mov     rax, [r8+8*r9]
        mov     rbx, [r15+8*r9]
        and     rbx, r10
        neg     rcx
        sbb     rax, rbx
        sbb     rcx, rcx
        mov     [r8+8*r9], rax
        inc     r9
        cmp     r9, rdi
        jb      curve25519_x25519_alt_wcorrloop
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
        je      curve25519_x25519_alt_zmontend
curve25519_x25519_alt_zmontloop:
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
        jne     curve25519_x25519_alt_zmontloop
curve25519_x25519_alt_zmontend:
        adc     r11, rsi
        mov     [r8+8*rdi-0x8], r11
        sbb     r11, r11
        neg     r11
        mov     rcx, rdi
        xor     r9, r9
curve25519_x25519_alt_zcmploop:
        mov     rax, [r8+8*r9]
        sbb     rax, [r15+8*r9]
        inc     r9
        dec     rcx
        jne     curve25519_x25519_alt_zcmploop
        sbb     r11, 0x0
        sbb     r11, r11
        not     r11
        xor     rcx, rcx
        xor     r9, r9
curve25519_x25519_alt_zcorrloop:
        mov     rax, [r8+8*r9]
        mov     rbx, [r15+8*r9]
        and     rbx, r11
        neg     rcx
        sbb     rax, rbx
        sbb     rcx, rcx
        mov     [r8+8*r9], rax
        inc     r9
        cmp     r9, rdi
        jb      curve25519_x25519_alt_zcorrloop
        mov     r8, [rsp+0x30]
        lea     r15, [r8+8*rdi]
        xor     r9, r9
        xor     r12, r12
        xor     r14, r14
        xor     rbp, rbp
        xor     rsi, rsi
curve25519_x25519_alt_crossloop:
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
        jb      curve25519_x25519_alt_crossloop
        xor     r9, r9
        mov     r10, r12
        mov     r11, rbp
        xor     r14, r12
        xor     rsi, rbp
curve25519_x25519_alt_optnegloop:
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
        jb      curve25519_x25519_alt_optnegloop
        sub     r14, r10
        sub     rsi, r11
        mov     r9, r13
curve25519_x25519_alt_shiftloop:
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
        jne     curve25519_x25519_alt_shiftloop
        not     rbp
        mov     rcx, [rsp+0x48]
        mov     r8, [rsp+0x38]
        mov     r15, [rsp+0x40]
        mov     r10, r12
        mov     r11, rbp
        xor     r9, r9
curve25519_x25519_alt_fliploop:
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
        jb      curve25519_x25519_alt_fliploop
        sub     QWORD PTR [rsp+0x20], 0x3a
        ja      curve25519_x25519_alt_outerloop

// Since we eventually want to return 0 when the result is the point at
// infinity, we force xn = 0 whenever zn = 0. This avoids building in a
// dependency on the behavior of modular inverse in out-of-scope cases.

        mov     rax, [rsp+160]
        or      rax, [rsp+168]
        or      rax, [rsp+176]
        or      rax, [rsp+184]
        mov     rcx, [rsp+320]
        cmovz   rcx, rax
        mov     [rsp+320], rcx
        mov     rcx, [rsp+328]
        cmovz   rcx, rax
        mov     [rsp+328], rcx
        mov     rcx, [rsp+336]
        cmovz   rcx, rax
        mov     [rsp+336], rcx
        mov     rcx, [rsp+344]
        cmovz   rcx, rax
        mov     [rsp+344], rcx

// Now the result is xn * (1/zn), fully reduced modulo p.

        mov     rbp, res
        mul_p25519(resx,xn,zm)

// Restore stack and registers

        add     rsp, NSPACE

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
