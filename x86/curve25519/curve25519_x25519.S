// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// The x25519 function for curve25519
// Inputs scalar[4], point[4]; output res[4]
//
// extern void curve25519_x25519
//   (uint64_t res[static 4],uint64_t scalar[static 4],uint64_t point[static 4])
//
// Given a scalar n and the X coordinate of an input point P = (X,Y) on
// curve25519 (Y can live in any extension field of characteristic 2^255-19),
// this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the
// point at infinity. Both n and X inputs are first slightly modified/mangled
// as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748);
// in particular the lower three bits of n are set to zero.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519)
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

// Macros wrapping up the basic field operation calls
// bignum_mul_p25519 and bignum_sqr_p25519.
// These two are only trivially different from pure
// function calls to those subroutines.

#define mul_p25519(P0,P1,P2)                    \
        xor    edi, edi;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x8];                   \
        mulx   rbx, rax, [P1];                  \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   r13, rax, [P1+0x18];             \
        adcx   r12, rax;                        \
        adox   r13, rdi;                        \
        adcx   r13, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x10];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   r14, rax, [P1+0x18];             \
        adcx   r13, rax;                        \
        adox   r14, rdi;                        \
        adcx   r14, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x18];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r13, rax;                        \
        adox   r14, rbx;                        \
        mulx   r15, rax, [P1+0x18];             \
        adcx   r14, rax;                        \
        adox   r15, rdi;                        \
        adcx   r15, rdi;                        \
        mov    edx, 0x26;                       \
        xor    edi, edi;                        \
        mulx   rbx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rbx;                         \
        mulx   rbx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rdi;                        \
        adcx   r12, rdi;                        \
        shld   r12, r11, 0x1;                   \
        mov    edx, 0x13;                       \
        inc    r12;                             \
        bts    r11, 63;                         \
        mulx   rbx, rax, r12;                   \
        add    r8, rax;                         \
        adc    r9, rbx;                         \
        adc    r10, rdi;                        \
        adc    r11, rdi;                        \
        sbb    rax, rax;                        \
        not    rax;                             \
        and    rax, rdx;                        \
        sub    r8, rax;                         \
        sbb    r9, rdi;                         \
        sbb    r10, rdi;                        \
        sbb    r11, rdi;                        \
        btr    r11, 63;                         \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

#define sqr_p25519(P0,P1)                       \
        mov    rdx, [P1];                       \
        mulx   r15, r8, rdx;                    \
        mulx   r10, r9, [P1+0x8];               \
        mulx   r12, r11, [P1+0x18];             \
        mov    rdx, [P1+0x10];                  \
        mulx   r14, r13, [P1+0x18];             \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rcx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rcx;                        \
        adcx   r13, rbx;                        \
        adox   r14, rbx;                        \
        adc    r14, rbx;                        \
        xor    ebx, ebx;                        \
        adcx   r9, r9;                          \
        adox   r9, r15;                         \
        mov    rdx, [P1+0x8];                   \
        mulx   rdx, rax, rdx;                   \
        adcx   r10, r10;                        \
        adox   r10, rax;                        \
        adcx   r11, r11;                        \
        adox   r11, rdx;                        \
        mov    rdx, [P1+0x10];                  \
        mulx   rdx, rax, rdx;                   \
        adcx   r12, r12;                        \
        adox   r12, rax;                        \
        adcx   r13, r13;                        \
        adox   r13, rdx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   r15, rax, rdx;                   \
        adcx   r14, r14;                        \
        adox   r14, rax;                        \
        adcx   r15, rbx;                        \
        adox   r15, rbx;                        \
        mov    edx, 0x26;                       \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rcx;                         \
        mulx   rcx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rcx;                        \
        mulx   rcx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        adcx   r12, rbx;                        \
        shld   r12, r11, 0x1;                   \
        mov    edx, 0x13;                       \
        lea    rax, [r12+0x1];                  \
        bts    r11, 0x3f;                       \
        imul   rax, rdx;                        \
        add    r8, rax;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        cmovb  rdx, rbx;                        \
        sub    r8, rdx;                         \
        sbb    r9, rbx;                         \
        sbb    r10, rbx;                        \
        sbb    r11, rbx;                        \
        btr    r11, 0x3f;                       \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Multiplication just giving a 5-digit result (actually < 39 * p_25519)
// by not doing anything beyond the first stage of reduction

#define mul_5(P0,P1,P2)                         \
        xor    edi, edi;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x8];                   \
        mulx   rbx, rax, [P1];                  \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   r13, rax, [P1+0x18];             \
        adcx   r12, rax;                        \
        adox   r13, rdi;                        \
        adcx   r13, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x10];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   r14, rax, [P1+0x18];             \
        adcx   r13, rax;                        \
        adox   r14, rdi;                        \
        adcx   r14, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x18];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r13, rax;                        \
        adox   r14, rbx;                        \
        mulx   r15, rax, [P1+0x18];             \
        adcx   r14, rax;                        \
        adox   r15, rdi;                        \
        adcx   r15, rdi;                        \
        mov    edx, 0x26;                       \
        xor    edi, edi;                        \
        mulx   rbx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rbx;                         \
        mulx   rbx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rdi;                        \
        adcx   r12, rdi;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11;                  \
        mov    [P0+0x20], r12

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        mov    rdx, [P1];                       \
        mulx   r15, r8, rdx;                    \
        mulx   r10, r9, [P1+0x8];               \
        mulx   r12, r11, [P1+0x18];             \
        mov    rdx, [P1+0x10];                  \
        mulx   r14, r13, [P1+0x18];             \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rcx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rcx;                        \
        adcx   r13, rbx;                        \
        adox   r14, rbx;                        \
        adc    r14, rbx;                        \
        xor    ebx, ebx;                        \
        adcx   r9, r9;                          \
        adox   r9, r15;                         \
        mov    rdx, [P1+0x8];                   \
        mulx   rdx, rax, rdx;                   \
        adcx   r10, r10;                        \
        adox   r10, rax;                        \
        adcx   r11, r11;                        \
        adox   r11, rdx;                        \
        mov    rdx, [P1+0x10];                  \
        mulx   rdx, rax, rdx;                   \
        adcx   r12, r12;                        \
        adox   r12, rax;                        \
        adcx   r13, r13;                        \
        adox   r13, rdx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   r15, rax, rdx;                   \
        adcx   r14, r14;                        \
        adox   r14, rax;                        \
        adcx   r15, rbx;                        \
        adox   r15, rbx;                        \
        mov    edx, 0x26;                       \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rcx;                         \
        mulx   rcx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rcx;                        \
        mulx   rcx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        adcx   r12, rbx;                        \
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

// Plain 4-digit add without any normalization
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result

#define add_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        add     rax, [P2];                      \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        adc     rax, [P2+8];                    \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        adc     rax, [P2+16];                   \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        adc     rax, [P2+24];                   \
        mov     [P0+24], rax

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

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

#define sub_4(P0,P1,P2)                         \
        mov     r8, [P1];                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     rax, [P1+24];                   \
        sbb     rax, [P2+24];                   \
        sub     r8, 19;                         \
        mov     [P0], r8;                       \
        sbb     r9, 0;                          \
        mov     [P0+8], r9;                     \
        sbb     r10, 0;                         \
        mov     [P0+16], r10;                   \
        sbb     rax, 0;                         \
        btc     rax, 63;                        \
        mov     [P0+24], rax

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

// Combined z = c * x + y with reduction only < 2 * p_25519
// It is assumed that 19 * (c * x + y) < 2^60 * 2^256 so we
// don't need a high mul in the final part.

#define cmadd_4(P0,C1,P2,P3)                    \
        mov     r8, [P3];                       \
        mov     r9, [P3+8];                     \
        mov     r10, [P3+16];                   \
        mov     r11, [P3+24];                   \
        xor     edi, edi;                       \
        mov     rdx, C1;                        \
        mulx    rbx, rax, [P2];                 \
        adcx    r8, rax;                        \
        adox    r9, rbx;                        \
        mulx    rbx, rax, [P2+8];               \
        adcx    r9, rax;                        \
        adox    r10, rbx;                       \
        mulx    rbx, rax, [P2+16];              \
        adcx    r10, rax;                       \
        adox    r11, rbx;                       \
        mulx    rbx, rax, [P2+24];              \
        adcx    r11, rax;                       \
        adox    rbx, rdi;                       \
        adcx    rbx, rdi;                       \
        shld    rbx, r11, 0x1;                  \
        btr     r11, 63;                        \
        mov     edx, 0x13;                      \
        imul    rbx, rdx;                       \
        add     r8, rbx;                        \
        adc     r9, rdi;                        \
        adc     r10, rdi;                       \
        adc     r11, rdi;                       \
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

S2N_BN_SYMBOL(curve25519_x25519):

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

// Copy the inputs to the local variables while mangling them:
//
//  - The scalar gets turned into 01xxx...xxx000 by tweaking bits.
//    Actually the top zero doesn't matter since the loop below
//    never looks at it, so we don't literally modify that.
//
//  - The point x coord is reduced mod 2^255 *then* mod 2^255-19

        mov     rax, [rsi]
        and     rax, ~7
        mov     [rsp], rax
        mov     rax, [rsi+8]
        mov     [rsp+8], rax
        mov     rax, [rsi+16]
        mov     [rsp+16], rax
        mov     rax, [rsi+24]
        bts     rax, 62
        mov     [rsp+24], rax

        mov     r8, [rdx]
        mov     r9, [rdx+8]
        mov     r10, [rdx+16]
        mov     r11, [rdx+24]
        btr     r11, 63
        mov     r12, 19
        xor     r13, r13
        xor     r14, r14
        xor     r15, r15
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        btr     r15, 63         // x >= 2^255 - 19 <=> x + 19 >= 2^255
        cmovc   r8, r12
        mov     [rsp+32], r8
        cmovc   r9, r13
        mov     [rsp+40], r9
        cmovc   r10, r14
        mov     [rsp+48], r10
        cmovc   r11, r15
        mov     [rsp+56], r11

// Initialize (xn,zn) = (1,0) and (xm,zm) = (x,1) with swap = 0
// We use the fact that the point x coordinate is still in registers

        mov     rax, 1
        mov     [rsp+320], rax
        mov     [rsp+96], rax
        xor     eax, eax
        mov     swap, rax
        mov     [rsp+160], rax
        mov     [rsp+328], rax
        mov     [rsp+104], rax
        mov     [rsp+168], rax
        mov     [rsp+336], rax
        mov     [rsp+112], rax
        mov     [rsp+176], rax
        mov     [rsp+344], rax
        mov     [rsp+120], rax
        mov     [rsp+184], rax
        mov     rax, [rsp+32]
        mov     [rsp+256], r8
        mov     [rsp+264], r9
        mov     [rsp+272], r10
        mov     [rsp+280], r11

// The outer loop over scalar bits from i = 254, ..., i = 0 (inclusive)
// This starts at 254, and so implicitly masks bit 255 of the scalar.

        mov     eax, 254
        mov     i, rax

scalarloop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn
// The adds don't need any normalization as they're fed to muls
// Just make sure the subs fit in 4 digits.

        sub_4(dm,xm,zm)
        add_4(sn,xn,zn)
        sub_4(dn,xn,zn)
        add_4(sm,xm,zm)

// ADDING: dmsn = dm * sn; dnsm = sm * dn
// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mul_5(dmsn,sn,dm)

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

        mul_5(dnsm,sm,dn)

// DOUBLING: d = (xt - zt)^2 normalized only to 4 digits

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2, normalized only to 4 digits

        sub5_4(dpro,dmsn,dnsm)
        sqr_4(s,s)
        add5_4(spro,dmsn,dnsm)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: xm' = (dmsn + dnsm)^2

        sqr_p25519(xm,spro)

// DOUBLING: e = 121666 * p + d

        cmadd_4(e,0x1db42,p,d)

// DOUBLING: xn' = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_p25519(xn,s,d)

// ADDING: zm' = x * (dmsn - dnsm)^2

        mul_p25519(zm,dpro,pointx)

// DOUBLING: zn' = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//               = p * (d + 121666 * p)

        mul_p25519(zn,p,e)

// Loop down as far as 0 (inclusive)

        mov     rax, i
        sub     rax, 1
        mov     i, rax
        jnc     scalarloop

// Since the scalar was forced to be a multiple of 8, we know it's even.
// Hence there is no need to multiplex: the projective answer is (xn,zn)
// and we can ignore (xm,zm); indeed we could have avoided the last three
// differential additions and just done the doublings.
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
copyloop:
        mov     rax, [rdx+8*r9]
        mov     rbx, [rcx+8*r9]
        mov     [r10+8*r9], rax
        mov     [r15+8*r9], rbx
        mov     [r8+8*r9], rbx
        mov     [rsi+8*r9], r11
        inc     r9
        cmp     r9, rdi
        jb      copyloop
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
outerloop:
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
toploop:
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
        jb      toploop
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
innerloop:
        mov     rax, rbp
        mov     rdi, rsi
        mov     r13, rcx
        mov     r15, rdx
        mov     rbx, 0x1
        neg     rdi
        and     rbx, r14
        cmove   rax, rbx
        cmove   rdi, rbx
        cmove   r13, rbx
        cmove   r15, rbx
        mov     rbx, r12
        add     rdi, r14
        mov     r8, rdi
        neg     rdi
        sub     rbx, rax
        cmovb   rbp, r12
        cmovb   rsi, r14
        cmovb   rcx, r10
        cmovb   rdx, r11
        cmovae  rdi, r8
        mov     r12, rbx
        not     rbx
        inc     rbx
        cmovb   r12, rbx
        mov     r14, rdi
        add     r10, r13
        add     r11, r15
        shr     r12, 1
        shr     r14, 1
        lea     rcx, [rcx+rcx]
        lea     rdx, [rdx+rdx]
        dec     r9
        jne     innerloop
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
congloop:
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
        jb      congloop
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
        je      wmontend
wmontloop:
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
        jne     wmontloop
wmontend:
        adc     r10, r14
        mov     [r8+8*rdi-0x8], r10
        sbb     r10, r10
        neg     r10
        mov     rcx, rdi
        xor     r9, r9
wcmploop:
        mov     rax, [r8+8*r9]
        sbb     rax, [r15+8*r9]
        inc     r9
        dec     rcx
        jne     wcmploop
        sbb     r10, 0x0
        sbb     r10, r10
        not     r10
        xor     rcx, rcx
        xor     r9, r9
wcorrloop:
        mov     rax, [r8+8*r9]
        mov     rbx, [r15+8*r9]
        and     rbx, r10
        neg     rcx
        sbb     rax, rbx
        sbb     rcx, rcx
        mov     [r8+8*r9], rax
        inc     r9
        cmp     r9, rdi
        jb      wcorrloop
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
        je      zmontend
zmontloop:
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
        jne     zmontloop
zmontend:
        adc     r11, rsi
        mov     [r8+8*rdi-0x8], r11
        sbb     r11, r11
        neg     r11
        mov     rcx, rdi
        xor     r9, r9
zcmploop:
        mov     rax, [r8+8*r9]
        sbb     rax, [r15+8*r9]
        inc     r9
        dec     rcx
        jne     zcmploop
        sbb     r11, 0x0
        sbb     r11, r11
        not     r11
        xor     rcx, rcx
        xor     r9, r9
zcorrloop:
        mov     rax, [r8+8*r9]
        mov     rbx, [r15+8*r9]
        and     rbx, r11
        neg     rcx
        sbb     rax, rbx
        sbb     rcx, rcx
        mov     [r8+8*r9], rax
        inc     r9
        cmp     r9, rdi
        jb      zcorrloop
        mov     r8, [rsp+0x30]
        lea     r15, [r8+8*rdi]
        xor     r9, r9
        xor     r12, r12
        xor     r14, r14
        xor     rbp, rbp
        xor     rsi, rsi
crossloop:
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
        jb      crossloop
        xor     r9, r9
        mov     r10, r12
        mov     r11, rbp
        xor     r14, r12
        xor     rsi, rbp
optnegloop:
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
        jb      optnegloop
        sub     r14, r10
        sub     rsi, r11
        mov     r9, r13
shiftloop:
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
        jne     shiftloop
        not     rbp
        mov     rcx, [rsp+0x48]
        mov     r8, [rsp+0x38]
        mov     r15, [rsp+0x40]
        mov     r10, r12
        mov     r11, rbp
        xor     r9, r9
fliploop:
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
        jb      fliploop
        sub     QWORD PTR [rsp+0x20], 0x3a
        ja      outerloop

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

// Now the result is xn * (1/zn).

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
