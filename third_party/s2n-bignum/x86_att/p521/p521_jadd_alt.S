// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jadd_alt
//      (uint64_t p3[static 27],uint64_t p1[static 27],uint64_t p2[static 27]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input points p1 and p2 are
// fully reduced mod p_521, that both z coordinates are nonzero and
// that neither p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents
// the same affine point as".
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jadd_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jadd_alt)
        .text

// Size of individual field elements

#define NUMSIZE 72

// Stable homes for input arguments during main code sequence
// These are where they arrive except for input_y, initially in %rdx

#define input_z %rdi
#define input_x %rsi
#define input_y %rcx

// Pointer-offset pairs for inputs and outputs

#define x_1 0(input_x)
#define y_1 NUMSIZE(input_x)
#define z_1 (2*NUMSIZE)(input_x)

#define x_2 0(input_y)
#define y_2 NUMSIZE(input_y)
#define z_2 (2*NUMSIZE)(input_y)

#define x_3 0(input_z)
#define y_3 NUMSIZE(input_z)
#define z_3 (2*NUMSIZE)(input_z)

// Pointer-offset pairs for temporaries, with some aliasing
// The tmp field is internal storage for field mul and sqr.
// NSPACE is the total stack needed for these temporaries

#define z1sq (NUMSIZE*0)(%rsp)
#define ww (NUMSIZE*0)(%rsp)
#define resx (NUMSIZE*0)(%rsp)

#define yd (NUMSIZE*1)(%rsp)
#define y2a (NUMSIZE*1)(%rsp)

#define x2a (NUMSIZE*2)(%rsp)
#define zzx2 (NUMSIZE*2)(%rsp)

#define zz (NUMSIZE*3)(%rsp)
#define t1 (NUMSIZE*3)(%rsp)

#define t2 (NUMSIZE*4)(%rsp)
#define x1a (NUMSIZE*4)(%rsp)
#define zzx1 (NUMSIZE*4)(%rsp)
#define resy (NUMSIZE*4)(%rsp)

#define xd (NUMSIZE*5)(%rsp)
#define z2sq (NUMSIZE*5)(%rsp)
#define resz (NUMSIZE*5)(%rsp)

#define y1a (NUMSIZE*6)(%rsp)

#define tmp (NUMSIZE*7)(%rsp)

#define NSPACE (NUMSIZE*8)

// Corresponds exactly to bignum_mul_p521_alt except temp storage

#define mul_p521(P0,P1,P2)                      \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     P2 ASM_LINE_END                 \
        movq    %rax, 504(%rsp)  ASM_LINE_END                 \
        movq    %rdx, %r9  ASM_LINE_END                        \
        xorq    %r10, %r10  ASM_LINE_END                       \
        xorq    %r11, %r11  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    %r11, %r11  ASM_LINE_END                       \
        movq    %r9, 512(%rsp)  ASM_LINE_END                  \
        xorq    %r12, %r12  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    %r12, %r12  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    %r10, 520(%rsp)  ASM_LINE_END                 \
        xorq    %r13, %r13  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    %r13, %r13  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    %r11, 528(%rsp)  ASM_LINE_END                 \
        xorq    %r14, %r14  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    %r14, %r14  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    %r12, 536(%rsp)  ASM_LINE_END                 \
        xorq    %r15, %r15  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    %r15, %r15  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    %r13, 544(%rsp)  ASM_LINE_END                 \
        xorq    %r8, %r8  ASM_LINE_END                         \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    %r8, %r8  ASM_LINE_END                         \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    %r14, 552(%rsp)  ASM_LINE_END                 \
        xorq    %r9, %r9  ASM_LINE_END                         \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    %r9, %r9  ASM_LINE_END                         \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    %r15, 560(%rsp)  ASM_LINE_END                 \
        xorq    %r10, %r10  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    %r10, %r10  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     P2 ASM_LINE_END                 \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    %r8, 568(%rsp)  ASM_LINE_END                  \
        xorq    %r11, %r11  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    %r11, %r11  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     0x8+P2 ASM_LINE_END             \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        xorq    %r12, %r12  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    %r12, %r12  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     0x10+P2 ASM_LINE_END            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        xorq    %r13, %r13  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    %r13, %r13  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P2 ASM_LINE_END            \
        addq    %rax, %r11  ASM_LINE_END                       \
        adcq    %rdx, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        xorq    %r14, %r14  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    %r14, %r14  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P2 ASM_LINE_END            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        xorq    %r15, %r15  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    %r15, %r15  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P2 ASM_LINE_END            \
        addq    %rax, %r13  ASM_LINE_END                       \
        adcq    %rdx, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        xorq    %r8, %r8  ASM_LINE_END                         \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    %r8, %r8  ASM_LINE_END                         \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P2 ASM_LINE_END            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P2 ASM_LINE_END            \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        imulq   0x40+P2, %rax  ASM_LINE_END                 \
        addq    %r8, %rax  ASM_LINE_END                        \
        movq    568(%rsp), %r8  ASM_LINE_END                  \
        movq    %r8, %rdx  ASM_LINE_END                        \
        andq    $0x1ff, %rdx  ASM_LINE_END                     \
        shrdq   $0x9, %r9, %r8  ASM_LINE_END                    \
        shrdq   $0x9, %r10, %r9  ASM_LINE_END                   \
        shrdq   $0x9, %r11, %r10  ASM_LINE_END                  \
        shrdq   $0x9, %r12, %r11  ASM_LINE_END                  \
        shrdq   $0x9, %r13, %r12  ASM_LINE_END                  \
        shrdq   $0x9, %r14, %r13  ASM_LINE_END                  \
        shrdq   $0x9, %r15, %r14  ASM_LINE_END                  \
        shrdq   $0x9, %rax, %r15  ASM_LINE_END                  \
        shrq    $0x9, %rax  ASM_LINE_END                       \
        addq    %rax, %rdx  ASM_LINE_END                       \
        stc ASM_LINE_END                                    \
        adcq    504(%rsp), %r8  ASM_LINE_END                  \
        adcq    512(%rsp), %r9  ASM_LINE_END                  \
        adcq    520(%rsp), %r10  ASM_LINE_END                 \
        adcq    528(%rsp), %r11  ASM_LINE_END                 \
        adcq    536(%rsp), %r12  ASM_LINE_END                 \
        adcq    544(%rsp), %r13  ASM_LINE_END                 \
        adcq    552(%rsp), %r14  ASM_LINE_END                 \
        adcq    560(%rsp), %r15  ASM_LINE_END                 \
        adcq    $0xfffffffffffffe00, %rdx  ASM_LINE_END        \
        cmc ASM_LINE_END                                    \
        sbbq    $0x0, %r8  ASM_LINE_END                        \
        movq    %r8, P0  ASM_LINE_END                       \
        sbbq    $0x0, %r9  ASM_LINE_END                        \
        movq    %r9, 0x8+P0  ASM_LINE_END                   \
        sbbq    $0x0, %r10  ASM_LINE_END                       \
        movq    %r10, 0x10+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r11  ASM_LINE_END                       \
        movq    %r11, 0x18+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r12  ASM_LINE_END                       \
        movq    %r12, 0x20+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r13  ASM_LINE_END                       \
        movq    %r13, 0x28+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r14  ASM_LINE_END                       \
        movq    %r14, 0x30+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r15  ASM_LINE_END                       \
        movq    %r15, 0x38+P0  ASM_LINE_END                 \
        sbbq    $0x0, %rdx  ASM_LINE_END                       \
        andq    $0x1ff, %rdx  ASM_LINE_END                     \
        movq    %rdx, 0x40+P0

// Corresponds to bignum_sqr_p521_alt except %rbp is used
// in place of %rcx and tmp is the temp storage location

#define sqr_p521(P0,P1)                         \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq    %rax ASM_LINE_END                            \
        movq    %rax, 504(%rsp)  ASM_LINE_END                 \
        movq    %rdx, %r9  ASM_LINE_END                        \
        xorq    %r10, %r10  ASM_LINE_END                       \
        xorq    %r11, %r11  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x8+P1 ASM_LINE_END             \
        addq    %rax, %rax  ASM_LINE_END                       \
        adcq    %rdx, %rdx  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        addq    %rax, %r9  ASM_LINE_END                        \
        adcq    %rdx, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    %r9, 512(%rsp)  ASM_LINE_END                  \
        xorq    %r12, %r12  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq    %rax ASM_LINE_END                            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x10+P1 ASM_LINE_END            \
        addq    %rax, %rax  ASM_LINE_END                       \
        adcq    %rdx, %rdx  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    %r10, 520(%rsp)  ASM_LINE_END                 \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x18+P1 ASM_LINE_END            \
        xorq    %r13, %r13  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x10+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r13, %r13  ASM_LINE_END                       \
        addq    %rbx, %r11  ASM_LINE_END                       \
        adcq    %rbp, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    %r11, 528(%rsp)  ASM_LINE_END                 \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x20+P1 ASM_LINE_END            \
        xorq    %r14, %r14  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x18+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r14, %r14  ASM_LINE_END                       \
        addq    %rbx, %r12  ASM_LINE_END                       \
        adcq    %rbp, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq    %rax ASM_LINE_END                            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    %r12, 536(%rsp)  ASM_LINE_END                 \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x28+P1 ASM_LINE_END            \
        xorq    %r15, %r15  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x20+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x18+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r15, %r15  ASM_LINE_END                       \
        addq    %rbx, %r13  ASM_LINE_END                       \
        adcq    %rbp, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        movq    %r13, 544(%rsp)  ASM_LINE_END                 \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x30+P1 ASM_LINE_END            \
        xorq    %r8, %r8  ASM_LINE_END                         \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x28+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r8, %r8  ASM_LINE_END                         \
        addq    %rbx, %r14  ASM_LINE_END                       \
        adcq    %rbp, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq    %rax ASM_LINE_END                            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    %r14, 552(%rsp)  ASM_LINE_END                 \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x38+P1 ASM_LINE_END            \
        xorq    %r9, %r9  ASM_LINE_END                         \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x30+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x20+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r9, %r9  ASM_LINE_END                         \
        addq    %rbx, %r15  ASM_LINE_END                       \
        adcq    %rbp, %r8  ASM_LINE_END                        \
        adcq    $0x0, %r9  ASM_LINE_END                        \
        movq    %r15, 560(%rsp)  ASM_LINE_END                 \
        movq    P1, %rax  ASM_LINE_END                      \
        mulq     0x40+P1 ASM_LINE_END            \
        xorq    %r10, %r10  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x38+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r10, %r10  ASM_LINE_END                       \
        addq    %rbx, %r8  ASM_LINE_END                        \
        adcq    %rbp, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq    %rax ASM_LINE_END                            \
        addq    %rax, %r8  ASM_LINE_END                        \
        adcq    %rdx, %r9  ASM_LINE_END                        \
        adcq    $0x0, %r10  ASM_LINE_END                       \
        movq    %r8, 568(%rsp)  ASM_LINE_END                  \
        movq    0x8+P1, %rax  ASM_LINE_END                  \
        mulq     0x40+P1 ASM_LINE_END            \
        xorq    %r11, %r11  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x28+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r11, %r11  ASM_LINE_END                       \
        addq    %rbx, %r9  ASM_LINE_END                        \
        adcq    %rbp, %r10  ASM_LINE_END                       \
        adcq    $0x0, %r11  ASM_LINE_END                       \
        movq    0x10+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P1 ASM_LINE_END            \
        xorq    %r12, %r12  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r12, %r12  ASM_LINE_END                       \
        addq    %rbx, %r10  ASM_LINE_END                       \
        adcq    %rbp, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq    %rax ASM_LINE_END                            \
        addq    %rax, %r10  ASM_LINE_END                       \
        adcq    %rdx, %r11  ASM_LINE_END                       \
        adcq    $0x0, %r12  ASM_LINE_END                       \
        movq    0x18+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P1 ASM_LINE_END            \
        xorq    %r13, %r13  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x30+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r13, %r13  ASM_LINE_END                       \
        addq    %rbx, %r11  ASM_LINE_END                       \
        adcq    %rbp, %r12  ASM_LINE_END                       \
        adcq    $0x0, %r13  ASM_LINE_END                       \
        movq    0x20+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P1 ASM_LINE_END            \
        xorq    %r14, %r14  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r14, %r14  ASM_LINE_END                       \
        addq    %rbx, %r12  ASM_LINE_END                       \
        adcq    %rbp, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq    %rax ASM_LINE_END                            \
        addq    %rax, %r12  ASM_LINE_END                       \
        adcq    %rdx, %r13  ASM_LINE_END                       \
        adcq    $0x0, %r14  ASM_LINE_END                       \
        movq    0x28+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P1 ASM_LINE_END            \
        xorq    %r15, %r15  ASM_LINE_END                       \
        movq    %rax, %rbx  ASM_LINE_END                       \
        movq    %rdx, %rbp  ASM_LINE_END                       \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x38+P1 ASM_LINE_END            \
        addq    %rax, %rbx  ASM_LINE_END                       \
        adcq    %rdx, %rbp  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        addq    %rbx, %rbx  ASM_LINE_END                       \
        adcq    %rbp, %rbp  ASM_LINE_END                       \
        adcq    %r15, %r15  ASM_LINE_END                       \
        addq    %rbx, %r13  ASM_LINE_END                       \
        adcq    %rbp, %r14  ASM_LINE_END                       \
        adcq    $0x0, %r15  ASM_LINE_END                       \
        xorq    %r8, %r8  ASM_LINE_END                         \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq    %rax ASM_LINE_END                            \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x30+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P1 ASM_LINE_END            \
        addq    %rax, %rax  ASM_LINE_END                       \
        adcq    %rdx, %rdx  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        addq    %rax, %r14  ASM_LINE_END                       \
        adcq    %rdx, %r15  ASM_LINE_END                       \
        adcq    $0x0, %r8  ASM_LINE_END                        \
        movq    0x38+P1, %rax  ASM_LINE_END                 \
        mulq     0x40+P1 ASM_LINE_END            \
        addq    %rax, %rax  ASM_LINE_END                       \
        adcq    %rdx, %rdx  ASM_LINE_END                       \
        addq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        movq    0x40+P1, %rax  ASM_LINE_END                 \
        imulq   %rax, %rax  ASM_LINE_END                       \
        addq    %r8, %rax  ASM_LINE_END                        \
        movq    568(%rsp), %r8  ASM_LINE_END                  \
        movq    %r8, %rdx  ASM_LINE_END                        \
        andq    $0x1ff, %rdx  ASM_LINE_END                     \
        shrdq   $0x9, %r9, %r8  ASM_LINE_END                    \
        shrdq   $0x9, %r10, %r9  ASM_LINE_END                   \
        shrdq   $0x9, %r11, %r10  ASM_LINE_END                  \
        shrdq   $0x9, %r12, %r11  ASM_LINE_END                  \
        shrdq   $0x9, %r13, %r12  ASM_LINE_END                  \
        shrdq   $0x9, %r14, %r13  ASM_LINE_END                  \
        shrdq   $0x9, %r15, %r14  ASM_LINE_END                  \
        shrdq   $0x9, %rax, %r15  ASM_LINE_END                  \
        shrq    $0x9, %rax  ASM_LINE_END                       \
        addq    %rax, %rdx  ASM_LINE_END                       \
        stc ASM_LINE_END                                    \
        adcq    504(%rsp), %r8  ASM_LINE_END                  \
        adcq    512(%rsp), %r9  ASM_LINE_END                  \
        adcq    520(%rsp), %r10  ASM_LINE_END                 \
        adcq    528(%rsp), %r11  ASM_LINE_END                 \
        adcq    536(%rsp), %r12  ASM_LINE_END                 \
        adcq    544(%rsp), %r13  ASM_LINE_END                 \
        adcq    552(%rsp), %r14  ASM_LINE_END                 \
        adcq    560(%rsp), %r15  ASM_LINE_END                 \
        adcq    $0xfffffffffffffe00, %rdx  ASM_LINE_END        \
        cmc ASM_LINE_END                                    \
        sbbq    $0x0, %r8  ASM_LINE_END                        \
        movq    %r8, P0  ASM_LINE_END                       \
        sbbq    $0x0, %r9  ASM_LINE_END                        \
        movq    %r9, 0x8+P0  ASM_LINE_END                   \
        sbbq    $0x0, %r10  ASM_LINE_END                       \
        movq    %r10, 0x10+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r11  ASM_LINE_END                       \
        movq    %r11, 0x18+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r12  ASM_LINE_END                       \
        movq    %r12, 0x20+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r13  ASM_LINE_END                       \
        movq    %r13, 0x28+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r14  ASM_LINE_END                       \
        movq    %r14, 0x30+P0  ASM_LINE_END                 \
        sbbq    $0x0, %r15  ASM_LINE_END                       \
        movq    %r15, 0x38+P0  ASM_LINE_END                 \
        sbbq    $0x0, %rdx  ASM_LINE_END                       \
        andq    $0x1ff, %rdx  ASM_LINE_END                     \
        movq    %rdx, 0x40+P0

// Corresponds exactly to bignum_sub_p521

#define sub_p521(P0,P1,P2)                      \
        movq    P1, %rax  ASM_LINE_END                       \
        subq    P2, %rax  ASM_LINE_END                       \
        movq    0x8+P1, %rdx  ASM_LINE_END                   \
        sbbq    0x8+P2, %rdx  ASM_LINE_END                   \
        movq    0x10+P1, %r8  ASM_LINE_END                   \
        sbbq    0x10+P2, %r8  ASM_LINE_END                   \
        movq    0x18+P1, %r9  ASM_LINE_END                   \
        sbbq    0x18+P2, %r9  ASM_LINE_END                   \
        movq    0x20+P1, %r10  ASM_LINE_END                  \
        sbbq    0x20+P2, %r10  ASM_LINE_END                  \
        movq    0x28+P1, %r11  ASM_LINE_END                  \
        sbbq    0x28+P2, %r11  ASM_LINE_END                  \
        movq    0x30+P1, %r12  ASM_LINE_END                  \
        sbbq    0x30+P2, %r12  ASM_LINE_END                  \
        movq    0x38+P1, %r13  ASM_LINE_END                  \
        sbbq    0x38+P2, %r13  ASM_LINE_END                  \
        movq    0x40+P1, %r14  ASM_LINE_END                  \
        sbbq    0x40+P2, %r14  ASM_LINE_END                  \
        sbbq    $0x0, %rax  ASM_LINE_END                        \
        movq    %rax, P0  ASM_LINE_END                       \
        sbbq    $0x0, %rdx  ASM_LINE_END                        \
        movq    %rdx, 0x8+P0  ASM_LINE_END                   \
        sbbq    $0x0, %r8  ASM_LINE_END                         \
        movq    %r8, 0x10+P0  ASM_LINE_END                   \
        sbbq    $0x0, %r9  ASM_LINE_END                         \
        movq    %r9, 0x18+P0  ASM_LINE_END                   \
        sbbq    $0x0, %r10  ASM_LINE_END                        \
        movq    %r10, 0x20+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r11  ASM_LINE_END                        \
        movq    %r11, 0x28+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r12  ASM_LINE_END                        \
        movq    %r12, 0x30+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r13  ASM_LINE_END                        \
        movq    %r13, 0x38+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r14  ASM_LINE_END                        \
        andq    $0x1ff, %r14  ASM_LINE_END                      \
        movq    %r14, 0x40+P0

// Additional macros to help with final multiplexing

#define load9(r0,r1,r2,r3,r4,r5,r6,r7,ra,P)     \
        movq    P, r0  ASM_LINE_END                        \
        movq    8+P, r1  ASM_LINE_END                      \
        movq    16+P, r2  ASM_LINE_END                     \
        movq    24+P, r3  ASM_LINE_END                     \
        movq    32+P, r4  ASM_LINE_END                     \
        movq    40+P, r5  ASM_LINE_END                     \
        movq    48+P, r6  ASM_LINE_END                     \
        movq    56+P, r7  ASM_LINE_END                     \
        movq    64+P, ra

#define store9(P,r0,r1,r2,r3,r4,r5,r6,r7,ra)    \
        movq    r0, P  ASM_LINE_END                        \
        movq    r1, 8+P  ASM_LINE_END                      \
        movq    r2, 16+P  ASM_LINE_END                     \
        movq    r3, 24+P  ASM_LINE_END                     \
        movq    r4, 32+P  ASM_LINE_END                     \
        movq    r5, 40+P  ASM_LINE_END                     \
        movq    r6, 48+P  ASM_LINE_END                     \
        movq    r7, 56+P  ASM_LINE_END                     \
        movq    ra, 64+P

#define muxload9(r0,r1,r2,r3,r4,r5,r6,r7,ra,P0,P1,P2)   \
        movq    P0, r0  ASM_LINE_END                               \
        cmovbq  P1, r0  ASM_LINE_END                               \
        cmovnbe P2, r0  ASM_LINE_END                               \
        movq    8+P0, r1  ASM_LINE_END                             \
        cmovbq  8+P1, r1  ASM_LINE_END                             \
        cmovnbe 8+P2, r1  ASM_LINE_END                             \
        movq    16+P0, r2  ASM_LINE_END                            \
        cmovbq  16+P1, r2  ASM_LINE_END                            \
        cmovnbe 16+P2, r2  ASM_LINE_END                            \
        movq    24+P0, r3  ASM_LINE_END                            \
        cmovbq  24+P1, r3  ASM_LINE_END                            \
        cmovnbe 24+P2, r3  ASM_LINE_END                            \
        movq    32+P0, r4  ASM_LINE_END                            \
        cmovbq  32+P1, r4  ASM_LINE_END                            \
        cmovnbe 32+P2, r4  ASM_LINE_END                            \
        movq    40+P0, r5  ASM_LINE_END                            \
        cmovbq  40+P1, r5  ASM_LINE_END                            \
        cmovnbe 40+P2, r5  ASM_LINE_END                            \
        movq    48+P0, r6  ASM_LINE_END                            \
        cmovbq  48+P1, r6  ASM_LINE_END                            \
        cmovnbe 48+P2, r6  ASM_LINE_END                            \
        movq    56+P0, r7  ASM_LINE_END                            \
        cmovbq  56+P1, r7  ASM_LINE_END                            \
        cmovnbe 56+P2, r7  ASM_LINE_END                            \
        movq    64+P0, ra  ASM_LINE_END                            \
        cmovbq  64+P1, ra  ASM_LINE_END                            \
        cmovnbe 64+P2, ra

#define copy9(P0,P1)                            \
        movq    P1, %rax  ASM_LINE_END                       \
        movq    %rax, P0  ASM_LINE_END                       \
        movq    8+P1, %rax  ASM_LINE_END                     \
        movq    %rax, 8+P0  ASM_LINE_END                     \
        movq    16+P1, %rax  ASM_LINE_END                    \
        movq    %rax, 16+P0  ASM_LINE_END                    \
        movq    24+P1, %rax  ASM_LINE_END                    \
        movq    %rax, 24+P0  ASM_LINE_END                    \
        movq    32+P1, %rax  ASM_LINE_END                    \
        movq    %rax, 32+P0  ASM_LINE_END                    \
        movq    40+P1, %rax  ASM_LINE_END                    \
        movq    %rax, 40+P0  ASM_LINE_END                    \
        movq    48+P1, %rax  ASM_LINE_END                    \
        movq    %rax, 48+P0  ASM_LINE_END                    \
        movq    56+P1, %rax  ASM_LINE_END                    \
        movq    %rax, 56+P0  ASM_LINE_END                    \
        movq    64+P1, %rax  ASM_LINE_END                    \
        movq    %rax, 64+P0

S2N_BN_SYMBOL(p521_jadd_alt):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

// Save registers and make room on stack for temporary variables

        pushq  %rbx
        pushq  %rbp
        pushq  %r12
        pushq  %r13
        pushq  %r14
        pushq  %r15

        subq   $NSPACE, %rsp

// Move the input arguments to stable places (two are already there)

        movq    %rdx, input_y

// Main code, just a sequence of basic field operations

        sqr_p521(z1sq,z_1)
        sqr_p521(z2sq,z_2)

        mul_p521(y1a,z_2,y_1)
        mul_p521(y2a,z_1,y_2)

        mul_p521(x2a,z1sq,x_2)
        mul_p521(x1a,z2sq,x_1)
        mul_p521(y2a,z1sq,y2a)
        mul_p521(y1a,z2sq,y1a)

        sub_p521(xd,x2a,x1a)
        sub_p521(yd,y2a,y1a)

        sqr_p521(zz,xd)
        sqr_p521(ww,yd)

        mul_p521(zzx1,zz,x1a)
        mul_p521(zzx2,zz,x2a)

        sub_p521(resx,ww,zzx1)
        sub_p521(t1,zzx2,zzx1)

        mul_p521(xd,xd,z_1)

        sub_p521(resx,resx,zzx2)

        sub_p521(t2,zzx1,resx)

        mul_p521(t1,t1,y1a)
        mul_p521(resz,xd,z_2)
        mul_p521(t2,yd,t2)

        sub_p521(resy,t2,t1)

// Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
// The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
// So "NBE" <=> ~(CF \/ ZF) <=> P1 = 0 /\ ~(P2 = 0)
// and "B"  <=> CF          <=> ~(P1 = 0) /\ P2 = 0
// and "Z"  <=> ZF          <=> (P1 = 0 <=> P2 = 0)

        load9(%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp,z_1)
        orq     %r9, %r8
        orq     %r11, %r10
        orq     %r13, %r12
        orq     %r15, %r14
        orq     %r10, %r8
        orq     %r14, %r12
        orq     %rbp, %r8
        orq     %r12, %r8
        negq    %r8
        sbbq    %rax, %rax

        load9(%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp,z_2)
        orq     %r9, %r8
        orq     %r11, %r10
        orq     %r13, %r12
        orq     %r15, %r14
        orq     %r10, %r8
        orq     %r14, %r12
        orq     %rbp, %r8
        orq     %r12, %r8
        negq    %r8
        sbbq    %rdx, %rdx

        cmpq    %rax, %rdx

// Multiplex the outputs accordingly. Re-store them in resz until there
// are no more loads, so there are no assumptions on input-output aliasing

        muxload9(%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp,resy,y_1,y_2)
        store9(resy,%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp)
        muxload9(%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp,resz,z_1,z_2)
        store9(resz,%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp)
        muxload9(%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp,resx,x_1,x_2)
        store9(x_3,%r8,%r9,%r10,%r11,%r12,%r13,%r14,%r15,%rbp)
        copy9(y_3,resy)
        copy9(z_3,resz)

// Restore stack and registers

        addq    $NSPACE, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbp
        popq    %rbx

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
