// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jdouble
//      (uint64_t p3[static 27],uint64_t p1[static 27]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// It is assumed that all coordinates of the input point are fully
// reduced mod p_521 and that the z coordinate is not zero.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jdouble)
        .text

// Size of individual field elements

#define NUMSIZE 72

// Stable homes for input arguments during main code sequence
// This is actually where they come in anyway and they stay there.

#define input_z %rdi
#define input_x %rsi

// Pointer-offset pairs for inputs and outputs

#define x_1 0(input_x)
#define y_1 NUMSIZE(input_x)
#define z_1 (2*NUMSIZE)(input_x)

#define x_3 0(input_z)
#define y_3 NUMSIZE(input_z)
#define z_3 (2*NUMSIZE)(input_z)

// Pointer-offset pairs for temporaries, with some aliasing
// The tmp field is internal storage for field mul and sqr.
// NSPACE is the total stack needed for these temporaries

#define z2 (NUMSIZE*0)(%rsp)
#define y2 (NUMSIZE*1)(%rsp)
#define x2p (NUMSIZE*2)(%rsp)
#define xy2 (NUMSIZE*3)(%rsp)

#define y4 (NUMSIZE*4)(%rsp)
#define t2 (NUMSIZE*4)(%rsp)

#define dx2 (NUMSIZE*5)(%rsp)
#define t1 (NUMSIZE*5)(%rsp)

#define d (NUMSIZE*6)(%rsp)
#define x4p (NUMSIZE*6)(%rsp)

#define tmp (NUMSIZE*7)(%rsp)

#define NSPACE (NUMSIZE*7+64)

// Corresponds exactly to bignum_mul_p521

#define mul_p521(P0,P1,P2)                      \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        movq    P2, %rdx  ASM_LINE_END                       \
        mulxq   P1, %r8, %r9  ASM_LINE_END                     \
        movq    %r8, 504(%rsp)  ASM_LINE_END                   \
        mulxq   0x8+P1, %rbx, %r10  ASM_LINE_END               \
        adcq    %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x10+P1, %rbx, %r11  ASM_LINE_END              \
        adcq    %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x18+P1, %rbx, %r12  ASM_LINE_END              \
        adcq    %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x20+P1, %rbx, %r13  ASM_LINE_END              \
        adcq    %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x28+P1, %rbx, %r14  ASM_LINE_END              \
        adcq    %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x30+P1, %rbx, %r15  ASM_LINE_END              \
        adcq    %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x38+P1, %rbx, %r8  ASM_LINE_END               \
        adcq    %rbx, %r15  ASM_LINE_END                        \
        adcq    %rcx, %r8  ASM_LINE_END                         \
        movq    0x8+P2, %rdx  ASM_LINE_END                   \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        movq    %r9, 512(%rsp)  ASM_LINE_END                   \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x38+P1, %rax, %r9  ASM_LINE_END               \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rcx, %r9  ASM_LINE_END                         \
        adcq    %rcx, %r9  ASM_LINE_END                         \
        movq    0x10+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        movq    %r10, 520(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x38+P1, %rax, %r10  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rcx, %r10  ASM_LINE_END                        \
        adcq    %rcx, %r10  ASM_LINE_END                        \
        movq    0x18+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        movq    %r11, 528(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r11  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rcx, %r11  ASM_LINE_END                        \
        adcq    %rcx, %r11  ASM_LINE_END                        \
        movq    0x20+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        movq    %r12, 536(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r12  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rcx, %r12  ASM_LINE_END                        \
        adcq    %rcx, %r12  ASM_LINE_END                        \
        movq    0x28+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        movq    %r13, 544(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r13  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rcx, %r13  ASM_LINE_END                        \
        adcq    %rcx, %r13  ASM_LINE_END                        \
        movq    0x30+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        movq    %r14, 552(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r14  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rcx, %r14  ASM_LINE_END                        \
        adcq    %rcx, %r14  ASM_LINE_END                        \
        movq    0x38+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        movq    %r15, 560(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r15  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rcx, %r15  ASM_LINE_END                        \
        adcq    %rcx, %r15  ASM_LINE_END                        \
        movq    0x40+P1, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P2, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x8+P2, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x10+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x18+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x20+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x28+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x30+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x38+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rcx, %rbx  ASM_LINE_END                        \
        adcq    %rbx, %rcx  ASM_LINE_END                        \
        movq    0x40+P2, %rdx  ASM_LINE_END                  \
        xorl    %eax, %eax  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %rcx  ASM_LINE_END                        \
        mulxq   0x40+P1, %rax, %rbx  ASM_LINE_END              \
        adcq    %rax, %rcx  ASM_LINE_END                        \
        movq    %r8, %rax  ASM_LINE_END                         \
        andq    $0x1ff, %rax  ASM_LINE_END                      \
        shrdq   $0x9, %r9, %r8  ASM_LINE_END                      \
        shrdq   $0x9, %r10, %r9  ASM_LINE_END                     \
        shrdq   $0x9, %r11, %r10  ASM_LINE_END                    \
        shrdq   $0x9, %r12, %r11  ASM_LINE_END                    \
        shrdq   $0x9, %r13, %r12  ASM_LINE_END                    \
        shrdq   $0x9, %r14, %r13  ASM_LINE_END                    \
        shrdq   $0x9, %r15, %r14  ASM_LINE_END                    \
        shrdq   $0x9, %rcx, %r15  ASM_LINE_END                    \
        shrq    $0x9, %rcx  ASM_LINE_END                        \
        addq    %rax, %rcx  ASM_LINE_END                        \
        stc ASM_LINE_END                                    \
        adcq    504(%rsp), %r8  ASM_LINE_END                   \
        adcq    512(%rsp), %r9  ASM_LINE_END                   \
        adcq    520(%rsp), %r10  ASM_LINE_END                  \
        adcq    528(%rsp), %r11  ASM_LINE_END                  \
        adcq    536(%rsp), %r12  ASM_LINE_END                  \
        adcq    544(%rsp), %r13  ASM_LINE_END                  \
        adcq    552(%rsp), %r14  ASM_LINE_END                  \
        adcq    560(%rsp), %r15  ASM_LINE_END                  \
        adcq    $0xfffffffffffffe00, %rcx  ASM_LINE_END         \
        cmc ASM_LINE_END                                    \
        sbbq    $0x0, %r8  ASM_LINE_END                         \
        movq    %r8, P0  ASM_LINE_END                        \
        sbbq    $0x0, %r9  ASM_LINE_END                         \
        movq    %r9, 0x8+P0  ASM_LINE_END                    \
        sbbq    $0x0, %r10  ASM_LINE_END                        \
        movq    %r10, 0x10+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r11  ASM_LINE_END                        \
        movq    %r11, 0x18+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r12  ASM_LINE_END                        \
        movq    %r12, 0x20+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r13  ASM_LINE_END                        \
        movq    %r13, 0x28+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r14  ASM_LINE_END                        \
        movq    %r14, 0x30+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r15  ASM_LINE_END                        \
        movq    %r15, 0x38+P0  ASM_LINE_END                  \
        sbbq    $0x0, %rcx  ASM_LINE_END                        \
        andq    $0x1ff, %rcx  ASM_LINE_END                      \
        movq    %rcx, 0x40+P0

// Corresponds exactly to bignum_sqr_p521

#define sqr_p521(P0,P1)                         \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        movq    P1, %rdx  ASM_LINE_END                       \
        mulxq   0x8+P1, %r9, %rax  ASM_LINE_END                \
        movq    %r9, 512(%rsp)  ASM_LINE_END                   \
        mulxq   0x10+P1, %r10, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        movq    %r10, 520(%rsp)  ASM_LINE_END                  \
        mulxq   0x18+P1, %r11, %rax  ASM_LINE_END              \
        adcxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x20+P1, %r12, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        mulxq   0x28+P1, %r13, %rax  ASM_LINE_END              \
        adcxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x30+P1, %r14, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        mulxq   0x38+P1, %r15, %r8  ASM_LINE_END               \
        adcxq   %rbx, %r15  ASM_LINE_END                        \
        adcxq   %rcx, %r8  ASM_LINE_END                         \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        movq    0x8+P1, %rdx  ASM_LINE_END                   \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        movq    %r11, 528(%rsp)  ASM_LINE_END                  \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        movq    %r12, 536(%rsp)  ASM_LINE_END                  \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x38+P1, %rax, %r9  ASM_LINE_END               \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rcx, %r9  ASM_LINE_END                         \
        movq    0x20+P1, %rdx  ASM_LINE_END                  \
        mulxq   0x28+P1, %rax, %r10  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rcx, %r10  ASM_LINE_END                        \
        adcxq   %rcx, %r10  ASM_LINE_END                        \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        movq    0x10+P1, %rdx  ASM_LINE_END                  \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        movq    %r13, 544(%rsp)  ASM_LINE_END                  \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        movq    %r14, 552(%rsp)  ASM_LINE_END                  \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x38+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        movq    0x30+P1, %rdx  ASM_LINE_END                  \
        mulxq   0x20+P1, %rax, %r11  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rcx, %r11  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %r12  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rcx, %r12  ASM_LINE_END                        \
        adcxq   %rcx, %r12  ASM_LINE_END                        \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        movq    0x18+P1, %rdx  ASM_LINE_END                  \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        movq    %r15, 560(%rsp)  ASM_LINE_END                  \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        movq    0x38+P1, %rdx  ASM_LINE_END                  \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %r13  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rcx, %r13  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %r14  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rcx, %r14  ASM_LINE_END                        \
        adcxq   %rcx, %r14  ASM_LINE_END                        \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        movq    P1, %rdx  ASM_LINE_END                       \
        mulxq   %rdx, %rax, %rbx  ASM_LINE_END                    \
        movq    %rax, 504(%rsp)  ASM_LINE_END                  \
        movq    512(%rsp), %rax  ASM_LINE_END                  \
        adcxq   %rax, %rax  ASM_LINE_END                        \
        adoxq   %rbx, %rax  ASM_LINE_END                        \
        movq    %rax, 512(%rsp)  ASM_LINE_END                  \
        movq    520(%rsp), %rax  ASM_LINE_END                  \
        movq    0x8+P1, %rdx  ASM_LINE_END                   \
        mulxq   %rdx, %rdx, %rbx  ASM_LINE_END                    \
        adcxq   %rax, %rax  ASM_LINE_END                        \
        adoxq   %rdx, %rax  ASM_LINE_END                        \
        movq    %rax, 520(%rsp)  ASM_LINE_END                  \
        movq    528(%rsp), %rax  ASM_LINE_END                  \
        adcxq   %rax, %rax  ASM_LINE_END                        \
        adoxq   %rbx, %rax  ASM_LINE_END                        \
        movq    %rax, 528(%rsp)  ASM_LINE_END                  \
        movq    536(%rsp), %rax  ASM_LINE_END                  \
        movq    0x10+P1, %rdx  ASM_LINE_END                  \
        mulxq   %rdx, %rdx, %rbx  ASM_LINE_END                    \
        adcxq   %rax, %rax  ASM_LINE_END                        \
        adoxq   %rdx, %rax  ASM_LINE_END                        \
        movq    %rax, 536(%rsp)  ASM_LINE_END                  \
        movq    544(%rsp), %rax  ASM_LINE_END                  \
        adcxq   %rax, %rax  ASM_LINE_END                        \
        adoxq   %rbx, %rax  ASM_LINE_END                        \
        movq    %rax, 544(%rsp)  ASM_LINE_END                  \
        movq    552(%rsp), %rax  ASM_LINE_END                  \
        movq    0x18+P1, %rdx  ASM_LINE_END                  \
        mulxq   %rdx, %rdx, %rbx  ASM_LINE_END                    \
        adcxq   %rax, %rax  ASM_LINE_END                        \
        adoxq   %rdx, %rax  ASM_LINE_END                        \
        movq    %rax, 552(%rsp)  ASM_LINE_END                  \
        movq    560(%rsp), %rax  ASM_LINE_END                  \
        adcxq   %rax, %rax  ASM_LINE_END                        \
        adoxq   %rbx, %rax  ASM_LINE_END                        \
        movq    %rax, 560(%rsp)  ASM_LINE_END                  \
        movq    0x20+P1, %rdx  ASM_LINE_END                  \
        mulxq   %rdx, %rdx, %rbx  ASM_LINE_END                    \
        adcxq   %r8, %r8  ASM_LINE_END                          \
        adoxq   %rdx, %r8  ASM_LINE_END                         \
        adcxq   %r9, %r9  ASM_LINE_END                          \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        movq    0x28+P1, %rdx  ASM_LINE_END                  \
        mulxq   %rdx, %rdx, %rbx  ASM_LINE_END                    \
        adcxq   %r10, %r10  ASM_LINE_END                        \
        adoxq   %rdx, %r10  ASM_LINE_END                        \
        adcxq   %r11, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        movq    0x30+P1, %rdx  ASM_LINE_END                  \
        mulxq   %rdx, %rdx, %rbx  ASM_LINE_END                    \
        adcxq   %r12, %r12  ASM_LINE_END                        \
        adoxq   %rdx, %r12  ASM_LINE_END                        \
        adcxq   %r13, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        movq    0x38+P1, %rdx  ASM_LINE_END                  \
        mulxq   %rdx, %rdx, %r15  ASM_LINE_END                    \
        adcxq   %r14, %r14  ASM_LINE_END                        \
        adoxq   %rdx, %r14  ASM_LINE_END                        \
        adcxq   %rcx, %r15  ASM_LINE_END                        \
        adoxq   %rcx, %r15  ASM_LINE_END                        \
        movq    0x40+P1, %rdx  ASM_LINE_END                  \
        movq    %rdx, %rcx  ASM_LINE_END                        \
        imulq   %rcx, %rcx  ASM_LINE_END                        \
        addq    %rdx, %rdx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %rcx  ASM_LINE_END                        \
        adcq    $0x0, %rcx  ASM_LINE_END                        \
        movq    %r8, %rax  ASM_LINE_END                         \
        andq    $0x1ff, %rax  ASM_LINE_END                      \
        shrdq   $0x9, %r9, %r8  ASM_LINE_END                      \
        shrdq   $0x9, %r10, %r9  ASM_LINE_END                     \
        shrdq   $0x9, %r11, %r10  ASM_LINE_END                    \
        shrdq   $0x9, %r12, %r11  ASM_LINE_END                    \
        shrdq   $0x9, %r13, %r12  ASM_LINE_END                    \
        shrdq   $0x9, %r14, %r13  ASM_LINE_END                    \
        shrdq   $0x9, %r15, %r14  ASM_LINE_END                    \
        shrdq   $0x9, %rcx, %r15  ASM_LINE_END                    \
        shrq    $0x9, %rcx  ASM_LINE_END                        \
        addq    %rax, %rcx  ASM_LINE_END                        \
        stc ASM_LINE_END                                    \
        adcq    504(%rsp), %r8  ASM_LINE_END                   \
        adcq    512(%rsp), %r9  ASM_LINE_END                   \
        adcq    520(%rsp), %r10  ASM_LINE_END                  \
        adcq    528(%rsp), %r11  ASM_LINE_END                  \
        adcq    536(%rsp), %r12  ASM_LINE_END                  \
        adcq    544(%rsp), %r13  ASM_LINE_END                  \
        adcq    552(%rsp), %r14  ASM_LINE_END                  \
        adcq    560(%rsp), %r15  ASM_LINE_END                  \
        adcq    $0xfffffffffffffe00, %rcx  ASM_LINE_END         \
        cmc ASM_LINE_END                                    \
        sbbq    $0x0, %r8  ASM_LINE_END                         \
        movq    %r8, P0  ASM_LINE_END                        \
        sbbq    $0x0, %r9  ASM_LINE_END                         \
        movq    %r9, 0x8+P0  ASM_LINE_END                    \
        sbbq    $0x0, %r10  ASM_LINE_END                        \
        movq    %r10, 0x10+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r11  ASM_LINE_END                        \
        movq    %r11, 0x18+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r12  ASM_LINE_END                        \
        movq    %r12, 0x20+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r13  ASM_LINE_END                        \
        movq    %r13, 0x28+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r14  ASM_LINE_END                        \
        movq    %r14, 0x30+P0  ASM_LINE_END                  \
        sbbq    $0x0, %r15  ASM_LINE_END                        \
        movq    %r15, 0x38+P0  ASM_LINE_END                  \
        sbbq    $0x0, %rcx  ASM_LINE_END                        \
        andq    $0x1ff, %rcx  ASM_LINE_END                      \
        movq    %rcx, 0x40+P0

// Corresponds exactly to bignum_add_p521

#define add_p521(P0,P1,P2)                      \
        stc ASM_LINE_END                                    \
        movq    P1, %rax  ASM_LINE_END                       \
        adcq    P2, %rax  ASM_LINE_END                       \
        movq    0x8+P1, %rbx  ASM_LINE_END                   \
        adcq    0x8+P2, %rbx  ASM_LINE_END                   \
        movq    0x10+P1, %r8  ASM_LINE_END                   \
        adcq    0x10+P2, %r8  ASM_LINE_END                   \
        movq    0x18+P1, %r9  ASM_LINE_END                   \
        adcq    0x18+P2, %r9  ASM_LINE_END                   \
        movq    0x20+P1, %r10  ASM_LINE_END                  \
        adcq    0x20+P2, %r10  ASM_LINE_END                  \
        movq    0x28+P1, %r11  ASM_LINE_END                  \
        adcq    0x28+P2, %r11  ASM_LINE_END                  \
        movq    0x30+P1, %r12  ASM_LINE_END                  \
        adcq    0x30+P2, %r12  ASM_LINE_END                  \
        movq    0x38+P1, %r13  ASM_LINE_END                  \
        adcq    0x38+P2, %r13  ASM_LINE_END                  \
        movq    0x40+P1, %r14  ASM_LINE_END                  \
        adcq    0x40+P2, %r14  ASM_LINE_END                  \
        movq    $0x200, %rdx  ASM_LINE_END                      \
        andq    %r14, %rdx  ASM_LINE_END                        \
        cmpq    $0x200, %rdx  ASM_LINE_END                      \
        sbbq    $0x0, %rax  ASM_LINE_END                        \
        movq    %rax, P0  ASM_LINE_END                       \
        sbbq    $0x0, %rbx  ASM_LINE_END                        \
        movq    %rbx, 0x8+P0  ASM_LINE_END                   \
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
        sbbq    %rdx, %r14  ASM_LINE_END                        \
        movq    %r14, 0x40+P0

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

// Weak multiplication not fully reducing

#define weakmul_p521(P0,P1,P2)                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        movq    P2, %rdx  ASM_LINE_END                       \
        mulxq   P1, %r8, %r9  ASM_LINE_END                     \
        movq    %r8, 504(%rsp)  ASM_LINE_END                   \
        mulxq   0x8+P1, %rbx, %r10  ASM_LINE_END               \
        adcq    %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x10+P1, %rbx, %r11  ASM_LINE_END              \
        adcq    %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x18+P1, %rbx, %r12  ASM_LINE_END              \
        adcq    %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x20+P1, %rbx, %r13  ASM_LINE_END              \
        adcq    %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x28+P1, %rbx, %r14  ASM_LINE_END              \
        adcq    %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x30+P1, %rbx, %r15  ASM_LINE_END              \
        adcq    %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x38+P1, %rbx, %r8  ASM_LINE_END               \
        adcq    %rbx, %r15  ASM_LINE_END                        \
        adcq    %rcx, %r8  ASM_LINE_END                         \
        movq    0x8+P2, %rdx  ASM_LINE_END                   \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        movq    %r9, 512(%rsp)  ASM_LINE_END                   \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x38+P1, %rax, %r9  ASM_LINE_END               \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rcx, %r9  ASM_LINE_END                         \
        adcq    %rcx, %r9  ASM_LINE_END                         \
        movq    0x10+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        movq    %r10, 520(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x38+P1, %rax, %r10  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rcx, %r10  ASM_LINE_END                        \
        adcq    %rcx, %r10  ASM_LINE_END                        \
        movq    0x18+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        movq    %r11, 528(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r11  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rcx, %r11  ASM_LINE_END                        \
        adcq    %rcx, %r11  ASM_LINE_END                        \
        movq    0x20+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        movq    %r12, 536(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r12  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rcx, %r12  ASM_LINE_END                        \
        adcq    %rcx, %r12  ASM_LINE_END                        \
        movq    0x28+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        movq    %r13, 544(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r13  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rcx, %r13  ASM_LINE_END                        \
        adcq    %rcx, %r13  ASM_LINE_END                        \
        movq    0x30+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        movq    %r14, 552(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r14  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rcx, %r14  ASM_LINE_END                        \
        adcq    %rcx, %r14  ASM_LINE_END                        \
        movq    0x38+P2, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %r8  ASM_LINE_END                         \
        movq    %r15, 560(%rsp)  ASM_LINE_END                  \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %r15  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rcx, %r15  ASM_LINE_END                        \
        adcq    %rcx, %r15  ASM_LINE_END                        \
        movq    0x40+P1, %rdx  ASM_LINE_END                  \
        xorl    %ecx, %ecx  ASM_LINE_END                        \
        mulxq   P2, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x8+P2, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x10+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x18+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x20+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x28+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x30+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x38+P2, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rcx, %rbx  ASM_LINE_END                        \
        adcq    %rbx, %rcx  ASM_LINE_END                        \
        movq    0x40+P2, %rdx  ASM_LINE_END                  \
        xorl    %eax, %eax  ASM_LINE_END                        \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                   \
        adcxq   %rax, %r8  ASM_LINE_END                         \
        adoxq   %rbx, %r9  ASM_LINE_END                         \
        mulxq   0x8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                         \
        adoxq   %rbx, %r10  ASM_LINE_END                        \
        mulxq   0x10+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                        \
        adoxq   %rbx, %r11  ASM_LINE_END                        \
        mulxq   0x18+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                        \
        adoxq   %rbx, %r12  ASM_LINE_END                        \
        mulxq   0x20+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                        \
        adoxq   %rbx, %r13  ASM_LINE_END                        \
        mulxq   0x28+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                        \
        adoxq   %rbx, %r14  ASM_LINE_END                        \
        mulxq   0x30+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                        \
        adoxq   %rbx, %r15  ASM_LINE_END                        \
        mulxq   0x38+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                        \
        adoxq   %rbx, %rcx  ASM_LINE_END                        \
        mulxq   0x40+P1, %rax, %rbx  ASM_LINE_END              \
        adcq    %rax, %rcx  ASM_LINE_END                        \
        movq    %r8, %rax  ASM_LINE_END                         \
        andq    $0x1ff, %rax  ASM_LINE_END                      \
        shrdq   $0x9, %r9, %r8  ASM_LINE_END                      \
        shrdq   $0x9, %r10, %r9  ASM_LINE_END                     \
        shrdq   $0x9, %r11, %r10  ASM_LINE_END                    \
        shrdq   $0x9, %r12, %r11  ASM_LINE_END                    \
        shrdq   $0x9, %r13, %r12  ASM_LINE_END                    \
        shrdq   $0x9, %r14, %r13  ASM_LINE_END                    \
        shrdq   $0x9, %r15, %r14  ASM_LINE_END                    \
        shrdq   $0x9, %rcx, %r15  ASM_LINE_END                    \
        shrq    $0x9, %rcx  ASM_LINE_END                        \
        addq    %rax, %rcx  ASM_LINE_END                        \
        addq    504(%rsp), %r8  ASM_LINE_END                   \
        movq    %r8, P0  ASM_LINE_END                        \
        adcq    512(%rsp), %r9  ASM_LINE_END                   \
        movq    %r9, 0x8+P0  ASM_LINE_END                    \
        adcq    520(%rsp), %r10  ASM_LINE_END                  \
        movq    %r10, 0x10+P0  ASM_LINE_END                  \
        adcq    528(%rsp), %r11  ASM_LINE_END                  \
        movq    %r11, 0x18+P0  ASM_LINE_END                  \
        adcq    536(%rsp), %r12  ASM_LINE_END                  \
        movq    %r12, 0x20+P0  ASM_LINE_END                  \
        adcq    544(%rsp), %r13  ASM_LINE_END                  \
        movq    %r13, 0x28+P0  ASM_LINE_END                  \
        adcq    552(%rsp), %r14  ASM_LINE_END                  \
        movq    %r14, 0x30+P0  ASM_LINE_END                  \
        adcq    560(%rsp), %r15  ASM_LINE_END                  \
        movq    %r15, 0x38+P0  ASM_LINE_END                  \
        adcq    $0, %rcx  ASM_LINE_END                          \
        movq    %rcx, 0x40+P0

// P0 = C * P1 - D * P2 == C * P1 + D * (p_521 - P2)

#define cmsub_p521(P0,C,P1,D,P2)                \
        movq    $D, %rdx  ASM_LINE_END                         \
        movq    64+P2, %rbx  ASM_LINE_END                   \
        xorq    $0x1FF, %rbx  ASM_LINE_END                     \
        movq    P2, %rax  ASM_LINE_END                      \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %r8, %r9  ASM_LINE_END                    \
        movq    8+P2, %rax  ASM_LINE_END                    \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %rax, %r10  ASM_LINE_END                  \
        addq    %rax, %r9  ASM_LINE_END                        \
        movq    16+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %rax, %r11  ASM_LINE_END                  \
        adcq    %rax, %r10  ASM_LINE_END                       \
        movq    24+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %rax, %r12  ASM_LINE_END                  \
        adcq    %rax, %r11  ASM_LINE_END                       \
        movq    32+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %rax, %r13  ASM_LINE_END                  \
        adcq    %rax, %r12  ASM_LINE_END                       \
        movq    40+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %rax, %r14  ASM_LINE_END                  \
        adcq    %rax, %r13  ASM_LINE_END                       \
        movq    48+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %rax, %r15  ASM_LINE_END                  \
        adcq    %rax, %r14  ASM_LINE_END                       \
        movq    56+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        mulxq   %rax, %rax, %rcx  ASM_LINE_END                  \
        adcq    %rax, %r15  ASM_LINE_END                       \
        mulxq   %rbx, %rbx, %rax  ASM_LINE_END                  \
        adcq    %rcx, %rbx  ASM_LINE_END                       \
        xorl    %eax, %eax  ASM_LINE_END                       \
        movq    $C, %rdx  ASM_LINE_END                         \
        mulxq   P1, %rax, %rcx  ASM_LINE_END                 \
        adcxq   %rax, %r8  ASM_LINE_END                        \
        adoxq   %rcx, %r9  ASM_LINE_END                        \
        mulxq   8+P1, %rax, %rcx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                        \
        adoxq   %rcx, %r10  ASM_LINE_END                       \
        mulxq   16+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                       \
        adoxq   %rcx, %r11  ASM_LINE_END                       \
        mulxq   24+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                       \
        adoxq   %rcx, %r12  ASM_LINE_END                       \
        mulxq   32+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                       \
        adoxq   %rcx, %r13  ASM_LINE_END                       \
        mulxq   40+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                       \
        adoxq   %rcx, %r14  ASM_LINE_END                       \
        mulxq   48+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                       \
        adoxq   %rcx, %r15  ASM_LINE_END                       \
        mulxq   56+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                       \
        adoxq   %rcx, %rbx  ASM_LINE_END                       \
        mulxq   64+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %rbx  ASM_LINE_END                       \
        movq    %r9, %rax  ASM_LINE_END                        \
        andq    %r10, %rax  ASM_LINE_END                       \
        andq    %r11, %rax  ASM_LINE_END                       \
        andq    %r12, %rax  ASM_LINE_END                       \
        andq    %r13, %rax  ASM_LINE_END                       \
        andq    %r14, %rax  ASM_LINE_END                       \
        andq    %r15, %rax  ASM_LINE_END                       \
        movq    %rbx, %rdx  ASM_LINE_END                       \
        shrq    $9, %rdx  ASM_LINE_END                         \
        orq     $~0x1FF, %rbx  ASM_LINE_END                    \
        leaq    1(%rdx), %rcx  ASM_LINE_END                   \
        addq    %r8, %rcx  ASM_LINE_END                        \
        movl    $0, %ecx  ASM_LINE_END                         \
        adcq    %rcx, %rax  ASM_LINE_END                       \
        movq    %rbx, %rax  ASM_LINE_END                       \
        adcq    %rcx, %rax  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        movq    %r8, P0  ASM_LINE_END                       \
        adcq    %rcx, %r9  ASM_LINE_END                        \
        movq    %r9, 8+P0  ASM_LINE_END                     \
        adcq    %rcx, %r10  ASM_LINE_END                       \
        movq    %r10, 16+P0  ASM_LINE_END                   \
        adcq    %rcx, %r11  ASM_LINE_END                       \
        movq    %r11, 24+P0  ASM_LINE_END                   \
        adcq    %rcx, %r12  ASM_LINE_END                       \
        movq    %r12, 32+P0  ASM_LINE_END                   \
        adcq    %rcx, %r13  ASM_LINE_END                       \
        movq    %r13, 40+P0  ASM_LINE_END                   \
        adcq    %rcx, %r14  ASM_LINE_END                       \
        movq    %r14, 48+P0  ASM_LINE_END                   \
        adcq    %rcx, %r15  ASM_LINE_END                       \
        movq    %r15, 56+P0  ASM_LINE_END                   \
        adcq    %rcx, %rbx  ASM_LINE_END                       \
        andq    $0x1FF, %rbx  ASM_LINE_END                     \
        movq    %rbx, 64+P0

// P0 = 3 * P1 - 8 * P2 == 3 * P1 + 8 * (p_521 - P2)

#define cmsub38_p521(P0,P1,P2)                  \
        movq    64+P2, %rbx  ASM_LINE_END                   \
        xorq    $0x1FF, %rbx  ASM_LINE_END                     \
        movq    56+P2, %r15  ASM_LINE_END                   \
        notq    %r15 ASM_LINE_END                            \
        shldq   $3, %r15, %rbx  ASM_LINE_END                    \
        movq    48+P2, %r14  ASM_LINE_END                   \
        notq    %r14 ASM_LINE_END                            \
        shldq   $3, %r14, %r15  ASM_LINE_END                    \
        movq    40+P2, %r13  ASM_LINE_END                   \
        notq    %r13 ASM_LINE_END                            \
        shldq   $3, %r13, %r14  ASM_LINE_END                    \
        movq    32+P2, %r12  ASM_LINE_END                   \
        notq    %r12 ASM_LINE_END                            \
        shldq   $3, %r12, %r13  ASM_LINE_END                    \
        movq    24+P2, %r11  ASM_LINE_END                   \
        notq    %r11 ASM_LINE_END                            \
        shldq   $3, %r11, %r12  ASM_LINE_END                    \
        movq    16+P2, %r10  ASM_LINE_END                   \
        notq    %r10 ASM_LINE_END                            \
        shldq   $3, %r10, %r11  ASM_LINE_END                    \
        movq    8+P2, %r9  ASM_LINE_END                     \
        notq    %r9 ASM_LINE_END                             \
        shldq   $3, %r9, %r10  ASM_LINE_END                     \
        movq    P2, %r8  ASM_LINE_END                       \
        notq    %r8 ASM_LINE_END                             \
        shldq   $3, %r8, %r9  ASM_LINE_END                      \
        shlq    $3, %r8  ASM_LINE_END                          \
        movq    $3, %rdx  ASM_LINE_END                         \
        xorl    %eax, %eax  ASM_LINE_END                       \
        mulxq   P1, %rax, %rcx  ASM_LINE_END                 \
        adcxq   %rax, %r8  ASM_LINE_END                        \
        adoxq   %rcx, %r9  ASM_LINE_END                        \
        mulxq   8+P1, %rax, %rcx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                        \
        adoxq   %rcx, %r10  ASM_LINE_END                       \
        mulxq   16+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                       \
        adoxq   %rcx, %r11  ASM_LINE_END                       \
        mulxq   24+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                       \
        adoxq   %rcx, %r12  ASM_LINE_END                       \
        mulxq   32+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                       \
        adoxq   %rcx, %r13  ASM_LINE_END                       \
        mulxq   40+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                       \
        adoxq   %rcx, %r14  ASM_LINE_END                       \
        mulxq   48+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r14  ASM_LINE_END                       \
        adoxq   %rcx, %r15  ASM_LINE_END                       \
        mulxq   56+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %r15  ASM_LINE_END                       \
        adoxq   %rcx, %rbx  ASM_LINE_END                       \
        mulxq   64+P1, %rax, %rcx  ASM_LINE_END              \
        adcxq   %rax, %rbx  ASM_LINE_END                       \
        movq    %r9, %rax  ASM_LINE_END                        \
        andq    %r10, %rax  ASM_LINE_END                       \
        andq    %r11, %rax  ASM_LINE_END                       \
        andq    %r12, %rax  ASM_LINE_END                       \
        andq    %r13, %rax  ASM_LINE_END                       \
        andq    %r14, %rax  ASM_LINE_END                       \
        andq    %r15, %rax  ASM_LINE_END                       \
        movq    %rbx, %rdx  ASM_LINE_END                       \
        shrq    $9, %rdx  ASM_LINE_END                         \
        orq     $~0x1FF, %rbx  ASM_LINE_END                    \
        leaq    1(%rdx), %rcx  ASM_LINE_END                   \
        addq    %r8, %rcx  ASM_LINE_END                        \
        movl    $0, %ecx  ASM_LINE_END                         \
        adcq    %rcx, %rax  ASM_LINE_END                       \
        movq    %rbx, %rax  ASM_LINE_END                       \
        adcq    %rcx, %rax  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        movq    %r8, P0  ASM_LINE_END                       \
        adcq    %rcx, %r9  ASM_LINE_END                        \
        movq    %r9, 8+P0  ASM_LINE_END                     \
        adcq    %rcx, %r10  ASM_LINE_END                       \
        movq    %r10, 16+P0  ASM_LINE_END                   \
        adcq    %rcx, %r11  ASM_LINE_END                       \
        movq    %r11, 24+P0  ASM_LINE_END                   \
        adcq    %rcx, %r12  ASM_LINE_END                       \
        movq    %r12, 32+P0  ASM_LINE_END                   \
        adcq    %rcx, %r13  ASM_LINE_END                       \
        movq    %r13, 40+P0  ASM_LINE_END                   \
        adcq    %rcx, %r14  ASM_LINE_END                       \
        movq    %r14, 48+P0  ASM_LINE_END                   \
        adcq    %rcx, %r15  ASM_LINE_END                       \
        movq    %r15, 56+P0  ASM_LINE_END                   \
        adcq    %rcx, %rbx  ASM_LINE_END                       \
        andq    $0x1FF, %rbx  ASM_LINE_END                     \
        movq    %rbx, 64+P0

// P0 = 4 * P1 - P2 = 4 * P1 + (p_521 - P2)

#define cmsub41_p521(P0,P1,P2)                  \
        movq    64+P1, %rbx  ASM_LINE_END                   \
        movq    56+P1, %r15  ASM_LINE_END                   \
        shldq   $2, %r15, %rbx  ASM_LINE_END                    \
        movq    48+P1, %r14  ASM_LINE_END                   \
        shldq   $2, %r14, %r15  ASM_LINE_END                    \
        movq    40+P1, %r13  ASM_LINE_END                   \
        shldq   $2, %r13, %r14  ASM_LINE_END                    \
        movq    32+P1, %r12  ASM_LINE_END                   \
        shldq   $2, %r12, %r13  ASM_LINE_END                    \
        movq    24+P1, %r11  ASM_LINE_END                   \
        shldq   $2, %r11, %r12  ASM_LINE_END                    \
        movq    16+P1, %r10  ASM_LINE_END                   \
        shldq   $2, %r10, %r11  ASM_LINE_END                    \
        movq    8+P1, %r9  ASM_LINE_END                     \
        shldq   $2, %r9, %r10  ASM_LINE_END                     \
        movq    P1, %r8  ASM_LINE_END                       \
        shldq   $2, %r8, %r9  ASM_LINE_END                      \
        shlq    $2, %r8  ASM_LINE_END                          \
        movq    64+P2, %rcx  ASM_LINE_END                   \
        xorq    $0x1FF, %rcx  ASM_LINE_END                     \
        movq    P2, %rax  ASM_LINE_END                      \
        notq    %rax ASM_LINE_END                            \
        addq    %rax, %r8  ASM_LINE_END                        \
        movq    8+P2, %rax  ASM_LINE_END                    \
        notq    %rax ASM_LINE_END                            \
        adcq    %rax, %r9  ASM_LINE_END                        \
        movq    16+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        adcq    %rax, %r10  ASM_LINE_END                       \
        movq    24+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        adcq    %rax, %r11  ASM_LINE_END                       \
        movq    32+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        adcq    %rax, %r12  ASM_LINE_END                       \
        movq    40+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        adcq    %rax, %r13  ASM_LINE_END                       \
        movq    48+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        adcq    %rax, %r14  ASM_LINE_END                       \
        movq    56+P2, %rax  ASM_LINE_END                   \
        notq    %rax ASM_LINE_END                            \
        adcq    %rax, %r15  ASM_LINE_END                       \
        adcq    %rcx, %rbx  ASM_LINE_END                       \
        movq    %r9, %rax  ASM_LINE_END                        \
        andq    %r10, %rax  ASM_LINE_END                       \
        andq    %r11, %rax  ASM_LINE_END                       \
        andq    %r12, %rax  ASM_LINE_END                       \
        andq    %r13, %rax  ASM_LINE_END                       \
        andq    %r14, %rax  ASM_LINE_END                       \
        andq    %r15, %rax  ASM_LINE_END                       \
        movq    %rbx, %rdx  ASM_LINE_END                       \
        shrq    $9, %rdx  ASM_LINE_END                         \
        orq     $~0x1FF, %rbx  ASM_LINE_END                    \
        leaq    1(%rdx), %rcx  ASM_LINE_END                   \
        addq    %r8, %rcx  ASM_LINE_END                        \
        movl    $0, %ecx  ASM_LINE_END                         \
        adcq    %rcx, %rax  ASM_LINE_END                       \
        movq    %rbx, %rax  ASM_LINE_END                       \
        adcq    %rcx, %rax  ASM_LINE_END                       \
        adcq    %rdx, %r8  ASM_LINE_END                        \
        movq    %r8, P0  ASM_LINE_END                       \
        adcq    %rcx, %r9  ASM_LINE_END                        \
        movq    %r9, 8+P0  ASM_LINE_END                     \
        adcq    %rcx, %r10  ASM_LINE_END                       \
        movq    %r10, 16+P0  ASM_LINE_END                   \
        adcq    %rcx, %r11  ASM_LINE_END                       \
        movq    %r11, 24+P0  ASM_LINE_END                   \
        adcq    %rcx, %r12  ASM_LINE_END                       \
        movq    %r12, 32+P0  ASM_LINE_END                   \
        adcq    %rcx, %r13  ASM_LINE_END                       \
        movq    %r13, 40+P0  ASM_LINE_END                   \
        adcq    %rcx, %r14  ASM_LINE_END                       \
        movq    %r14, 48+P0  ASM_LINE_END                   \
        adcq    %rcx, %r15  ASM_LINE_END                       \
        movq    %r15, 56+P0  ASM_LINE_END                   \
        adcq    %rcx, %rbx  ASM_LINE_END                       \
        andq    $0x1FF, %rbx  ASM_LINE_END                     \
        movq    %rbx, 64+P0

S2N_BN_SYMBOL(p521_jdouble):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Save registers and make room on stack for temporary variables

        pushq  %rbx
        pushq  %r12
        pushq  %r13
        pushq  %r14
        pushq  %r15

        subq    $NSPACE, %rsp

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        sqr_p521(z2,z_1)
        sqr_p521(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        add_p521(t1,x_1,z2)
        sub_p521(t2,x_1,z2)
        mul_p521(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_p521(t1,y_1,z_1)
        sqr_p521(x4p,x2p)
        weakmul_p521(xy2,x_1,y2)

// t2 = (y + z)^2

        sqr_p521(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p521(d,12,xy2,9,x4p)
        sub_p521(t1,t2,z2)

// y4 = y^4

        sqr_p521(y4,y2)

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_p521(z_3,t1,y2)
        weakmul_p521(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_p521(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p521(y_3,dx2,y4)

// Restore stack and registers

        addq    $NSPACE, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbx

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
