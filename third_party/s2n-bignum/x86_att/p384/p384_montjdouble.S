// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjdouble
//      (uint64_t p3[static 18],uint64_t p1[static 18]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjdouble)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Pointer-offset pairs for inputs and outputs
// These assume %rdi = p3, %rsi = p1. The latter stays true
// but montsqr below modifies %rdi as well. Thus, we need
// to save %rdi and restore it before the writes to outputs.

#define x_1 0(%rsi)
#define y_1 NUMSIZE(%rsi)
#define z_1 (2*NUMSIZE)(%rsi)

#define x_3 0(%rdi)
#define y_3 NUMSIZE(%rdi)
#define z_3 (2*NUMSIZE)(%rdi)

// Pointer-offset pairs for temporaries, with some aliasing
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

// Safe place for pointer to the output

#define input_z (NUMSIZE*7)(%rsp)

#define NSPACE (NUMSIZE*7+8)

// Corresponds exactly to bignum_montmul_p384

#define montmul_p384(P0,P1,P2)                  \
        movq   P2, %rdx  ASM_LINE_END                        \
        xorl   %r15d, %r15d  ASM_LINE_END                       \
        mulxq  P1, %r8, %r9  ASM_LINE_END                      \
        mulxq  0x8+P1, %rbx, %r10  ASM_LINE_END                \
        addq   %rbx, %r9  ASM_LINE_END                          \
        mulxq  0x10+P1, %rbx, %r11  ASM_LINE_END               \
        adcq   %rbx, %r10  ASM_LINE_END                         \
        mulxq  0x18+P1, %rbx, %r12  ASM_LINE_END               \
        adcq   %rbx, %r11  ASM_LINE_END                         \
        mulxq  0x20+P1, %rbx, %r13  ASM_LINE_END               \
        adcq   %rbx, %r12  ASM_LINE_END                         \
        mulxq  0x28+P1, %rbx, %r14  ASM_LINE_END               \
        adcq   %rbx, %r13  ASM_LINE_END                         \
        adcq   %r15, %r14  ASM_LINE_END                         \
        movq   %r8, %rdx  ASM_LINE_END                          \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r8, %rdx  ASM_LINE_END                          \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rbx, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %r8, %rbx  ASM_LINE_END                      \
        adcq   %r8, %rax  ASM_LINE_END                          \
        adcq   %rdx, %rbx  ASM_LINE_END                         \
        adcl   %ebp, %ebp  ASM_LINE_END                         \
        subq   %rax, %r9  ASM_LINE_END                          \
        sbbq   %rbx, %r10  ASM_LINE_END                         \
        sbbq   %rbp, %r11  ASM_LINE_END                         \
        sbbq   $0x0, %r12  ASM_LINE_END                         \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        sbbq   $0x0, %rdx  ASM_LINE_END                         \
        addq   %rdx, %r14  ASM_LINE_END                         \
        adcq   $0x0, %r15  ASM_LINE_END                         \
        movq   0x8+P2, %rdx  ASM_LINE_END                    \
        xorl   %r8d, %r8d  ASM_LINE_END                         \
        mulxq  P1, %rax, %rbx  ASM_LINE_END                    \
        adcxq  %rax, %r9  ASM_LINE_END                          \
        adoxq  %rbx, %r10  ASM_LINE_END                         \
        mulxq  0x8+P1, %rax, %rbx  ASM_LINE_END                \
        adcxq  %rax, %r10  ASM_LINE_END                         \
        adoxq  %rbx, %r11  ASM_LINE_END                         \
        mulxq  0x10+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r11  ASM_LINE_END                         \
        adoxq  %rbx, %r12  ASM_LINE_END                         \
        mulxq  0x18+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r12  ASM_LINE_END                         \
        adoxq  %rbx, %r13  ASM_LINE_END                         \
        mulxq  0x20+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r13  ASM_LINE_END                         \
        adoxq  %rbx, %r14  ASM_LINE_END                         \
        adoxq  %r8, %r15  ASM_LINE_END                          \
        mulxq  0x28+P1, %rax, %rbx  ASM_LINE_END               \
        adcq   %rax, %r14  ASM_LINE_END                         \
        adcq   %rbx, %r15  ASM_LINE_END                         \
        adcq   %r8, %r8  ASM_LINE_END                           \
        movq   %r9, %rdx  ASM_LINE_END                          \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r9, %rdx  ASM_LINE_END                          \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rbx, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %r9, %rbx  ASM_LINE_END                      \
        adcq   %r9, %rax  ASM_LINE_END                          \
        adcq   %rdx, %rbx  ASM_LINE_END                         \
        adcl   %ebp, %ebp  ASM_LINE_END                         \
        subq   %rax, %r10  ASM_LINE_END                         \
        sbbq   %rbx, %r11  ASM_LINE_END                         \
        sbbq   %rbp, %r12  ASM_LINE_END                         \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        sbbq   $0x0, %r14  ASM_LINE_END                         \
        sbbq   $0x0, %rdx  ASM_LINE_END                         \
        addq   %rdx, %r15  ASM_LINE_END                         \
        adcq   $0x0, %r8  ASM_LINE_END                          \
        movq   0x10+P2, %rdx  ASM_LINE_END                   \
        xorl   %r9d, %r9d  ASM_LINE_END                         \
        mulxq  P1, %rax, %rbx  ASM_LINE_END                    \
        adcxq  %rax, %r10  ASM_LINE_END                         \
        adoxq  %rbx, %r11  ASM_LINE_END                         \
        mulxq  0x8+P1, %rax, %rbx  ASM_LINE_END                \
        adcxq  %rax, %r11  ASM_LINE_END                         \
        adoxq  %rbx, %r12  ASM_LINE_END                         \
        mulxq  0x10+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r12  ASM_LINE_END                         \
        adoxq  %rbx, %r13  ASM_LINE_END                         \
        mulxq  0x18+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r13  ASM_LINE_END                         \
        adoxq  %rbx, %r14  ASM_LINE_END                         \
        mulxq  0x20+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r14  ASM_LINE_END                         \
        adoxq  %rbx, %r15  ASM_LINE_END                         \
        adoxq  %r9, %r8  ASM_LINE_END                           \
        mulxq  0x28+P1, %rax, %rbx  ASM_LINE_END               \
        adcq   %rax, %r15  ASM_LINE_END                         \
        adcq   %rbx, %r8  ASM_LINE_END                          \
        adcq   %r9, %r9  ASM_LINE_END                           \
        movq   %r10, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r10, %rdx  ASM_LINE_END                         \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rbx, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %r10, %rbx  ASM_LINE_END                     \
        adcq   %r10, %rax  ASM_LINE_END                         \
        adcq   %rdx, %rbx  ASM_LINE_END                         \
        adcl   %ebp, %ebp  ASM_LINE_END                         \
        subq   %rax, %r11  ASM_LINE_END                         \
        sbbq   %rbx, %r12  ASM_LINE_END                         \
        sbbq   %rbp, %r13  ASM_LINE_END                         \
        sbbq   $0x0, %r14  ASM_LINE_END                         \
        sbbq   $0x0, %r15  ASM_LINE_END                         \
        sbbq   $0x0, %rdx  ASM_LINE_END                         \
        addq   %rdx, %r8  ASM_LINE_END                          \
        adcq   $0x0, %r9  ASM_LINE_END                          \
        movq   0x18+P2, %rdx  ASM_LINE_END                   \
        xorl   %r10d, %r10d  ASM_LINE_END                       \
        mulxq  P1, %rax, %rbx  ASM_LINE_END                    \
        adcxq  %rax, %r11  ASM_LINE_END                         \
        adoxq  %rbx, %r12  ASM_LINE_END                         \
        mulxq  0x8+P1, %rax, %rbx  ASM_LINE_END                \
        adcxq  %rax, %r12  ASM_LINE_END                         \
        adoxq  %rbx, %r13  ASM_LINE_END                         \
        mulxq  0x10+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r13  ASM_LINE_END                         \
        adoxq  %rbx, %r14  ASM_LINE_END                         \
        mulxq  0x18+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r14  ASM_LINE_END                         \
        adoxq  %rbx, %r15  ASM_LINE_END                         \
        mulxq  0x20+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r15  ASM_LINE_END                         \
        adoxq  %rbx, %r8  ASM_LINE_END                          \
        adoxq  %r10, %r9  ASM_LINE_END                          \
        mulxq  0x28+P1, %rax, %rbx  ASM_LINE_END               \
        adcq   %rax, %r8  ASM_LINE_END                          \
        adcq   %rbx, %r9  ASM_LINE_END                          \
        adcq   %r10, %r10  ASM_LINE_END                         \
        movq   %r11, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r11, %rdx  ASM_LINE_END                         \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rbx, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %r11, %rbx  ASM_LINE_END                     \
        adcq   %r11, %rax  ASM_LINE_END                         \
        adcq   %rdx, %rbx  ASM_LINE_END                         \
        adcl   %ebp, %ebp  ASM_LINE_END                         \
        subq   %rax, %r12  ASM_LINE_END                         \
        sbbq   %rbx, %r13  ASM_LINE_END                         \
        sbbq   %rbp, %r14  ASM_LINE_END                         \
        sbbq   $0x0, %r15  ASM_LINE_END                         \
        sbbq   $0x0, %r8  ASM_LINE_END                          \
        sbbq   $0x0, %rdx  ASM_LINE_END                         \
        addq   %rdx, %r9  ASM_LINE_END                          \
        adcq   $0x0, %r10  ASM_LINE_END                         \
        movq   0x20+P2, %rdx  ASM_LINE_END                   \
        xorl   %r11d, %r11d  ASM_LINE_END                       \
        mulxq  P1, %rax, %rbx  ASM_LINE_END                    \
        adcxq  %rax, %r12  ASM_LINE_END                         \
        adoxq  %rbx, %r13  ASM_LINE_END                         \
        mulxq  0x8+P1, %rax, %rbx  ASM_LINE_END                \
        adcxq  %rax, %r13  ASM_LINE_END                         \
        adoxq  %rbx, %r14  ASM_LINE_END                         \
        mulxq  0x10+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r14  ASM_LINE_END                         \
        adoxq  %rbx, %r15  ASM_LINE_END                         \
        mulxq  0x18+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r15  ASM_LINE_END                         \
        adoxq  %rbx, %r8  ASM_LINE_END                          \
        mulxq  0x20+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r8  ASM_LINE_END                          \
        adoxq  %rbx, %r9  ASM_LINE_END                          \
        adoxq  %r11, %r10  ASM_LINE_END                         \
        mulxq  0x28+P1, %rax, %rbx  ASM_LINE_END               \
        adcq   %rax, %r9  ASM_LINE_END                          \
        adcq   %rbx, %r10  ASM_LINE_END                         \
        adcq   %r11, %r11  ASM_LINE_END                         \
        movq   %r12, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r12, %rdx  ASM_LINE_END                         \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rbx, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %r12, %rbx  ASM_LINE_END                     \
        adcq   %r12, %rax  ASM_LINE_END                         \
        adcq   %rdx, %rbx  ASM_LINE_END                         \
        adcl   %ebp, %ebp  ASM_LINE_END                         \
        subq   %rax, %r13  ASM_LINE_END                         \
        sbbq   %rbx, %r14  ASM_LINE_END                         \
        sbbq   %rbp, %r15  ASM_LINE_END                         \
        sbbq   $0x0, %r8  ASM_LINE_END                          \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        sbbq   $0x0, %rdx  ASM_LINE_END                         \
        addq   %rdx, %r10  ASM_LINE_END                         \
        adcq   $0x0, %r11  ASM_LINE_END                         \
        movq   0x28+P2, %rdx  ASM_LINE_END                   \
        xorl   %r12d, %r12d  ASM_LINE_END                       \
        mulxq  P1, %rax, %rbx  ASM_LINE_END                    \
        adcxq  %rax, %r13  ASM_LINE_END                         \
        adoxq  %rbx, %r14  ASM_LINE_END                         \
        mulxq  0x8+P1, %rax, %rbx  ASM_LINE_END                \
        adcxq  %rax, %r14  ASM_LINE_END                         \
        adoxq  %rbx, %r15  ASM_LINE_END                         \
        mulxq  0x10+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r15  ASM_LINE_END                         \
        adoxq  %rbx, %r8  ASM_LINE_END                          \
        mulxq  0x18+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r8  ASM_LINE_END                          \
        adoxq  %rbx, %r9  ASM_LINE_END                          \
        mulxq  0x20+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r9  ASM_LINE_END                          \
        adoxq  %rbx, %r10  ASM_LINE_END                         \
        adoxq  %r12, %r11  ASM_LINE_END                         \
        mulxq  0x28+P1, %rax, %rbx  ASM_LINE_END               \
        adcq   %rax, %r10  ASM_LINE_END                         \
        adcq   %rbx, %r11  ASM_LINE_END                         \
        adcq   %r12, %r12  ASM_LINE_END                         \
        movq   %r13, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r13, %rdx  ASM_LINE_END                         \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rbx, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %r13, %rbx  ASM_LINE_END                     \
        adcq   %r13, %rax  ASM_LINE_END                         \
        adcq   %rdx, %rbx  ASM_LINE_END                         \
        adcl   %ebp, %ebp  ASM_LINE_END                         \
        subq   %rax, %r14  ASM_LINE_END                         \
        sbbq   %rbx, %r15  ASM_LINE_END                         \
        sbbq   %rbp, %r8  ASM_LINE_END                          \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        sbbq   $0x0, %r10  ASM_LINE_END                         \
        sbbq   $0x0, %rdx  ASM_LINE_END                         \
        addq   %rdx, %r11  ASM_LINE_END                         \
        adcq   $0x0, %r12  ASM_LINE_END                         \
        xorl   %edx, %edx  ASM_LINE_END                         \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        xorl   %r13d, %r13d  ASM_LINE_END                       \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        addq   %r14, %rax  ASM_LINE_END                         \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        adcq   %r15, %rbx  ASM_LINE_END                         \
        movl   $0x1, %ecx  ASM_LINE_END                         \
        adcq   %r8, %rcx  ASM_LINE_END                          \
        adcq   %r9, %rdx  ASM_LINE_END                          \
        adcq   %r10, %rbp  ASM_LINE_END                         \
        adcq   %r11, %r13  ASM_LINE_END                         \
        adcq   $0x0, %r12  ASM_LINE_END                         \
        cmovne %rax, %r14  ASM_LINE_END                         \
        cmovne %rbx, %r15  ASM_LINE_END                         \
        cmovne %rcx, %r8  ASM_LINE_END                          \
        cmovne %rdx, %r9  ASM_LINE_END                          \
        cmovne %rbp, %r10  ASM_LINE_END                         \
        cmovne %r13, %r11  ASM_LINE_END                         \
        movq   %r14, P0  ASM_LINE_END                        \
        movq   %r15, 0x8+P0  ASM_LINE_END                    \
        movq   %r8, 0x10+P0  ASM_LINE_END                    \
        movq   %r9, 0x18+P0  ASM_LINE_END                    \
        movq   %r10, 0x20+P0  ASM_LINE_END                   \
        movq   %r11, 0x28+P0

// Corresponds exactly to bignum_montsqr_p384

#define montsqr_p384(P0,P1)                     \
        movq   P1, %rdx  ASM_LINE_END                        \
        mulxq  0x8+P1, %r9, %r10  ASM_LINE_END                 \
        mulxq  0x18+P1, %r11, %r12  ASM_LINE_END               \
        mulxq  0x28+P1, %r13, %r14  ASM_LINE_END               \
        movq   0x18+P1, %rdx  ASM_LINE_END                   \
        mulxq  0x20+P1, %r15, %rcx  ASM_LINE_END               \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   0x10+P1, %rdx  ASM_LINE_END                   \
        mulxq  P1, %rax, %rbx  ASM_LINE_END                    \
        adcxq  %rax, %r10  ASM_LINE_END                         \
        adoxq  %rbx, %r11  ASM_LINE_END                         \
        mulxq  0x8+P1, %rax, %rbx  ASM_LINE_END                \
        adcxq  %rax, %r11  ASM_LINE_END                         \
        adoxq  %rbx, %r12  ASM_LINE_END                         \
        movq   0x8+P1, %rdx  ASM_LINE_END                    \
        mulxq  0x18+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r12  ASM_LINE_END                         \
        adoxq  %rbx, %r13  ASM_LINE_END                         \
        mulxq  0x20+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r13  ASM_LINE_END                         \
        adoxq  %rbx, %r14  ASM_LINE_END                         \
        mulxq  0x28+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r14  ASM_LINE_END                         \
        adoxq  %rbx, %r15  ASM_LINE_END                         \
        adcxq  %rbp, %r15  ASM_LINE_END                         \
        adoxq  %rbp, %rcx  ASM_LINE_END                         \
        adcq   %rbp, %rcx  ASM_LINE_END                         \
        xorl   %ebp, %ebp  ASM_LINE_END                         \
        movq   0x20+P1, %rdx  ASM_LINE_END                   \
        mulxq  P1, %rax, %rbx  ASM_LINE_END                    \
        adcxq  %rax, %r12  ASM_LINE_END                         \
        adoxq  %rbx, %r13  ASM_LINE_END                         \
        movq   0x10+P1, %rdx  ASM_LINE_END                   \
        mulxq  0x18+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r13  ASM_LINE_END                         \
        adoxq  %rbx, %r14  ASM_LINE_END                         \
        mulxq  0x20+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq  %rax, %r14  ASM_LINE_END                         \
        adoxq  %rbx, %r15  ASM_LINE_END                         \
        mulxq  0x28+P1, %rax, %rdx  ASM_LINE_END               \
        adcxq  %rax, %r15  ASM_LINE_END                         \
        adoxq  %rdx, %rcx  ASM_LINE_END                         \
        movq   0x28+P1, %rdx  ASM_LINE_END                   \
        mulxq  0x20+P1, %rbx, %rbp  ASM_LINE_END               \
        mulxq  0x18+P1, %rax, %rdx  ASM_LINE_END               \
        adcxq  %rax, %rcx  ASM_LINE_END                         \
        adoxq  %rdx, %rbx  ASM_LINE_END                         \
        movl   $0x0, %eax  ASM_LINE_END                         \
        adcxq  %rax, %rbx  ASM_LINE_END                         \
        adoxq  %rax, %rbp  ASM_LINE_END                         \
        adcq   %rax, %rbp  ASM_LINE_END                         \
        xorq   %rax, %rax  ASM_LINE_END                         \
        movq   P1, %rdx  ASM_LINE_END                        \
        mulxq  P1, %r8, %rax  ASM_LINE_END                     \
        adcxq  %r9, %r9  ASM_LINE_END                           \
        adoxq  %rax, %r9  ASM_LINE_END                          \
        movq   0x8+P1, %rdx  ASM_LINE_END                    \
        mulxq  %rdx, %rax, %rdx  ASM_LINE_END                     \
        adcxq  %r10, %r10  ASM_LINE_END                         \
        adoxq  %rax, %r10  ASM_LINE_END                         \
        adcxq  %r11, %r11  ASM_LINE_END                         \
        adoxq  %rdx, %r11  ASM_LINE_END                         \
        movq   0x10+P1, %rdx  ASM_LINE_END                   \
        mulxq  %rdx, %rax, %rdx  ASM_LINE_END                     \
        adcxq  %r12, %r12  ASM_LINE_END                         \
        adoxq  %rax, %r12  ASM_LINE_END                         \
        adcxq  %r13, %r13  ASM_LINE_END                         \
        adoxq  %rdx, %r13  ASM_LINE_END                         \
        movq   0x18+P1, %rdx  ASM_LINE_END                   \
        mulxq  %rdx, %rax, %rdx  ASM_LINE_END                     \
        adcxq  %r14, %r14  ASM_LINE_END                         \
        adoxq  %rax, %r14  ASM_LINE_END                         \
        adcxq  %r15, %r15  ASM_LINE_END                         \
        adoxq  %rdx, %r15  ASM_LINE_END                         \
        movq   0x20+P1, %rdx  ASM_LINE_END                   \
        mulxq  %rdx, %rax, %rdx  ASM_LINE_END                     \
        adcxq  %rcx, %rcx  ASM_LINE_END                         \
        adoxq  %rax, %rcx  ASM_LINE_END                         \
        adcxq  %rbx, %rbx  ASM_LINE_END                         \
        adoxq  %rdx, %rbx  ASM_LINE_END                         \
        movq   0x28+P1, %rdx  ASM_LINE_END                   \
        mulxq  %rdx, %rax, %rdi  ASM_LINE_END                     \
        adcxq  %rbp, %rbp  ASM_LINE_END                         \
        adoxq  %rax, %rbp  ASM_LINE_END                         \
        movl   $0x0, %eax  ASM_LINE_END                         \
        adcxq  %rax, %rdi  ASM_LINE_END                         \
        adoxq  %rax, %rdi  ASM_LINE_END                         \
        movq   %rbx, P0  ASM_LINE_END                        \
        movq   %r8, %rdx  ASM_LINE_END                          \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r8, %rdx  ASM_LINE_END                          \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %r8, %rax  ASM_LINE_END                      \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %rbx, %r8  ASM_LINE_END                      \
        addq   %rbx, %rax  ASM_LINE_END                         \
        adcq   %rdx, %r8  ASM_LINE_END                          \
        movl   $0x0, %ebx  ASM_LINE_END                         \
        adcq   %rbx, %rbx  ASM_LINE_END                         \
        subq   %rax, %r9  ASM_LINE_END                          \
        sbbq   %r8, %r10  ASM_LINE_END                          \
        sbbq   %rbx, %r11  ASM_LINE_END                         \
        sbbq   $0x0, %r12  ASM_LINE_END                         \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        movq   %rdx, %r8  ASM_LINE_END                          \
        sbbq   $0x0, %r8  ASM_LINE_END                          \
        movq   %r9, %rdx  ASM_LINE_END                          \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r9, %rdx  ASM_LINE_END                          \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %r9, %rax  ASM_LINE_END                      \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %rbx, %r9  ASM_LINE_END                      \
        addq   %rbx, %rax  ASM_LINE_END                         \
        adcq   %rdx, %r9  ASM_LINE_END                          \
        movl   $0x0, %ebx  ASM_LINE_END                         \
        adcq   %rbx, %rbx  ASM_LINE_END                         \
        subq   %rax, %r10  ASM_LINE_END                         \
        sbbq   %r9, %r11  ASM_LINE_END                          \
        sbbq   %rbx, %r12  ASM_LINE_END                         \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        sbbq   $0x0, %r8  ASM_LINE_END                          \
        movq   %rdx, %r9  ASM_LINE_END                          \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        movq   %r10, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r10, %rdx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %r10, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %rbx, %r10  ASM_LINE_END                     \
        addq   %rbx, %rax  ASM_LINE_END                         \
        adcq   %rdx, %r10  ASM_LINE_END                         \
        movl   $0x0, %ebx  ASM_LINE_END                         \
        adcq   %rbx, %rbx  ASM_LINE_END                         \
        subq   %rax, %r11  ASM_LINE_END                         \
        sbbq   %r10, %r12  ASM_LINE_END                         \
        sbbq   %rbx, %r13  ASM_LINE_END                         \
        sbbq   $0x0, %r8  ASM_LINE_END                          \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        movq   %rdx, %r10  ASM_LINE_END                         \
        sbbq   $0x0, %r10  ASM_LINE_END                         \
        movq   %r11, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r11, %rdx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %r11, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %rbx, %r11  ASM_LINE_END                     \
        addq   %rbx, %rax  ASM_LINE_END                         \
        adcq   %rdx, %r11  ASM_LINE_END                         \
        movl   $0x0, %ebx  ASM_LINE_END                         \
        adcq   %rbx, %rbx  ASM_LINE_END                         \
        subq   %rax, %r12  ASM_LINE_END                         \
        sbbq   %r11, %r13  ASM_LINE_END                         \
        sbbq   %rbx, %r8  ASM_LINE_END                          \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        sbbq   $0x0, %r10  ASM_LINE_END                         \
        movq   %rdx, %r11  ASM_LINE_END                         \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r12, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r12, %rdx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %r12, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %rbx, %r12  ASM_LINE_END                     \
        addq   %rbx, %rax  ASM_LINE_END                         \
        adcq   %rdx, %r12  ASM_LINE_END                         \
        movl   $0x0, %ebx  ASM_LINE_END                         \
        adcq   %rbx, %rbx  ASM_LINE_END                         \
        subq   %rax, %r13  ASM_LINE_END                         \
        sbbq   %r12, %r8  ASM_LINE_END                          \
        sbbq   %rbx, %r9  ASM_LINE_END                          \
        sbbq   $0x0, %r10  ASM_LINE_END                         \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %rdx, %r12  ASM_LINE_END                         \
        sbbq   $0x0, %r12  ASM_LINE_END                         \
        movq   %r13, %rdx  ASM_LINE_END                         \
        shlq   $0x20, %rdx  ASM_LINE_END                        \
        addq   %r13, %rdx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %r13, %rax  ASM_LINE_END                     \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        mulxq  %rbx, %rbx, %r13  ASM_LINE_END                     \
        addq   %rbx, %rax  ASM_LINE_END                         \
        adcq   %rdx, %r13  ASM_LINE_END                         \
        movl   $0x0, %ebx  ASM_LINE_END                         \
        adcq   %rbx, %rbx  ASM_LINE_END                         \
        subq   %rax, %r8  ASM_LINE_END                          \
        sbbq   %r13, %r9  ASM_LINE_END                          \
        sbbq   %rbx, %r10  ASM_LINE_END                         \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        sbbq   $0x0, %r12  ASM_LINE_END                         \
        movq   %rdx, %r13  ASM_LINE_END                         \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        movq   P0, %rbx  ASM_LINE_END                        \
        addq   %r8, %r14  ASM_LINE_END                          \
        adcq   %r9, %r15  ASM_LINE_END                          \
        adcq   %r10, %rcx  ASM_LINE_END                         \
        adcq   %r11, %rbx  ASM_LINE_END                         \
        adcq   %r12, %rbp  ASM_LINE_END                         \
        adcq   %r13, %rdi  ASM_LINE_END                         \
        movl   $0x0, %r8d  ASM_LINE_END                         \
        adcq   %r8, %r8  ASM_LINE_END                           \
        xorq   %r11, %r11  ASM_LINE_END                         \
        xorq   %r12, %r12  ASM_LINE_END                         \
        xorq   %r13, %r13  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        addq   %r14, %rax  ASM_LINE_END                         \
        movl   $0xffffffff, %r9d  ASM_LINE_END                  \
        adcq   %r15, %r9  ASM_LINE_END                          \
        movl   $0x1, %r10d  ASM_LINE_END                        \
        adcq   %rcx, %r10  ASM_LINE_END                         \
        adcq   %rbx, %r11  ASM_LINE_END                         \
        adcq   %rbp, %r12  ASM_LINE_END                         \
        adcq   %rdi, %r13  ASM_LINE_END                         \
        adcq   $0x0, %r8  ASM_LINE_END                          \
        cmovne %rax, %r14  ASM_LINE_END                         \
        cmovne %r9, %r15  ASM_LINE_END                          \
        cmovne %r10, %rcx  ASM_LINE_END                         \
        cmovne %r11, %rbx  ASM_LINE_END                         \
        cmovne %r12, %rbp  ASM_LINE_END                         \
        cmovne %r13, %rdi  ASM_LINE_END                         \
        movq   %r14, P0  ASM_LINE_END                        \
        movq   %r15, 0x8+P0  ASM_LINE_END                    \
        movq   %rcx, 0x10+P0  ASM_LINE_END                   \
        movq   %rbx, 0x18+P0  ASM_LINE_END                   \
        movq   %rbp, 0x20+P0  ASM_LINE_END                   \
        movq   %rdi, 0x28+P0

#define sub_p384(P0,P1,P2)                      \
        movq   P1, %rax  ASM_LINE_END                        \
        subq   P2, %rax  ASM_LINE_END                        \
        movq   0x8+P1, %rdx  ASM_LINE_END                    \
        sbbq   0x8+P2, %rdx  ASM_LINE_END                    \
        movq   0x10+P1, %r8  ASM_LINE_END                    \
        sbbq   0x10+P2, %r8  ASM_LINE_END                    \
        movq   0x18+P1, %r9  ASM_LINE_END                    \
        sbbq   0x18+P2, %r9  ASM_LINE_END                    \
        movq   0x20+P1, %r10  ASM_LINE_END                   \
        sbbq   0x20+P2, %r10  ASM_LINE_END                   \
        movq   0x28+P1, %r11  ASM_LINE_END                   \
        sbbq   0x28+P2, %r11  ASM_LINE_END                   \
        sbbq   %rcx, %rcx  ASM_LINE_END                         \
        movl   $0xffffffff, %ebx  ASM_LINE_END                  \
        andq   %rbx, %rcx  ASM_LINE_END                         \
        xorq   %rbx, %rbx  ASM_LINE_END                         \
        subq   %rcx, %rbx  ASM_LINE_END                         \
        subq   %rbx, %rax  ASM_LINE_END                         \
        movq   %rax, P0  ASM_LINE_END                        \
        sbbq   %rcx, %rdx  ASM_LINE_END                         \
        movq   %rdx, 0x8+P0  ASM_LINE_END                    \
        sbbq   %rax, %rax  ASM_LINE_END                         \
        andq   %rbx, %rcx  ASM_LINE_END                         \
        negq   %rax ASM_LINE_END                             \
        sbbq   %rcx, %r8  ASM_LINE_END                          \
        movq   %r8, 0x10+P0  ASM_LINE_END                    \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        movq   %r9, 0x18+P0  ASM_LINE_END                    \
        sbbq   $0x0, %r10  ASM_LINE_END                         \
        movq   %r10, 0x20+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r11, 0x28+P0

// Simplified bignum_add_p384, without carry chain suspension

#define add_p384(P0,P1,P2)                      \
        movq   P1, %rax  ASM_LINE_END                        \
        addq   P2, %rax  ASM_LINE_END                        \
        movq   0x8+P1, %rcx  ASM_LINE_END                    \
        adcq   0x8+P2, %rcx  ASM_LINE_END                    \
        movq   0x10+P1, %r8  ASM_LINE_END                    \
        adcq   0x10+P2, %r8  ASM_LINE_END                    \
        movq   0x18+P1, %r9  ASM_LINE_END                    \
        adcq   0x18+P2, %r9  ASM_LINE_END                    \
        movq   0x20+P1, %r10  ASM_LINE_END                   \
        adcq   0x20+P2, %r10  ASM_LINE_END                   \
        movq   0x28+P1, %r11  ASM_LINE_END                   \
        adcq   0x28+P2, %r11  ASM_LINE_END                   \
        movl   $0x0, %edx  ASM_LINE_END                         \
        adcq   %rdx, %rdx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rbp  ASM_LINE_END          \
        addq   %rbp, %rax  ASM_LINE_END                         \
        movl   $0xffffffff, %ebp  ASM_LINE_END                  \
        adcq   %rbp, %rcx  ASM_LINE_END                         \
        adcq   $0x1, %r8  ASM_LINE_END                          \
        adcq   $0x0, %r9  ASM_LINE_END                          \
        adcq   $0x0, %r10  ASM_LINE_END                         \
        adcq   $0x0, %r11  ASM_LINE_END                         \
        adcq   $0xffffffffffffffff, %rdx  ASM_LINE_END          \
        movl   $1, %ebx  ASM_LINE_END                           \
        andq   %rdx, %rbx  ASM_LINE_END                         \
        andq   %rbp, %rdx  ASM_LINE_END                         \
        xorq   %rbp, %rbp  ASM_LINE_END                         \
        subq   %rdx, %rbp  ASM_LINE_END                         \
        subq   %rbp, %rax  ASM_LINE_END                         \
        movq   %rax, P0  ASM_LINE_END                        \
        sbbq   %rdx, %rcx  ASM_LINE_END                         \
        movq   %rcx, 0x8+P0  ASM_LINE_END                    \
        sbbq   %rbx, %r8  ASM_LINE_END                          \
        movq   %r8, 0x10+P0  ASM_LINE_END                    \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        movq   %r9, 0x18+P0  ASM_LINE_END                    \
        sbbq   $0x0, %r10  ASM_LINE_END                         \
        movq   %r10, 0x20+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r11, 0x28+P0

// P0 = 4 * P1 - P2

#define cmsub41_p384(P0,P1,P2)                  \
        movq    40+P1, %rdx  ASM_LINE_END                   \
        movq    %rdx, %r13  ASM_LINE_END                       \
        shrq    $62, %rdx  ASM_LINE_END                        \
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
        addq    $1, %rdx  ASM_LINE_END                         \
        subq   P2, %r8  ASM_LINE_END                        \
        sbbq   0x8+P2, %r9  ASM_LINE_END                    \
        sbbq   0x10+P2, %r10  ASM_LINE_END                  \
        sbbq   0x18+P2, %r11  ASM_LINE_END                  \
        sbbq   0x20+P2, %r12  ASM_LINE_END                  \
        sbbq   0x28+P2, %r13  ASM_LINE_END                  \
        sbbq   $0, %rdx  ASM_LINE_END                           \
        xorq   %rcx, %rcx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rax, %rcx  ASM_LINE_END                     \
        adcxq  %rax, %r8  ASM_LINE_END                          \
        adoxq  %rcx, %r9  ASM_LINE_END                          \
        movl   $0xffffffff, %eax  ASM_LINE_END                  \
        mulxq  %rax, %rax, %rcx  ASM_LINE_END                     \
        adcxq  %rax, %r9  ASM_LINE_END                          \
        adoxq  %rcx, %r10  ASM_LINE_END                         \
        adcxq  %rdx, %r10  ASM_LINE_END                         \
        movl   $0x0, %eax  ASM_LINE_END                         \
        movl   $0x0, %ecx  ASM_LINE_END                         \
        adoxq  %rax, %rax  ASM_LINE_END                         \
        adcq   %rax, %r11  ASM_LINE_END                         \
        adcq   %rcx, %r12  ASM_LINE_END                         \
        adcq   %rcx, %r13  ASM_LINE_END                         \
        adcq   %rcx, %rcx  ASM_LINE_END                         \
        subq   $0x1, %rcx  ASM_LINE_END                         \
        movl   $0xffffffff, %edx  ASM_LINE_END                  \
        xorq   %rax, %rax  ASM_LINE_END                         \
        andq   %rcx, %rdx  ASM_LINE_END                         \
        subq   %rdx, %rax  ASM_LINE_END                         \
        andq   $0x1, %rcx  ASM_LINE_END                         \
        subq   %rax, %r8  ASM_LINE_END                          \
        movq   %r8, P0  ASM_LINE_END                         \
        sbbq   %rdx, %r9  ASM_LINE_END                          \
        movq   %r9, 0x8+P0  ASM_LINE_END                     \
        sbbq   %rcx, %r10  ASM_LINE_END                         \
        movq   %r10, 0x10+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r11, 0x18+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r12  ASM_LINE_END                         \
        movq   %r12, 0x20+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        movq   %r13, 0x28+P0

// P0 = C * P1 - D * P2

#define cmsub_p384(P0,C,P1,D,P2)                \
        movq    $0x00000000ffffffff, %r8  ASM_LINE_END         \
        subq    P2, %r8  ASM_LINE_END                       \
        movq    $0xffffffff00000000, %r9  ASM_LINE_END         \
        sbbq    8+P2, %r9  ASM_LINE_END                     \
        movq    $0xfffffffffffffffe, %r10  ASM_LINE_END        \
        sbbq    16+P2, %r10  ASM_LINE_END                   \
        movq    $0xffffffffffffffff, %r11  ASM_LINE_END        \
        sbbq    24+P2, %r11  ASM_LINE_END                   \
        movq    $0xffffffffffffffff, %r12  ASM_LINE_END        \
        sbbq    32+P2, %r12  ASM_LINE_END                   \
        movq    $0xffffffffffffffff, %r13  ASM_LINE_END        \
        sbbq    40+P2, %r13  ASM_LINE_END                   \
        movq    $D, %rdx  ASM_LINE_END                         \
        mulxq   %r8, %r8, %rax  ASM_LINE_END                     \
        mulxq   %r9, %r9, %rcx  ASM_LINE_END                     \
        addq    %rax, %r9  ASM_LINE_END                        \
        mulxq   %r10, %r10, %rax  ASM_LINE_END                   \
        adcq    %rcx, %r10  ASM_LINE_END                       \
        mulxq   %r11, %r11, %rcx  ASM_LINE_END                   \
        adcq    %rax, %r11  ASM_LINE_END                       \
        mulxq   %r12, %r12, %rax  ASM_LINE_END                   \
        adcq    %rcx, %r12  ASM_LINE_END                       \
        mulxq   %r13, %r13, %r14  ASM_LINE_END                   \
        adcq    %rax, %r13  ASM_LINE_END                       \
        adcq    $1, %r14  ASM_LINE_END                         \
        xorl    %ecx, %ecx  ASM_LINE_END                       \
        movq    $C, %rdx  ASM_LINE_END                         \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                 \
        adcxq   %rax, %r8  ASM_LINE_END                        \
        adoxq   %rbx, %r9  ASM_LINE_END                        \
        mulxq   8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                        \
        adoxq   %rbx, %r10  ASM_LINE_END                       \
        mulxq   16+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                       \
        adoxq   %rbx, %r11  ASM_LINE_END                       \
        mulxq   24+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                       \
        adoxq   %rbx, %r12  ASM_LINE_END                       \
        mulxq   32+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                       \
        adoxq   %rbx, %r13  ASM_LINE_END                       \
        mulxq   40+P1, %rax, %rdx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                       \
        adoxq   %r14, %rdx  ASM_LINE_END                       \
        adcxq   %rcx, %rdx  ASM_LINE_END                       \
        xorq   %rcx, %rcx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rax, %rcx  ASM_LINE_END                     \
        adcxq  %rax, %r8  ASM_LINE_END                          \
        adoxq  %rcx, %r9  ASM_LINE_END                          \
        movl   $0xffffffff, %eax  ASM_LINE_END                  \
        mulxq  %rax, %rax, %rcx  ASM_LINE_END                     \
        adcxq  %rax, %r9  ASM_LINE_END                          \
        adoxq  %rcx, %r10  ASM_LINE_END                         \
        adcxq  %rdx, %r10  ASM_LINE_END                         \
        movl   $0x0, %eax  ASM_LINE_END                         \
        movl   $0x0, %ecx  ASM_LINE_END                         \
        adoxq  %rax, %rax  ASM_LINE_END                         \
        adcq   %rax, %r11  ASM_LINE_END                         \
        adcq   %rcx, %r12  ASM_LINE_END                         \
        adcq   %rcx, %r13  ASM_LINE_END                         \
        adcq   %rcx, %rcx  ASM_LINE_END                         \
        subq   $0x1, %rcx  ASM_LINE_END                         \
        movl   $0xffffffff, %edx  ASM_LINE_END                  \
        xorq   %rax, %rax  ASM_LINE_END                         \
        andq   %rcx, %rdx  ASM_LINE_END                         \
        subq   %rdx, %rax  ASM_LINE_END                         \
        andq   $0x1, %rcx  ASM_LINE_END                         \
        subq   %rax, %r8  ASM_LINE_END                          \
        movq   %r8, P0  ASM_LINE_END                         \
        sbbq   %rdx, %r9  ASM_LINE_END                          \
        movq   %r9, 0x8+P0  ASM_LINE_END                     \
        sbbq   %rcx, %r10  ASM_LINE_END                         \
        movq   %r10, 0x10+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r11, 0x18+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r12  ASM_LINE_END                         \
        movq   %r12, 0x20+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        movq   %r13, 0x28+P0

// A weak version of add that only guarantees sum in 6 digits

#define weakadd_p384(P0,P1,P2)                  \
        movq   P1, %rax  ASM_LINE_END                        \
        addq   P2, %rax  ASM_LINE_END                        \
        movq   0x8+P1, %rcx  ASM_LINE_END                    \
        adcq   0x8+P2, %rcx  ASM_LINE_END                    \
        movq   0x10+P1, %r8  ASM_LINE_END                    \
        adcq   0x10+P2, %r8  ASM_LINE_END                    \
        movq   0x18+P1, %r9  ASM_LINE_END                    \
        adcq   0x18+P2, %r9  ASM_LINE_END                    \
        movq   0x20+P1, %r10  ASM_LINE_END                   \
        adcq   0x20+P2, %r10  ASM_LINE_END                   \
        movq   0x28+P1, %r11  ASM_LINE_END                   \
        adcq   0x28+P2, %r11  ASM_LINE_END                   \
        sbbq   %rdx, %rdx  ASM_LINE_END                         \
        movl   $1, %ebx  ASM_LINE_END                           \
        andq   %rdx, %rbx  ASM_LINE_END                         \
        movl   $0xffffffff, %ebp  ASM_LINE_END                  \
        andq   %rbp, %rdx  ASM_LINE_END                         \
        xorq   %rbp, %rbp  ASM_LINE_END                         \
        subq   %rdx, %rbp  ASM_LINE_END                         \
        addq   %rbp, %rax  ASM_LINE_END                         \
        movq   %rax, P0  ASM_LINE_END                        \
        adcq   %rdx, %rcx  ASM_LINE_END                         \
        movq   %rcx, 0x8+P0  ASM_LINE_END                    \
        adcq   %rbx, %r8  ASM_LINE_END                          \
        movq   %r8, 0x10+P0  ASM_LINE_END                    \
        adcq   $0x0, %r9  ASM_LINE_END                          \
        movq   %r9, 0x18+P0  ASM_LINE_END                    \
        adcq   $0x0, %r10  ASM_LINE_END                         \
        movq   %r10, 0x20+P0  ASM_LINE_END                   \
        adcq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r11, 0x28+P0

// P0 = 3 * P1 - 8 * P2

#define cmsub38_p384(P0,P1,P2)                  \
        movq    $0x00000000ffffffff, %r8  ASM_LINE_END         \
        subq    P2, %r8  ASM_LINE_END                       \
        movq    $0xffffffff00000000, %r9  ASM_LINE_END         \
        sbbq    8+P2, %r9  ASM_LINE_END                     \
        movq    $0xfffffffffffffffe, %r10  ASM_LINE_END        \
        sbbq    16+P2, %r10  ASM_LINE_END                   \
        movq    $0xffffffffffffffff, %r11  ASM_LINE_END        \
        sbbq    24+P2, %r11  ASM_LINE_END                   \
        movq    $0xffffffffffffffff, %r12  ASM_LINE_END        \
        sbbq    32+P2, %r12  ASM_LINE_END                   \
        movq    $0xffffffffffffffff, %r13  ASM_LINE_END        \
        sbbq    40+P2, %r13  ASM_LINE_END                   \
        movq    %r13, %r14  ASM_LINE_END                       \
        shrq    $61, %r14  ASM_LINE_END                        \
        shldq   $3, %r12, %r13  ASM_LINE_END                    \
        shldq   $3, %r11, %r12  ASM_LINE_END                    \
        shldq   $3, %r10, %r11  ASM_LINE_END                    \
        shldq   $3, %r9, %r10  ASM_LINE_END                     \
        shldq   $3, %r8, %r9  ASM_LINE_END                      \
        shlq    $3, %r8  ASM_LINE_END                          \
        addq    $1, %r14  ASM_LINE_END                         \
        xorl    %ecx, %ecx  ASM_LINE_END                       \
        movq    $3, %rdx  ASM_LINE_END                         \
        mulxq   P1, %rax, %rbx  ASM_LINE_END                 \
        adcxq   %rax, %r8  ASM_LINE_END                        \
        adoxq   %rbx, %r9  ASM_LINE_END                        \
        mulxq   8+P1, %rax, %rbx  ASM_LINE_END               \
        adcxq   %rax, %r9  ASM_LINE_END                        \
        adoxq   %rbx, %r10  ASM_LINE_END                       \
        mulxq   16+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r10  ASM_LINE_END                       \
        adoxq   %rbx, %r11  ASM_LINE_END                       \
        mulxq   24+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r11  ASM_LINE_END                       \
        adoxq   %rbx, %r12  ASM_LINE_END                       \
        mulxq   32+P1, %rax, %rbx  ASM_LINE_END              \
        adcxq   %rax, %r12  ASM_LINE_END                       \
        adoxq   %rbx, %r13  ASM_LINE_END                       \
        mulxq   40+P1, %rax, %rdx  ASM_LINE_END              \
        adcxq   %rax, %r13  ASM_LINE_END                       \
        adoxq   %r14, %rdx  ASM_LINE_END                       \
        adcxq   %rcx, %rdx  ASM_LINE_END                       \
        xorq   %rcx, %rcx  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        mulxq  %rax, %rax, %rcx  ASM_LINE_END                     \
        adcxq  %rax, %r8  ASM_LINE_END                          \
        adoxq  %rcx, %r9  ASM_LINE_END                          \
        movl   $0xffffffff, %eax  ASM_LINE_END                  \
        mulxq  %rax, %rax, %rcx  ASM_LINE_END                     \
        adcxq  %rax, %r9  ASM_LINE_END                          \
        adoxq  %rcx, %r10  ASM_LINE_END                         \
        adcxq  %rdx, %r10  ASM_LINE_END                         \
        movl   $0x0, %eax  ASM_LINE_END                         \
        movl   $0x0, %ecx  ASM_LINE_END                         \
        adoxq  %rax, %rax  ASM_LINE_END                         \
        adcq   %rax, %r11  ASM_LINE_END                         \
        adcq   %rcx, %r12  ASM_LINE_END                         \
        adcq   %rcx, %r13  ASM_LINE_END                         \
        adcq   %rcx, %rcx  ASM_LINE_END                         \
        subq   $0x1, %rcx  ASM_LINE_END                         \
        movl   $0xffffffff, %edx  ASM_LINE_END                  \
        xorq   %rax, %rax  ASM_LINE_END                         \
        andq   %rcx, %rdx  ASM_LINE_END                         \
        subq   %rdx, %rax  ASM_LINE_END                         \
        andq   $0x1, %rcx  ASM_LINE_END                         \
        subq   %rax, %r8  ASM_LINE_END                          \
        movq   %r8, P0  ASM_LINE_END                         \
        sbbq   %rdx, %r9  ASM_LINE_END                          \
        movq   %r9, 0x8+P0  ASM_LINE_END                     \
        sbbq   %rcx, %r10  ASM_LINE_END                         \
        movq   %r10, 0x10+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r11, 0x18+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r12  ASM_LINE_END                         \
        movq   %r12, 0x20+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r13  ASM_LINE_END                         \
        movq   %r13, 0x28+P0

S2N_BN_SYMBOL(p384_montjdouble):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Save registers and make room on stack for temporary variables
// Save the output pointer %rdi which gets overwritten in earlier
// operations before it is used.

        pushq  %rbx
        pushq  %rbp
        pushq  %r12
        pushq  %r13
        pushq  %r14
        pushq  %r15

        subq    $NSPACE, %rsp

        movq    %rdi, input_z

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_p384(z2,z_1)
        montsqr_p384(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        weakadd_p384(t1,x_1,z2)
        sub_p384(t2,x_1,z2)
        montmul_p384(x2p,t1,t2)

// t1 = y + z
// x4p = x2p^2
// xy2 = x * y^2

        add_p384(t1,y_1,z_1)
        montsqr_p384(x4p,x2p)
        montmul_p384(xy2,x_1,y2)

// t2 = (y + z)^2

        montsqr_p384(t2,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p384(d,12,xy2,9,x4p)
        sub_p384(t1,t2,z2)

// y4 = y^4

        montsqr_p384(y4,y2)

// Restore the output pointer to write to x_3, y_3 and z_3.

        movq    input_z, %rdi

// z_3' = 2 * y * z
// dx2 = d * x2p

        sub_p384(z_3,t1,y2)
        montmul_p384(dx2,d,x2p)

// x' = 4 * xy2 - d

        cmsub41_p384(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p384(y_3,dx2,y4)

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
