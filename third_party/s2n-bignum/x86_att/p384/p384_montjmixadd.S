// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjmixadd
//      (uint64_t p3[static 18],uint64_t p1[static 18],uint64_t p2[static 12]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjmixadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjmixadd)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Pointer-offset pairs for inputs and outputs
// These assume %rdi = p3, %rsi = p1 and %rcx = p2,
// which needs to be set up explicitly before use.
// However the %rdi value never changes.

#define x_1 0(%rsi)
#define y_1 NUMSIZE(%rsi)
#define z_1 (2*NUMSIZE)(%rsi)

#define x_2 0(%rcx)
#define y_2 NUMSIZE(%rcx)

#define x_3 0(%rdi)
#define y_3 NUMSIZE(%rdi)
#define z_3 (2*NUMSIZE)(%rdi)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define zp2 (NUMSIZE*0)(%rsp)
#define ww (NUMSIZE*0)(%rsp)
#define resx (NUMSIZE*0)(%rsp)

#define yd (NUMSIZE*1)(%rsp)
#define y2a (NUMSIZE*1)(%rsp)

#define x2a (NUMSIZE*2)(%rsp)
#define zzx2 (NUMSIZE*2)(%rsp)

#define zz (NUMSIZE*3)(%rsp)
#define t1 (NUMSIZE*3)(%rsp)

#define t2 (NUMSIZE*4)(%rsp)
#define zzx1 (NUMSIZE*4)(%rsp)
#define resy (NUMSIZE*4)(%rsp)

#define xd (NUMSIZE*5)(%rsp)
#define resz (NUMSIZE*5)(%rsp)

// Temporaries for the actual input pointers

#define input_x (NUMSIZE*6)(%rsp)
#define input_y (NUMSIZE*6+8)(%rsp)

#define NSPACE (NUMSIZE*6+16)

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
        mulxq  %rdx, %rax, %rsi  ASM_LINE_END                     \
        adcxq  %rbp, %rbp  ASM_LINE_END                         \
        adoxq  %rax, %rbp  ASM_LINE_END                         \
        movl   $0x0, %eax  ASM_LINE_END                         \
        adcxq  %rax, %rsi  ASM_LINE_END                         \
        adoxq  %rax, %rsi  ASM_LINE_END                         \
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
        adcq   %r13, %rsi  ASM_LINE_END                         \
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
        adcq   %rsi, %r13  ASM_LINE_END                         \
        adcq   $0x0, %r8  ASM_LINE_END                          \
        cmovne %rax, %r14  ASM_LINE_END                         \
        cmovne %r9, %r15  ASM_LINE_END                          \
        cmovne %r10, %rcx  ASM_LINE_END                         \
        cmovne %r11, %rbx  ASM_LINE_END                         \
        cmovne %r12, %rbp  ASM_LINE_END                         \
        cmovne %r13, %rsi  ASM_LINE_END                         \
        movq   %r14, P0  ASM_LINE_END                        \
        movq   %r15, 0x8+P0  ASM_LINE_END                    \
        movq   %rcx, 0x10+P0  ASM_LINE_END                   \
        movq   %rbx, 0x18+P0  ASM_LINE_END                   \
        movq   %rbp, 0x20+P0  ASM_LINE_END                   \
        movq   %rsi, 0x28+P0

// Almost-Montgomery variant which we use when an input to other muls
// with the other argument fully reduced (which is always safe).

#define amontsqr_p384(P0,P1)                    \
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
        mulxq  %rdx, %rax, %rsi  ASM_LINE_END                     \
        adcxq  %rbp, %rbp  ASM_LINE_END                         \
        adoxq  %rax, %rbp  ASM_LINE_END                         \
        movl   $0x0, %eax  ASM_LINE_END                         \
        adcxq  %rax, %rsi  ASM_LINE_END                         \
        adoxq  %rax, %rsi  ASM_LINE_END                         \
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
        adcq   %r13, %rsi  ASM_LINE_END                         \
        movl   $0x0, %r8d  ASM_LINE_END                         \
        movq   $0xffffffff00000001, %rax  ASM_LINE_END          \
        movl   $0xffffffff, %r9d  ASM_LINE_END                  \
        movl   $0x1, %r10d  ASM_LINE_END                        \
        cmovnc %r8, %rax  ASM_LINE_END                         \
        cmovnc %r8, %r9  ASM_LINE_END                          \
        cmovnc %r8, %r10  ASM_LINE_END                         \
        addq   %rax, %r14  ASM_LINE_END                        \
        adcq   %r9, %r15  ASM_LINE_END                         \
        adcq   %r10, %rcx  ASM_LINE_END                        \
        adcq   %r8, %rbx  ASM_LINE_END                         \
        adcq   %r8, %rbp  ASM_LINE_END                         \
        adcq   %r8, %rsi  ASM_LINE_END                         \
        movq   %r14, P0  ASM_LINE_END                        \
        movq   %r15, 0x8+P0  ASM_LINE_END                    \
        movq   %rcx, 0x10+P0  ASM_LINE_END                   \
        movq   %rbx, 0x18+P0  ASM_LINE_END                   \
        movq   %rbp, 0x20+P0  ASM_LINE_END                   \
        movq   %rsi, 0x28+P0

// Corresponds exactly to bignum_sub_p384

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
        movl   $0xffffffff, %esi  ASM_LINE_END                  \
        andq   %rsi, %rcx  ASM_LINE_END                         \
        xorq   %rsi, %rsi  ASM_LINE_END                         \
        subq   %rcx, %rsi  ASM_LINE_END                         \
        subq   %rsi, %rax  ASM_LINE_END                         \
        movq   %rax, P0  ASM_LINE_END                        \
        sbbq   %rcx, %rdx  ASM_LINE_END                         \
        movq   %rdx, 0x8+P0  ASM_LINE_END                    \
        sbbq   %rax, %rax  ASM_LINE_END                         \
        andq   %rsi, %rcx  ASM_LINE_END                         \
        negq   %rax ASM_LINE_END                             \
        sbbq   %rcx, %r8  ASM_LINE_END                          \
        movq   %r8, 0x10+P0  ASM_LINE_END                    \
        sbbq   $0x0, %r9  ASM_LINE_END                          \
        movq   %r9, 0x18+P0  ASM_LINE_END                    \
        sbbq   $0x0, %r10  ASM_LINE_END                         \
        movq   %r10, 0x20+P0  ASM_LINE_END                   \
        sbbq   $0x0, %r11  ASM_LINE_END                         \
        movq   %r11, 0x28+P0

// Additional macros to help with final multiplexing

#define testzero6(P)                            \
        movq    P, %rax  ASM_LINE_END                       \
        movq    8+P, %rdx  ASM_LINE_END                     \
        orq     16+P, %rax  ASM_LINE_END                    \
        orq     24+P, %rdx  ASM_LINE_END                    \
        orq     32+P, %rax  ASM_LINE_END                    \
        orq     40+P, %rdx  ASM_LINE_END                    \
        orq     %rdx, %rax

#define mux6(r0,r1,r2,r3,r4,r5,PNE,PEQ)         \
        movq    PEQ, %rax  ASM_LINE_END                     \
        movq    PNE, r0  ASM_LINE_END                      \
        cmovzq  %rax, r0  ASM_LINE_END                        \
        movq    8+PEQ, %rax  ASM_LINE_END                   \
        movq    8+PNE, r1  ASM_LINE_END                    \
        cmovzq  %rax, r1  ASM_LINE_END                        \
        movq    16+PEQ, %rax  ASM_LINE_END                  \
        movq    16+PNE, r2  ASM_LINE_END                   \
        cmovzq  %rax, r2  ASM_LINE_END                        \
        movq    24+PEQ, %rax  ASM_LINE_END                  \
        movq    24+PNE, r3  ASM_LINE_END                   \
        cmovzq  %rax, r3  ASM_LINE_END                        \
        movq    32+PEQ, %rax  ASM_LINE_END                  \
        movq    32+PNE, r4  ASM_LINE_END                   \
        cmovzq  %rax, r4  ASM_LINE_END                        \
        movq    40+PEQ, %rax  ASM_LINE_END                  \
        movq    40+PNE, r5  ASM_LINE_END                   \
        cmovzq  %rax, r5

#define load6(r0,r1,r2,r3,r4,r5,P)              \
        movq    P, r0  ASM_LINE_END                        \
        movq    8+P, r1  ASM_LINE_END                      \
        movq    16+P, r2  ASM_LINE_END                     \
        movq    24+P, r3  ASM_LINE_END                     \
        movq    32+P, r4  ASM_LINE_END                     \
        movq    40+P, r5

#define store6(P,r0,r1,r2,r3,r4,r5)             \
        movq    r0, P  ASM_LINE_END                        \
        movq    r1, 8+P  ASM_LINE_END                      \
        movq    r2, 16+P  ASM_LINE_END                     \
        movq    r3, 24+P  ASM_LINE_END                     \
        movq    r4, 32+P  ASM_LINE_END                     \
        movq    r5, 40+P

S2N_BN_SYMBOL(p384_montjmixadd):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

// Save registers and make room on stack for temporary variables
// Put the input arguments in non-volatile places on the stack

        pushq  %rbx
        pushq  %rbp
        pushq  %r12
        pushq  %r13
        pushq  %r14
        pushq  %r15

        subq    $NSPACE, %rsp

        movq    %rsi, input_x
        movq    %rdx, input_y

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        amontsqr_p384(zp2,z_1)

        movq    input_x, %rsi
        movq    input_y, %rcx
        montmul_p384(y2a,z_1,y_2)

        movq    input_y, %rcx
        montmul_p384(x2a,zp2,x_2)

        montmul_p384(y2a,zp2,y2a)

        movq    input_x, %rsi
        sub_p384(xd,x2a,x_1)
        movq    input_x, %rsi
        sub_p384(yd,y2a,y_1)

        amontsqr_p384(zz,xd)
        montsqr_p384(ww,yd)

        movq    input_x, %rsi
        montmul_p384(zzx1,zz,x_1)
        montmul_p384(zzx2,zz,x2a)

        sub_p384(resx,ww,zzx1)
        sub_p384(t1,zzx2,zzx1)

        movq    input_x, %rsi
        montmul_p384(resz,xd,z_1)

        sub_p384(resx,resx,zzx2)

        sub_p384(t2,zzx1,resx)

        movq    input_x, %rsi
        montmul_p384(t1,t1,y_1)
        montmul_p384(t2,yd,t2)

        sub_p384(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        movq    input_x, %rsi
        testzero6(z_1)

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with a z = 1 coordinate (in
// Montgomery form so not the simple constant 1 but rather 2^384 - p_384),
// hence giving 0 + p2 = p2 for the final result.

        movq    input_y, %rcx
        mux6(%r8,%r9,%r10,%r11,%rbx,%rbp,resx,x_2)
        mux6(%r12,%r13,%r14,%r15,%rdx,%rcx,resy,y_2)

        store6(x_3,%r8,%r9,%r10,%r11,%rbx,%rbp)
        store6(y_3,%r12,%r13,%r14,%r15,%rdx,%rcx)

        load6(%r8,%r9,%r10,%r11,%rbx,%rbp,resz)
        movq    $0xffffffff00000001, %rax
        cmovzq  %rax, %r8
        movl    $0x00000000ffffffff, %eax
        cmovzq  %rax, %r9
        movq    $1, %rax
        cmovzq  %rax, %r10
        movl    $0, %eax
        cmovzq  %rax, %r11
        cmovzq  %rax, %rbx
        cmovzq  %rax, %rbp

        store6(z_3,%r8,%r9,%r10,%r11,%rbx,%rbp)

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
