// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// The x25519 function for curve25519
// Inputs scalar[4], point[4]; output res[4]
//
// extern void curve25519_x25519
//   (uint64_t res[static 4],uint64_t scalar[static 4],uint64_t point[static 4])
//
// The function has a second prototype considering the arguments as arrays
// of bytes rather than 64-bit words. The underlying code is the same, since
// the x86 platform is little-endian.
//
// extern void curve25519_x25519_byte
//   (uint8_t res[static 32],uint8_t scalar[static 32],uint8_t point[static 32])
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


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519_byte)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519_byte)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for the input result argument during the whole body
// and other variables that are only needed prior to the modular inverse.

#define res  12*NUMSIZE(%rsp)
#define i  12*NUMSIZE+8(%rsp)
#define swap  12*NUMSIZE+16(%rsp)

// Pointers to result x coord to be written, assuming the base "res"
// has been loaded into %rbp

#define resx 0(%rbp)

// Pointer-offset pairs for temporaries on stack with some aliasing.
// Both dmsn and dnsm need space for >= 5 digits, and we allocate 8

#define scalar (0*NUMSIZE)(%rsp)

#define pointx (1*NUMSIZE)(%rsp)

#define dm (2*NUMSIZE)(%rsp)

#define zm (3*NUMSIZE)(%rsp)
#define sm (3*NUMSIZE)(%rsp)
#define dpro (3*NUMSIZE)(%rsp)

#define sn (4*NUMSIZE)(%rsp)

#define zn (5*NUMSIZE)(%rsp)
#define dn (5*NUMSIZE)(%rsp)
#define e (5*NUMSIZE)(%rsp)

#define dmsn (6*NUMSIZE)(%rsp)
#define p (6*NUMSIZE)(%rsp)

#define xm (8*NUMSIZE)(%rsp)
#define dnsm (8*NUMSIZE)(%rsp)
#define spro (8*NUMSIZE)(%rsp)

#define xn (10*NUMSIZE)(%rsp)
#define s (10*NUMSIZE)(%rsp)

#define d (11*NUMSIZE)(%rsp)

// Total size to reserve on the stack
// This includes space for the 3 other variables above
// and rounds up to a multiple of 32

#define NSPACE (13*NUMSIZE)

// Macro wrapping up the basic field operation bignum_mul_p25519, only
// trivially different from a pure function call to that subroutine.

#define mul_p25519(P0,P1,P2)                    \
        xorl   %edi, %edi ;                        \
        movq   P2, %rdx ;                       \
        mulxq  P1, %r8, %r9 ;                    \
        mulxq  0x8+P1, %rax, %r10 ;              \
        addq   %rax, %r9 ;                         \
        mulxq  0x10+P1, %rax, %r11 ;             \
        adcq   %rax, %r10 ;                        \
        mulxq  0x18+P1, %rax, %r12 ;             \
        adcq   %rax, %r11 ;                        \
        adcq   %rdi, %r12 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x8+P2, %rdx ;                   \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x18+P1, %rax, %r13 ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rdi, %r13 ;                        \
        adcxq  %rdi, %r13 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x10+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x18+P1, %rax, %r14 ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rdi, %r14 ;                        \
        adcxq  %rdi, %r14 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x18+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        mulxq  0x18+P1, %rax, %r15 ;             \
        adcxq  %rax, %r14 ;                        \
        adoxq  %rdi, %r15 ;                        \
        adcxq  %rdi, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %edi, %edi ;                        \
        mulxq  %r12, %rax, %rbx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rbx, %r9 ;                         \
        mulxq  %r13, %rax, %rbx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  %r14, %rax, %rbx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rdi, %r12 ;                        \
        adcxq  %rdi, %r12 ;                        \
        shldq  $0x1, %r11, %r12 ;                   \
        movl   $0x13, %edx ;                       \
        incq   %r12;                             \
        bts    $63, %r11 ;                         \
        mulxq  %r12, %rax, %rbx ;                   \
        addq   %rax, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rdi, %r10 ;                        \
        adcq   %rdi, %r11 ;                        \
        sbbq   %rax, %rax ;                        \
        notq   %rax;                             \
        andq   %rdx, %rax ;                        \
        subq   %rax, %r8 ;                         \
        sbbq   %rdi, %r9 ;                         \
        sbbq   %rdi, %r10 ;                        \
        sbbq   %rdi, %r11 ;                        \
        btr    $63, %r11 ;                         \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// A version of multiplication that only guarantees output < 2 * p_25519.
// This basically skips the +1 and final correction in quotient estimation.

#define mul_4(P0,P1,P2)                         \
        xorl   %ecx, %ecx ;                        \
        movq   P2, %rdx ;                       \
        mulxq  P1, %r8, %r9 ;                    \
        mulxq  0x8+P1, %rax, %r10 ;              \
        addq   %rax, %r9 ;                         \
        mulxq  0x10+P1, %rax, %r11 ;             \
        adcq   %rax, %r10 ;                        \
        mulxq  0x18+P1, %rax, %r12 ;             \
        adcq   %rax, %r11 ;                        \
        adcq   %rcx, %r12 ;                        \
        xorl   %ecx, %ecx ;                        \
        movq   0x8+P2, %rdx ;                   \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x18+P1, %rax, %r13 ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rcx, %r13 ;                        \
        adcxq  %rcx, %r13 ;                        \
        xorl   %ecx, %ecx ;                        \
        movq   0x10+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x18+P1, %rax, %r14 ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rcx, %r14 ;                        \
        adcxq  %rcx, %r14 ;                        \
        xorl   %ecx, %ecx ;                        \
        movq   0x18+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        mulxq  0x18+P1, %rax, %r15 ;             \
        adcxq  %rax, %r14 ;                        \
        adoxq  %rcx, %r15 ;                        \
        adcxq  %rcx, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %ecx, %ecx ;                        \
        mulxq  %r12, %rax, %rbx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rbx, %r9 ;                         \
        mulxq  %r13, %rax, %rbx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  %r14, %rax, %rbx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rcx, %r12 ;                        \
        adcxq  %rcx, %r12 ;                        \
        shldq  $0x1, %r11, %r12 ;                   \
        btr    $0x3f, %r11 ;                       \
        movl   $0x13, %edx ;                       \
        imulq  %r12, %rdx ;                        \
        addq   %rdx, %r8 ;                         \
        adcq   %rcx, %r9 ;                         \
        adcq   %rcx, %r10 ;                        \
        adcq   %rcx, %r11 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Multiplication just giving a 5-digit result (actually < 39 * p_25519)
// by not doing anything beyond the first stage of reduction

#define mul_5(P0,P1,P2)                         \
        xorl   %edi, %edi ;                        \
        movq   P2, %rdx ;                       \
        mulxq  P1, %r8, %r9 ;                    \
        mulxq  0x8+P1, %rax, %r10 ;              \
        addq   %rax, %r9 ;                         \
        mulxq  0x10+P1, %rax, %r11 ;             \
        adcq   %rax, %r10 ;                        \
        mulxq  0x18+P1, %rax, %r12 ;             \
        adcq   %rax, %r11 ;                        \
        adcq   %rdi, %r12 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x8+P2, %rdx ;                   \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x18+P1, %rax, %r13 ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rdi, %r13 ;                        \
        adcxq  %rdi, %r13 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x10+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x18+P1, %rax, %r14 ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rdi, %r14 ;                        \
        adcxq  %rdi, %r14 ;                        \
        xorl   %edi, %edi ;                        \
        movq   0x18+P2, %rdx ;                  \
        mulxq  P1, %rax, %rbx ;                  \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        mulxq  0x8+P1, %rax, %rbx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rbx, %r13 ;                        \
        mulxq  0x10+P1, %rax, %rbx ;             \
        adcxq  %rax, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        mulxq  0x18+P1, %rax, %r15 ;             \
        adcxq  %rax, %r14 ;                        \
        adoxq  %rdi, %r15 ;                        \
        adcxq  %rdi, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %edi, %edi ;                        \
        mulxq  %r12, %rax, %rbx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rbx, %r9 ;                         \
        mulxq  %r13, %rax, %rbx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rbx, %r10 ;                        \
        mulxq  %r14, %rax, %rbx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rbx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rdi, %r12 ;                        \
        adcxq  %rdi, %r12 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0 ;                  \
        movq   %r12, 0x20+P0

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        movq   P1, %rdx ;                       \
        mulxq  %rdx, %r8, %r15 ;                    \
        mulxq  0x8+P1, %r9, %r10 ;               \
        mulxq  0x18+P1, %r11, %r12 ;             \
        movq   0x10+P1, %rdx ;                  \
        mulxq  0x18+P1, %r13, %r14 ;             \
        xorl   %ebx, %ebx ;                        \
        mulxq  P1, %rax, %rcx ;                  \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rcx, %r11 ;                        \
        mulxq  0x8+P1, %rax, %rcx ;              \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rcx, %r12 ;                        \
        movq   0x18+P1, %rdx ;                  \
        mulxq  0x8+P1, %rax, %rcx ;              \
        adcxq  %rax, %r12 ;                        \
        adoxq  %rcx, %r13 ;                        \
        adcxq  %rbx, %r13 ;                        \
        adoxq  %rbx, %r14 ;                        \
        adcq   %rbx, %r14 ;                        \
        xorl   %ebx, %ebx ;                        \
        adcxq  %r9, %r9 ;                          \
        adoxq  %r15, %r9 ;                         \
        movq   0x8+P1, %rdx ;                   \
        mulxq  %rdx, %rax, %rdx ;                   \
        adcxq  %r10, %r10 ;                        \
        adoxq  %rax, %r10 ;                        \
        adcxq  %r11, %r11 ;                        \
        adoxq  %rdx, %r11 ;                        \
        movq   0x10+P1, %rdx ;                  \
        mulxq  %rdx, %rax, %rdx ;                   \
        adcxq  %r12, %r12 ;                        \
        adoxq  %rax, %r12 ;                        \
        adcxq  %r13, %r13 ;                        \
        adoxq  %rdx, %r13 ;                        \
        movq   0x18+P1, %rdx ;                  \
        mulxq  %rdx, %rax, %r15 ;                   \
        adcxq  %r14, %r14 ;                        \
        adoxq  %rax, %r14 ;                        \
        adcxq  %rbx, %r15 ;                        \
        adoxq  %rbx, %r15 ;                        \
        movl   $0x26, %edx ;                       \
        xorl   %ebx, %ebx ;                        \
        mulxq  %r12, %rax, %rcx ;                   \
        adcxq  %rax, %r8 ;                         \
        adoxq  %rcx, %r9 ;                         \
        mulxq  %r13, %rax, %rcx ;                   \
        adcxq  %rax, %r9 ;                         \
        adoxq  %rcx, %r10 ;                        \
        mulxq  %r14, %rax, %rcx ;                   \
        adcxq  %rax, %r10 ;                        \
        adoxq  %rcx, %r11 ;                        \
        mulxq  %r15, %rax, %r12 ;                   \
        adcxq  %rax, %r11 ;                        \
        adoxq  %rbx, %r12 ;                        \
        adcxq  %rbx, %r12 ;                        \
        shldq  $0x1, %r11, %r12 ;                   \
        btr    $0x3f, %r11 ;                       \
        movl   $0x13, %edx ;                       \
        imulq  %r12, %rdx ;                        \
        addq   %rdx, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rbx, %r10 ;                        \
        adcq   %rbx, %r11 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Add 5-digit inputs and normalize to 4 digits

#define add5_4(P0,P1,P2)                        \
        movq    P1, %r8 ;                       \
        addq    P2, %r8 ;                       \
        movq    8+P1, %r9 ;                     \
        adcq    8+P2, %r9 ;                     \
        movq    16+P1, %r10 ;                   \
        adcq    16+P2, %r10 ;                   \
        movq    24+P1, %r11 ;                   \
        adcq    24+P2, %r11 ;                   \
        movq    32+P1, %r12 ;                   \
        adcq    32+P2, %r12 ;                   \
        xorl    %ebx, %ebx ;                       \
        shldq  $0x1, %r11, %r12 ;                   \
        btr    $0x3f, %r11 ;                       \
        movl   $0x13, %edx ;                       \
        imulq  %r12, %rdx ;                        \
        addq   %rdx, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rbx, %r10 ;                        \
        adcq   %rbx, %r11 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Modular addition with double modulus 2 * p_25519 = 2^256 - 38.
// This only ensures that the result fits in 4 digits, not that it is reduced
// even w.r.t. double modulus. The result is always correct modulo provided
// the sum of the inputs is < 2^256 + 2^256 - 38, so in particular provided
// at least one of them is reduced double modulo.

#define add_twice4(P0,P1,P2)                    \
        movq    P1, %r8 ;                       \
        xorl    %ecx, %ecx ;                       \
        addq    P2, %r8 ;                       \
        movq    0x8+P1, %r9 ;                   \
        adcq    0x8+P2, %r9 ;                   \
        movq    0x10+P1, %r10 ;                 \
        adcq    0x10+P2, %r10 ;                 \
        movq    0x18+P1, %r11 ;                 \
        adcq    0x18+P2, %r11 ;                 \
        movl    $38, %eax ;                        \
        cmovncq %rcx, %rax ;                       \
        addq    %rax, %r8 ;                        \
        adcq    %rcx, %r9 ;                        \
        adcq    %rcx, %r10 ;                       \
        adcq    %rcx, %r11 ;                       \
        movq    %r8, P0 ;                       \
        movq    %r9, 0x8+P0 ;                   \
        movq    %r10, 0x10+P0 ;                 \
        movq    %r11, 0x18+P0

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(P0,P1,P2)                    \
        movq    P1, %r8 ;                       \
        xorl    %ebx, %ebx ;                       \
        subq    P2, %r8 ;                       \
        movq    8+P1, %r9 ;                     \
        sbbq    8+P2, %r9 ;                     \
        movl    $38, %ecx ;                        \
        movq    16+P1, %r10 ;                   \
        sbbq    16+P2, %r10 ;                   \
        movq    24+P1, %rax ;                   \
        sbbq    24+P2, %rax ;                   \
        cmovncq %rbx, %rcx ;                       \
        subq    %rcx, %r8 ;                        \
        sbbq    %rbx, %r9 ;                        \
        sbbq    %rbx, %r10 ;                       \
        sbbq    %rbx, %rax ;                       \
        movq    %r8, P0 ;                       \
        movq    %r9, 8+P0 ;                     \
        movq    %r10, 16+P0 ;                   \
        movq    %rax, 24+P0

// 5-digit subtraction with upward bias to make it positive, adding
// 1000 * (2^255 - 19) = 2^256 * 500 - 19000, then normalizing to 4 digits

#define sub5_4(P0,P1,P2)                        \
        movq    P1, %r8 ;                       \
        subq    P2, %r8 ;                       \
        movq    8+P1, %r9 ;                     \
        sbbq    8+P2, %r9 ;                     \
        movq    16+P1, %r10 ;                   \
        sbbq    16+P2, %r10 ;                   \
        movq    24+P1, %r11 ;                   \
        sbbq    24+P2, %r11 ;                   \
        movq    32+P1, %r12 ;                   \
        sbbq    32+P2, %r12 ;                   \
        xorl    %ebx, %ebx ;                       \
        subq    $19000, %r8 ;                      \
        sbbq    %rbx, %r9 ;                        \
        sbbq    %rbx, %r10 ;                       \
        sbbq    %rbx, %r11 ;                       \
        sbbq    %rbx, %r12 ;                       \
        addq    $500, %r12 ;                       \
        shldq  $0x1, %r11, %r12 ;                   \
        btr    $0x3f, %r11 ;                       \
        movl   $0x13, %edx ;                       \
        imulq  %r12, %rdx ;                        \
        addq   %rdx, %r8 ;                         \
        adcq   %rbx, %r9 ;                         \
        adcq   %rbx, %r10 ;                        \
        adcq   %rbx, %r11 ;                        \
        movq   %r8, P0 ;                        \
        movq   %r9, 0x8+P0 ;                    \
        movq   %r10, 0x10+P0 ;                  \
        movq   %r11, 0x18+P0

// Combined z = c * x + y with reduction only < 2 * p_25519
// It is assumed that 19 * (c * x + y) < 2^60 * 2^256 so we
// don't need a high mul in the final part.

#define cmadd_4(P0,C1,P2,P3)                    \
        movq    P3, %r8 ;                       \
        movq    8+P3, %r9 ;                     \
        movq    16+P3, %r10 ;                   \
        movq    24+P3, %r11 ;                   \
        xorl    %edi, %edi ;                       \
        movq    $C1, %rdx ;                        \
        mulxq   P2, %rax, %rbx ;                 \
        adcxq   %rax, %r8 ;                        \
        adoxq   %rbx, %r9 ;                        \
        mulxq   8+P2, %rax, %rbx ;               \
        adcxq   %rax, %r9 ;                        \
        adoxq   %rbx, %r10 ;                       \
        mulxq   16+P2, %rax, %rbx ;              \
        adcxq   %rax, %r10 ;                       \
        adoxq   %rbx, %r11 ;                       \
        mulxq   24+P2, %rax, %rbx ;              \
        adcxq   %rax, %r11 ;                       \
        adoxq   %rdi, %rbx ;                       \
        adcxq   %rdi, %rbx ;                       \
        shldq   $0x1, %r11, %rbx ;                  \
        btr     $63, %r11 ;                        \
        movl    $0x13, %edx ;                      \
        imulq   %rdx, %rbx ;                       \
        addq    %rbx, %r8 ;                        \
        adcq    %rdi, %r9 ;                        \
        adcq    %rdi, %r10 ;                       \
        adcq    %rdi, %r11 ;                       \
        movq    %r8, P0 ;                       \
        movq    %r9, 0x8+P0 ;                   \
        movq    %r10, 0x10+P0 ;                 \
        movq    %r11, 0x18+P0

// Multiplex: z := if NZ then x else y

#define mux_4(P0,P1,P2)                         \
        movq    P1, %rax ;                      \
        movq    P2, %rcx ;                      \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, P0 ;                      \
        movq    8+P1, %rax ;                    \
        movq    8+P2, %rcx ;                    \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, 8+P0 ;                    \
        movq    16+P1, %rax ;                   \
        movq    16+P2, %rcx ;                   \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, 16+P0 ;                   \
        movq    24+P1, %rax ;                   \
        movq    24+P2, %rcx ;                   \
        cmovzq  %rcx, %rax ;                       \
        movq    %rax, 24+P0

S2N_BN_SYMBOL(curve25519_x25519):
S2N_BN_SYMBOL(curve25519_x25519_byte):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

// Save registers, make room for temps, preserve input arguments.

        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        subq    $NSPACE, %rsp

// Move the output pointer to a stable place

        movq    %rdi, res

// Copy the inputs to the local variables with minimal mangling:
//
//  - The scalar is in principle turned into 01xxx...xxx000 but
//    in the structure below the special handling of these bits is
//    explicit in the main computation; the scalar is just copied.
//
//  - The point x coord is reduced mod 2^255 by masking off the
//    top bit. In the main loop we only need reduction < 2 * p_25519.

        movq    (%rsi), %rax
        movq    %rax, (%rsp)
        movq    8(%rsi), %rax
        movq    %rax, 8(%rsp)
        movq    16(%rsi), %rax
        movq    %rax, 16(%rsp)
        movq    24(%rsi), %rax
        movq    %rax, 24(%rsp)

        movq    (%rdx), %r8
        movq    8(%rdx), %r9
        movq    16(%rdx), %r10
        movq    24(%rdx), %r11
        btr     $63, %r11
        movq    %r8, 32(%rsp)
        movq    %r9, 40(%rsp)
        movq    %r10, 48(%rsp)
        movq    %r11, 56(%rsp)

// Initialize with explicit doubling in order to handle set bit 254.
// Set swap = 1 and (xm,zm) = (x,1) then double as (xn,zn) = 2 * (x,1).
// We use the fact that the point x coordinate is still in registers.
// Since zm = 1 we could do the doubling with an operation count of
// 2 * S + M instead of 2 * S + 2 * M, but it doesn't seem worth
// the slight complication arising from a different linear combination.

        movl    $1, %eax
        movq    %rax, swap
        movq    %r8, 256(%rsp)
        movq    %rax, 96(%rsp)
        xorl    %eax, %eax
        movq    %r9, 264(%rsp)
        movq    %rax, 104(%rsp)
        movq    %r10, 272(%rsp)
        movq    %rax, 112(%rsp)
        movq    %r11, 280(%rsp)
        movq    %rax, 120(%rsp)

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

        movl    $253, %eax
        movq    %rax, i

curve25519_x25519_scalarloop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn

        sub_twice4(dm,xm,zm)
        add_twice4(sn,xn,zn)
        sub_twice4(dn,xn,zn)
        add_twice4(sm,xm,zm)

// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        movq    i, %rdx
        movq    %rdx, %rcx
        shrq    $6, %rdx
        movq    (%rsp,%rdx,8), %rdx
        shrq    %cl, %rdx
        andq    $1, %rdx
        cmpq    swap, %rdx
        movq    %rdx, swap
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

        movq    i, %rax
        subq    $1, %rax
        movq    %rax, i
        cmpq    $3, %rax
        jnc     curve25519_x25519_scalarloop

// Multiplex directly into (xn,zn) then do three pure doubling steps;
// this accounts for the implicit zeroing of the three lowest bits
// of the scalar. On the very last doubling we *fully* reduce zn mod
// p_25519 to ease checking for degeneracy below.

        movq    swap, %rdx
        testq   %rdx, %rdx
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

        movq    $-19, %rax
        movq    $-1, %rcx
        movq    $0x7fffffffffffffff, %rdx
        movq    %rax, 128(%rsp)
        movq    %rcx, 136(%rsp)
        movq    %rcx, 144(%rsp)
        movq    %rdx, 152(%rsp)

// Prepare to call the modular inverse function to get zm = 1/zn

        movq    $4, %rdi
        leaq    96(%rsp), %rsi
        leaq    160(%rsp), %rdx
        leaq    128(%rsp), %rcx
        leaq    192(%rsp), %r8

// Inline copy of bignum_modinv, identical except for stripping out the
// prologue and epilogue saving and restoring registers and the initial
// test for k = 0 (which is trivially false here since k = 4). For more
// details and explanations see "x86/generic/bignum_modinv.S". Note
// that the stack it uses for its own temporaries is 80 bytes so it
// only overwrites pointx, scalar and dm, which are no longer needed.

        movq    %rsi, 0x40(%rsp)
        movq    %r8, 0x38(%rsp)
        movq    %rcx, 0x48(%rsp)
        leaq    (%r8,%rdi,8), %r10
        movq    %r10, 0x30(%rsp)
        leaq    (%r10,%rdi,8), %r15
        xorq    %r11, %r11
        xorq    %r9, %r9
curve25519_x25519_copyloop:
        movq    (%rdx,%r9,8), %rax
        movq    (%rcx,%r9,8), %rbx
        movq    %rax, (%r10,%r9,8)
        movq    %rbx, (%r15,%r9,8)
        movq    %rbx, (%r8,%r9,8)
        movq    %r11, (%rsi,%r9,8)
        incq    %r9
        cmpq    %rdi, %r9
        jb      curve25519_x25519_copyloop
        movq    (%r8), %rax
        movq    %rax, %rbx
        decq    %rbx
        movq    %rbx, (%r8)
        movq    %rax, %rbp
        movq    %rax, %r12
        shlq    $0x2, %rbp
        subq    %rbp, %r12
        xorq    $0x2, %r12
        movq    %r12, %rbp
        imulq   %rax, %rbp
        movl    $0x2, %eax
        addq    %rbp, %rax
        addq    $0x1, %rbp
        imulq   %rax, %r12
        imulq   %rbp, %rbp
        movl    $0x1, %eax
        addq    %rbp, %rax
        imulq   %rax, %r12
        imulq   %rbp, %rbp
        movl    $0x1, %eax
        addq    %rbp, %rax
        imulq   %rax, %r12
        imulq   %rbp, %rbp
        movl    $0x1, %eax
        addq    %rbp, %rax
        imulq   %rax, %r12
        movq    %r12, 0x28(%rsp)
        movq    %rdi, %rax
        shlq    $0x7, %rax
        movq    %rax, 0x20(%rsp)
curve25519_x25519_outerloop:
        movq    0x20(%rsp), %r13
        addq    $0x3f, %r13
        shrq    $0x6, %r13
        cmpq    %rdi, %r13
        cmovaeq %rdi, %r13
        xorq    %r12, %r12
        xorq    %r14, %r14
        xorq    %rbp, %rbp
        xorq    %rsi, %rsi
        xorq    %r11, %r11
        movq    0x30(%rsp), %r8
        leaq    (%r8,%rdi,8), %r15
        xorq    %r9, %r9
curve25519_x25519_toploop:
        movq    (%r8,%r9,8), %rbx
        movq    (%r15,%r9,8), %rcx
        movq    %r11, %r10
        andq    %r12, %r10
        andq    %rbp, %r11
        movq    %rbx, %rax
        orq     %rcx, %rax
        negq    %rax
        cmovbq  %r10, %r14
        cmovbq  %r11, %rsi
        cmovbq  %rbx, %r12
        cmovbq  %rcx, %rbp
        sbbq    %r11, %r11
        incq    %r9
        cmpq    %r13, %r9
        jb      curve25519_x25519_toploop
        movq    %r12, %rax
        orq     %rbp, %rax
        bsrq    %rax, %rcx
        xorq    $0x3f, %rcx
        shldq   %cl, %r14, %r12
        shldq   %cl, %rsi, %rbp
        movq    (%r8), %rax
        movq    %rax, %r14
        movq    (%r15), %rax
        movq    %rax, %rsi
        movl    $0x1, %r10d
        movl    $0x0, %r11d
        movl    $0x0, %ecx
        movl    $0x1, %edx
        movl    $0x3a, %r9d
        movq    %rdi, 0x8(%rsp)
        movq    %r13, 0x10(%rsp)
        movq    %r8, (%rsp)
        movq    %r15, 0x18(%rsp)
curve25519_x25519_innerloop:
        xorl    %eax, %eax
        xorl    %ebx, %ebx
        xorq    %r8, %r8
        xorq    %r15, %r15
        btq     $0x0, %r14
        cmovbq  %rbp, %rax
        cmovbq  %rsi, %rbx
        cmovbq  %rcx, %r8
        cmovbq  %rdx, %r15
        movq    %r14, %r13
        subq    %rbx, %r14
        subq    %r13, %rbx
        movq    %r12, %rdi
        subq    %rax, %rdi
        cmovbq  %r12, %rbp
        leaq    -0x1(%rdi), %r12
        cmovbq  %rbx, %r14
        cmovbq  %r13, %rsi
        notq    %r12
        cmovbq  %r10, %rcx
        cmovbq  %r11, %rdx
        cmovaeq %rdi, %r12
        shrq    $1, %r14
        addq    %r8, %r10
        addq    %r15, %r11
        shrq    $1, %r12
        addq    %rcx, %rcx
        addq    %rdx, %rdx
        decq    %r9
        jne     curve25519_x25519_innerloop
        movq    0x8(%rsp), %rdi
        movq    0x10(%rsp), %r13
        movq    (%rsp), %r8
        movq    0x18(%rsp), %r15
        movq    %r10, (%rsp)
        movq    %r11, 0x8(%rsp)
        movq    %rcx, 0x10(%rsp)
        movq    %rdx, 0x18(%rsp)
        movq    0x38(%rsp), %r8
        movq    0x40(%rsp), %r15
        xorq    %r14, %r14
        xorq    %rsi, %rsi
        xorq    %r10, %r10
        xorq    %r11, %r11
        xorq    %r9, %r9
curve25519_x25519_congloop:
        movq    (%r8,%r9,8), %rcx
        movq    (%rsp), %rax
        mulq    %rcx
        addq    %rax, %r14
        adcq    $0x0, %rdx
        movq    %rdx, %r12
        movq    0x10(%rsp), %rax
        mulq    %rcx
        addq    %rax, %rsi
        adcq    $0x0, %rdx
        movq    %rdx, %rbp
        movq    (%r15,%r9,8), %rcx
        movq    0x8(%rsp), %rax
        mulq    %rcx
        addq    %rax, %r14
        adcq    %rdx, %r12
        shrdq   $0x3a, %r14, %r10
        movq    %r10, (%r8,%r9,8)
        movq    %r14, %r10
        movq    %r12, %r14
        movq    0x18(%rsp), %rax
        mulq    %rcx
        addq    %rax, %rsi
        adcq    %rdx, %rbp
        shrdq   $0x3a, %rsi, %r11
        movq    %r11, (%r15,%r9,8)
        movq    %rsi, %r11
        movq    %rbp, %rsi
        incq    %r9
        cmpq    %rdi, %r9
        jb      curve25519_x25519_congloop
        shldq   $0x6, %r10, %r14
        shldq   $0x6, %r11, %rsi
        movq    0x48(%rsp), %r15
        movq    (%r8), %rbx
        movq    0x28(%rsp), %r12
        imulq   %rbx, %r12
        movq    (%r15), %rax
        mulq    %r12
        addq    %rbx, %rax
        movq    %rdx, %r10
        movl    $0x1, %r9d
        movq    %rdi, %rcx
        decq    %rcx
        je      curve25519_x25519_wmontend
curve25519_x25519_wmontloop:
        adcq    (%r8,%r9,8), %r10
        sbbq    %rbx, %rbx
        movq    (%r15,%r9,8), %rax
        mulq    %r12
        subq    %rbx, %rdx
        addq    %r10, %rax
        movq    %rax, -0x8(%r8,%r9,8)
        movq    %rdx, %r10
        incq    %r9
        decq    %rcx
        jne     curve25519_x25519_wmontloop
curve25519_x25519_wmontend:
        adcq    %r14, %r10
        movq    %r10, -0x8(%r8,%rdi,8)
        sbbq    %r10, %r10
        negq    %r10
        movq    %rdi, %rcx
        xorq    %r9, %r9
curve25519_x25519_wcmploop:
        movq    (%r8,%r9,8), %rax
        sbbq    (%r15,%r9,8), %rax
        incq    %r9
        decq    %rcx
        jne     curve25519_x25519_wcmploop
        sbbq    $0x0, %r10
        sbbq    %r10, %r10
        notq    %r10
        xorq    %rcx, %rcx
        xorq    %r9, %r9
curve25519_x25519_wcorrloop:
        movq    (%r8,%r9,8), %rax
        movq    (%r15,%r9,8), %rbx
        andq    %r10, %rbx
        negq    %rcx
        sbbq    %rbx, %rax
        sbbq    %rcx, %rcx
        movq    %rax, (%r8,%r9,8)
        incq    %r9
        cmpq    %rdi, %r9
        jb      curve25519_x25519_wcorrloop
        movq    0x40(%rsp), %r8
        movq    (%r8), %rbx
        movq    0x28(%rsp), %rbp
        imulq   %rbx, %rbp
        movq    (%r15), %rax
        mulq    %rbp
        addq    %rbx, %rax
        movq    %rdx, %r11
        movl    $0x1, %r9d
        movq    %rdi, %rcx
        decq    %rcx
        je      curve25519_x25519_zmontend
curve25519_x25519_zmontloop:
        adcq    (%r8,%r9,8), %r11
        sbbq    %rbx, %rbx
        movq    (%r15,%r9,8), %rax
        mulq    %rbp
        subq    %rbx, %rdx
        addq    %r11, %rax
        movq    %rax, -0x8(%r8,%r9,8)
        movq    %rdx, %r11
        incq    %r9
        decq    %rcx
        jne     curve25519_x25519_zmontloop
curve25519_x25519_zmontend:
        adcq    %rsi, %r11
        movq    %r11, -0x8(%r8,%rdi,8)
        sbbq    %r11, %r11
        negq    %r11
        movq    %rdi, %rcx
        xorq    %r9, %r9
curve25519_x25519_zcmploop:
        movq    (%r8,%r9,8), %rax
        sbbq    (%r15,%r9,8), %rax
        incq    %r9
        decq    %rcx
        jne     curve25519_x25519_zcmploop
        sbbq    $0x0, %r11
        sbbq    %r11, %r11
        notq    %r11
        xorq    %rcx, %rcx
        xorq    %r9, %r9
curve25519_x25519_zcorrloop:
        movq    (%r8,%r9,8), %rax
        movq    (%r15,%r9,8), %rbx
        andq    %r11, %rbx
        negq    %rcx
        sbbq    %rbx, %rax
        sbbq    %rcx, %rcx
        movq    %rax, (%r8,%r9,8)
        incq    %r9
        cmpq    %rdi, %r9
        jb      curve25519_x25519_zcorrloop
        movq    0x30(%rsp), %r8
        leaq    (%r8,%rdi,8), %r15
        xorq    %r9, %r9
        xorq    %r12, %r12
        xorq    %r14, %r14
        xorq    %rbp, %rbp
        xorq    %rsi, %rsi
curve25519_x25519_crossloop:
        movq    (%r8,%r9,8), %rcx
        movq    (%rsp), %rax
        mulq    %rcx
        addq    %rax, %r14
        adcq    $0x0, %rdx
        movq    %rdx, %r10
        movq    0x10(%rsp), %rax
        mulq    %rcx
        addq    %rax, %rsi
        adcq    $0x0, %rdx
        movq    %rdx, %r11
        movq    (%r15,%r9,8), %rcx
        movq    0x8(%rsp), %rax
        mulq    %rcx
        subq    %r12, %rdx
        subq    %rax, %r14
        sbbq    %rdx, %r10
        sbbq    %r12, %r12
        movq    %r14, (%r8,%r9,8)
        movq    %r10, %r14
        movq    0x18(%rsp), %rax
        mulq    %rcx
        subq    %rbp, %rdx
        subq    %rax, %rsi
        sbbq    %rdx, %r11
        sbbq    %rbp, %rbp
        movq    %rsi, (%r15,%r9,8)
        movq    %r11, %rsi
        incq    %r9
        cmpq    %r13, %r9
        jb      curve25519_x25519_crossloop
        xorq    %r9, %r9
        movq    %r12, %r10
        movq    %rbp, %r11
        xorq    %r12, %r14
        xorq    %rbp, %rsi
curve25519_x25519_optnegloop:
        movq    (%r8,%r9,8), %rax
        xorq    %r12, %rax
        negq    %r10
        adcq    $0x0, %rax
        sbbq    %r10, %r10
        movq    %rax, (%r8,%r9,8)
        movq    (%r15,%r9,8), %rax
        xorq    %rbp, %rax
        negq    %r11
        adcq    $0x0, %rax
        sbbq    %r11, %r11
        movq    %rax, (%r15,%r9,8)
        incq    %r9
        cmpq    %r13, %r9
        jb      curve25519_x25519_optnegloop
        subq    %r10, %r14
        subq    %r11, %rsi
        movq    %r13, %r9
curve25519_x25519_shiftloop:
        movq    -0x8(%r8,%r9,8), %rax
        movq    %rax, %r10
        shrdq   $0x3a, %r14, %rax
        movq    %rax, -0x8(%r8,%r9,8)
        movq    %r10, %r14
        movq    -0x8(%r15,%r9,8), %rax
        movq    %rax, %r11
        shrdq   $0x3a, %rsi, %rax
        movq    %rax, -0x8(%r15,%r9,8)
        movq    %r11, %rsi
        decq    %r9
        jne     curve25519_x25519_shiftloop
        notq    %rbp
        movq    0x48(%rsp), %rcx
        movq    0x38(%rsp), %r8
        movq    0x40(%rsp), %r15
        movq    %r12, %r10
        movq    %rbp, %r11
        xorq    %r9, %r9
curve25519_x25519_fliploop:
        movq    %rbp, %rdx
        movq    (%rcx,%r9,8), %rax
        andq    %rax, %rdx
        andq    %r12, %rax
        movq    (%r8,%r9,8), %rbx
        xorq    %r12, %rbx
        negq    %r10
        adcq    %rbx, %rax
        sbbq    %r10, %r10
        movq    %rax, (%r8,%r9,8)
        movq    (%r15,%r9,8), %rbx
        xorq    %rbp, %rbx
        negq    %r11
        adcq    %rbx, %rdx
        sbbq    %r11, %r11
        movq    %rdx, (%r15,%r9,8)
        incq    %r9
        cmpq    %rdi, %r9
        jb      curve25519_x25519_fliploop
        subq    $0x3a,  0x20(%rsp)
        ja      curve25519_x25519_outerloop

// Since we eventually want to return 0 when the result is the point at
// infinity, we force xn = 0 whenever zn = 0. This avoids building in a
// dependency on the behavior of modular inverse in out-of-scope cases.

        movq    160(%rsp), %rax
        orq     168(%rsp), %rax
        orq     176(%rsp), %rax
        orq     184(%rsp), %rax
        movq    320(%rsp), %rcx
        cmovzq  %rax, %rcx
        movq    %rcx, 320(%rsp)
        movq    328(%rsp), %rcx
        cmovzq  %rax, %rcx
        movq    %rcx, 328(%rsp)
        movq    336(%rsp), %rcx
        cmovzq  %rax, %rcx
        movq    %rcx, 336(%rsp)
        movq    344(%rsp), %rcx
        cmovzq  %rax, %rcx
        movq    %rcx, 344(%rsp)

// Now the result is xn * (1/zn), fully reduced modulo p.

        movq    res, %rbp
        mul_p25519(resx,xn,zm)

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
