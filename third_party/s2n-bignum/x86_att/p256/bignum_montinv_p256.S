// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery inverse modulo p_256 = 2^256 - 2^224 + 2^192 + 2^96 - 1
// Input x[4]; output z[4]
//
// extern void bignum_montinv_p256(uint64_t z[static 4],uint64_t x[static 4]);
//
// If the 4-digit input x is coprime to p_256, i.e. is not divisible
// by it, returns z < p_256 such that x * z == 2^512 (mod p_256). This
// is effectively "Montgomery inverse" because if we consider x and z as
// Montgomery forms of X and Z, i.e. x == 2^256 * X and z == 2^256 * Z
// (both mod p_256) then X * Z == 1 (mod p_256). That is, this function
// gives the analog of the modular inverse bignum_inv_p256 but with both
// input and output in the Montgomery domain. Note that x does not need
// to be reduced modulo p_256, but the output always is. If the input
// is divisible (i.e. is 0 or p_256), then there can be no solution to
// the congruence x * z == 2^512 (mod p_256), and z = 0 is returned.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montinv_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montinv_p256)
        .text

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define f 0(%rsp)
#define g (5*N)(%rsp)
#define u (10*N)(%rsp)
#define v (15*N)(%rsp)
#define tmp  (20*N)(%rsp)
#define tmp2  (21*N)(%rsp)
#define i  (22*N)(%rsp)
#define d  (23*N)(%rsp)

#define mat (24*N)(%rsp)

// Backup for the input pointer

#define res  (28*N)(%rsp)

// Total size to reserve on the stack

#define NSPACE (30*N)

// Syntactic variants to make x86_att version simpler to generate

#define F 0
#define G (5*N)
#define U (10*N)
#define V (15*N)
#define MAT (24*N)

#define ff  (%rsp)
#define gg  (5*N)(%rsp)

// ---------------------------------------------------------------------------
// Core signed almost-Montgomery reduction macro from u[4..0] to u[3..0].
// ---------------------------------------------------------------------------

#define amontred(P)                                                     \
/* We only know the input is -2^316 < x < 2^316. To do traditional  */  \
/* unsigned Montgomery reduction, start by adding 2^61 * p_256.     */  \
        movq    $0xe000000000000000, %r8  ASM_LINE_END                                 \
        addq    P, %r8  ASM_LINE_END                                                \
        movq    $0xffffffffffffffff, %r9  ASM_LINE_END                                 \
        adcq    8+P, %r9  ASM_LINE_END                                              \
        movq    $0x000000001fffffff, %r10  ASM_LINE_END                                \
        adcq    16+P, %r10  ASM_LINE_END                                            \
        movq    $0x2000000000000000, %r11  ASM_LINE_END                                \
        adcq    24+P, %r11  ASM_LINE_END                                            \
        movq    $0x1fffffffe0000000, %r12  ASM_LINE_END                                \
        adcq    32+P, %r12  ASM_LINE_END                                            \
/* Let [%r8 ASM_LINE_END%rbx] = 2^32 * w and [%rdx;%rax] = (2^64 - 2^32 + 1) * w */     \
/* where w is the lowest word */                                        \
        movq    %r8, %rbx  ASM_LINE_END                                                \
        shlq    $32, %rbx  ASM_LINE_END                                                \
        movq    $0xffffffff00000001, %rax  ASM_LINE_END                                \
        mulq    %r8 ASM_LINE_END                                                     \
        shrq    $32, %r8  ASM_LINE_END                                                 \
/* Hence basic addition of (2^256 - 2^224 + 2^192 + 2^96) * w */        \
        addq    %rbx, %r9  ASM_LINE_END                                                \
        adcq    %r8, %r10  ASM_LINE_END                                                \
        adcq    %rax, %r11  ASM_LINE_END                                               \
        adcq    %rdx, %r12  ASM_LINE_END                                               \
/* Now capture carry and subtract p_256 if set (almost-Montgomery) */   \
        sbbq    %rax, %rax  ASM_LINE_END                                               \
        movl    $0x00000000ffffffff, %ebx  ASM_LINE_END                                \
        andq    %rax, %rbx  ASM_LINE_END                                               \
        movq    $0xffffffff00000001, %rdx  ASM_LINE_END                                \
        andq    %rax, %rdx  ASM_LINE_END                                               \
        subq    %rax, %r9  ASM_LINE_END                                                \
        movq    %r9, P  ASM_LINE_END                                                \
        sbbq    %rbx, %r10  ASM_LINE_END                                               \
        movq    %r10, 8+P  ASM_LINE_END                                             \
        sbbq    $0, %r11  ASM_LINE_END                                                 \
        movq    %r11, 16+P  ASM_LINE_END                                            \
        sbbq    %rdx, %r12  ASM_LINE_END                                               \
        movq    %r12, 24+P

// Very similar to a subroutine call to the s2n-bignum word_divstep59.
// But different in register usage and returning the final matrix as
//
// [ %r8   %r10]
// [ %r12  %r14]
//
// and also returning the matrix still negated (which doesn't matter)

#define divstep59(din,fin,gin)                                          \
        movq    din, %rsi  ASM_LINE_END                                               \
        movq    fin, %rdx  ASM_LINE_END                                               \
        movq    gin, %rcx  ASM_LINE_END                                               \
        movq    %rdx, %rbx  ASM_LINE_END                                               \
        andq    $0xfffff, %rbx  ASM_LINE_END                                           \
        movabsq $0xfffffe0000000000, %rax  ASM_LINE_END                                \
        orq     %rax, %rbx  ASM_LINE_END                                               \
        andq    $0xfffff, %rcx  ASM_LINE_END                                           \
        movabsq $0xc000000000000000, %rax  ASM_LINE_END                                \
        orq     %rax, %rcx  ASM_LINE_END                                               \
        movq    $0xfffffffffffffffe, %rax  ASM_LINE_END                                \
        xorl    %ebp, %ebp  ASM_LINE_END                                               \
        movl    $0x2, %edx  ASM_LINE_END                                               \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        testq   %rsi, %rsi  ASM_LINE_END                                               \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        testq   $0x1, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        movl    $0x100000, %eax  ASM_LINE_END                                          \
        leaq    (%rbx,%rax), %rdx  ASM_LINE_END                                         \
        leaq    (%rcx,%rax), %rdi  ASM_LINE_END                                         \
        shlq    $0x16, %rdx  ASM_LINE_END                                              \
        shlq    $0x16, %rdi  ASM_LINE_END                                              \
        sarq    $0x2b, %rdx  ASM_LINE_END                                              \
        sarq    $0x2b, %rdi  ASM_LINE_END                                              \
        movabsq $0x20000100000, %rax  ASM_LINE_END                                     \
        leaq    (%rbx,%rax), %rbx  ASM_LINE_END                                         \
        leaq    (%rcx,%rax), %rcx  ASM_LINE_END                                         \
        sarq    $0x2a, %rbx  ASM_LINE_END                                              \
        sarq    $0x2a, %rcx  ASM_LINE_END                                              \
        movq    %rdx, MAT(%rsp)  ASM_LINE_END                                         \
        movq    %rbx, MAT+0x8(%rsp)  ASM_LINE_END                                     \
        movq    %rdi, MAT+0x10(%rsp)  ASM_LINE_END                                    \
        movq    %rcx, MAT+0x18(%rsp)  ASM_LINE_END                                    \
        movq    fin, %r12  ASM_LINE_END                                               \
        imulq   %r12, %rdi  ASM_LINE_END                                               \
        imulq   %rdx, %r12  ASM_LINE_END                                               \
        movq    gin, %r13  ASM_LINE_END                                               \
        imulq   %r13, %rbx  ASM_LINE_END                                               \
        imulq   %rcx, %r13  ASM_LINE_END                                               \
        addq    %rbx, %r12  ASM_LINE_END                                               \
        addq    %rdi, %r13  ASM_LINE_END                                               \
        sarq    $0x14, %r12  ASM_LINE_END                                              \
        sarq    $0x14, %r13  ASM_LINE_END                                              \
        movq    %r12, %rbx  ASM_LINE_END                                               \
        andq    $0xfffff, %rbx  ASM_LINE_END                                           \
        movabsq $0xfffffe0000000000, %rax  ASM_LINE_END                                \
        orq     %rax, %rbx  ASM_LINE_END                                               \
        movq    %r13, %rcx  ASM_LINE_END                                               \
        andq    $0xfffff, %rcx  ASM_LINE_END                                           \
        movabsq $0xc000000000000000, %rax  ASM_LINE_END                                \
        orq     %rax, %rcx  ASM_LINE_END                                               \
        movq    $0xfffffffffffffffe, %rax  ASM_LINE_END                                \
        movl    $0x2, %edx  ASM_LINE_END                                               \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        testq   %rsi, %rsi  ASM_LINE_END                                               \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        testq   $0x1, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        movl    $0x100000, %eax  ASM_LINE_END                                          \
        leaq    (%rbx,%rax), %r8  ASM_LINE_END                                          \
        leaq    (%rcx,%rax), %r10  ASM_LINE_END                                         \
        shlq    $0x16, %r8  ASM_LINE_END                                               \
        shlq    $0x16, %r10  ASM_LINE_END                                              \
        sarq    $0x2b, %r8  ASM_LINE_END                                               \
        sarq    $0x2b, %r10  ASM_LINE_END                                              \
        movabsq $0x20000100000, %rax  ASM_LINE_END                                     \
        leaq    (%rbx,%rax), %r15  ASM_LINE_END                                         \
        leaq    (%rcx,%rax), %r11  ASM_LINE_END                                         \
        sarq    $0x2a, %r15  ASM_LINE_END                                              \
        sarq    $0x2a, %r11  ASM_LINE_END                                              \
        movq    %r13, %rbx  ASM_LINE_END                                               \
        movq    %r12, %rcx  ASM_LINE_END                                               \
        imulq   %r8, %r12  ASM_LINE_END                                                \
        imulq   %r15, %rbx  ASM_LINE_END                                               \
        addq    %rbx, %r12  ASM_LINE_END                                               \
        imulq   %r11, %r13  ASM_LINE_END                                               \
        imulq   %r10, %rcx  ASM_LINE_END                                               \
        addq    %rcx, %r13  ASM_LINE_END                                               \
        sarq    $0x14, %r12  ASM_LINE_END                                              \
        sarq    $0x14, %r13  ASM_LINE_END                                              \
        movq    %r12, %rbx  ASM_LINE_END                                               \
        andq    $0xfffff, %rbx  ASM_LINE_END                                           \
        movabsq $0xfffffe0000000000, %rax  ASM_LINE_END                                \
        orq     %rax, %rbx  ASM_LINE_END                                               \
        movq    %r13, %rcx  ASM_LINE_END                                               \
        andq    $0xfffff, %rcx  ASM_LINE_END                                           \
        movabsq $0xc000000000000000, %rax  ASM_LINE_END                                \
        orq     %rax, %rcx  ASM_LINE_END                                               \
        movq    MAT(%rsp), %rax  ASM_LINE_END                                         \
        imulq   %r8, %rax  ASM_LINE_END                                                \
        movq    MAT+0x10(%rsp), %rdx  ASM_LINE_END                                    \
        imulq   %r15, %rdx  ASM_LINE_END                                               \
        imulq   MAT+0x8(%rsp), %r8  ASM_LINE_END                                      \
        imulq   MAT+0x18(%rsp), %r15  ASM_LINE_END                                    \
        addq    %r8, %r15  ASM_LINE_END                                                \
        leaq    (%rax,%rdx), %r9  ASM_LINE_END                                          \
        movq    MAT(%rsp), %rax  ASM_LINE_END                                         \
        imulq   %r10, %rax  ASM_LINE_END                                               \
        movq    MAT+0x10(%rsp), %rdx  ASM_LINE_END                                    \
        imulq   %r11, %rdx  ASM_LINE_END                                               \
        imulq   MAT+0x8(%rsp), %r10  ASM_LINE_END                                     \
        imulq   MAT+0x18(%rsp), %r11  ASM_LINE_END                                    \
        addq    %r10, %r11  ASM_LINE_END                                               \
        leaq    (%rax,%rdx), %r13  ASM_LINE_END                                         \
        movq    $0xfffffffffffffffe, %rax  ASM_LINE_END                                \
        movl    $0x2, %edx  ASM_LINE_END                                               \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        testq   %rsi, %rsi  ASM_LINE_END                                               \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        testq   $0x1, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        cmovs   %rbp, %r8  ASM_LINE_END                                                \
        movq    %rbx, %rdi  ASM_LINE_END                                               \
        testq   %rdx, %rcx  ASM_LINE_END                                               \
        cmoveq  %rbp, %r8  ASM_LINE_END                                                \
        cmoveq  %rbp, %rdi  ASM_LINE_END                                               \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        xorq    %r8, %rdi  ASM_LINE_END                                                \
        xorq    %r8, %rsi  ASM_LINE_END                                                \
        btq     $0x3f, %r8  ASM_LINE_END                                               \
        cmovbq  %rcx, %rbx  ASM_LINE_END                                               \
        movq    %rax, %r8  ASM_LINE_END                                                \
        subq    %rax, %rsi  ASM_LINE_END                                               \
        leaq    (%rcx,%rdi), %rcx  ASM_LINE_END                                         \
        sarq    $1, %rcx  ASM_LINE_END                                                 \
        movl    $0x100000, %eax  ASM_LINE_END                                          \
        leaq    (%rbx,%rax), %r8  ASM_LINE_END                                          \
        leaq    (%rcx,%rax), %r12  ASM_LINE_END                                         \
        shlq    $0x15, %r8  ASM_LINE_END                                               \
        shlq    $0x15, %r12  ASM_LINE_END                                              \
        sarq    $0x2b, %r8  ASM_LINE_END                                               \
        sarq    $0x2b, %r12  ASM_LINE_END                                              \
        movabsq $0x20000100000, %rax  ASM_LINE_END                                     \
        leaq    (%rbx,%rax), %r10  ASM_LINE_END                                         \
        leaq    (%rcx,%rax), %r14  ASM_LINE_END                                         \
        sarq    $0x2b, %r10  ASM_LINE_END                                              \
        sarq    $0x2b, %r14  ASM_LINE_END                                              \
        movq    %r9, %rax  ASM_LINE_END                                                \
        imulq   %r8, %rax  ASM_LINE_END                                                \
        movq    %r13, %rdx  ASM_LINE_END                                               \
        imulq   %r10, %rdx  ASM_LINE_END                                               \
        imulq   %r15, %r8  ASM_LINE_END                                                \
        imulq   %r11, %r10  ASM_LINE_END                                               \
        addq    %r8, %r10  ASM_LINE_END                                                \
        leaq    (%rax,%rdx), %r8  ASM_LINE_END                                          \
        movq    %r9, %rax  ASM_LINE_END                                                \
        imulq   %r12, %rax  ASM_LINE_END                                               \
        movq    %r13, %rdx  ASM_LINE_END                                               \
        imulq   %r14, %rdx  ASM_LINE_END                                               \
        imulq   %r15, %r12  ASM_LINE_END                                               \
        imulq   %r11, %r14  ASM_LINE_END                                               \
        addq    %r12, %r14  ASM_LINE_END                                               \
        leaq    (%rax,%rdx), %r12

S2N_BN_SYMBOL(bignum_montinv_p256):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Save registers and make room for temporaries

        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15

        subq    $NSPACE, %rsp

// Save the return pointer for the end so we can overwrite %rdi later

        movq    %rdi, res

// Create constant [%rdx;%rcx;%rbx;%rax] = p_256 and copy it into the variable f
// including the 5th zero digit

        xorl    %ecx, %ecx
        movl    $0x00000000ffffffff, %edx
        movq    %rdx, %rbx
        leaq    -1(%rcx), %rax
        negq    %rdx
        movq    %rax, F(%rsp)
        movq    %rbx, F+8(%rsp)
        movq    %rcx, F+16(%rsp)
        movq    %rdx, F+24(%rsp)
        movq    %rcx, F+32(%rsp)

// Now reduce the input modulo p_256, first negating the constant to get
// [%rdx;%rcx;%rbx;%rax] = 2^256 - p_256, adding it to x and hence getting
// the comparison x < p_256 <=> (2^256 - p_256) + x < 2^256 and choosing
// g accordingly.

        movq    (%rsi), %r8
        movq    8(%rsi), %r9
        movq    16(%rsi), %r10
        movq    24(%rsi), %r11

        leaq    1(%rcx), %rax
        addq    %r8, %rax
        leaq    -1(%rdx), %rbx
        adcq    %r9, %rbx
        notq    %rcx
        adcq    %r10, %rcx
        notq    %rdx
        adcq    %r11, %rdx

        cmovncq %r8, %rax
        cmovncq %r9, %rbx
        cmovncq %r10, %rcx
        cmovncq %r11, %rdx

        movq    %rax, G(%rsp)
        movq    %rbx, G+8(%rsp)
        movq    %rcx, G+16(%rsp)
        movq    %rdx, G+24(%rsp)
        xorl    %eax, %eax
        movq    %rax, G+32(%rsp)

// Also maintain reduced < 2^256 vector [u,v] such that
// [f,g] == x * 2^{5*i-562} * [u,v] (mod p_256)
// starting with [p_256,x] == x * 2^{5*0-562} * [0,2^562] (mod p_256)
// The weird-looking 5*i modifications come in because we are doing
// 64-bit word-sized Montgomery reductions at each stage, which is
// 5 bits more than the 59-bit requirement to keep things stable.
// After the 10th and last iteration and sign adjustment, when
// f == 1 for in-scope cases, we have x * 2^{50-562} * u == 1, i.e.
// x * u == 2^512 as required.

        xorl    %eax, %eax
        movq    %rax, U(%rsp)
        movq    %rax, U+8(%rsp)
        movq    %rax, U+16(%rsp)
        movq    %rax, U+24(%rsp)

        movq    $0x000c000000140000, %rax
        movq    %rax, V(%rsp)
        movq    $0xffe8000000000000, %rax
        movq    %rax, V+8(%rsp)
        movq    $0xfffbffffffefffff, %rax
        movq    %rax, V+16(%rsp)
        movq    $0x000bffffffebffff, %rax
        movq    %rax, V+24(%rsp)

// Start of main loop. We jump into the middle so that the divstep
// portion is common to the special tenth iteration after a uniform
// first 9.

        movq    $10, i
        movq    $1, d
        jmp     bignum_montinv_p256_midloop

bignum_montinv_p256_loop:

// Separate out the matrix into sign-magnitude pairs

        movq    %r8, %r9
        sarq    $63, %r9
        xorq    %r9, %r8
        subq    %r9, %r8

        movq    %r10, %r11
        sarq    $63, %r11
        xorq    %r11, %r10
        subq    %r11, %r10

        movq    %r12, %r13
        sarq    $63, %r13
        xorq    %r13, %r12
        subq    %r13, %r12

        movq    %r14, %r15
        sarq    $63, %r15
        xorq    %r15, %r14
        subq    %r15, %r14

// Adjust the initial values to allow for complement instead of negation
// This initial offset is the same for [f,g] and [u,v] compositions.
// Save it in temporary storage for the [u,v] part and do [f,g] first.

        movq    %r8, %rax
        andq    %r9, %rax
        movq    %r10, %rdi
        andq    %r11, %rdi
        addq    %rax, %rdi
        movq    %rdi, tmp

        movq    %r12, %rax
        andq    %r13, %rax
        movq    %r14, %rsi
        andq    %r15, %rsi
        addq    %rax, %rsi
        movq    %rsi, tmp2

// Now the computation of the updated f and g values. This maintains a
// 2-word carry between stages so we can conveniently insert the shift
// right by 59 before storing back, and not overwrite digits we need
// again of the old f and g values.
//
// Digit 0 of [f,g]

        xorl    %ebx, %ebx
        movq    F(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %rdi
        adcq    %rdx, %rbx
        movq    G(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %rdi
        adcq    %rdx, %rbx

        xorl    %ebp, %ebp
        movq    F(%rsp), %rax
        xorq    %r13, %rax
        mulq    %r12
        addq    %rax, %rsi
        adcq    %rdx, %rbp
        movq    G(%rsp), %rax
        xorq    %r15, %rax
        mulq    %r14
        addq    %rax, %rsi
        adcq    %rdx, %rbp

// Digit 1 of [f,g]

        xorl    %ecx, %ecx
        movq    F+N(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %rbx
        adcq    %rdx, %rcx
        movq    G+N(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %rbx
        adcq    %rdx, %rcx
        shrdq   $59, %rbx, %rdi
        movq    %rdi, F(%rsp)

        xorl    %edi, %edi
        movq    F+N(%rsp), %rax
        xorq    %r13, %rax
        mulq    %r12
        addq    %rax, %rbp
        adcq    %rdx, %rdi
        movq    G+N(%rsp), %rax
        xorq    %r15, %rax
        mulq    %r14
        addq    %rax, %rbp
        adcq    %rdx, %rdi
        shrdq   $59, %rbp, %rsi
        movq    %rsi, G(%rsp)

// Digit 2 of [f,g]

        xorl    %esi, %esi
        movq    F+2*N(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %rcx
        adcq    %rdx, %rsi
        movq    G+2*N(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %rcx
        adcq    %rdx, %rsi
        shrdq   $59, %rcx, %rbx
        movq    %rbx, F+N(%rsp)

        xorl    %ebx, %ebx
        movq    F+2*N(%rsp), %rax
        xorq    %r13, %rax
        mulq    %r12
        addq    %rax, %rdi
        adcq    %rdx, %rbx
        movq    G+2*N(%rsp), %rax
        xorq    %r15, %rax
        mulq    %r14
        addq    %rax, %rdi
        adcq    %rdx, %rbx
        shrdq   $59, %rdi, %rbp
        movq    %rbp, G+N(%rsp)

// Digits 3 and 4 of [f,g]

        movq    F+3*N(%rsp), %rax
        xorq    %r9, %rax
        movq    F+4*N(%rsp), %rbp
        xorq    %r9, %rbp
        andq    %r8, %rbp
        negq    %rbp
        mulq    %r8
        addq    %rax, %rsi
        adcq    %rdx, %rbp
        movq    G+3*N(%rsp), %rax
        xorq    %r11, %rax
        movq    G+4*N(%rsp), %rdx
        xorq    %r11, %rdx
        andq    %r10, %rdx
        subq    %rdx, %rbp
        mulq    %r10
        addq    %rax, %rsi
        adcq    %rdx, %rbp
        shrdq   $59, %rsi, %rcx
        movq    %rcx, F+2*N(%rsp)
        shrdq   $59, %rbp, %rsi
        sarq    $59, %rbp

        movq    F+3*N(%rsp), %rax
        movq    %rsi, F+3*N(%rsp)

        movq    F+4*N(%rsp), %rsi
        movq    %rbp, F+4*N(%rsp)

        xorq    %r13, %rax
        xorq    %r13, %rsi
        andq    %r12, %rsi
        negq    %rsi
        mulq    %r12
        addq    %rax, %rbx
        adcq    %rdx, %rsi
        movq    G+3*N(%rsp), %rax
        xorq    %r15, %rax
        movq    G+4*N(%rsp), %rdx
        xorq    %r15, %rdx
        andq    %r14, %rdx
        subq    %rdx, %rsi
        mulq    %r14
        addq    %rax, %rbx
        adcq    %rdx, %rsi
        shrdq   $59, %rbx, %rdi
        movq    %rdi, G+2*N(%rsp)
        shrdq   $59, %rsi, %rbx
        movq    %rbx, G+3*N(%rsp)
        sarq    $59, %rsi
        movq    %rsi, G+4*N(%rsp)

// Get the initial carries back from storage and do the [u,v] accumulation

        movq    tmp, %rbx
        movq    tmp2, %rbp

// Digit 0 of [u,v]

        xorl    %ecx, %ecx
        movq    U(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %rbx
        adcq    %rdx, %rcx
        movq    V(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %rbx
        adcq    %rdx, %rcx

        xorl    %esi, %esi
        movq    U(%rsp), %rax
        xorq    %r13, %rax
        mulq    %r12
        movq    %rbx, U(%rsp)
        addq    %rax, %rbp
        adcq    %rdx, %rsi
        movq    V(%rsp), %rax
        xorq    %r15, %rax
        mulq    %r14
        addq    %rax, %rbp
        adcq    %rdx, %rsi
        movq    %rbp, V(%rsp)

// Digit 1 of [u,v]

        xorl    %ebx, %ebx
        movq    U+N(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %rcx
        adcq    %rdx, %rbx
        movq    V+N(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %rcx
        adcq    %rdx, %rbx

        xorl    %ebp, %ebp
        movq    U+N(%rsp), %rax
        xorq    %r13, %rax
        mulq    %r12
        movq    %rcx, U+N(%rsp)
        addq    %rax, %rsi
        adcq    %rdx, %rbp
        movq    V+N(%rsp), %rax
        xorq    %r15, %rax
        mulq    %r14
        addq    %rax, %rsi
        adcq    %rdx, %rbp
        movq    %rsi, V+N(%rsp)

// Digit 2 of [u,v]

        xorl    %ecx, %ecx
        movq    U+2*N(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %rbx
        adcq    %rdx, %rcx
        movq    V+2*N(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %rbx
        adcq    %rdx, %rcx

        xorl    %esi, %esi
        movq    U+2*N(%rsp), %rax
        xorq    %r13, %rax
        mulq    %r12
        movq    %rbx, U+2*N(%rsp)
        addq    %rax, %rbp
        adcq    %rdx, %rsi
        movq    V+2*N(%rsp), %rax
        xorq    %r15, %rax
        mulq    %r14
        addq    %rax, %rbp
        adcq    %rdx, %rsi
        movq    %rbp, V+2*N(%rsp)

// Digits 3 and 4 of u (top is unsigned)

        movq    U+3*N(%rsp), %rax
        xorq    %r9, %rax
        movq    %r9, %rbx
        andq    %r8, %rbx
        negq    %rbx
        mulq    %r8
        addq    %rax, %rcx
        adcq    %rdx, %rbx
        movq    V+3*N(%rsp), %rax
        xorq    %r11, %rax
        movq    %r11, %rdx
        andq    %r10, %rdx
        subq    %rdx, %rbx
        mulq    %r10
        addq    %rax, %rcx
        adcq    %rbx, %rdx

// Preload for last use of old u digit 3

        movq    U+3*N(%rsp), %rax
        movq    %rcx, U+3*N(%rsp)
        movq    %rdx, U+4*N(%rsp)

// Digits 3 and 4 of v (top is unsigned)

        xorq    %r13, %rax
        movq    %r13, %rcx
        andq    %r12, %rcx
        negq    %rcx
        mulq    %r12
        addq    %rax, %rsi
        adcq    %rdx, %rcx
        movq    V+3*N(%rsp), %rax
        xorq    %r15, %rax
        movq    %r15, %rdx
        andq    %r14, %rdx
        subq    %rdx, %rcx
        mulq    %r14
        addq    %rax, %rsi
        adcq    %rcx, %rdx
        movq    %rsi, V+3*N(%rsp)
        movq    %rdx, V+4*N(%rsp)

// Montgomery reduction of u

        amontred(u)

// Montgomery reduction of v

        amontred(v)

bignum_montinv_p256_midloop:

        divstep59(d,ff,gg)
        movq    %rsi, d

// Next iteration

        decq    i
        jnz     bignum_montinv_p256_loop

// The 10th and last iteration does not need anything except the
// u value and the sign of f; the latter can be obtained from the
// lowest word of f. So it's done differently from the main loop.
// Find the sign of the new f. For this we just need one digit
// since we know (for in-scope cases) that f is either +1 or -1.
// We don't explicitly shift right by 59 either, but looking at
// bit 63 (or any bit >= 60) of the unshifted result is enough
// to distinguish -1 from +1; this is then made into a mask.

        movq    F(%rsp), %rax
        movq    G(%rsp), %rcx
        imulq   %r8, %rax
        imulq   %r10, %rcx
        addq    %rcx, %rax
        sarq    $63, %rax

// Now separate out the matrix into sign-magnitude pairs
// and adjust each one based on the sign of f.
//
// Note that at this point we expect |f|=1 and we got its
// sign above, so then since [f,0] == x * 2^{-512} [u,v] (mod p_256)
// we want to flip the sign of u according to that of f.

        movq    %r8, %r9
        sarq    $63, %r9
        xorq    %r9, %r8
        subq    %r9, %r8
        xorq    %rax, %r9

        movq    %r10, %r11
        sarq    $63, %r11
        xorq    %r11, %r10
        subq    %r11, %r10
        xorq    %rax, %r11

        movq    %r12, %r13
        sarq    $63, %r13
        xorq    %r13, %r12
        subq    %r13, %r12
        xorq    %rax, %r13

        movq    %r14, %r15
        sarq    $63, %r15
        xorq    %r15, %r14
        subq    %r15, %r14
        xorq    %rax, %r15

// Adjust the initial value to allow for complement instead of negation

        movq    %r8, %rax
        andq    %r9, %rax
        movq    %r10, %r12
        andq    %r11, %r12
        addq    %rax, %r12

// Digit 0 of [u]

        xorl    %r13d, %r13d
        movq    U(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %r12
        adcq    %rdx, %r13
        movq    V(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %r12
        adcq    %rdx, %r13

// Digit 1 of [u]

        xorl    %r14d, %r14d
        movq    U+N(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %r13
        adcq    %rdx, %r14
        movq    V+N(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %r13
        adcq    %rdx, %r14

// Digit 2 of [u]

        xorl    %r15d, %r15d
        movq    U+2*N(%rsp), %rax
        xorq    %r9, %rax
        mulq    %r8
        addq    %rax, %r14
        adcq    %rdx, %r15
        movq    V+2*N(%rsp), %rax
        xorq    %r11, %rax
        mulq    %r10
        addq    %rax, %r14
        adcq    %rdx, %r15

// Digits 3 and 4 of u (top is unsigned)

        movq    U+3*N(%rsp), %rax
        xorq    %r9, %rax
        andq    %r8, %r9
        negq    %r9
        mulq    %r8
        addq    %rax, %r15
        adcq    %rdx, %r9
        movq    V+3*N(%rsp), %rax
        xorq    %r11, %rax
        movq    %r11, %rdx
        andq    %r10, %rdx
        subq    %rdx, %r9
        mulq    %r10
        addq    %rax, %r15
        adcq    %rdx, %r9

// Store back and Montgomery reduce u

        movq    %r12, U(%rsp)
        movq    %r13, U+N(%rsp)
        movq    %r14, U+2*N(%rsp)
        movq    %r15, U+3*N(%rsp)
        movq    %r9, U+4*N(%rsp)

        amontred(u)

// Perform final strict reduction mod p_256 and copy to output

        movq    U(%rsp), %r8
        movq    U+N(%rsp), %r9
        movq    U+2*N(%rsp), %r10
        movq    U+3*N(%rsp), %r11

        movl    $1, %eax
        movl    $0xffffffff, %ebx
        leaq    -2(%rax), %rcx
        leaq    -1(%rbx), %rdx
        notq    %rbx

        addq    %r8, %rax
        adcq    %r9, %rbx
        adcq    %r10, %rcx
        adcq    %r11, %rdx

        cmovncq %r8, %rax
        cmovncq %r9, %rbx
        cmovncq %r10, %rcx
        cmovncq %r11, %rdx

        movq    res, %rdi
        movq    %rax, (%rdi)
        movq    %rbx, N(%rdi)
        movq    %rcx, 2*N(%rdi)
        movq    %rdx, 3*N(%rdi)

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
