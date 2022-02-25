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
// Square modulo p_25519, z := (x^2) mod p_25519
// Input x[4]; output z[4]
//
//    extern void bignum_sqr_p25519
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_sqr_p25519
        .globl  _bignum_sqr_p25519
        .text

#define z %rdi
#define x %rsi

// Use this fairly consistently for a zero

#define zero %rbx
#define zeroe %ebx

// Add %rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using %rax and %rcx as temporaries

#define mulpadd(high,low,m)             \
        mulxq   m, %rax, %rcx ;            \
        adcxq   %rax, low ;               \
        adoxq   %rcx, high

// mulpade(high,low,m) adds %rdx * m to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using %rax as a temporary, assuming high created from scratch
// and that zero has value zero.

#define mulpade(high,low,m)             \
        mulxq   m, %rax, high ;           \
        adcxq   %rax, low ;               \
        adoxq   zero, high

bignum_sqr_p25519:
_bignum_sqr_p25519:

// Save more registers to play with

        pushq   %rbx
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15

// Compute [%r15;%r8] = [00] which we use later, but mainly
// set up an initial window [%r14;...;%r9] = [23;03;01]

        movq    (x), %rdx
        mulxq   %rdx, %r8, %r15
        mulxq   8(x), %r9, %r10
        mulxq   24(x), %r11, %r12
        movq    16(x), %rdx
        mulxq   24(x), %r13, %r14

// Clear our zero register, and also initialize the flags for the carry chain

        xorl    zeroe, zeroe

// Chain in the addition of 02 + 12 + 13 to that window (no carry-out possible)
// This gives all the "heterogeneous" terms of the squaring ready to double

        mulpadd(%r11,%r10,(x))
        mulpadd(%r12,%r11,8(x))
        movq    24(x), %rdx
        mulpadd(%r13,%r12,8(x))
        adcxq   zero, %r13
        adoxq   zero, %r14
        adcq    zero, %r14

// Double and add to the 00 + 11 + 22 + 33 terms

        xorl    zeroe, zeroe
        adcxq   %r9, %r9
        adoxq   %r15, %r9
        movq    8(x), %rdx
        mulxq   %rdx, %rax, %rdx
        adcxq   %r10, %r10
        adoxq   %rax, %r10
        adcxq   %r11, %r11
        adoxq   %rdx, %r11
        movq    16(x), %rdx
        mulxq   %rdx, %rax, %rdx
        adcxq   %r12, %r12
        adoxq   %rax, %r12
        adcxq   %r13, %r13
        adoxq   %rdx, %r13
        movq    24(x), %rdx
        mulxq   %rdx, %rax, %r15
        adcxq   %r14, %r14
        adoxq   %rax, %r14
        adcxq   zero, %r15
        adoxq   zero, %r15

// Now we have the full 8-digit product 2^256 * h + l where
// h = [%r15,%r14,%r13,%r12] and l = [%r11,%r10,%r9,%r8]
// and this is == 38 * h + l (mod p_25519)

        movl    $38, %edx
        xorl    zeroe, zeroe
        mulpadd(%r9,%r8,%r12)
        mulpadd(%r10,%r9,%r13)
        mulpadd(%r11,%r10,%r14)
        mulpade(%r12,%r11,%r15)
        adcxq   zero, %r12

// Now we have reduced to 5 digits, 2^255 * h + l = [%r12,%r11,%r10,%r9,%r8]
// Use q = h + 1 as the initial quotient estimate, either right or 1 too big.

        shldq   $1, %r11, %r12
        movl    $19, %edx
        leaq    1(%r12), %rax
        bts     $63, %r11
        imulq   %rdx, %rax
        addq    %rax, %r8
        adcq    zero, %r9
        adcq    zero, %r10
        adcq    zero, %r11

// Now the effective answer is 2^256 * (CF - 1) + [u3,u2,u1,u0]
// So we correct if CF = 0 by subtracting 19, either way masking to
// 255 bits, i.e. by effectively adding p_25519 to the "full" answer

        sbbq    %rax, %rax
        notq    %rax
        andq    %rdx, %rax
        subq    %rax, %r8
        sbbq    zero, %r9
        sbbq    zero, %r10
        sbbq    zero, %r11
        btr     $63, %r11

// Write everything back

        movq    %r8, (z)
        movq    %r9, 8(z)
        movq    %r10, 16(z)
        movq    %r11, 24(z)

// Restore registers and return

        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbx

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
