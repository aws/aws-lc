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
// Square, z := x^2
// Input x[32]; output z[64]; temporary buffer t[>=72]
//
//    extern void bignum_ksqr_32_64
//     (uint64_t z[static 64], uint64_t x[static 32], uint64_t t[static 72]);
//
// This is a Karatsuba-style function squaring half-sized results
// and using temporary buffer t for intermediate results. The size of 72
// is an overstatement for compatibility with the ARM version; it actually
// only uses 65 elements of t (64 + 1 for a suspended carry).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = t
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_ksqr_32_64
        .text

#define k 16

#define z rdi
#define x rsi
#define t rcx

bignum_ksqr_32_64:

// Save callee-preserved registers once and for all at the outset
// Later we further reshuffle the input arguments to avoid extra saves

        push   rbp
        push   rbx
        push   r12
        push   r13
        push   r14
        push   r15

// Move the temp space pointer since we need rdx for multiplications

        mov     t, rdx

// Square the low half

        call    local_bignum_sqr_16_32

// Square the high half; from here on x and z are modified

        lea     x,[x+8*k]               // input at x+8*k
        lea     z,[z+8*2*k]             // result at z+8*2*k
        call    local_bignum_sqr_16_32

// Form |x_lo - x_hi|, stored at t

        mov     rax, [x-8*k]
        sub     rax, [x]
        mov     [t], rax
        .set i,  1
        .rep k-1
        mov     rax, [x-8*k+8*i]
        sbb     rax, [x+8*i]
        mov     [t+8*i], rax
        .set i,  (i+1)
        .endr

        mov     ebx, 0
        sbb     rax, rax                // Maintain CF, set ZF for cmovs

        .set i,  0
        .rep k
        mov     rdx, [t+8*i]
        mov     rax, rdx
        not     rdx
        adcx    rdx, rbx
        cmovz   rdx, rax
        mov     [t+8*i], rdx
        .set i,  (i+1)
        .endr

// Compose the middle parts [2,1] + [1,0] + [3,2]
// Put the low half of this at t[k] and the top half in place at z[2k]; a
// fully in-place version is awkward with the otherwise beneficial double
// carry chain. Stash the carry suspended from the 3k position at the end of
// the temp buffer t[4*k].

        xor     edx, edx
        .set i,  0
        .rep k
        mov     rax, [z-8*2*k+8*k+8*i]
        adcx    rax, [z-8*2*k+8*i]
        adox    rax, [z-8*2*k+8*2*k+8*i]
        mov     [t+8*k+8*i], rax
        .set i,  (i+1)
        .endr

        .rep k
        mov     rax, [z-8*2*k+8*k+8*i]
        adcx    rax, [z-8*2*k+8*i]
        adox    rax, [z-8*2*k+8*2*k+8*i]
        mov     [z-8*2*k+8*k+8*i], rax
        .set i,  (i+1)
        .endr

        adox    rdx, rdx
        adc     rdx, 0
        mov     [t+8*4*k], rdx

// Square the absolute difference, putting the result M at t[2k].
// This involves another shuffle so now t' = z_orig and x' = t_orig
// while z' points within the temp buffer to the product M itself

        mov     x, t
        lea     t, [z-8*2*k]
        lea     z, [x+8*2*k]
        call    local_bignum_sqr_16_32

// Subtract M, pausing at the 3k position to bump down accumulated carry.
// The carry cannot go negative since it's the top word of a value
// of the form ... + h^2 + l^2 - (h - l)^2 >= 0

        mov     rax, [x+8*k]
        sub     rax, [z]
        mov     [t+8*k], rax

        .set i,  1

        .rep (k-1)
        mov     rax, [x+8*k+8*i]
        sbb     rax, [z+8*i]
        mov     [t+8*k+8*i], rax
        .set i,  (i+1)
        .endr

        .rep k
        mov     rax, [t+8*k+8*i]
        sbb     rax, [z+8*i]
        mov     [t+8*k+8*i], rax
        .set i,  (i+1)
        .endr

        mov     rdx, [x+8*4*k]
        sbb     rdx, 0

// Finally propagate the carry to the top quarter

        xor     eax, eax
        add     [t+8*3*k],rdx
        .set i,  1
        .rep k-1
        adc     [t+8*3*k+8*i], rax
        .set i,  (i+1)
        .endr

// Restore registers and return

        pop    r15
        pop    r14
        pop    r13
        pop    r12
        pop    rbx
        pop    rbp

        ret

// Local copy of the half-length subroutine

local_bignum_sqr_16_32:
        xor    ebp, ebp
        mov    rdx, [x]
        mulx   rax, r9, [x+0x8]
        mov    [z+0x8], r9
        mulx   rbx, r10, [x+0x10]
        adcx   r10, rax
        mov    [z+0x10], r10
        mulx   rax, r11, [x+0x18]
        adcx   r11, rbx
        mulx   rbx, r12, [x+0x20]
        adcx   r12, rax
        mulx   rax, r13, [x+0x28]
        adcx   r13, rbx
        mulx   rbx, r14, [x+0x30]
        adcx   r14, rax
        mulx   r8, r15, [x+0x38]
        adcx   r15, rbx
        adcx   r8, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x8]
        mulx   rbx, rax, [x+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mov    [z+0x18], r11
        mulx   rbx, rax, [x+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mov    [z+0x20], r12
        mulx   rbx, rax, [x+0x20]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [x+0x38]
        adcx   r8, rax
        adox   r9, rbp
        mov    rdx, [x+0x20]
        mulx   r10, rax, [x+0x28]
        adcx   r9, rax
        adox   r10, rbp
        adcx   r10, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x10]
        mulx   rbx, rax, [x+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mov    [z+0x28], r13
        mulx   rbx, rax, [x+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mov    [z+0x30], r14
        mulx   rbx, rax, [x+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x38]
        adcx   r9, rax
        adox   r10, rbx
        mov    rdx, [x+0x30]
        mulx   r11, rax, [x+0x20]
        adcx   r10, rax
        adox   r11, rbp
        mulx   r12, rax, [x+0x28]
        adcx   r11, rax
        adox   r12, rbp
        adcx   r12, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x18]
        mulx   rbx, rax, [x+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mov    [z+0x38], r15
        mulx   rbx, rax, [x+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x38]
        adcx   r10, rax
        adox   r11, rbx
        mov    rdx, [x+0x38]
        mulx   rbx, rax, [x+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [x+0x28]
        adcx   r12, rax
        adox   r13, rbp
        mulx   r14, rax, [x+0x30]
        adcx   r13, rax
        adox   r14, rbp
        adcx   r14, rbp
        mov    rdx, [x+0x40]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r8, rax
        adox   r9, rbx
        mov    [z+0x40], r8
        mulx   rbx, rax, [x+0x8]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [x+0x30]
        adcx   r14, rax
        adox   r15, rbp
        mulx   r8, rax, [x+0x38]
        adcx   r15, rax
        adox   r8, rbp
        adcx   r8, rbp
        mov    rdx, [x+0x48]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r9, rax
        adox   r10, rbx
        mov    [z+0x48], r9
        mulx   rbx, rax, [x+0x8]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [x+0x38]
        adcx   r8, rax
        adox   r9, rbp
        adcx   r9, rbp
        mov    rdx, [x+0x50]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r10, rax
        adox   r11, rbx
        mov    [z+0x50], r10
        mulx   rbx, rax, [x+0x8]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   r10, rax, [x+0x38]
        adcx   r9, rax
        adox   r10, rbp
        adcx   r10, rbp
        mov    rdx, [x+0x58]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r11, rax
        adox   r12, rbx
        mov    [z+0x58], r11
        mulx   rbx, rax, [x+0x8]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   r11, rax, [x+0x38]
        adcx   r10, rax
        adox   r11, rbp
        adcx   r11, rbp
        mov    rdx, [x+0x60]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r12, rax
        adox   r13, rbx
        mov    [z+0x60], r12
        mulx   rbx, rax, [x+0x8]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r10, rax
        adox   r11, rbx
        mulx   r12, rax, [x+0x38]
        adcx   r11, rax
        adox   r12, rbp
        adcx   r12, rbp
        mov    rdx, [x+0x68]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r13, rax
        adox   r14, rbx
        mov    [z+0x68], r13
        mulx   rbx, rax, [x+0x8]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [x+0x38]
        adcx   r12, rax
        adox   r13, rbp
        adcx   r13, rbp
        mov    rdx, [x+0x70]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r14, rax
        adox   r15, rbx
        mov    [z+0x70], r14
        mulx   rbx, rax, [x+0x8]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r12, rax
        adox   r13, rbx
        mulx   r14, rax, [x+0x38]
        adcx   r13, rax
        adox   r14, rbp
        adcx   r14, rbp
        mov    rdx, [x+0x78]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r15, rax
        adox   r8, rbx
        mov    [z+0x78], r15
        mulx   rbx, rax, [x+0x8]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [x+0x38]
        adcx   r14, rax
        adox   r15, rbp
        adcx   r15, rbp
        mov    [z+0x80], r8
        mov    [z+0x88], r9
        mov    [z+0x90], r10
        mov    [z+0x98], r11
        mov    [z+0xa0], r12
        mov    [z+0xa8], r13
        mov    [z+0xb0], r14
        mov    [z+0xb8], r15
        xor    ebp, ebp
        mov    r9, [z+0x88]
        mov    r10, [z+0x90]
        mov    r11, [z+0x98]
        mov    r12, [z+0xa0]
        mov    r13, [z+0xa8]
        mov    r14, [z+0xb0]
        mov    r15, [z+0xb8]
        mov    rdx, [x+0x40]
        mulx   rbx, rax, [x+0x48]
        adcx   r9, rax
        adox   r10, rbx
        mov    [z+0x88], r9
        mulx   rbx, rax, [x+0x50]
        adcx   r10, rax
        adox   r11, rbx
        mov    [z+0x90], r10
        mulx   rbx, rax, [x+0x58]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x60]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x68]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r14, rax
        adox   r15, rbx
        mulx   r8, rax, [x+0x78]
        adcx   r15, rax
        adox   r8, rbp
        adcx   r8, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x48]
        mulx   rbx, rax, [x+0x50]
        adcx   r11, rax
        adox   r12, rbx
        mov    [z+0x98], r11
        mulx   rbx, rax, [x+0x58]
        adcx   r12, rax
        adox   r13, rbx
        mov    [z+0xa0], r12
        mulx   rbx, rax, [x+0x60]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x68]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [x+0x78]
        adcx   r8, rax
        adox   r9, rbp
        mov    rdx, [x+0x60]
        mulx   r10, rax, [x+0x68]
        adcx   r9, rax
        adox   r10, rbp
        adcx   r10, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x50]
        mulx   rbx, rax, [x+0x58]
        adcx   r13, rax
        adox   r14, rbx
        mov    [z+0xa8], r13
        mulx   rbx, rax, [x+0x60]
        adcx   r14, rax
        adox   r15, rbx
        mov    [z+0xb0], r14
        mulx   rbx, rax, [x+0x68]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x78]
        adcx   r9, rax
        adox   r10, rbx
        mov    rdx, [x+0x70]
        mulx   r11, rax, [x+0x60]
        adcx   r10, rax
        adox   r11, rbp
        mulx   r12, rax, [x+0x68]
        adcx   r11, rax
        adox   r12, rbp
        adcx   r12, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x58]
        mulx   rbx, rax, [x+0x60]
        adcx   r15, rax
        adox   r8, rbx
        mov    [z+0xb8], r15
        mulx   rbx, rax, [x+0x68]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x78]
        adcx   r10, rax
        adox   r11, rbx
        mov    rdx, [x+0x78]
        mulx   rbx, rax, [x+0x60]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [x+0x68]
        adcx   r12, rax
        adox   r13, rbp
        mulx   r14, rax, [x+0x70]
        adcx   r13, rax
        adox   r14, rbp
        adcx   r14, rbp
        mov    [z+0xc0], r8
        mov    [z+0xc8], r9
        mov    [z+0xd0], r10
        mov    [z+0xd8], r11
        mov    [z+0xe0], r12
        mov    [z+0xe8], r13
        mov    [z+0xf0], r14
        xor    ebp, ebp
        mov    rdx, [x]
        mulx   rbx, rax, rdx
        mov    [z], rax
        mov    rdx, [z+0x8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x8], rdx
        mov    rdx, [x+0x8]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x10]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x10], rdx
        mov    rdx, [z+0x18]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x18], rdx
        mov    rdx, [x+0x10]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x20]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x20], rdx
        mov    rdx, [z+0x28]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x28], rdx
        mov    rdx, [x+0x18]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x30]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x30], rdx
        mov    rdx, [z+0x38]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x38], rdx
        mov    rdx, [x+0x20]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x40]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x40], rdx
        mov    rdx, [z+0x48]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x48], rdx
        mov    rdx, [x+0x28]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x50]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x50], rdx
        mov    rdx, [z+0x58]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x58], rdx
        mov    rdx, [x+0x30]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x60]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x60], rdx
        mov    rdx, [z+0x68]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x68], rdx
        mov    rdx, [x+0x38]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x70]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x70], rdx
        mov    rdx, [z+0x78]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x78], rdx
        mov    rdx, [x+0x40]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x80]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x80], rdx
        mov    rdx, [z+0x88]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x88], rdx
        mov    rdx, [x+0x48]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x90]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x90], rdx
        mov    rdx, [z+0x98]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x98], rdx
        mov    rdx, [x+0x50]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xa0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xa0], rdx
        mov    rdx, [z+0xa8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xa8], rdx
        mov    rdx, [x+0x58]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xb0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xb0], rdx
        mov    rdx, [z+0xb8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xb8], rdx
        mov    rdx, [x+0x60]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xc0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xc0], rdx
        mov    rdx, [z+0xc8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xc8], rdx
        mov    rdx, [x+0x68]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xd0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xd0], rdx
        mov    rdx, [z+0xd8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xd8], rdx
        mov    rdx, [x+0x70]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xe0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xe0], rdx
        mov    rdx, [z+0xe8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xe8], rdx
        mov    rdx, [x+0x78]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xf0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xf0], rdx
        adcx   rbx, rbp
        adox   rbx, rbp
        mov    [z+0xf8], rbx
        ret
