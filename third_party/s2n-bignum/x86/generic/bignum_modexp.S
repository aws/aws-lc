// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Modular exponentiation for arbitrary odd modulus
// Inputs a[k], p[k], m[k]; output z[k], temporary buffer t[>=3*k]
//
//   extern void bignum_modexp
//    (uint64_t k,uint64_t *z, uint64_t *a,uint64_t *p,uint64_t *m,uint64_t *t);
//
// Does z := (a^p) mod m where all numbers are k-digit and m is odd
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = a, RCX = p, R8 = m, R9 = t
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = a, R9 = p, [RSP+40] = m, [RSP+48] = t
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_modexp)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_modexp)
        .text

// Local variables, all kept on the stack

#define k [rsp]
#define res [rsp+8]
#define a [rsp+16]
#define p [rsp+24]
#define m [rsp+32]
#define x [rsp+40]
#define i [rsp+48]
#define y [rsp+56]
#define z [rsp+64]

#define VARSIZE 72

S2N_BN_SYMBOL(bignum_modexp):

// The Windows version literally calls the standard ABI version.
// This simplifies the proofs since subroutine offsets are fixed.

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
        mov     r9, [rsp+64]
        call    bignum_modexp_standard
        pop    rsi
        pop    rdi
        ret

bignum_modexp_standard:
#endif

// Real start of the standard ABI code.
// Bump down the stack to make room for local variables

        sub     rsp, VARSIZE

// If size is zero (which falsifies the oddness condition) do nothing

        test    rdi, rdi
        jz      end

// Set up local variables based on input parameters

        mov     k, rdi
        mov     res, rsi
        mov     a, rdx
        mov     p, rcx
        mov     m, r8
        mov     x, r9
        lea     rax, [r9+8*rdi]
        mov     y, rax
        lea     rax, [rax+8*rdi]
        mov     z, rax

// Let x == 2^64k * a (mod m) and initialize z == 2^64k * 1 (mod m)

        mov     rdi, k
        mov     rsi, z
        mov     rdx, m
        mov     rcx, y
        call    local_amontifier

        mov     rdi, k
        mov     rsi, x
        mov     rdx, z
        mov     rcx, a
        mov     r8, m
        call    local_amontmul

        mov     rdi, k
        mov     rsi, z
        mov     rdx, z
        mov     rcx, m
        call    local_demont

// Main loop with z == 2^64k * a^(p >> 2^i) (mod m)

        mov     rax, k
        shl     rax, 6
        mov     i, rax

loop:
        sub     rax, 1
        mov     i, rax

        mov     rdi, k
        mov     rsi, y
        mov     rdx, z
        mov     rcx, z
        mov     r8, m
        call    local_amontmul

        mov     rdi, k
        mov     rsi, z
        mov     rdx, x
        mov     rcx, y
        mov     r8, m
        call    local_amontmul

        mov     rdx, i
        mov     rcx, rdx
        shr     rdx, 6
        mov     rsi, p
        mov     rdi, [rsi+8*rdx]
        shr     rdi, cl
        and     rdi, 1

        mov     rsi, k
        mov     rdx, z
        mov     rcx, z
        mov     r8, y
        call    local_mux

        mov     rax, i
        test    rax, rax
        jnz     loop

// Convert back from Montgomery representation and copy the result
// (via a degenerate case of multiplexing) into the output buffer

        mov     rdi, k
        mov     rsi, z
        mov     rdx, z
        mov     rcx, m
        call    local_demont

        xor     edi, edi
        mov     rsi, k
        mov     rdx, res
        mov     rcx, z
        mov     r8, z
        call    local_mux

// Restore the stack pointer and return

end:
        add     rsp, VARSIZE
        ret

// Local copy of bignum_amontifier

local_amontifier:
         push   rbp
         push   rbx
         push   r12
         push   r13
         mov    r12, rdx
         mov    r13, rcx
         test   rdi, rdi
         je     amontifier_end
         xor    rbx, rbx
copyinloop:
         mov    rcx, [r12+8*rbx]
         mov    [r13+8*rbx], rcx
         inc    rbx
         cmp    rbx, rdi
         jb     copyinloop
         mov    rbx, rdi
         dec    rbx
         je     normalized
normloop:
         xor    rbp, rbp
         mov    r11, rdi
         neg    rcx
         mov    eax, 0x0
shufloop:
         mov    rcx, rax
         mov    rax, [r13+8*rbp]
         cmovb  rcx, rax
         mov    [r13+8*rbp], rcx
         inc    rbp
         dec    r11
         jne    shufloop
         dec    rbx
         jne    normloop
normalized:
         bsr    rcx, rcx
         xor    rcx, 0x3f
         xor    r9, r9
         xor    rbx, rbx
bitloop:
         mov    rax, [r13+8*rbx]
         mov    rbp, rax
         shld   rax, r9, cl
         mov    [r13+8*rbx], rax
         mov    r9, rbp
         inc    rbx
         cmp    rbx, rdi
         jb     bitloop
         mov    r11, [r13+8*rdi-0x8]
         mov    r8d, 0x1
         mov    r9, r11
         neg    r9
         mov    ebx, 0x3e
estloop:
         add    r8, r8
         mov    rax, r11
         sub    rax, r9
         cmp    r9, rax
         sbb    rax, rax
         not    rax
         sub    r8, rax
         add    r9, r9
         and    rax, r11
         sub    r9, rax
         dec    rbx
         jne    estloop
         inc    r9
         cmp    r11, r9
         adc    r8, 0x0
         xor    rcx, rcx
         xor    rbx, rbx
mulloop:
         mov    rax, [r13+8*rbx]
         mul    r8
         add    rax, rcx
         adc    rdx, 0x0
         mov    [rsi+8*rbx], rax
         mov    rcx, rdx
         inc    rbx
         cmp    rbx, rdi
         jb     mulloop
         movabs rax, 0x4000000000000000
         sub    rcx, rax
         sbb    r8, r8
         not    r8
         xor    rcx, rcx
         xor    rbx, rbx
remloop:
         mov    rax, [r13+8*rbx]
         and    rax, r8
         neg    rcx
         sbb    rax, [rsi+8*rbx]
         sbb    rcx, rcx
         mov    [rsi+8*rbx], rax
         inc    rbx
         cmp    rbx, rdi
         jb     remloop
         xor    rcx, rcx
         xor    rbp, rbp
         xor    r9, r9
dubloop1:
         mov    rax, [rsi+8*rbp]
         shrd   rcx, rax, 0x3f
         neg    r9
         sbb    rcx, [r13+8*rbp]
         sbb    r9, r9
         mov    [rsi+8*rbp], rcx
         mov    rcx, rax
         inc    rbp
         cmp    rbp, rdi
         jb     dubloop1
         shr    rcx, 0x3f
         add    rcx, r9
         xor    rbp, rbp
         xor    r9, r9
corrloop1:
         mov    rax, [r13+8*rbp]
         and    rax, rcx
         neg    r9
         adc    rax, [rsi+8*rbp]
         sbb    r9, r9
         mov    [rsi+8*rbp], rax
         inc    rbp
         cmp    rbp, rdi
         jb     corrloop1
         xor    rcx, rcx
         xor    rbp, rbp
         xor    r9, r9
dubloop2:
         mov    rax, [rsi+8*rbp]
         shrd   rcx, rax, 0x3f
         neg    r9
         sbb    rcx, [r13+8*rbp]
         sbb    r9, r9
         mov    [rsi+8*rbp], rcx
         mov    rcx, rax
         inc    rbp
         cmp    rbp, rdi
         jb     dubloop2
         shr    rcx, 0x3f
         add    rcx, r9
         xor    rbp, rbp
         xor    r9, r9
corrloop2:
         mov    rax, [r13+8*rbp]
         and    rax, rcx
         neg    r9
         adc    rax, [rsi+8*rbp]
         sbb    r9, r9
         mov    [rsi+8*rbp], rax
         mov    [r13+8*rbp], rax
         inc    rbp
         cmp    rbp, rdi
         jb     corrloop2
         xor    r11, r11
         mov    rbx, rdi
modloop:
         xor    r9, r9
         mov    r8, rdi
         xor    rbp, rbp
         xor    rcx, rcx
cmaloop:
         adc    rcx, r9
         sbb    r10, r10
         mov    rax, [rsi+8*rbp]
         mul    r11
         sub    rdx, r10
         add    rax, rcx
         mov    r9, [r13+8*rbp]
         mov    [r13+8*rbp], rax
         mov    rcx, rdx
         inc    rbp
         dec    r8
         jne    cmaloop
         adc    r9, rcx
         mov    r11, r9
         sbb    r10, r10
         xor    rbp, rbp
         xor    rcx, rcx
oaloop:
         mov    rax, [r13+8*rbp]
         mov    r9, [rsi+8*rbp]
         and    r9, r10
         neg    rcx
         adc    rax, r9
         sbb    rcx, rcx
         mov    [r13+8*rbp], rax
         inc    rbp
         cmp    rbp, rdi
         jb     oaloop
         sub    r11, rcx
         dec    rbx
         jne    modloop
         mov    rax, [r12]
         mov    rcx, rax
         mov    r9, rax
         shl    rcx, 0x2
         sub    r9, rcx
         xor    r9, 0x2
         mov    rcx, r9
         imul   rcx, rax
         mov    eax, 0x2
         add    rax, rcx
         add    rcx, 0x1
         imul   r9, rax
         imul   rcx, rcx
         mov    eax, 0x1
         add    rax, rcx
         imul   r9, rax
         imul   rcx, rcx
         mov    eax, 0x1
         add    rax, rcx
         imul   r9, rax
         imul   rcx, rcx
         mov    eax, 0x1
         add    rax, rcx
         imul   r9, rax
         mov    rcx, [r13]
         imul   r9, rcx
         mov    rax, [r12]
         mul    r9
         add    rax, rcx
         mov    rcx, rdx
         mov    ebp, 0x1
         mov    r8, rdi
         dec    r8
         je     montifend
montifloop:
         adc    rcx, [r13+8*rbp]
         sbb    r10, r10
         mov    rax, [r12+8*rbp]
         mul    r9
         sub    rdx, r10
         add    rax, rcx
         mov    [r13+8*rbp-0x8], rax
         mov    rcx, rdx
         inc    rbp
         dec    r8
         jne    montifloop
montifend:
         adc    r11, rcx
         sbb    r10, r10
         mov    [r13+8*rdi-0x8], r11
         xor    rbp, rbp
         xor    rcx, rcx
osloop:
         mov    rax, [r13+8*rbp]
         mov    r9, [r12+8*rbp]
         and    r9, r10
         neg    rcx
         sbb    rax, r9
         sbb    rcx, rcx
         mov    [rsi+8*rbp], rax
         inc    rbp
         cmp    rbp, rdi
         jb     osloop
amontifier_end:
         pop    r13
         pop    r12
         pop    rbx
         pop    rbp
         ret

// Local copy of bignum_amontmul

local_amontmul:
         push   rbx
         push   rbp
         push   r12
         push   r13
         push   r14
         push   r15
         sub    rsp, 0x8
         test   rdi, rdi
         je     amont_end
         mov    r9, rdx
         mov    rax, [r8]
         mov    rdx, rax
         mov    rbx, rax
         shl    rdx, 0x2
         sub    rbx, rdx
         xor    rbx, 0x2
         mov    rdx, rbx
         imul   rdx, rax
         mov    eax, 0x2
         add    rax, rdx
         add    rdx, 0x1
         imul   rbx, rax
         imul   rdx, rdx
         mov    eax, 0x1
         add    rax, rdx
         imul   rbx, rax
         imul   rdx, rdx
         mov    eax, 0x1
         add    rax, rdx
         imul   rbx, rax
         imul   rdx, rdx
         mov    eax, 0x1
         add    rax, rdx
         imul   rbx, rax
         mov    [rsp], rbx
         xor    r13, r13
         xor    rbx, rbx
zoop:
         mov    [rsi+8*rbx], r13
         inc    rbx
         cmp    rbx, rdi
         jb     zoop
         xor    r14, r14
outeramontloop:
         mov    rbp, [r9+8*r13]
         xor    rbx, rbx
         xor    r10, r10
         xor    r15, r15
         mov    r12, rdi
maddloop:
         adc    r10, [rsi+8*rbx]
         sbb    r11, r11
         mov    rax, [rcx+8*rbx]
         mul    rbp
         sub    rdx, r11
         add    rax, r10
         mov    [rsi+8*rbx], rax
         mov    r10, rdx
         inc    rbx
         dec    r12
         jne    maddloop
         adc    r14, r10
         adc    r15, r15
         mov    r11, [rsi]
         mov    rbp, [rsp]
         imul   rbp, r11
         mov    rax, [r8]
         mul    rbp
         add    rax, r11
         mov    r10, rdx
         mov    ebx, 0x1
         mov    r12, rdi
         dec    r12
         je     montend
montloop:
         adc    r10, [rsi+8*rbx]
         sbb    r11, r11
         mov    rax, [r8+8*rbx]
         mul    rbp
         sub    rdx, r11
         add    rax, r10
         mov    [rsi+8*rbx-0x8], rax
         mov    r10, rdx
         inc    rbx
         dec    r12
         jne    montloop
montend:
         adc    r10, r14
         adc    r15, 0x0
         mov    r14, r15
         mov    [rsi+8*rbx-0x8], r10
         inc    r13
         cmp    r13, rdi
         jb     outeramontloop
         xor    rbp, rbp
         sub    rbp, r14
         xor    r11, r11
         xor    rbx, rbx
acorrloop:
         mov    rax, [r8+8*rbx]
         and    rax, rbp
         neg    r11
         sbb    [rsi+8*rbx], rax
         sbb    r11, r11
         inc    rbx
         cmp    rbx, rdi
         jb     acorrloop
amont_end:
         add    rsp, 0x8
         pop    r15
         pop    r14
         pop    r13
         pop    r12
         pop    rbp
         pop    rbx
         ret

// Local copy of bignum_demont

local_demont:
         push   rbx
         push   rbp
         push   r12
         test   rdi, rdi
         je     demont_end
         mov    rax, [rcx]
         mov    rbx, rax
         mov    r8, rax
         shl    rbx, 0x2
         sub    r8, rbx
         xor    r8, 0x2
         mov    rbx, r8
         imul   rbx, rax
         mov    eax, 0x2
         add    rax, rbx
         add    rbx, 0x1
         imul   r8, rax
         imul   rbx, rbx
         mov    eax, 0x1
         add    rax, rbx
         imul   r8, rax
         imul   rbx, rbx
         mov    eax, 0x1
         add    rax, rbx
         imul   r8, rax
         imul   rbx, rbx
         mov    eax, 0x1
         add    rax, rbx
         imul   r8, rax
         xor    rbx, rbx
iloop:
         mov    rax, [rdx+8*rbx]
         mov    [rsi+8*rbx], rax
         inc    rbx
         cmp    rbx, rdi
         jb     iloop
         xor    r9, r9
outerdemontloop:
         mov    r11, [rsi]
         mov    rbp, r8
         imul   rbp, r11
         mov    rax, [rcx]
         mul    rbp
         add    rax, r11
         mov    r10, rdx
         mov    ebx, 0x1
         mov    r12, rdi
         dec    r12
         je     demontend
demontloop:
         adc    r10, [rsi+8*rbx]
         sbb    r11, r11
         mov    rax, [rcx+8*rbx]
         mul    rbp
         sub    rdx, r11
         add    rax, r10
         mov    [rsi+8*rbx-0x8], rax
         mov    r10, rdx
         inc    rbx
         dec    r12
         jne    demontloop
demontend:
         adc    r10, 0x0
         mov    [rsi+8*rbx-0x8], r10
         inc    r9
         cmp    r9, rdi
         jb     outerdemontloop
         xor    rbx, rbx
         mov    r12, rdi
cmploop:
         mov    rax, [rsi+8*rbx]
         sbb    rax, [rcx+8*rbx]
         inc    rbx
         dec    r12
         jne    cmploop
         sbb    rbp, rbp
         not    rbp
         xor    r11, r11
         xor    rbx, rbx
dcorrloop:
         mov    rax, [rcx+8*rbx]
         and    rax, rbp
         neg    r11
         sbb    [rsi+8*rbx], rax
         sbb    r11, r11
         inc    rbx
         cmp    rbx, rdi
         jb     dcorrloop
demont_end:
         pop    r12
         pop    rbp
         pop    rbx
         ret

// Local copy of bignum_mux

local_mux:
         test   rsi, rsi
         je     muxend
         xor    r9, r9
         neg    rdi
muxloop:
         mov    rax, [rcx+8*r9]
         mov    rdi, [r8+8*r9]
         cmovae rax, rdi
         mov    [rdx+8*r9], rax
         inc    r9
         dec    rsi
         jne    muxloop
muxend:
         ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
