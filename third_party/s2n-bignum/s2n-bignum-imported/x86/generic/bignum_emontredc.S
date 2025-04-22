// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended Montgomery reduce, returning results in input-output buffer
// Inputs z[2*k], m[k], w; outputs function return (extra result bit) and z[2*k]
//
//    extern uint64_t bignum_emontredc
//     (uint64_t k, uint64_t *z, uint64_t *m, uint64_t w);
//
// Assumes that z initially holds a 2k-digit bignum z_0, m is a k-digit odd
// bignum and m * w == -1 (mod 2^64). This function also uses z for the output
// as well as returning a carry c of 0 or 1. This encodes two numbers: in the
// lower half of the z buffer we have q = z[0..k-1], while the upper half
// together with the carry gives r = 2^{64k}*c + z[k..2k-1]. These values
// satisfy z_0 + q * m = 2^{64k} * r, i.e. r gives a raw (unreduced) Montgomery
// reduction while q gives the multiplier that was used. Another way of
// thinking of it is that if z' is the output z with the lower half replaced
// with zeros, then z_0 + q * m = 2^{128k} * c + z'.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = m, RCX = w, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = m, R9 = w, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_emontredc)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_emontredc)
        .text

// Argument m comes in in rdx but we copy it to r8

#define k rdi
#define z rsi
#define m r8
#define w rcx

// General temp, low part of product and mul input
#define a rax
// General temp, High part of product
#define b rdx
// Home for i'th digit or Montgomery multiplier
#define d rbx

// Outer loop counter
#define i r9
// Inner loop counter
#define j r10

#define h r11
#define e r12
#define t r13
#define c r14

#define cshort r14d
#define jshort r10d


S2N_BN_SYMBOL(bignum_emontredc):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Save registers

        push    rbx
        push    r12
        push    r13
        push    r14

// Initialize top carry to zero immediately to catch the k = 0 case

        xor     c, c

// If k = 0 the whole operation is trivial

        test    k, k
        jz      bignum_emontredc_end

// Move m into its permanent home since we need RDX for muls

        mov     m, rdx

// Launch into the outer loop

        xor     i, i
bignum_emontredc_outerloop:
        mov     e, [z]
        mov     d, w
        imul    d, e
        mov     a, [m]
        mul     d
        mov     [z], d
        add     a, e            // Will be zero but want the carry
        mov     h, rdx
        mov     jshort, 1
        mov     t, k
        dec     t
        jz      bignum_emontredc_montend

bignum_emontredc_montloop:
        adc     h, [z+8*j]
        sbb     e, e
        mov     a, [m+8*j]
        mul     d
        sub     rdx, e
        add     a, h
        mov     [z+8*j], a
        mov     h, rdx
        inc     j
        dec     t
        jnz     bignum_emontredc_montloop

bignum_emontredc_montend:
        adc     h, c
        mov     cshort, 0
        adc     c, 0
        mov     a, [z+8*k]
        add     a, h
        mov     [z+8*k], a
        adc     c, 0

// End of outer loop.

        add     z, 8    // For simple indexing, z pointer moves
        inc     i
        cmp     i, k
        jc      bignum_emontredc_outerloop

bignum_emontredc_end:

// Put the top carry in the expected place, restore registers and return

        mov     rax, c
        pop     r14
        pop     r13
        pop     r12
        pop     rbx
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
