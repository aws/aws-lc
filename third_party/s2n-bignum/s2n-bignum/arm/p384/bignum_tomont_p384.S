// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^384 * x) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_tomont_p384
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p384)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p384_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p384_alt)
        .text
        .balign 4

// ----------------------------------------------------------------------------
// Core "x |-> (2^64 * x) mod p_384" macro, with x assumed to be < p_384.
// Input is in [d6;d5;d4;d3;d2;d1] and output in [d5;d4;d3;d2;d1;d0]
// using d6 as well as t1, t2, t3 as temporaries.
// ----------------------------------------------------------------------------

#define modstep_p384(d6,d5,d4,d3,d2,d1,d0, t1,t2,t3)                        \
/* Initial quotient approximation q = min (h + 1) (2^64 - 1) */             \
        adds    d6, d6, #1;                                         \
        csetm   t3, cs;                                             \
        add     d6, d6, t3;                                         \
        orn     t3, xzr, t3;                                        \
        sub     t2, d6, #1;                                         \
        sub     t1, xzr, d6;                                        \
/* Correction term [d6;t2;t1;d0] = q * (2^384 - p_384) */                   \
        lsl     d0, t1, #32;                                        \
        extr    t1, t2, t1, #32;                                    \
        lsr     t2, t2, #32;                                        \
        adds    d0, d0, d6;                                         \
        adcs    t1, t1, xzr;                                        \
        adcs    t2, t2, d6;                                         \
        adc     d6, xzr, xzr;                                       \
/* Addition to the initial value */                                         \
        adds    d1, d1, t1;                                         \
        adcs    d2, d2, t2;                                         \
        adcs    d3, d3, d6;                                         \
        adcs    d4, d4, xzr;                                        \
        adcs    d5, d5, xzr;                                        \
        adc     t3, t3, xzr;                                        \
/* Use net top of the 7-word answer in t3 for masked correction */          \
        mov     t1, #0x00000000ffffffff;                            \
        and     t1, t1, t3;                                         \
        adds    d0, d0, t1;                                         \
        eor     t1, t1, t3;                                         \
        adcs    d1, d1, t1;                                         \
        mov     t1, #0xfffffffffffffffe;                            \
        and     t1, t1, t3;                                         \
        adcs    d2, d2, t1;                                         \
        adcs    d3, d3, t3;                                         \
        adcs    d4, d4, t3;                                         \
        adc     d5, d5, t3

S2N_BN_SYMBOL(bignum_tomont_p384):

S2N_BN_SYMBOL(bignum_tomont_p384_alt):

#define d0 x2
#define d1 x3
#define d2 x4
#define d3 x5
#define d4 x6
#define d5 x7
#define d6 x8

#define t1 x9
#define t2 x10
#define t3 x11

#define n0 x8
#define n1 x9
#define n2 x10
#define n3 x11
#define n4 x12
#define n5 x1

// Load the inputs

        ldp     d0, d1, [x1]
        ldp     d2, d3, [x1, #16]
        ldp     d4, d5, [x1, #32]

// Do an initial reduction to make sure this is < p_384, using just
// a copy of the bignum_mod_p384_6 code. This is needed to set up the
// invariant "input < p_384" for the main modular reduction steps.

        mov     n0, #0x00000000ffffffff
        mov     n1, #0xffffffff00000000
        mov     n2, #0xfffffffffffffffe
        subs    n0, d0, n0
        sbcs    n1, d1, n1
        sbcs    n2, d2, n2
        adcs    n3, d3, xzr
        adcs    n4, d4, xzr
        adcs    n5, d5, xzr
        csel    d0, d0, n0, cc
        csel    d1, d1, n1, cc
        csel    d2, d2, n2, cc
        csel    d3, d3, n3, cc
        csel    d4, d4, n4, cc
        csel    d5, d5, n5, cc

// Successively multiply by 2^64 and reduce

        modstep_p384(d5,d4,d3,d2,d1,d0,d6, t1,t2,t3)
        modstep_p384(d4,d3,d2,d1,d0,d6,d5, t1,t2,t3)
        modstep_p384(d3,d2,d1,d0,d6,d5,d4, t1,t2,t3)
        modstep_p384(d2,d1,d0,d6,d5,d4,d3, t1,t2,t3)
        modstep_p384(d1,d0,d6,d5,d4,d3,d2, t1,t2,t3)
        modstep_p384(d0,d6,d5,d4,d3,d2,d1, t1,t2,t3)

// Store the result and return

        stp     d1, d2, [x0]
        stp     d3, d4, [x0, #16]
        stp     d5, d6, [x0, #32]

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
