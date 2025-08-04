// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Copy bignum with zero-extension or truncation, z := x
// Input x[n]; output z[k]
//
//    extern void bignum_copy(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x);
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n, X3 = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_copy)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_copy)
        .text
        .balign 4

#define k x0
#define z x1
#define n x2
#define x x3

#define i x4
#define a x5


S2N_BN_SYMBOL(bignum_copy):

// Replace n with min(k,n) so we are definitely safe copying those
// Initialize the element counter to 0

        cmp     k, n
        csel    n, k, n, cc
        mov     i, #0

// If min(k,n) = 0 jump to the padding stage

        cbz     n, bignum_copy_padding

bignum_copy_copyloop:
        ldr     a, [x, i, lsl #3]
        str     a, [z, i, lsl #3]
        add     i, i, #1
        cmp     i, n
        bcc     bignum_copy_copyloop

bignum_copy_padding:
        cmp     i, k
        bcs     bignum_copy_end
bignum_copy_padloop:
        str     xzr, [z, i, lsl #3]
        add     i, i, #1
        cmp     i, k
        bcc     bignum_copy_padloop

bignum_copy_end:
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
