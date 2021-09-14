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
// Return bignum of power of 2, z := 2^n
// Input n; output z[k]
//
//    extern void bignum_pow2 (uint64_t k, uint64_t *z, uint64_t n);
//
// The result is as usual mod 2^{64*k}, so will be zero if n >= 64*k.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n
// ----------------------------------------------------------------------------

        .globl  bignum_pow2
        .text
        .balign 4

#define k x0
#define z x1
#define n x2

#define w x3
#define i x4
#define a x5


bignum_pow2:

// If k = 0 the result is trivially zero

                cbz     k, end

// Create the index n at which to write the nonzero word and the word w itself
// Note that the ARM manual explicitly says that shift counts are taken modulo
// the datasize, so we don't need to mask the lower 6 bits of n ourselves.

                mov     w, #1
                lsl     w, w, n
                lsr     n, n, #6

// Now in a constant-time fashion set the n'th word to w and others to zero

                mov     i, xzr
loop:
                cmp     i, n
                csel    a, w, xzr, eq
                str     a, [z, i, lsl #3]
                add     i, i, #1
                cmp     i, k
                bcc     loop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
