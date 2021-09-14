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
// Negated modular inverse, z := (-1/x) mod 2^{64k}
// Input x[k]; output z[k]
//
//    extern void bignum_negmodinv
//     (uint64_t k, uint64_t *z, uint64_t *x);
//
// Assuming x is odd (otherwise nothing makes sense) the result satisfies
//
//       x * z + 1 == 0 (mod 2^{64 * k})
//
// but is not necessarily reduced mod x.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = x
// ----------------------------------------------------------------------------

        .globl  bignum_negmodinv
        .text
        .balign 4

#define k x0
#define z x1
#define x x2

#define w x3
#define a x4
#define m x5
#define h x6
#define l x7
#define e x8
#define i x9



bignum_negmodinv:

// If k = 0 do nothing

                cbz     k, end

// Compute word-level negated modular inverse w for x[0].

                ldr     a, [x]
                lsl     w, a, #2
                sub     w, a, w
                eor     w, w, #2
                mov     h, #1
                madd    h, a, w, h
                mul     l, h, h
                madd    w, h, w, w
                mul     h, l, l
                madd    w, l, w, w
                mul     l, h, h
                madd    w, h, w, w
                madd    w, l, w, w

// Write that as lowest word of the output, then if k = 1 we're finished

                str     w, [z]
                cmp     k, #1
                beq     end

// Otherwise compute and write the other digits (1..k-1) of w * x + 1.
// Note that at this point CF was set by the comparison (subtraction) "k - 1".
// Since k >= 2 if we got here, this subtraction didn't carry; allowing
// for the inverted carry on ARM that means that CF is guaranteed to be set.
// This allows us to ignore the nominal "a * w + 1" from adding the low
// part of the product, since its only contribution is to set the carry
// flag. Thus, we only calculate the high part of a * w explicitly.

                umulh   h, a, w
                mov     i, #1
initloop:
                ldr     a, [x, i, lsl #3]
                mul     l, a, w
                adcs    l, l, h
                umulh   h, a, w
                str     l, [z, i, lsl #3]
                add     i, i, #1
                sub     a, k, i
                cbnz    a, initloop

// For simpler indexing, z := z + 8 and k := k - 1 per outer iteration
// Then we can use the same index for x and for z and effective size k.
//
// But we also offset k by 1 so the "real" size is k + 1, which is why the
// test at the end of the inner loop is i < k <=> i' = i + 1 < k + 1.
// This lets us avoid some special cases inside the loop at the cost
// of needing the additional "finale" tail for the final iteration
// since we do one outer loop iteration too few.

                subs    k, k, #2
                beq     finale

outerloop:
                add     z, z, #8
                ldr     e, [z]
                mul     m, e, w
                str     m, [z]
                ldr     a, [x]
                umulh   h, a, m
                subs    xzr, e, #1         // Effective carry from a * m + e
                mov     i, #1
innerloop:
                ldr     a, [x, i, lsl #3]
                ldr     e, [z, i, lsl #3]
                mul     l, a, m
                adcs    e, e, h
                umulh   h, a, m
                adc     h, h, xzr
                adds    e, e, l
                str     e, [z, i, lsl #3]
                sub     a, i, k
                add     i, i, #1
                cbnz    a, innerloop

                subs    k, k, #1
                bne     outerloop

finale:
                ldr     e, [z, #8]
                mul     m, e, w
                str     m, [z, #8]

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
