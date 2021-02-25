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
// Input x[k]; output z[k]; temporary buffer t[>=k]
//
//    extern void bignum_negmodinv
//     (uint64_t k, uint64_t *z, uint64_t *t, uint64_t *x);
//
// The output is z with t (at least k words) used as a temporary buffer.
// Assuming x is odd (otherwise nothing makes sense) the result satisfies
//
//       x * z + 1 == 0 (mod 2^{64 * k})
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = t, X3 = x
// ----------------------------------------------------------------------------

#define y x16
#define a x17

// This is undisturbed by our local_mulc calls

#define k x0

// These we can put in the right place for bignum_mulc calls

#define b x4
#define x x5

// Ditto this, though for second it becomes b2 - b

#define b2 x2

.text

.globl bignum_negmodinv
.extern wordnegmodinv
.extern bignum_mul
.extern bignum_mulc

bignum_negmodinv:

// If length = 0 do nothing else

                cbz     x0, end

// So now we can assume k >= 1. Preserve the parameters from function calls

                mov     x, x1
                mov     y, x2
                mov     a, x3

// Initially set up a 1-word modular inverse in x as our starting-point

// ************************************
// Hacked version of wordnegmodinv.S using later registers x7-x9 only
// ************************************

                ldr     x7, [a]

                lsl x8, x7, 2
                sub x8, x7, x8
                eor x8, x8, 2
                mov x9, 1
                madd x9, x7, x8, x9
                mul x7, x9, x9
                madd x8, x9, x8, x8
                mul x9, x7, x7
                madd x8, x7, x8, x8
                mul x7, x9, x9
                madd x8, x9, x8, x8
                madd x8, x7, x8, x8

                str     x8, [x]

// ************************************
// ******* BACK TO MAIN BIGNUM-LEVEL ROUTINE
// ************************************

// If in fact we only have k = 1 then that's already the final answer

                cmp     k, 1
                beq     end

// We can now assume k >= 2; set b = 1 to indicate 1-word accuracy

                mov     b, 1

// Now the start of the main loop; part of our loop invariant is that b < k

mainloop:

// Set b2 = min(2 * b,k)
// Note that we don't need to consider overflow in 2 * b
// Besides being a crazy number, we must then violate nonoverlapping
// since the numbers would be >= 2^63 words and so > 2^64 bytes long

                add     b2, b, b
                cmp     k, b2
                csel    b2, k, b2, cc

// Set y = a * x + 1
// Actually because of the optimization below we could add
// any nonzero word, since the high part would be the same.

                mov     x1, y
                mov     x3, a
                mov     x6, 1

// [y,b2] := [a,b2] * [x,b] + 1

// ************************************
// Hacked version of bignum_mulc using same x2=m in place of x0 for p.
// THIS IS NOT THE STANDARD CALLING CONVENTION
// ************************************

                mov x7, xzr
                mov x9, xzr
outerloop1:     mov x8, xzr
                add x11, x9, 1
                cmp x11, x2
                csel x12, x11, x2, cc
                subs x11, x11, x4
                csel x11, x11, xzr, cs
                subs x10, x12, x11
                bls innerend1
                lsl x14, x11, 3
                add x14, x14, x3
                sub x15, x9, x12
                lsl x15, x15, 3
                add x15, x15, x5
innerloop1:     ldr x11, [x14], #8
                ldr x12, [x15, x10, LSL 3]
                mul x13, x11, x12
                umulh x11, x11, x12
                adds x6, x6, x13
                adcs x7, x7, x11
                adc x8, x8, xzr
                subs x10, x10, 1
                bne innerloop1
innerend1:      str x6, [x1, x9, LSL 3]
                mov x6, x7
                mov x7, x8
                add x9, x9, 1
                cmp x9, x2
                bcc outerloop1

// ************************************
// ******* BACK TO MAIN BIGNUM-LEVEL ROUTINE
// ************************************

// Set x' = x * y + x = (y + 1) * x = (a * x + 2) * x
// There is a nice optimization here: the low b of x
// are already correct, by the inductive hypothesis.
// And the bottom b of y = a * x + 1 is zero too.
// Hence to get x + x * y we can do x * y_hi and store
// it in the high part of x. Remember that in general
// b2 - b < b, and we need to allow for sizes that
// are not exactly a power of 2, hence the b2 - b to
// get the size of the top "half".

                lsl     x6, b, 3

                add     x1, x, x6

// NB: temporarily "b2" = b2 - b to save space

                sub     b2, b2, b
                add     x3, y, x6
                mov     x6, 0

// [x+8*b,b2-b] := [y+8*b,b2-b] * [x,b]

// ************************************
// Hacked version of bignum_mulc using same x2=m in place of x0 for p.
// THIS IS NOT THE STANDARD CALLING CONVENTION
// ************************************

                mov x7, xzr
                mov x9, xzr
outerloop2:     mov x8, xzr
                add x11, x9, 1
                cmp x11, x2
                csel x12, x11, x2, cc
                subs x11, x11, x4
                csel x11, x11, xzr, cs
                subs x10, x12, x11
                bls innerend2
                lsl x14, x11, 3
                add x14, x14, x3
                sub x15, x9, x12
                lsl x15, x15, 3
                add x15, x15, x5
innerloop2:     ldr x11, [x14], #8
                ldr x12, [x15, x10, LSL 3]
                mul x13, x11, x12
                umulh x11, x11, x12
                adds x6, x6, x13
                adcs x7, x7, x11
                adc x8, x8, xzr
                subs x10, x10, 1
                bne innerloop2
innerend2:      str x6, [x1, x9, LSL 3]
                mov x6, x7
                mov x7, x8
                add x9, x9, 1
                cmp x9, x2
                bcc outerloop2

// ************************************
// ******* BACK TO MAIN BIGNUM-LEVEL ROUTINE
// ************************************

// Set b = b2 and loop if it's not the whole bignum

                add     b, b, b2
                cmp     b, k
                bcc     mainloop

end:
                ret
