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
// Convert single digit to bignum, z := n
// Input n; output z[k]
//
//    extern void bignum_of_word (uint64_t k, uint64_t *z, uint64_t n);
//
// Create a k-digit (digit=64 bits) bignum at z with value n (mod 2^k)
// where n is a word. The "mod 2^k" only matters in the degenerate k = 0 case.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = n
// ----------------------------------------------------------------------------

        .globl  bignum_of_word
        .text
        .balign 4

#define k x0
#define z x1
#define n x2


bignum_of_word:

                cbz     k, end                  // if k = 0 do nothing

                str     n, [z]                  // Set zeroth word to n
                subs    k, k, #1                 // k := k - 1
                beq     end                     // and if that's 0, finish

loop:
                str     xzr, [z, k, lsl #3]
                subs    k, k, #1
                bne     loop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
