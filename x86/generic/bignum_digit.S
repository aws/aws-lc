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
// Select digit x[n]
// Inputs x[k], n; output function return
//
//    extern uint64_t bignum_digit (uint64_t k, uint64_t *x, uint64_t n);
//
// n'th digit of a k-digit (digit=64 bits) bignum, in constant-time style.
// Indexing starts at 0, which is the least significant digit (little-endian).
// Returns zero if n >= k, i.e. we read a digit off the end of the bignum.
//
// Standard x86-64 ABI: RDI = k, RSI = x, RDX = n, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_digit
        .text

#define k rdi
#define x rsi
#define n rdx

#define d rax
#define i rcx
#define a r8

bignum_digit:

// Set the default digit to 0, and for length zero finish immediately

                xor     d, d
                test    k,k
                jz      end

// Main loop: run over all the digits and take note of the n'th one

                xor     i, i
loop:
                mov     a, [x+8*i]
                cmp     i, n
                cmovz   d, a
                inc     i
                cmp     i, k
                jc      loop

// Return

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
