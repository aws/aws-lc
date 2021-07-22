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
// 256-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero
// Input x[4]; output function return
//
//    extern uint64_t bignum_nonzero_4(uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = x, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_nonzero_4
        .text

#define x rdi
#define a rax
#define d rdx
#define dshort edx



bignum_nonzero_4:

// Generate a = an OR of all the words in the bignum

                mov     a, [x]
                mov     d, [x+8*1]
                or      a, [x+8*2]
                or      d, [x+8*3]
                or      a, d

// Set a standard C condition based on whether a is nonzero

                mov     dshort, 1
                cmovnz  a, d

                ret
