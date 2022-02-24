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
// 384-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero
// Input x[6]; output function return
//
//    extern uint64_t bignum_nonzero_6(uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = x, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_nonzero_6
        .globl  _bignum_nonzero_6
        .text

#define x %rdi
#define a %rax
#define d %rdx
#define dshort %edx



bignum_nonzero_6:
_bignum_nonzero_6:

// Generate a = an OR of all the words in the bignum

                movq    (x), a
                movq    8(x), d
                orq     16(x), a
                orq     24(x), d
                orq     32(x), a
                orq     40(x), d
                orq     d, a

// Set a standard C condition based on whether a is nonzero

                movl    $1, dshort
                cmovnzq d, a

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
