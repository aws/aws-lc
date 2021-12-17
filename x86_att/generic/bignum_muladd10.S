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
// Multiply bignum by 10 and add word: z := 10 * z + d
// Inputs z[k], d; outputs function return (carry) and z[k]
//
//    extern uint64_t bignum_muladd10 (uint64_t k, uint64_t *z, uint64_t d);
//
// Although typically the input d < 10, this is not actually required.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = d, returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_muladd10
        .text

#define k %rdi
#define z %rsi
#define d %rcx

#define a %rax
#define l %rax

#define h %rdx
#define i %r8
#define ten %r9
#define tenshort %r9d

bignum_muladd10:

// Move carry input to permanent home, and if k = 0 skip the main loop

                movq    %rdx, d
                testq   k, k
                jz      end

// Simple loop

                xorq    i, i
                movl    $10, tenshort
loop:
                movq    (z,i,8), a
                mulq    ten
                addq    d, l
                movq    l, (z,i,8)
                adcq    $0, h
                movq    h, d
                incq    i
                cmpq    k, i
                jc      loop

// Return the final carry

end:
                movq    d, %rax
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
