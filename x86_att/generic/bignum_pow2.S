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
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n
// ----------------------------------------------------------------------------


        .globl  bignum_pow2
        .text

#define k %rdi
#define z %rsi
#define n %rdx

#define i %rcx
#define w %rax
#define a %r8

#define wshort %eax



bignum_pow2:

// If k = 0 do nothing

                testq   k, k
                jz      end

// Create the index n at which to write the nonzero word and the word w itself
// Note that the x86 manual explicitly says that shift counts are taken modulo
// the datasize, so we don't need to mask the lower 6 bits of n ourselves.

                movl    $1, wshort
                movq    n, %rcx
                shlq    %cl, w
                shrq    $6, n

// Now in a constant-time fashion set the n'th word to w and others to zero

                xorq    i, i
loop:
                xorq    a, a
                cmpq    n, i
                cmovzq  w, a
                movq    a, (z,i,8)
                incq    i
                cmpq    k, i
                jc      loop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
