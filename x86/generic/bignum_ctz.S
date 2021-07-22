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
// Count trailing zero bits
// Input x[k]; output function return
//
//    extern uint64_t bignum_ctz (uint64_t k, uint64_t *x);
//
//
// In the case of a zero bignum as input the result is 64 * k
//
// In principle this has a precondition k < 2^58, but obviously that
// is always true in practice because of address space limitations
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_ctz
        .text

#define k rdi
#define x rsi
#define i rdx
#define w rcx
#define a rax

#define wshort ecx



bignum_ctz:

// If the bignum is zero-length, just return 0

                xor     rax, rax
                test    k, k
                jz      end

// Use w = a[i-1] to store nonzero words in a top-down sweep
// Set the initial default to be as if we had a 1 word directly above

                mov     i, k
                inc     i
                mov     wshort, 1

loop:
                mov     a, [x+8*k-8]
                test    a, a
                cmovne  i, k
                cmovne  w, a
                dec     k
                jnz     loop

// Now w = a[i-1] is the lowest nonzero word, or in the zero case the
// default of the "extra" 1 = a[k]. We now want 64*(i-1) + ctz(w).
// Note that this code does not rely on the behavior of the BSF instruction
// for zero inputs, which is undefined according to the manual.

                dec     i
                shl     i, 6
                bsf     rax, w
                add     rax, i

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
