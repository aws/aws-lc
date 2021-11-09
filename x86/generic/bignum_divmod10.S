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
// Divide bignum by 10: z' := z div 10, returning remainder z mod 10
// Inputs z[k]; outputs function return (remainder) and z[k]
//
//    extern uint64_t bignum_divmod10 (uint64_t k, uint64_t *z);
//
// Standard x86-64 ABI: RDI = k, RSI = z, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_divmod10
        .text

#define k rdi
#define z rsi

#define d rcx

#define l rdx
#define r rax

#define q r8
#define h r8

#define s r9
#define w r10

#define rshort eax
#define wshort r10d

bignum_divmod10:

// Initialize remainder to 0 and if k = 0 return

                xor     rshort, rshort
                test    k, k
                jz      end

// Straightforward top-down loop doing 10 * q + r' := 2^64 * r + d

                mov     s, 0x3333333333333334
                mov     wshort, 0x3333333

divloop:
                mov     d, [z+8*k-8]

// First re-split and shift so 2^28 * h + l = (2^64 * r + d) / 2
// Then (2^64 * r + d) / 10 = [(2^28 - 1) / 5] * h + (h + l) / 5

                mov     l, d
                shl     l, 35
                shld    r, d, 35
                shr     l, 36
                mov     h, r

                add     r, l
                mul     s
                imul    h, w
                add     q, l
                mov     [z+8*k-8], q

// Generate the new remainder r = d - 10 * q
// Since r <= 9 we only need the low part computation ignoring carries

                lea     q, [q+4*q]
                neg     q
                lea     r, [d+2*q]

                dec     k
                jnz     divloop

// Return rax = r as the final remainder

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
