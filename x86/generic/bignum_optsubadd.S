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
// Optionally subtract or add, z := x + sgn(p) * y interpreting p as signed
// Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_optsubadd
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y);
//
// If p has top bit set (i.e. is negative as a signed int) return z := x - y
// Else if p is nonzero (i.e. is positive as a signed int) return z := x + y
// Otherwise (i.e. p is zero) return z := x
//
// Return in RDI = the top carry, which will be 0 or 1, and appropriate for
// addition or subtraction respectively (and always zero for p = 0)
//
// 2^{64*k} * -carryout + z = x - y [for subtraction]
// 2^{64*k} * carryout + z = x + y [for addition]
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = p, R8 = y, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_optsubadd
        .text

#define k rdi
#define z rsi
#define x rdx
#define p rcx
#define y r8

#define c rax
#define i r9
#define m rcx
#define q r10
#define a r11


bignum_optsubadd:

// Initialize top carry to zero in all cases (also return value)

                xor     c, c

// If k = 0 do nothing

                test    k, k
                jz      end

// Turn the input p into two bitmasks, m indicating to use the y input at
// all (same register as p) and q indicating a sign-flip

                mov     q, p
                sar     q, 63
                neg     p
                sbb     m, m

// Generate an initial carry-in for the negating case only to add 1; this
// is because we are actually going to do complements of the words of y

                mov     c, q

// Now go round the loop for i=0...k-1, saving the carry in c each iteration

                xor     i, i
loop:
                mov     a, [y+8*i]
                xor     a, q
                and     a, m
                neg     c
                adc     a, [x+8*i]
                sbb     c, c
                mov     [z+8*i], a
                inc     i
                cmp     i, k
                jc      loop

// Return carry flag, fixing up inversion for negative case

                xor     rax, q
                neg     rax

end:            ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
