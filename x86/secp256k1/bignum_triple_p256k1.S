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
// Triple modulo p_256k1, z := (3 * x) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_triple_p256k1
//      (uint64_t z[static 4], uint64_t x[static 4]);
//
// The input x can be any 4-digit bignum, not necessarily reduced modulo
// p_256k1, and the result is always fully reduced, z = (3 * x) mod p_256k1.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_triple_p256k1
        .text

#define z rdi
#define x rsi

// Main digits of intermediate results

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

// Quotient estimate = top of product + 1

#define q rdx

// Other temporary variables and their short version

#define a rax
#define c rcx

#define ashort eax
#define qshort edx

bignum_triple_p256k1:

// First do the multiplication by 3, getting z = [h; d3; ...; d0]
// but immediately form the quotient estimate q = h + 1

                xor     ashort, ashort

                mov     q, [x]
                mov     d0, q
                adcx    q, q
                adox    d0, q
                mov     q, [x+8]
                mov     d1, q
                adcx    q, q
                adox    d1, q
                mov     q, [x+16]
                mov     d2, q
                adcx    q, q
                adox    d2, q
                mov     q, [x+24]
                mov     d3, q
                adcx    q, q
                adox    d3, q

// For this limited range a simple quotient estimate of q = h + 1 works, where
// h = floor(z / 2^256). Then -p_256k1 <= z - q * p_256k1 < p_256k1.

                mov     qshort, 1
                adcx    q, a
                adox    q, a

// Initial subtraction of z - q * p_256k1, actually by adding q * 4294968273.

                mov     c, 4294968273
                xor     a, a
                imul    q, c
                add     d0, q
                adc     d1, a
                adc     d2, a
                adc     d3, a

// With z = 2^256 * h + l, the underlying result z' is actually
// (2^256 * h + l) - q * (2^256 - 4294968273) = (l + q * 4294968273) - 2^256
// so carry-clear <=> z' is negative. Correct by subtracting in that case.
// In any case, write final result to z as we go.

                cmovc   c, a

                sub     d0, c
                mov     [z], d0
                sbb     d1, a
                mov     [z+8], d1
                sbb     d2, a
                mov     [z+16],d2
                sbb     d3, a
                mov     [z+24],d3

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
