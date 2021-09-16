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
// Single-word negated modular inverse (-1/a) mod 2^64
// Input a; output function return
//
//    extern uint64_t word_negmodinv (uint64_t a);
//
// A 64-bit function that returns a negated multiplicative inverse mod 2^64
// of its input, assuming that input is odd. Given odd input a, the result z
// will satisfy a * z + 1 == 0 (mod 2^64), i.e. a 64-bit word multiplication
// a * z will give -1.
//
// Standard x86-64 ABI: RDI = a, returns RAX
// ----------------------------------------------------------------------------


        .globl  word_negmodinv
        .text

word_negmodinv:

// Initial magical 5-bit approximation x = (a - a<<2) xor 2

                movq    %rdi, %rcx
                movq    %rdi, %rax
                shlq    $2, %rcx
                subq    %rcx, %rax
                xorq    $2, %rax

// Now refine to 64-bit congruence

                movq    %rax, %rcx // %rcx = x
                imulq   %rdi, %rcx // %rcx = a * x
                movl    $2, %edx
                addq    %rcx, %rdx // %rdx = 1 + e = 2 + a * x
                addq    $1, %rcx // %rcx = e = a * x + 1

                imulq   %rdx, %rax // %rax = x * (1 + e)

                imulq   %rcx, %rcx // %rcx = e^2
                movl    $1, %edx
                addq    %rcx, %rdx
                imulq   %rdx, %rax // %rax = x * (1 + e) * (1 + e^2)

                imulq   %rcx, %rcx // %rcx = e^4
                movl    $1, %edx
                addq    %rcx, %rdx
                imulq   %rdx, %rax // %rax = x * (1 + e) * (1 + e^2) * (1 + e^4)

                imulq   %rcx, %rcx // %rcx = e^8
                movl    $1, %edx
                addq    %rcx, %rdx
                imulq   %rdx, %rax // %rax = x * (1 + e) * ... * * (1 + e^8)

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
