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
// Count leading zero bits in a single word
// Input a; output function return
//
//    extern uint64_t word_clz (uint64_t a);
//
// Standard x86-64 ABI: RDI = a, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  word_clz
        .text

word_clz:

// First do rax = 63 - bsr(a), which is right except (maybe) for zero inputs

        bsr     rax, rdi
        xor     rax, 63

// Force return of 64 in the zero-input case

        mov     edx, 64
        test    rdi, rdi
        cmove   rax, rdx

        ret
