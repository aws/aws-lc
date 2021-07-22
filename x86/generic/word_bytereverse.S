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
// Reverse the order of bytes in a 64-bit word
//
//    extern uint64_t word_bytereverse (uint64_t a);
//
// Standard x86-64 ABI: RDI = a, returns RAX
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  word_bytereverse
        .text

// Just uses the x86 BSWAP instruction, which does the job directly

word_bytereverse:

                mov     rax, rdi
                bswap   rax
                ret
