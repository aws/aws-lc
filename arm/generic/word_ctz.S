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
// Count trailing zero bits in a single word
// Input a; output function return
//
//    extern uint64_t word_ctz (uint64_t a);
//
// Standard ARM ABI: X0 = a, returns X0
// ----------------------------------------------------------------------------

        .globl  word_ctz
        .text

word_ctz:

// ARM doesn't have a direct word ctz instruction, so we emulate it via
// ctz(w) = 64 - clz(~w & (w-1)). This is depending, for cases of the form
// ctz(....1), on the behavior clz(0) = 64, which is guaranteed according
// to the ARM manual.

                mvn     x1, x0
                sub     x0, x0, #1
                and     x0, x0, x1
                clz     x1, x0
                mov     x0, #64
                sub     x0, x0, x1

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
