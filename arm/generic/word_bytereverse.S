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
// Standard ARM ABI: X0 = a, returns X0
// ----------------------------------------------------------------------------

        .globl  word_bytereverse
        .text

word_bytereverse:

                mov     x1, #0xFFFF0000FFFF0000
                mov     x2, #0x0000FFFF0000FFFF
                and     x1, x1, x0
                and     x2, x2, x0
                ror     x1, x1, #32
                orr     x0, x1, x2

                mov     x1, #0xFF00FF00FF00FF00
                mov     x2, #0x00FF00FF00FF00FF
                and     x1, x1, x0
                and     x2, x2, x0
                ror     x1, x1, #24
                ror     x2, x2, #8
                orr     x0, x1, x2

                ret
