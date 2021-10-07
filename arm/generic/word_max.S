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
// Return maximum of two unsigned 64-bit words
// Inputs a, b; output function return
//
//    extern uint64_t word_max (uint64_t a, uint64_t b);
//
// Standard ARM ABI: X0 = a, X1 = b, returns X0
// ----------------------------------------------------------------------------

        .globl  word_max
        .text
        .balign 4

#define a x0
#define b x1

word_max:

        cmp     a, b
        csel    x0, a, b, cs
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
