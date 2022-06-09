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
// Return minimum of two unsigned 64-bit words
// Inputs a, b; output function return
//
//    extern uint64_t word_min (uint64_t a, uint64_t b);
//
// Standard x86-64 ABI: RDI = a, RSI = b, returns RAX
// Microsoft x64 ABI:   RCX = a, RDX = b, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(word_min)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(word_min)
        .text

#define a %rdi
#define b %rsi

S2N_BN_SYMBOL(word_min):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

        movq    a, %rax
        cmpq    b, a
        cmovncq b, %rax
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
