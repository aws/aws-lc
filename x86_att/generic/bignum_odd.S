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
// Test bignum for odd-ness
// Input x[k]; output function return
//
//    extern uint64_t bignum_odd (uint64_t k, uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_odd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_odd)
        .text

S2N_BN_SYMBOL(bignum_odd):

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Load RAX with the lowest digit for k > 0, else 0

        xorq    %rax, %rax
        testq   %rdi, %rdi
        cmovnzq (%rsi), %rax

// Now just return the LSB

        andq    $1, %rax
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
