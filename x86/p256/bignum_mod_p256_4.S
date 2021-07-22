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
// Reduce modulo field characteristic, z := x mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_mod_p256_4
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_mod_p256_4
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9

#define n1 r10
#define n3 r11
#define c rax

#define n1short r10d



bignum_mod_p256_4:

// Load the input and subtract to get [d3;d3;d1;d1] = x - p_256 (modulo 2^256)
// The constants n1 and n3 in [n3; 0; n1; -1] = p_256 are saved for later

        mov     d0, [x]
        sub     d0, -1
        mov     d1, [x+8]
        mov     n1short, 0x00000000ffffffff
        sbb     d1, n1
        mov     d2, [x+16]
        sbb     d2, 0
        mov     n3, 0xffffffff00000001
        mov     d3, [x+24]
        sbb     d3, n3

// Capture the carry to determine whether to add back p_256, and use
// it to create a masked p_256' = [n3; 0; n1; c]

        sbb     c, c
        and     n1, c
        and     n3, c

// Do the corrective addition and copy to output

        add     d0, c
        mov     [z], d0
        adc     d1, n1
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16], d2
        adc     d3, n3
        mov     [z+24], d3

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
