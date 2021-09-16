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
// Copy bignum with zero-extension or truncation, z := x
// Input x[n]; output z[k]
//
//    extern void bignum_copy
//      (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x
// ----------------------------------------------------------------------------


        .globl  bignum_copy
        .text

#define k %rdi
#define z %rsi
#define n %rdx
#define x %rcx

#define i %r8
#define a %rax



bignum_copy:

// Replace RDX = n with RDX = min(k,n) so we are definitely safe copying those
// Initialize the element counter to 0

                cmpq    n, k
                cmovcq  k, n
                xorq    i, i

// If min(k,n) = 0 jump to the padding stage

                testq   n, n
                jz      padding

copyloop:       movq    (x,i,8), a
                movq    a, (z,i,8)
                incq    i
                cmpq    n, i
                jc      copyloop

padding:
                cmpq    k, i
                jnc     end
                xorq    a, a

padloop:        movq    a, (z,i,8)
                incq    i
                cmpq    k, i
                jc      padloop

end:            ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
