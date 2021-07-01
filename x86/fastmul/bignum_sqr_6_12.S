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
// Square, z := x^2
// Input x[6]; output z[12]
//
//    extern void bignum_sqr_6_12 (uint64_t z[static 12], uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

.intel_syntax noprefix

// These are actually right

#define z rdi
#define x rsi

// A zero register

#define zero rbp

// Other registers

#define d1 r8
#define d2 r9
#define d3 r10
#define d4 r11
#define d5 r12
#define d6 r13
#define d7 r14
#define d8 r15
#define d9 rbx

// Care is needed: re-using the zero register

#define d10 rbp

                .globl  bignum_sqr_6_12
                .text

bignum_sqr_6_12:

// Save more registers to play with

        push    rbp
        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15

// Set up an initial window [d8;...d1] = [34;05;03;01]

        mov     rdx, [x]
        mulx    d2, d1, [x+8*1]
        mulx    d4, d3, [x+8*3]
        mulx    d6, d5, [x+8*5]
        mov     rdx, [x+8*3]
        mulx    d8, d7, [x+8*4]

// Clear our zero register, and also initialize the flags for the carry chain

        xor     zero, zero

// Chain in the addition of 02 + 12 + 13 + 14 + 15 to that window
// (no carry-out possible since we add it to the top of a product)

        mov     rdx, [x+8*2]
        mulx    rcx, rax, [x]
        adcx    d2, rax
        adox    d3, rcx
        mulx    rcx, rax, [x+8*1]
        adcx    d3, rax
        adox    d4, rcx
        mov     rdx, [x+8*1]
        mulx    rcx, rax, [x+8*3]
        adcx    d4, rax
        adox    d5, rcx
        mulx    rcx, rax, [x+8*4]
        adcx    d5, rax
        adox    d6, rcx
        mulx    rcx, rax, [x+8*5]
        adcx    d6, rax
        adox    d7, rcx
        adcx    d7, zero
        adox    d8, zero
        adcx    d8, zero

// Again zero out the flags. Actually they are already cleared but it may
// help decouple these in the OOO engine not to wait for the chain above

        xor     zero, zero

// Now chain in the 04 + 23 + 24 + 25 + 35 + 45 terms
// We are running out of registers and here our zero register is not zero!

        mov     rdx, [x+8*4]
        mulx    rcx, rax, [x]
        adcx    d4, rax
        adox    d5, rcx
        mov     rdx, [x+8*2]
        mulx    rcx, rax, [x+8*3]
        adcx    d5, rax
        adox    d6, rcx
        mulx    rcx, rax, [x+8*4]
        adcx    d6, rax
        adox    d7, rcx
        mulx    rcx, rax, [x+8*5]
        adcx    d7, rax
        adox    d8, rcx
        mov     rdx, [x+8*3]
        mulx    d9, rax, [x+8*5]
        adcx    d8, rax
        adox    d9, zero
        mov     rdx, [x+8*4]
        mulx    d10, rax, [x+8*5]
        adcx    d9, rax
        mov     eax, 0
        adox    d10, rax
        adcx    d10, rax

// Again, just for a clear fresh start for the flags

        xor     rax, rax

// Double and add to the 00 + 11 + 22 + 33 + 44 + 55 terms
//
// We could use shift-double but this seems tidier and in larger squarings
// it was actually more efficient. I haven't experimented with this small
// case to see how much that matters. Note: the writeback here is sprinkled
// into the sequence in such a way that things still work if z = x, i.e. if
// the output overwrites the input buffer and beyond.

        mov     rdx, [x]
        mulx    rdx, rax, rdx
        mov     [z], rax
        adcx    d1, d1
        adox    d1, rdx
        mov     rdx, [x+8*1]
        mov     [z+8*1], d1
        mulx    rdx, rax, rdx
        adcx    d2, d2
        adox    d2, rax
        adcx    d3, d3
        adox    d3, rdx
        mov     rdx, [x+8*2]
        mov     [z+8*2], d2
        mulx    rdx, rax, rdx
        adcx    d4, d4
        adox    d4, rax
        adcx    d5, d5
        adox    d5, rdx
        mov     rdx, [x+8*3]
        mov     [z+8*3], d3
        mulx    rdx, rax, rdx
        adcx    d6, d6
        adox    d6, rax
        adcx    d7, d7
        adox    d7, rdx
        mov     rdx, [x+8*4]
        mov     [z+8*4], d4
        mulx    rdx, rax, rdx
        adcx    d8, d8
        adox    d8, rax
        adcx    d9, d9
        adox    d9, rdx
        mov     rdx, [x+8*5]
        mov     [z+8*5], d5
        mulx    rdx, rax, rdx
        mov     [z+8*6], d6
        adcx    d10, d10
        mov     [z+8*7], d7
        adox    d10, rax
        mov     [z+8*8], d8
        mov     eax, 0
        mov     [z+8*9], d9
        adcx    rdx, rax
        mov     [z+8*10], d10
        adox    rdx, rax
        mov     [z+8*11], rdx

// Restore saved registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx
        pop     rbp

        ret
