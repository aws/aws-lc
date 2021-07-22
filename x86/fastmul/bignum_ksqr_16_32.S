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
// Input x[16]; output z[32]; temporary buffer t[>=24]
//
//    extern void bignum_ksqr_16_32
//     (uint64_t z[static 32], uint64_t x[static 16], uint64_t t[static 24]);
//
// In this x86 code the final temporary space argument t is unused, but
// it is retained in the prototype above for API consistency with ARM.
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = t
// ----------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  bignum_ksqr_16_32
        .text

#define z rdi
#define x rsi

// A zero register

#define zero rbp
#define zeroe ebp

// ------------------------------------------------------------------------
// mulpadd i, j adds rdx * x[i] into the window  at the i+j point
// ------------------------------------------------------------------------

.macro mulpadd arg1,arg2
        mulx    rbx, rax, [x+8*\arg1]
.if ((\arg1 + \arg2) % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif ((\arg1 + \arg2) % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif ((\arg1 + \arg2) % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif ((\arg1 + \arg2) % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
.elseif ((\arg1 + \arg2) % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
.elseif ((\arg1 + \arg2) % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
.elseif ((\arg1 + \arg2) % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
.elseif ((\arg1 + \arg2) % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
.endif

.endm

// ------------------------------------------------------------------------
// mulpade i, j adds rdx * x[i] into the window at i+j
// but re-creates the top word assuming nothing to add there
// ------------------------------------------------------------------------

.macro mulpade arg1,arg2
.if ((\arg1 + \arg2) % 8 == 0)
        mulx    r9, rax, [x+8*\arg1]
        adcx    r8, rax
        adox    r9, zero
.elseif ((\arg1 + \arg2) % 8 == 1)
        mulx    r10, rax, [x+8*\arg1]
        adcx    r9, rax
        adox    r10, zero
.elseif ((\arg1 + \arg2) % 8 == 2)
        mulx    r11, rax, [x+8*\arg1]
        adcx    r10, rax
        adox    r11, zero
.elseif ((\arg1 + \arg2) % 8 == 3)
        mulx    r12, rax, [x+8*\arg1]
        adcx    r11, rax
        adox    r12, zero
.elseif ((\arg1 + \arg2) % 8 == 4)
        mulx    r13, rax, [x+8*\arg1]
        adcx    r12, rax
        adox    r13, zero
.elseif ((\arg1 + \arg2) % 8 == 5)
        mulx    r14, rax, [x+8*\arg1]
        adcx    r13, rax
        adox    r14, zero
.elseif ((\arg1 + \arg2) % 8 == 6)
        mulx    r15, rax, [x+8*\arg1]
        adcx    r14, rax
        adox    r15, zero
.elseif ((\arg1 + \arg2) % 8 == 7)
        mulx    r8, rax, [x+8*\arg1]
        adcx    r15, rax
        adox    r8, zero
.endif

.endm

// ------------------------------------------------------------------------
// addrow i,j adds z[i+j] + x[i..i+7] * x[j] into the window
// ------------------------------------------------------------------------

.macro addrow arg1,arg2
        mov     rdx, [x+8*\arg2]
        xor     zeroe, zeroe    // Get a known flag state and give a zero reg

.if ((\arg1 + \arg2) % 8 == 0)
        adox    r8, [z+8*(\arg1+\arg2)]
.elseif ((\arg1 + \arg2) % 8 == 1)
        adox    r9, [z+8*(\arg1+\arg2)]
.elseif ((\arg1 + \arg2) % 8 == 2)
        adox    r10, [z+8*(\arg1+\arg2)]
.elseif ((\arg1 + \arg2) % 8 == 3)
        adox    r11, [z+8*(\arg1+\arg2)]
.elseif ((\arg1 + \arg2) % 8 == 4)
        adox    r12, [z+8*(\arg1+\arg2)]
.elseif ((\arg1 + \arg2) % 8 == 5)
        adox    r13, [z+8*(\arg1+\arg2)]
.elseif ((\arg1 + \arg2) % 8 == 6)
        adox    r14, [z+8*(\arg1+\arg2)]
.elseif ((\arg1 + \arg2) % 8 == 7)
        adox    r15, [z+8*(\arg1+\arg2)]
.endif

        mulpadd \arg1, \arg2

.if ((\arg1 + \arg2) % 8 == 0)
        mov     [z+8*(\arg1+\arg2)], r8
.elseif ((\arg1 + \arg2) % 8 == 1)
        mov     [z+8*(\arg1+\arg2)], r9
.elseif ((\arg1 + \arg2) % 8 == 2)
        mov     [z+8*(\arg1+\arg2)], r10
.elseif ((\arg1 + \arg2) % 8 == 3)
        mov     [z+8*(\arg1+\arg2)], r11
.elseif ((\arg1 + \arg2) % 8 == 4)
        mov     [z+8*(\arg1+\arg2)], r12
.elseif ((\arg1 + \arg2) % 8 == 5)
        mov     [z+8*(\arg1+\arg2)], r13
.elseif ((\arg1 + \arg2) % 8 == 6)
        mov     [z+8*(\arg1+\arg2)], r14
.elseif ((\arg1 + \arg2) % 8 == 7)
        mov     [z+8*(\arg1+\arg2)], r15
.endif

        mulpadd (\arg1+1), \arg2
        mulpadd (\arg1+2), \arg2
        mulpadd (\arg1+3), \arg2
        mulpadd (\arg1+4), \arg2
        mulpadd (\arg1+5), \arg2
        mulpade (\arg1+6), \arg2
        mulpade (\arg1+7), \arg2

.if ((\arg1 + \arg2) % 8 == 0)
        adcx    r8, zero
.elseif ((\arg1 + \arg2) % 8 == 1)
        adcx    r9, zero
.elseif ((\arg1 + \arg2) % 8 == 2)
        adcx    r10, zero
.elseif ((\arg1 + \arg2) % 8 == 3)
        adcx    r11, zero
.elseif ((\arg1 + \arg2) % 8 == 4)
        adcx    r12, zero
.elseif ((\arg1 + \arg2) % 8 == 5)
        adcx    r13, zero
.elseif ((\arg1 + \arg2) % 8 == 6)
        adcx    r14, zero
.elseif ((\arg1 + \arg2) % 8 == 7)
        adcx    r15, zero
.endif


.endm


// ------------------------------------------------------------------------
// Adds off-diagonal part of x[i..i+7]^2 into the window, writes 0..7 back
// ------------------------------------------------------------------------

.macro sqr arg1

        xor     zeroe, zeroe

// Set up the initial window

        mov     r9, [z+16*\arg1+8*1]
        mov     r10, [z+16*\arg1+8*2]
        mov     r11, [z+16*\arg1+8*3]
        mov     r12, [z+16*\arg1+8*4]
        mov     r13, [z+16*\arg1+8*5]
        mov     r14, [z+16*\arg1+8*6]
        mov     r15, [z+16*\arg1+8*7]

// Add in the first diagonal [r8..r10] + 2 wb = 10 + 20 + 30 + 40 + 50 + 60 + 70

        mov     rdx, [x+8*\arg1+8*0]
        mulpadd (\arg1+1), (\arg1+0)
        mov     [z+16*\arg1+8*1],r9
        mulpadd (\arg1+2), (\arg1+0)
        mov     [z+16*\arg1+8*2],r10
        mulpadd (\arg1+3), (\arg1+0)
        mulpadd (\arg1+4), (\arg1+0)
        mulpadd (\arg1+5), (\arg1+0)
        mulpadd (\arg1+6), (\arg1+0)
        mulpade (\arg1+7), (\arg1+0)
        adcx    r8, zero

// Add in the next diagonal = 21 + 31 + 41 + 51 + 61 + 71 + 54

        xor     zeroe, zeroe
        mov     rdx, [x+8*\arg1+8*1]
        mulpadd (\arg1+2), (\arg1+1)
        mov     [z+16*\arg1+8*3], r11
        mulpadd (\arg1+3), (\arg1+1)
        mov     [z+16*\arg1+8*4], r12
        mulpadd (\arg1+4), (\arg1+1)
        mulpadd (\arg1+5), (\arg1+1)
        mulpadd (\arg1+6), (\arg1+1)
        mulpade (\arg1+7), (\arg1+1)
        mov     rdx, [x+8*\arg1+8*4]
        mulpade (\arg1+5), (\arg1+4)
        adcx    r10, zero

// And the next one = 32 + 42 + 52 + 62 + 72 + 64 + 65

        xor     zeroe, zeroe
        mov     rdx, [x+8*\arg1+8*2]
        mulpadd (\arg1+3), (\arg1+2)
        mov     [z+16*\arg1+8*5], r13
        mulpadd (\arg1+4), (\arg1+2)
        mov     [z+16*\arg1+8*6], r14
        mulpadd (\arg1+5), (\arg1+2)
        mulpadd (\arg1+6), (\arg1+2)
        mulpadd (\arg1+7), (\arg1+2)
        mov     rdx, [x+8*\arg1+8*6]
        mulpade (\arg1+4), (\arg1+6)
        mulpade (\arg1+5), (\arg1+6)
        adcx    r12, zero

// And the final one = 43 + 53 + 63 + 73 + 74 + 75 + 76

        xor     zeroe, zeroe
        mov     rdx, [x+8*\arg1+8*3]
        mulpadd (\arg1+4), (\arg1+3)
        mov     [z+16*\arg1+8*7], r15
        mulpadd (\arg1+5), (\arg1+3)
        mulpadd (\arg1+6), (\arg1+3)
        mulpadd (\arg1+7), (\arg1+3)
        mov     rdx, [x+8*\arg1+8*7]
        mulpadd (\arg1+4), (\arg1+7)
        mulpade (\arg1+5), (\arg1+7)
        mulpade (\arg1+6), (\arg1+7)
        adcx    r14, zero
.endm

// ------------------------------------------------------------------------
// Multiply-add: z := z + x[i...i+7] * x
// ------------------------------------------------------------------------

.macro addrows arg1

        sqr \arg1

        .set i,  (\arg1+8)
.rep (8-\arg1)
        addrow \arg1, i
        .set i,  (i+1)
.endr

        mov     [z+8*(16+\arg1)], r8
        mov     [z+8*(17+\arg1)], r9
        mov     [z+8*(18+\arg1)], r10
        mov     [z+8*(19+\arg1)], r11
        mov     [z+8*(20+\arg1)], r12
        mov     [z+8*(21+\arg1)], r13
        mov     [z+8*(22+\arg1)], r14
.endm


// ------------------------------------------------------------------------
// mulrow i,j adds x[i..i+7] * x[j] into the window
// just like addrow but no addition of z[i+j]
// ------------------------------------------------------------------------

.macro mulrow arg1,arg2
        mov     rdx, [x+8*\arg2]
        xor     zeroe, zeroe    // Get a known flag state and give a zero reg

        mulpadd \arg1, \arg2

.if ((\arg1 + \arg2) % 8 == 0)
        mov     [z+8*(\arg1+\arg2)], r8
.elseif ((\arg1 + \arg2) % 8 == 1)
        mov     [z+8*(\arg1+\arg2)], r9
.elseif ((\arg1 + \arg2) % 8 == 2)
        mov     [z+8*(\arg1+\arg2)], r10
.elseif ((\arg1 + \arg2) % 8 == 3)
        mov     [z+8*(\arg1+\arg2)], r11
.elseif ((\arg1 + \arg2) % 8 == 4)
        mov     [z+8*(\arg1+\arg2)], r12
.elseif ((\arg1 + \arg2) % 8 == 5)
        mov     [z+8*(\arg1+\arg2)], r13
.elseif ((\arg1 + \arg2) % 8 == 6)
        mov     [z+8*(\arg1+\arg2)], r14
.elseif ((\arg1 + \arg2) % 8 == 7)
        mov     [z+8*(\arg1+\arg2)], r15
.endif

        mulpadd (\arg1+1), \arg2
        mulpadd (\arg1+2), \arg2
        mulpadd (\arg1+3), \arg2
        mulpadd (\arg1+4), \arg2
        mulpadd (\arg1+5), \arg2
.if ((\arg1 + \arg2) % 8 == 0)
        mulpade (\arg1+6), \arg2
.else
        mulpadd (\arg1+6), \arg2
.endif

        mulpade (\arg1+7), \arg2

.if ((\arg1 + \arg2) % 8 == 0)
        adcx    r8, zero
.elseif ((\arg1 + \arg2) % 8 == 1)
        adcx    r9, zero
.elseif ((\arg1 + \arg2) % 8 == 2)
        adcx    r10, zero
.elseif ((\arg1 + \arg2) % 8 == 3)
        adcx    r11, zero
.elseif ((\arg1 + \arg2) % 8 == 4)
        adcx    r12, zero
.elseif ((\arg1 + \arg2) % 8 == 5)
        adcx    r13, zero
.elseif ((\arg1 + \arg2) % 8 == 6)
        adcx    r14, zero
.elseif ((\arg1 + \arg2) % 8 == 7)
        adcx    r15, zero
.endif


.endm

// ------------------------------------------------------------------------
// Compute off-diagonal part of x[0..7]^2, write back 1..7 elements and
// set up the high part in the standard register window. DOES NOT WRITE z[0]!
// ------------------------------------------------------------------------

.macro sqrz

        xor     zeroe, zeroe

// Set initial window [r8..r10] + 2 wb = 10 + 20 + 30 + 40 + 50 + 60 + 70

        mov     rdx, [x+8*0]
        mulx    rax, r9, [x+8*1]
        mov     [z+8*1], r9
        mulx    rbx, r10, [x+8*2]
        adcx    r10, rax
        mov     [z+8*2], r10
        mulx    rax, r11, [x+8*3]
        adcx    r11, rbx
        mulx    rbx, r12, [x+8*4]
        adcx    r12, rax
        mulx    rax, r13, [x+8*5]
        adcx    r13, rbx
        mulx    rbx, r14, [x+8*6]
        adcx    r14, rax
        mulx    r8, r15, [x+8*7]
        adcx    r15, rbx
        adcx    r8, zero

// Add in the next diagonal = 21 + 31 + 41 + 51 + 61 + 71 + 54

        xor     zeroe, zeroe
        mov     rdx, [x+8*1]
        mulpadd 2, 1
        mov     [z+8*3], r11
        mulpadd 3, 1
        mov     [z+8*4], r12
        mulpadd 4, 1
        mulpadd 5, 1
        mulpadd 6, 1
        mulpade 7, 1
        mov     rdx, [x+8*4]
        mulpade 5, 4
        adcx    r10, zero

// And the next one = 32 + 42 + 52 + 62 + 72 + 64 + 65

        xor     zeroe, zeroe
        mov     rdx, [x+8*2]
        mulpadd 3, 2
        mov     [z+8*5], r13
        mulpadd 4, 2
        mov     [z+8*6], r14
        mulpadd 5, 2
        mulpadd 6, 2
        mulpadd 7, 2
        mov     rdx, [x+8*6]
        mulpade 4, 6
        mulpade 5, 6
        adcx    r12, zero

// And the final one = 43 + 53 + 63 + 73 + 74 + 75 + 76

        xor     zeroe, zeroe
        mov     rdx, [x+8*3]
        mulpadd 4, 3
        mov     [z+8*7], r15
        mulpadd 5, 3
        mulpadd 6, 3
        mulpadd 7, 3
        mov     rdx, [x+8*7]
        mulpadd 4, 7
        mulpade 5, 7
        mulpade 6, 7
        adcx    r14, zero
.endm

// ------------------------------------------------------------------------
// Multiply-add: z := x[0...7] * x off-diagonal elements
// ------------------------------------------------------------------------

.macro mulrows
        sqrz

        .set i,  8
.rep 8
        mulrow 0, i
        .set i,  (i+1)
.endr

        mov     [z+8*16], r8
        mov     [z+8*17], r9
        mov     [z+8*18], r10
        mov     [z+8*19], r11
        mov     [z+8*20], r12
        mov     [z+8*21], r13
        mov     [z+8*22], r14
        mov     [z+8*23], r15
.endm

// ------------------------------------------------------------------------
// The actual code
// ------------------------------------------------------------------------



bignum_ksqr_16_32:

// Save more registers to play with

        push    rbp
        push    rbx
        push    r12
        push    r13
        push    r14
        push    r15

// Now just systematically add in the rows to get all off-diagonal elements

        mulrows
        addrows 8

// Double and add the diagonal elements. Note that z[0] was never written above

        xor     zeroe, zeroe
        mov     rdx, [x+8*0]
        mulx    rbx, rax, rdx
        mov     [z+8*0], rax

        mov     rdx, [z+8*1]
        adcx    rdx, rdx
        adox    rdx, rbx
        mov     [z+8*1], rdx

        .set i,  1
.rep 14
        mov     rdx, [x+8*i]
        mulx    rbx, rax, rdx

        mov     rdx, [z+8*(2*i)]
        adcx    rdx, rdx
        adox    rdx, rax
        mov     [z+8*(2*i)], rdx

        mov     rdx, [z+8*(2*i+1)]
        adcx    rdx, rdx
        adox    rdx, rbx
        mov     [z+8*(2*i+1)], rdx
        .set i,  (i+1)
.endr

        mov     rdx, [x+8*i]
        mulx    rbx, rax, rdx

        mov     rdx, [z+8*(2*i)]
        adcx    rdx, rdx
        adox    rdx, rax
        mov     [z+8*(2*i)], rdx

        adcx    rbx, zero
        adox    rbx, zero
        mov     [z+8*(2*i+1)], rbx
        .set i,  (i+1)


// Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx
        pop     rbp

        ret
