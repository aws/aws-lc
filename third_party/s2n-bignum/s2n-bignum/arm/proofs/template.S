// -------------------------------------------------------------------------
// Simulator for single ARM register-only instruction:
//
//         uint64_t harness(uint64_t *regfile);
//
// Copies state from "regfile" into registers, flags and a small buffer
// starting at the stack pointer.
//
//         X0 = regfile[0]
//         X1 = regfile[1]
//         ...
//         X30 = regfile[30]
//
//         NF:ZF:CF:VF = regfile[31] & 0xF
//
//         Q0.d[0] = regfile[32]
//         Q0.d[1] = regfile[33]
//         ...
//         Q31.d[1] = regfile[95]
//
//         [SP+0,..,SP+7] = reg[96]
//         ...
//         [SP+248,...,SP+255] = reg[127]
//
// executes the instruction at "modinst", then copies the new state
// back into the same array, also returning new value X0 directly.
// -------------------------------------------------------------------------

        .globl  harness, _harness
        .text
        .balign 4

#define regfile x0

#define pccode x20

harness:
_harness:

// Save non-modifiable input registers

                str     q31, [sp, -16]!
                str     q30, [sp, -16]!
                str     q29, [sp, -16]!
                str     q28, [sp, -16]!
                str     q27, [sp, -16]!
                str     q26, [sp, -16]!
                str     q25, [sp, -16]!
                str     q24, [sp, -16]!
                str     q23, [sp, -16]!
                str     q22, [sp, -16]!
                str     q21, [sp, -16]!
                str     q20, [sp, -16]!
                str     q19, [sp, -16]!
                str     q18, [sp, -16]!
                str     q17, [sp, -16]!
                str     q16, [sp, -16]!
                str     q15, [sp, -16]!
                str     q14, [sp, -16]!
                str     q13, [sp, -16]!
                str     q12, [sp, -16]!
                str     q11, [sp, -16]!
                str     q10, [sp, -16]!
                str     q9,  [sp, -16]!
                str     q8,  [sp, -16]!
                str     q7,  [sp, -16]!
                str     q6,  [sp, -16]!
                str     q5,  [sp, -16]!
                str     q4,  [sp, -16]!
                str     q3,  [sp, -16]!
                str     q2,  [sp, -16]!
                str     q1,  [sp, -16]!
                str     q0,  [sp, -16]!
                stp     x30, xzr,  [sp, -16]!
                stp     x28, x29,  [sp, -16]!
                stp     x26, x27,  [sp, -16]!
                stp     x24, x25,  [sp, -16]!
                stp     x22, x23,  [sp, -16]!
                stp     x20, x21,  [sp, -16]!
                stp     x18, x19,  [sp, -16]!

// Also save the "regfile" pointer on the stack

                stp     x0, x1,    [sp, -16]!

// Create little 256-byte buffer and copy in the contents

                sub     sp, sp, #256
                ldr     q31, [regfile, 768]
                str     q31, [sp]
                ldr     q31, [regfile, 768+1*16]
                str     q31, [sp, 1*16]
                ldr     q31, [regfile, 768+2*16]
                str     q31, [sp, 2*16]
                ldr     q31, [regfile, 768+3*16]
                str     q31, [sp, 3*16]
                ldr     q31, [regfile, 768+4*16]
                str     q31, [sp, 4*16]
                ldr     q31, [regfile, 768+5*16]
                str     q31, [sp, 5*16]
                ldr     q31, [regfile, 768+6*16]
                str     q31, [sp, 6*16]
                ldr     q31, [regfile, 768+7*16]
                str     q31, [sp, 7*16]
                ldr     q31, [regfile, 768+8*16]
                str     q31, [sp, 8*16]
                ldr     q31, [regfile, 768+9*16]
                str     q31, [sp, 9*16]
                ldr     q31, [regfile, 768+10*16]
                str     q31, [sp, 10*16]
                ldr     q31, [regfile, 768+11*16]
                str     q31, [sp, 11*16]
                ldr     q31, [regfile, 768+12*16]
                str     q31, [sp, 12*16]
                ldr     q31, [regfile, 768+13*16]
                str     q31, [sp, 13*16]
                ldr     q31, [regfile, 768+14*16]
                str     q31, [sp, 14*16]
                ldr     q31, [regfile, 768+15*16]
                str     q31, [sp, 15*16]

// Load new register contents from regfile (last overwrites args)

                ldr     q31, [regfile, 16*47]
                ldr     q30, [regfile, 16*46]
                ldr     q29, [regfile, 16*45]
                ldr     q28, [regfile, 16*44]
                ldr     q27, [regfile, 16*43]
                ldr     q26, [regfile, 16*42]
                ldr     q25, [regfile, 16*41]
                ldr     q24, [regfile, 16*40]
                ldr     q23, [regfile, 16*39]
                ldr     q22, [regfile, 16*38]
                ldr     q21, [regfile, 16*37]
                ldr     q20, [regfile, 16*36]
                ldr     q19, [regfile, 16*35]
                ldr     q18, [regfile, 16*34]
                ldr     q17, [regfile, 16*33]
                ldr     q16, [regfile, 16*32]
                ldr     q15, [regfile, 16*31]
                ldr     q14, [regfile, 16*30]
                ldr     q13, [regfile, 16*29]
                ldr     q12, [regfile, 16*28]
                ldr     q11, [regfile, 16*27]
                ldr     q10, [regfile, 16*26]
                ldr     q9,  [regfile, 16*25]
                ldr     q8,  [regfile, 16*24]
                ldr     q7,  [regfile, 16*23]
                ldr     q6,  [regfile, 16*22]
                ldr     q5,  [regfile, 16*21]
                ldr     q4,  [regfile, 16*20]
                ldr     q3,  [regfile, 16*19]
                ldr     q2,  [regfile, 16*18]
                ldr     q1,  [regfile, 16*17]
                ldr     q0,  [regfile, 16*16]
                ldp     x30, x29,  [regfile, 16*15]
                lsl     x29, x29, #28
                msr     nzcv, x29
                ldp     x28, x29,  [regfile, 16*14]
                ldp     x26, x27,  [regfile, 16*13]
                ldp     x24, x25,  [regfile, 16*12]
                ldp     x22, x23,  [regfile, 16*11]
                ldp     x20, x21,  [regfile, 16*10]
                ldp     x18, x19,  [regfile, 16*9]
                ldp     x16, x17,  [regfile, 16*8]
                ldp     x14, x15,  [regfile, 16*7]
                ldp     x12, x13,  [regfile, 16*6]
                ldp     x10, x11,  [regfile, 16*5]
                ldp     x8, x9,    [regfile, 16*4]
                ldp     x6, x7,    [regfile, 16*3]
                ldp     x4, x5,    [regfile, 16*2]
                ldp     x2, x3,    [regfile, 16*1]
                ldp     x0, x1,    [regfile, 16*0]

// Execute the instruction, which may be modified from this placeholder

modinst:
                .inst      ICODE   // To be modified by script

// Copy new state back to the buffer

                stp     x0, x1, [sp, -16]!
                ldr     regfile, [sp, 256+16]

                str     q31, [regfile, 16*47]
                str     q30, [regfile, 16*46]
                str     q29, [regfile, 16*45]
                str     q28, [regfile, 16*44]
                str     q27, [regfile, 16*43]
                str     q26, [regfile, 16*42]
                str     q25, [regfile, 16*41]
                str     q24, [regfile, 16*40]
                str     q23, [regfile, 16*39]
                str     q22, [regfile, 16*38]
                str     q21, [regfile, 16*37]
                str     q20, [regfile, 16*36]
                str     q19, [regfile, 16*35]
                str     q18, [regfile, 16*34]
                str     q17, [regfile, 16*33]
                str     q16, [regfile, 16*32]
                str     q15, [regfile, 16*31]
                str     q14, [regfile, 16*30]
                str     q13, [regfile, 16*29]
                str     q12, [regfile, 16*28]
                str     q11, [regfile, 16*27]
                str     q10, [regfile, 16*26]
                str     q9,  [regfile, 16*25]
                str     q8,  [regfile, 16*24]
                str     q7,  [regfile, 16*23]
                str     q6,  [regfile, 16*22]
                str     q5,  [regfile, 16*21]
                str     q4,  [regfile, 16*20]
                str     q3,  [regfile, 16*19]
                str     q2,  [regfile, 16*18]
                str     q1,  [regfile, 16*17]
                str     q0,  [regfile, 16*16]

                mrs     x1, nzcv
                lsr     x1, x1, #28
                and     x1, x1, #0xF
                stp     x30, x1,   [regfile, 16*15]

                stp     x28, x29,  [regfile, 16*14]
                stp     x26, x27,  [regfile, 16*13]
                stp     x24, x25,  [regfile, 16*12]
                stp     x22, x23,  [regfile, 16*11]
                stp     x20, x21,  [regfile, 16*10]
                stp     x18, x19,  [regfile, 16*9]
                stp     x16, x17,  [regfile, 16*8]
                stp     x14, x15,  [regfile, 16*7]
                stp     x12, x13,  [regfile, 16*6]
                stp     x10, x11,  [regfile, 16*5]
                stp     x8, x9,    [regfile, 16*4]
                stp     x6, x7,    [regfile, 16*3]
                stp     x4, x5,    [regfile, 16*2]
                stp     x2, x3,    [regfile, 16*1]

                ldp     x2, x3,    [sp], #16

                stp     x2, x3,    [regfile, 16*0]

// Copy back contents of the buffer and deallocate stack
// This includes getting rid of the space for "regfile"
// which is still safely in  x0 now

                ldr     q31, [sp]
                str     q31, [regfile, 768]
                ldr     q31, [sp, 1*16]
                str     q31, [regfile, 768+1*16]
                ldr     q31, [sp, 2*16]
                str     q31, [regfile, 768+2*16]
                ldr     q31, [sp, 3*16]
                str     q31, [regfile, 768+3*16]
                ldr     q31, [sp, 4*16]
                str     q31, [regfile, 768+4*16]
                ldr     q31, [sp, 5*16]
                str     q31, [regfile, 768+5*16]
                ldr     q31, [sp, 6*16]
                str     q31, [regfile, 768+6*16]
                ldr     q31, [sp, 7*16]
                str     q31, [regfile, 768+7*16]
                ldr     q31, [sp, 8*16]
                str     q31, [regfile, 768+8*16]
                ldr     q31, [sp, 9*16]
                str     q31, [regfile, 768+9*16]
                ldr     q31, [sp, 10*16]
                str     q31, [regfile, 768+10*16]
                ldr     q31, [sp, 11*16]
                str     q31, [regfile, 768+11*16]
                ldr     q31, [sp, 12*16]
                str     q31, [regfile, 768+12*16]
                ldr     q31, [sp, 13*16]
                str     q31, [regfile, 768+13*16]
                ldr     q31, [sp, 14*16]
                str     q31, [regfile, 768+14*16]
                ldr     q31, [sp, 15*16]
                str     q31, [regfile, 768+15*16]
                add     sp, sp, #256+16

// Load back the preserved registers

                ldp     x18, x19, [sp], #16
                ldp     x20, x21, [sp], #16
                ldp     x22, x23, [sp], #16
                ldp     x24, x25, [sp], #16
                ldp     x26, x27, [sp], #16
                ldp     x28, x29, [sp], #16
                ldp     x30, xzr, [sp], #16
                ldr     q0,  [sp], #16
                ldr     q1,  [sp], #16
                ldr     q2,  [sp], #16
                ldr     q3,  [sp], #16
                ldr     q4,  [sp], #16
                ldr     q5,  [sp], #16
                ldr     q6,  [sp], #16
                ldr     q7,  [sp], #16
                ldr     q8,  [sp], #16
                ldr     q9,  [sp], #16
                ldr     q10, [sp], #16
                ldr     q11, [sp], #16
                ldr     q12, [sp], #16
                ldr     q13, [sp], #16
                ldr     q14, [sp], #16
                ldr     q15, [sp], #16
                ldr     q16, [sp], #16
                ldr     q17, [sp], #16
                ldr     q18, [sp], #16
                ldr     q19, [sp], #16
                ldr     q20, [sp], #16
                ldr     q21, [sp], #16
                ldr     q22, [sp], #16
                ldr     q23, [sp], #16
                ldr     q24, [sp], #16
                ldr     q25, [sp], #16
                ldr     q26, [sp], #16
                ldr     q27, [sp], #16
                ldr     q28, [sp], #16
                ldr     q29, [sp], #16
                ldr     q30, [sp], #16
                ldr     q31, [sp], #16

// Also return x0 from the instruction, which was moved to x2

                mov     x0, x2

                ret
