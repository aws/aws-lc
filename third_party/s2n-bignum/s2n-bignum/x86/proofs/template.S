// -------------------------------------------------------------------------
// Simulator for single x86 register-only instruction:
//
//         uint64_t harness(uint64_t *regfile);
//
// Copies state from "regfile" into registers, flags and a small buffer
// starting at the stack pointer as follows:
//
//      RAX = regfile[0]
//      RCX = regfile[1]
//      RDX = regfile[2]
//      RBX = regfile[3]
//      OF:0:0:0:SF:ZF:0:AF:0:PF:0:CF = regfile[4]
//      RBP = regfile[5]
//      RSI = regfile[6]
//      RDI = regfile[7]
//       R8 = regfile[8]
//       R9 = regfile[9]
//      R10 = regfile[10]
//      R11 = regfile[11]
//      R12 = regfile[12]
//      R13 = regfile[13]
//      R14 = regfile[14]
//      R15 = regfile[15]
//      YMM0.d[0] = regfile[16]
//      YMM0.d[1] = regfile[17]
//      YMM0.d[2] = regfile[18]
//      YMM0.d[3] = regfile[19]
//      YMM1.d[0] = regfile[20]
//      ...
//      YMM15.d[2] = regfile[78]
//      YMM15.d[3] = regfile[79]
//
//      [SP+0,...,SP+7] = regfile[80]
//      ...
//      [SP+248,...,SP+255] = regfile[111]
//
// executes the instruction at "modinst", then copies the new state
// back into the same array, also returning new value RAX directly.
//
// The flags are encoded at the bits they occur in EFLAGS and packed
// into the field corresponding to RSP (which is not modified) in the
// standard x86 register numbering:
// -------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  harness, _harness
        .text

harness:
_harness:

// Save non-modifiable input registers and input arguments on the stack

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

// Also save the "rdi" pointer rdi

        push    rdi

// Create little 256-byte buffer and copy in the contents
// We can use ymm0 because it hasn't been set yet
        sub rsp, 256
        vmovdqu ymm0, [rdi+640+0*32]
        vmovdqu [rsp], ymm0
        vmovdqu ymm0, [rdi+640+1*32]
        vmovdqu [rsp+1*32], ymm0
        vmovdqu ymm0, [rdi+640+2*32]
        vmovdqu [rsp+2*32], ymm0
        vmovdqu ymm0, [rdi+640+3*32]
        vmovdqu [rsp+3*32], ymm0
        vmovdqu ymm0, [rdi+640+4*32]
        vmovdqu [rsp+4*32], ymm0
        vmovdqu ymm0, [rdi+640+5*32]
        vmovdqu [rsp+5*32], ymm0
        vmovdqu ymm0, [rdi+640+6*32]
        vmovdqu [rsp+6*32], ymm0
        vmovdqu ymm0, [rdi+640+7*32]
        vmovdqu [rsp+7*32], ymm0

// Load new register contents from rdi (last overwrites the input pointer)

        pushfq
        pop     rcx
        mov     rax, [rdi+4*8]
        mov     rbx, 0b100011010101
        and     rax, rbx
        not     rbx
        and     rcx, rbx
        or      rax, rcx
        push    rax
        popfq

        mov     rax, [rdi+0*8]
        mov     rcx, [rdi+1*8]
        mov     rdx, [rdi+2*8]
        mov     rbx, [rdi+3*8]
        mov     rbp, [rdi+5*8]
        mov     rsi, [rdi+6*8]
        mov      r8, [rdi+8*8]
        mov      r9, [rdi+9*8]
        mov     r10, [rdi+10*8]
        mov     r11, [rdi+11*8]
        mov     r12, [rdi+12*8]
        mov     r13, [rdi+13*8]
        mov     r14, [rdi+14*8]
        mov     r15, [rdi+15*8]

        vmovdqu ymm0, [rdi+16*8]
        vmovdqu ymm1, [rdi+20*8]
        vmovdqu ymm2, [rdi+24*8]
        vmovdqu ymm3, [rdi+28*8]
        vmovdqu ymm4, [rdi+32*8]
        vmovdqu ymm5, [rdi+36*8]
        vmovdqu ymm6, [rdi+40*8]
        vmovdqu ymm7, [rdi+44*8]
        vmovdqu ymm8, [rdi+48*8]
        vmovdqu ymm9, [rdi+52*8]
        vmovdqu ymm10, [rdi+56*8]
        vmovdqu ymm11, [rdi+60*8]
        vmovdqu ymm12, [rdi+64*8]
        vmovdqu ymm13, [rdi+68*8]
        vmovdqu ymm14, [rdi+72*8]
        vmovdqu ymm15, [rdi+76*8]

        mov     rdi, [rdi+7*8]

// Execute the instruction, which may be modified from this placeholder

modinst:
        .byte ICODE

// Copy new state back to the buffer

        push    rdi
        mov     rdi, [rsp+256+8]
        mov     [rdi+0*8], rax

        pushfq
        pop     rax
        and     rax, 0b100011010101
        mov     [rdi+4*8], rax

        vmovdqu [rdi+16*8],  ymm0
        vmovdqu [rdi+20*8],  ymm1
        vmovdqu [rdi+24*8],  ymm2
        vmovdqu [rdi+28*8],  ymm3
        vmovdqu [rdi+32*8],  ymm4
        vmovdqu [rdi+36*8],  ymm5
        vmovdqu [rdi+40*8],  ymm6
        vmovdqu [rdi+44*8],  ymm7
        vmovdqu [rdi+48*8],  ymm8
        vmovdqu [rdi+52*8],  ymm9
        vmovdqu [rdi+56*8], ymm10
        vmovdqu [rdi+60*8], ymm11
        vmovdqu [rdi+64*8], ymm12
        vmovdqu [rdi+68*8], ymm13
        vmovdqu [rdi+72*8], ymm14
        vmovdqu [rdi+76*8], ymm15

        mov     [rdi+1*8],  rcx
        mov     [rdi+2*8],  rdx
        mov     [rdi+3*8],  rbx
        mov     [rdi+5*8],  rbp
        mov     [rdi+6*8],  rsi
        mov     [rdi+8*8],   r8
        mov     [rdi+9*8],   r9
        mov     [rdi+10*8], r10
        mov     [rdi+11*8], r11
        mov     [rdi+12*8], r12
        mov     [rdi+13*8], r13
        mov     [rdi+14*8], r14
        mov     [rdi+15*8], r15
        pop     rcx
        mov     [rdi+7*8],  rcx

// Copy back contents of the buffer and deallocate stack
// We can use ymm0 because its value has already been saved to regfile
        vmovdqu ymm0, [rsp]
        vmovdqu [rdi+640+0*32], ymm0
        vmovdqu ymm0, [rsp+1*32]
        vmovdqu [rdi+640+1*32], ymm0
        vmovdqu ymm0, [rsp+2*32]
        vmovdqu [rdi+640+2*32], ymm0
        vmovdqu ymm0, [rsp+3*32]
        vmovdqu [rdi+640+3*32], ymm0
        vmovdqu ymm0, [rsp+4*32]
        vmovdqu [rdi+640+4*32], ymm0
        vmovdqu ymm0, [rsp+5*32]
        vmovdqu [rdi+640+5*32], ymm0
        vmovdqu ymm0, [rsp+6*32]
        vmovdqu [rdi+640+6*32], ymm0
        vmovdqu ymm0, [rsp+7*32]
        vmovdqu [rdi+640+7*32], ymm0
        add rsp, 256

// Dummy pop to match push of rdi

        pop     rdi

// Load back the preserved registers

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

// Also return rax from the instruction

        mov     rax, [rdi+0*8]
        ret
