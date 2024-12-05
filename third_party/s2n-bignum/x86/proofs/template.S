// -------------------------------------------------------------------------
// Simulator for single x86 register-only instruction:
//
//         uint64_t harness(uint64_t *regfile);
//
// Copies state from "regfile" into registers and flags as follows:
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
//
// executes the instruction at "modinst", then copies the new state
// back into the same array, also returning new value RAX directly.
//
// The flags are encoded at the bits they occur in EFLAGS and packed
// into the field corresponding to RSP (which is not modified) in the
// standard x86 register numbering:
// -------------------------------------------------------------------------

        .intel_syntax noprefix
        .globl  harness
        .text

harness:

// Save non-modifiable input registers and input arguments on the stack

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

// Also save the "rdi" pointer rdi

        push    rdi

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

        mov     rdi, [rdi+7*8]

// Execute the instruction, which may be modified from this placeholder

modinst:
        .byte ICODE

// Copy new state back to the buffer

        push    rdi
        mov     rdi, [rsp+8]
        mov     [rdi+0*8], rax

        pushfq
        pop     rax
        and     rax, 0b100011010101
        mov     [rdi+4*8], rax

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
