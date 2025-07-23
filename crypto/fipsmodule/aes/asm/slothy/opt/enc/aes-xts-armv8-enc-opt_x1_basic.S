// The following xts encrypt is from MacBook M3 build folder
// after moving around some instructions

#if !defined(__has_feature)
#define __has_feature(x) 0
#endif
#if __has_feature(memory_sanitizer) && !defined(OPENSSL_NO_ASM)
#define OPENSSL_NO_ASM
#endif

#include <openssl/asm_base.h>

#if !defined(OPENSSL_NO_ASM) && defined(__AARCH64EL__)
#if defined(__ELF__)
#include <openssl/boringssl_prefix_symbols_asm.h>
#include <openssl/arm_arch.h>
.arch   armv8-a+crypto
.text
.globl  aes_hw_slothy_xts_encrypt
.hidden aes_hw_slothy_xts_encrypt
.type   aes_hw_slothy_xts_encrypt,%function
#elif defined(__APPLE__)
#if defined(BORINGSSL_PREFIX)
#include <boringssl_prefix_symbols_asm.h>
#endif
#include <openssl/arm_arch.h>
.text
.globl	_aes_hw_slothy_xts_encrypt
.private_extern	_aes_hw_slothy_xts_encrypt
#else
#error Unknown configuration
#endif

#if __ARM_MAX_ARCH__ >= 8

.align  4


#define STACK_BASE_VREGS 0
#define STACK_SIZE_VREGS (6*16)

.macro save_vregs
     stp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
     stp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
     stp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        stp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

.macro save_regs
        stp  x19, x20, [sp, #(STACK_BASE_VREGS + 16*4)]
      stp  x21, x22, [sp, #(STACK_BASE_VREGS + 16*5)]
.endm

.macro restore_vregs
        ldp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
        ldp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
        ldp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        ldp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

.macro restore_regs
        ldp  x19, x20, [sp, #(STACK_BASE_VREGS + 16*4)]
        ldp  x21, x22, [sp, #(STACK_BASE_VREGS + 16*5)]
.endm

// A single AES round
// Prevent SLOTHY from unfolding because uArchs tend to fuse AESMC+AESE
.macro aesr data, key // @slothy:no-unfold
        aese  \data, \key
        aesmc \data, \data
.endm

.macro tweak lo, hi
        extr  x22, x10, x10, #32
        extr  x10, x10,  x9, #63
        and   w11, w19, w22, asr#31
        eor   x9,  x11,  x9, lsl#1
        fmov  \lo,  x9
        fmov  \hi, x10
.endm

_aes_hw_slothy_xts_encrypt:
aes_hw_slothy_xts_encrypt:
  # AARCH64_VALID_CALL_TARGET

        sub sp, sp, #STACK_SIZE_VREGS
        save_vregs
        save_regs

        cmp   x2, #16 // AES-XTS needs at least one block
        b.lt  Lxts_abort
.align  4
Lxts_enc_big_size:  // Encrypt input size >= 16 bytes
        and  x21, x2, #0xf    // store the tail value of length%16
        and  x2, x2, #-16    // len &= 0x1..110000, now divisible by 16
        subs x2, x2, #16

        // Firstly, encrypt the iv with key2, as the first iv of XEX.
        ldr  w6, [x4,#240]
        ld1  {v0.4s}, [x4], #16
        ld1  {v6.16b}, [x5]
        sub  w6, w6, #2
        ld1  {v1.4s}, [x4], #16

Loop_iv_enc:
        aesr v6.16b, v0.16b
        ld1  {v0.4s}, [x4], #16
        subs w6, w6, #2
        aesr v6.16b, v1.16b
        ld1  {v1.4s}, [x4], #16
        b.gt Loop_iv_enc

        aesr v6.16b, v0.16b
        ld1  {v0.4s}, [x4]
        aese v6.16b, v1.16b
        eor  v6.16b, v6.16b, v0.16b

        // set up registers and constant for tweak
        fmov  x9, d6
        fmov  x10, v6.d[1]
        mov   w19, #0x87

        mov x7, x3
        ld1 {v16.4s,v17.4s},[x7], #32         // load key schedule
        ld1 {v12.4s,v13.4s},[x7], #32
        ld1 {v14.4s,v15.4s},[x7], #32
        ld1 {v4.4s,v5.4s},  [x7], #32
        ld1 {v18.4s,v19.4s},[x7], #32
        ld1 {v20.4s,v21.4s},[x7], #32
        ld1 {v22.4s,v23.4s},[x7], #32
        ld1 {v7.4s},        [x7]

.align  4
        ldr q9, [x0], #0x10
        sub x2, x2, #16
cbz x2, Loop1x_xts_enc_postamble
Loop1x_xts_enc:
                                          // Instructions:    25
                                          // Expected cycles: 38
                                          // Expected IPC:    0.66
                                          //
                                          // Cycle bound:     38.0
                                          // IPC bound:       0.66
                                          //
                                          // Wall time:     1.02s
                                          // User time:     1.02s
                                          //
                                          // --------- cycle (expected) ---------->
                                          // 0                        25
                                          // |------------------------|------------
        eor v9.16B, v9.16B, v6.16B        // *.....................................
        extr x13, x10, x10, #32           // *.....................................
        extr x10, x10, x9, #63            // *.....................................
        and w13, w19, w13, asr #31        // .*....................................
        aesr v9.16b, v16.16b              // ..*...................................
        eor x9, x13, x9, lsl #1           // ..*...................................
        aesr v9.16b, v17.16b              // ....*.................................
        aesr v9.16b, v12.16b              // ......*...............................
        aesr v9.16b, v13.16b              // ........*.............................
        aesr v9.16b, v14.16b              // ..........*...........................
        aesr v9.16b, v15.16b              // ............*.........................
        aesr v9.16b, v4.16b               // ..............*.......................
        aesr v9.16b, v5.16b               // ................*.....................
        aesr v9.16b, v18.16b              // ..................*...................
        aesr v9.16b, v19.16b              // ....................*.................
        aesr v9.16b, v20.16b              // ......................*...............
        aesr v9.16b, v21.16b              // ........................*.............
        aesr v9.16b, v22.16b              // ..........................*...........
        aese v9.16b, v23.16b              // ............................*.........
        eor v9.16B, v9.16B, v7.16B        // ..............................*.......
        eor v3.16B, v9.16B, v6.16B        // ................................*.....
        fmov d6, x9                       // ................................*.....
        ldr q9, [x0], #0x10               // .................................e....
        str q3, [x1], #0x10               // ..................................*...
        fmov v6.d[1], x10                 // ...................................*..

                                                    // ----------- cycle (expected) ----------->
                                                    // 0                        25
                                                    // |------------------------|---------------
        // ldr q0, [x0], #0x10                      // e....'................................~..
        // eor  v0.16b,v0.16b,v6.16b                // .....*...................................
        // aesr    v0.16b, v16.16b                  // .....'.*.................................
        // aesr    v0.16b, v17.16b                  // .....'...*...............................
        // aesr    v0.16b, v12.16b                  // .....'.....*.............................
        // aesr    v0.16b, v13.16b                  // .....'.......*...........................
        // aesr    v0.16b, v14.16b                  // .....'.........*.........................
        // aesr    v0.16b, v15.16b                  // .....'...........*.......................
        // aesr    v0.16b, v4.16b                   // .....'.............*.....................
        // aesr    v0.16b, v5.16b                   // .....'...............*...................
        // aesr    v0.16b, v18.16b                  // .....'.................*.................
        // aesr    v0.16b, v19.16b                  // .....'...................*...............
        // aesr    v0.16b, v20.16b                  // .....'.....................*.............
        // aesr    v0.16b, v21.16b                  // .....'.......................*...........
        // aesr    v0.16b, v22.16b                  // .....'.........................*.........
        // aese  v0.16b,v23.16b                     // .....'...........................*.......
        // eor  v0.16b,v0.16b,v7.16b                // .....'.............................*.....
        // eor  v0.16b,v0.16b,v6.16b                // .....'...............................*...
        // extr  x22, x10, x10, #32                 // .....*...................................
        // extr  x10, x10,  x9, #63                 // .....*...................................
        // and   w11, w19, w22, asr#31              // .....'*..................................
        // eor   x9,  x11,  x9, lsl#1               // .....'.*.................................
        // fmov  d6,  x9                            // .....'...............................*...
        // fmov  v6.d[1], x10                       // ..~..'..................................*
        // str q0, [x1], #0x10                      // .~...'.................................*.

        subs x2, x2, #0x10
        b.hs Loop1x_xts_enc
Loop1x_xts_enc_postamble:// end of loop kernel
        eor v9.16B, v9.16B, v6.16B// before encryption, xor with iv
        extr x13, x10, x10, #32
        extr x10, x10, x9, #63
        and w13, w19, w13, asr #31
        aesr v9.16b, v16.16b
        eor x9, x13, x9, lsl #1
        aesr v9.16b, v17.16b
        aesr v9.16b, v12.16b
        aesr v9.16b, v13.16b
        aesr v9.16b, v14.16b
        aesr v9.16b, v15.16b
        aesr v9.16b, v4.16b
        aesr v9.16b, v5.16b
        aesr v9.16b, v18.16b
        aesr v9.16b, v19.16b
        aesr v9.16b, v20.16b
        aesr v9.16b, v21.16b
        aesr v9.16b, v22.16b
        aese v9.16b, v23.16b
        eor v9.16B, v9.16B, v7.16B
        eor v3.16B, v9.16B, v6.16B
        fmov d6, x9
        str q3, [x1], #0x10
        fmov v6.d[1], x10
        b Loop1x_xts_enc_end
Loop1x_xts_enc_end:

.align  5
Lxts_enc_done:
        // Process the tail block with cipher stealing.
        tst  x21,#0xf
        b.eq  Lxts_abort

        mov  x20,x0
        mov  x13,x1
        sub  x1,x1,#16
.composite_enc_loop:
        subs  x21,x21,#1
        ldrb  w15,[x1,x21]
        ldrb  w14,[x20,x21]
        strb  w15,[x13,x21]
        strb  w14,[x1,x21]
        b.gt  .composite_enc_loop
Lxts_enc_load_done:
        ld1  {v26.16b},[x1]
        eor  v26.16b,v26.16b,v6.16b

        // Encrypt the composite block to get the last second encrypted text block
        ldr  w6,[x3,#240]        // load key schedule...
        ld1  {v0.16b},[x3],#16
        sub  w6,w6,#2
        ld1  {v1.16b},[x3],#16     // load key schedule...
Loop_final_enc:
        aesr    v26.16b, v0.16b
        ld1  {v0.4s},[x3],#16
        subs  w6,w6,#2
        aesr    v26.16b, v1.16b
        ld1  {v1.4s},[x3],#16
        b.gt  Loop_final_enc

        aesr    v26.16b, v0.16b
        ld1  {v0.4s},[x3]
        aese  v26.16b,v1.16b
        eor  v26.16b,v26.16b,v0.16b
        eor  v26.16b,v26.16b,v6.16b
        st1  {v26.16b},[x1]

Lxts_abort:
        restore_regs

Lxts_enc_final_abort:
        restore_vregs
        add sp, sp, #STACK_SIZE_VREGS
        ret

#endif
#endif  // !OPENSSL_NO_ASM && defined(__AARCH64EL__) && defined(__APPLE__)
#if defined(__ELF__)
// See https: // www.airs.com/blog/archives/518.
.section .note.GNU-stack,"",%progbits
#endif
