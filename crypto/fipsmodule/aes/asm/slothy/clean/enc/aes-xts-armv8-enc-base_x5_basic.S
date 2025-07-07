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
        // subs x2, x2, #16

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

        // The iv for second block
        // x9- iv(low), x10 - iv(high)
        // the five ivs stored into, v6.16b,v8.16b,v9.16b,v10.16b,v11.16b
        fmov  x9, d6
        fmov  x10, v6.d[1]
        mov   w19, #0x87
        tweak d8, v8.d[1]

        mov x7, x3
        ld1 {v16.4s,v17.4s},[x7], #32         // load key schedule
        ld1 {v12.4s,v13.4s},[x7], #32
        ld1 {v14.4s,v15.4s},[x7], #32
        ld1 {v4.4s,v5.4s},  [x7], #32
        ld1 {v18.4s,v19.4s},[x7], #32
        ld1 {v20.4s,v21.4s},[x7], #32
        ld1 {v22.4s,v23.4s},[x7], #32
        ld1 {v7.4s},        [x7]

// Encryption
Lxts_enc:
        cmp x2,#32
        b.lo Lxts_enc_tail1x   // when input = 1 with tail

        cmp x2,#48
        b.lo  Lxts_enc_tail2x    // when input size  = 2

        // The iv for third block
        tweak d9,v9.d[1]

        cmp x2,#64
        b.lo  Lxts_enc_tail3x

        // The iv for fourth block
        tweak d10,v10.d[1]

        cmp x2,#80
        b.lo  Lxts_enc_tail4x

        // The iv for fifth block
        tweak d11,v11.d[1]

.align  4
Loop5x_xts_enc:
        ldp q0, q1, [x0], #0x50
        ldp q24, q25, [x0, #-0x30]
        ldr q26, [x0, #-0x10]

        eor  v0.16b,v0.16b,v6.16b          // before encryption, xor with iv
        eor  v1.16b,v1.16b,v8.16b
        eor  v24.16b,v24.16b,v9.16b
        eor  v25.16b,v25.16b,v10.16b
        eor  v26.16b,v26.16b,v11.16b

        aesr    v0.16b, v16.16b
        aesr    v1.16b, v16.16b
        aesr    v24.16b, v16.16b
        aesr    v25.16b, v16.16b
        aesr    v26.16b, v16.16b

        aesr    v0.16b, v17.16b
        aesr    v1.16b, v17.16b
        aesr    v24.16b, v17.16b
        aesr    v25.16b, v17.16b
        aesr    v26.16b, v17.16b

        aesr    v0.16b, v12.16b
        aesr    v1.16b, v12.16b
        aesr    v24.16b, v12.16b
        aesr    v25.16b, v12.16b
        aesr    v26.16b, v12.16b

        aesr    v0.16b, v13.16b
        aesr    v1.16b, v13.16b
        aesr    v24.16b, v13.16b
        aesr    v25.16b, v13.16b
        aesr    v26.16b, v13.16b

        aesr    v0.16b, v14.16b
        aesr    v1.16b, v14.16b
        aesr    v24.16b, v14.16b
        aesr    v25.16b, v14.16b
        aesr    v26.16b, v14.16b

        aesr    v0.16b, v15.16b
        aesr    v1.16b, v15.16b
        aesr    v24.16b, v15.16b
        aesr    v25.16b, v15.16b
        aesr    v26.16b, v15.16b

        aesr    v0.16b, v4.16b
        aesr    v1.16b, v4.16b
        aesr    v24.16b, v4.16b
        aesr    v25.16b, v4.16b
        aesr    v26.16b, v4.16b

        aesr    v0.16b, v5.16b
        aesr    v1.16b, v5.16b
        aesr    v24.16b, v5.16b
        aesr    v25.16b, v5.16b
        aesr    v26.16b, v5.16b

        aesr    v0.16b, v18.16b
        aesr    v1.16b, v18.16b
        aesr    v24.16b, v18.16b
        aesr    v25.16b, v18.16b
        aesr    v26.16b, v18.16b

        aesr    v0.16b, v19.16b
        aesr    v1.16b, v19.16b
        aesr    v24.16b, v19.16b
        aesr    v25.16b, v19.16b
        aesr    v26.16b, v19.16b

        aesr    v0.16b, v20.16b
        aesr    v1.16b, v20.16b
        aesr    v24.16b, v20.16b
        aesr    v25.16b, v20.16b
        aesr    v26.16b, v20.16b

        aesr    v0.16b, v21.16b
        aesr    v1.16b, v21.16b
        aesr    v24.16b, v21.16b
        aesr    v25.16b, v21.16b
        aesr    v26.16b, v21.16b

        aesr    v0.16b, v22.16b
        aesr    v1.16b, v22.16b
        aesr    v24.16b, v22.16b
        aesr    v25.16b, v22.16b
        aesr    v26.16b, v22.16b

        aese  v0.16b,v23.16b
        aese  v1.16b,v23.16b
        aese  v24.16b,v23.16b
        aese  v25.16b,v23.16b
        aese  v26.16b,v23.16b

        eor  v0.16b,v0.16b,v7.16b
        eor  v0.16b,v0.16b,v6.16b
        // The iv for first block of one iteration
        tweak d6,v6.d[1]
        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v8.16b

        // The iv for second block
        tweak d8,v8.d[1]
        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v9.16b

        // The iv for third block
        tweak d9,v9.d[1]
        eor  v25.16b,v25.16b,v7.16b
        eor  v25.16b,v25.16b,v10.16b

        // The iv for fourth block
        tweak d10,v10.d[1]
        eor  v26.16b,v26.16b,v7.16b
        eor  v26.16b,v26.16b,v11.16b

        // The iv for fifth block
        tweak d11,v11.d[1]

        stp q0, q1, [x1], #0x50
        stp q24, q25, [x1, #-0x30]
        str q26, [x1, #-0x10]

        subs x2,x2,#0x50 // @slothy:core

        cmp x2,#0x50
        b.lo Loop5x_enc_after

        b.hs  Loop5x_xts_enc

Loop5x_enc_after:
        cmp x2,#0x0
        b.eq  Lxts_enc_done

        cmp x2,#0x10
        b.eq Lxts_enc_tail1x

        cmp x2,#0x20
        b.eq Lxts_enc_tail2x

        cmp x2,#0x30
        b.eq Lxts_enc_tail3x

        cmp x2,#0x40
        b.eq Lxts_enc_tail4x

.align  4
Lxts_enc_tail4x:
        ld1  {v0.16b}, [x0],#16              // the first block
        ld1  {v1.16b}, [x0],#16  // the second block
        ld1  {v24.16b},[x0],#16 // the third block
        ld1  {v25.16b},[x0],#16  // the fourth block

        eor  v0.16b,v0.16b,v6.16b
        eor  v1.16b,v1.16b,v8.16b
        eor  v24.16b,v24.16b,v9.16b
        eor  v25.16b,v25.16b,v10.16b

        aesr    v0.16b, v16.16b
        aesr    v1.16b, v16.16b
        aesr    v24.16b, v16.16b
        aesr    v25.16b, v16.16b

        aesr    v0.16b, v17.16b
        aesr    v1.16b, v17.16b
        aesr    v24.16b, v17.16b
        aesr    v25.16b, v17.16b

        aesr    v0.16b, v12.16b
        aesr    v1.16b, v12.16b
        aesr    v24.16b, v12.16b
        aesr    v25.16b, v12.16b

        aesr    v0.16b, v13.16b
        aesr    v1.16b, v13.16b
        aesr    v24.16b, v13.16b
        aesr    v25.16b, v13.16b

        aesr    v0.16b, v14.16b
        aesr    v1.16b, v14.16b
        aesr    v24.16b, v14.16b
        aesr    v25.16b, v14.16b

        aesr    v0.16b, v15.16b
        aesr    v1.16b, v15.16b
        aesr    v24.16b, v15.16b
        aesr    v25.16b, v15.16b

        aesr    v0.16b, v4.16b
        aesr    v1.16b, v4.16b
        aesr    v24.16b, v4.16b
        aesr    v25.16b, v4.16b

        aesr    v0.16b, v5.16b
        aesr    v1.16b, v5.16b
        aesr    v24.16b, v5.16b
        aesr    v25.16b, v5.16b

        aesr    v0.16b, v18.16b
        aesr    v1.16b, v18.16b
        aesr    v24.16b, v18.16b
        aesr    v25.16b, v18.16b

        aesr    v0.16b, v19.16b
        aesr    v1.16b, v19.16b
        aesr    v24.16b, v19.16b
        aesr    v25.16b, v19.16b

        aesr    v0.16b, v20.16b
        aesr    v1.16b, v20.16b
        aesr    v24.16b, v20.16b
        aesr    v25.16b, v20.16b

        aesr    v0.16b, v21.16b
        aesr    v1.16b, v21.16b
        aesr    v24.16b, v21.16b
        aesr    v25.16b, v21.16b

        aesr    v0.16b, v22.16b
        aesr    v1.16b, v22.16b
        aesr    v24.16b, v22.16b
        aesr    v25.16b, v22.16b

        aese  v0.16b,v23.16b
        aese  v1.16b,v23.16b
        aese  v24.16b,v23.16b
        aese  v25.16b,v23.16b

        eor  v0.16b,v0.16b,v7.16b
        eor  v0.16b,v0.16b,v6.16b

        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v8.16b

        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v9.16b

        eor  v25.16b,v25.16b,v7.16b
        eor  v25.16b,v25.16b,v10.16b

        st1  {v0.16b,v1.16b},[x1],#32
        st1  {v24.16b,v25.16b},[x1],#32

        // The iv for tail
        fmov  x9,d10
        fmov  x10,v10.d[1]
        tweak d6,v6.d[1]

        b  Lxts_enc_done

.align  4
Lxts_enc_tail3x:
        ld1  {v0.16b,v1.16b}, [x0],#32
        ld1  {v24.16b}, [x0],#16

        eor  v0.16b,v0.16b,v6.16b
        eor  v1.16b,v1.16b,v8.16b
        eor  v24.16b,v24.16b,v9.16b

        // First round with v16
        aesr    v0.16b, v16.16b
        aesr    v1.16b, v16.16b
        aesr    v24.16b, v16.16b

        // Second round with v17
        aesr    v0.16b, v17.16b
        aesr    v1.16b, v17.16b
        aesr    v24.16b, v17.16b

        // Third round with v12
        aesr    v0.16b, v12.16b
        aesr    v1.16b, v12.16b
        aesr    v24.16b, v12.16b

        // Fourth round with v13
        aesr    v0.16b, v13.16b
        aesr    v1.16b, v13.16b
        aesr    v24.16b, v13.16b

        // Fifth round with v14
        aesr    v0.16b, v14.16b
        aesr    v1.16b, v14.16b
        aesr    v24.16b, v14.16b

        // Sixth round with v15
        aesr    v0.16b, v15.16b
        aesr    v1.16b, v15.16b
        aesr    v24.16b, v15.16b

        // Seventh round with v4
        aesr    v0.16b, v4.16b
        aesr    v1.16b, v4.16b
        aesr    v24.16b, v4.16b

        // Eighth round with v5
        aesr    v0.16b, v5.16b
        aesr    v1.16b, v5.16b
        aesr    v24.16b, v5.16b

        // 9th round with v18
        aesr    v0.16b, v18.16b
        aesr    v1.16b, v18.16b
        aesr    v24.16b, v18.16b

        // 10th round with v19
        aesr    v0.16b, v19.16b
        aesr    v1.16b, v19.16b
        aesr    v24.16b, v19.16b

        aesr    v0.16b, v20.16b
        aesr    v1.16b, v20.16b
        aesr    v24.16b, v20.16b

        aesr    v0.16b, v21.16b
        aesr    v1.16b, v21.16b
        aesr    v24.16b, v21.16b

        aesr    v0.16b, v22.16b
        aesr    v1.16b, v22.16b
        aesr    v24.16b, v22.16b

        aese  v0.16b,v23.16b
        aese  v1.16b,v23.16b
        aese  v24.16b,v23.16b

        eor  v0.16b,v0.16b,v7.16b
        eor  v0.16b,v0.16b,v6.16b
        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v8.16b
        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v9.16b

        st1  {v0.16b,v1.16b},[x1],#32
        st1  {v24.16b},[x1],#16

        // The iv for tail
        fmov  x9,d9
        fmov  x10,v9.d[1]
        tweak d6,v6.d[1]

        b Lxts_enc_done  // done processing three blocks

Lxts_enc_tail2x:
        ld1  {v0.16b,v1.16b},[x0],#32  // the first block

        eor  v0.16b,v0.16b,v6.16b
        eor  v1.16b,v1.16b,v8.16b

        // First round with v16
        aesr    v0.16b, v16.16b
        aesr    v1.16b, v16.16b

        // Second round with v17
        aesr    v0.16b, v17.16b
        aesr    v1.16b, v17.16b

        // Third round with v12
        aesr    v0.16b, v12.16b
        aesr    v1.16b, v12.16b

        // Fourth round with v13
        aesr    v0.16b, v13.16b
        aesr    v1.16b, v13.16b

        // Fifth round with v14
        aesr    v0.16b, v14.16b
        aesr    v1.16b, v14.16b

        // Sixth round with v15
        aesr    v0.16b, v15.16b
        aesr    v1.16b, v15.16b

        // Seventh round with v4
        aesr    v0.16b, v4.16b
        aesr    v1.16b, v4.16b

        // Eighth round with v5
        aesr    v0.16b, v5.16b
        aesr    v1.16b, v5.16b

        // 9th round with v18
        aesr    v0.16b, v18.16b
        aesr    v1.16b, v18.16b

        // 10th round with v19
        aesr    v0.16b, v19.16b
        aesr    v1.16b, v19.16b

        aesr    v0.16b, v20.16b
        aesr    v1.16b, v20.16b

        aesr    v0.16b, v21.16b
        aesr    v1.16b, v21.16b

        aesr    v0.16b, v22.16b
        aesr    v1.16b, v22.16b

        aese  v0.16b,v23.16b
        aese  v1.16b,v23.16b

        eor  v0.16b,v0.16b,v7.16b
        eor  v0.16b,v0.16b,v6.16b
        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v8.16b

        st1  {v0.16b,v1.16b},[x1],#32

        // The iv for tail
        fmov  x9,d8
        fmov  x10,v8.d[1]
        tweak d6,v6.d[1]
        b  Lxts_enc_done

Lxts_enc_tail1x:
        ld1  {v0.16b}, [x0],#16  // the first block

        eor  v0.16b,v0.16b,v6.16b

        // First round with v16
        aesr    v0.16b, v16.16b

        // Second round with v17
        aesr    v0.16b, v17.16b

        // Third round with v12
        aesr    v0.16b, v12.16b

        // Fourth round with v13
        aesr    v0.16b, v13.16b

        // Fifth round with v14
        aesr    v0.16b, v14.16b

        // Sixth round with v15
        aesr    v0.16b, v15.16b

        // Seventh round with v4
        aesr    v0.16b, v4.16b

        // Eighth round with v5
        aesr    v0.16b, v5.16b

        // 9th round with v18
        aesr    v0.16b, v18.16b

        // 10th round with v19
        aesr    v0.16b, v19.16b

        aesr    v0.16b, v20.16b
        aesr    v0.16b, v21.16b
        aesr    v0.16b, v22.16b
        aese  v0.16b,v23.16b

        eor  v0.16b,v0.16b,v7.16b
        eor  v0.16b,v0.16b,v6.16b
        st1  {v0.16b},[x1],#16

        // tweak for tail
        fmov  x9,d6
        fmov  x10,v6.d[1]
        tweak d6,v6.d[1]
        b  Lxts_enc_done

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
// See https://www.airs.com/blog/archives/518.
.section .note.GNU-stack,"",%progbits
#endif
