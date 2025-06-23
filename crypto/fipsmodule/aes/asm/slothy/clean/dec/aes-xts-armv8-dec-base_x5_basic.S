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
.globl    aes_hw_slothy_xts_decrypt
.hidden    aes_hw_slothy_xts_decrypt
.type    aes_hw_slothy_xts_decrypt,%function
#elif defined(__APPLE__)
#if defined(BORINGSSL_PREFIX)
#include <boringssl_prefix_symbols_asm.h>
#endif
#include <openssl/arm_arch.h>
.text
.globl    _aes_hw_slothy_xts_decrypt
.private_extern    _aes_hw_slothy_xts_decrypt
#else
#error Unknown configuration
#endif

#if __ARM_MAX_ARCH__ >= 8

.align    5

#define STACK_BASE_VREGS 0
#define STACK_SIZE_VREGS (4*16)

.macro save_vregs
        stp    d8,d9,[sp,#(STACK_BASE_VREGS + 16*0)]
        stp    d10,d11,[sp,#(STACK_BASE_VREGS + 16*1)]
.endm

.macro save_regs
        stp    x19,x20,[sp,#(STACK_BASE_VREGS + 16*2)]
        stp    x21,x22,[sp,#(STACK_BASE_VREGS + 16*3)]
.endm

.macro restore_vregs
        ldp    d8,d9,[sp,#(STACK_BASE_VREGS + 16*0)]
        ldp    d10,d11,[sp,#(STACK_BASE_VREGS + 16*1)]
.endm

.macro restore_regs
        ldp    x19,x20,[sp,#(STACK_BASE_VREGS + 16*2)]
        ldp    x21,x22,[sp,#(STACK_BASE_VREGS + 16*3)]
.endm

// A single AES round
// Prevent SLOTHY from unfolding because uArchs tend to fuse AESMC+AESE
.macro aesr data, key // @slothy:no-unfold
        aese  \data, \key
        aesmc \data, \data
.endm

// A single AESD round
// Prevent SLOTHY from unfolding because uArchs tend to fuse AESIMC+AESD
.macro aesdr data, key // @slothy:no-unfold
        aesd  \data, \key
        aesimc \data, \data
.endm

.macro tweak lo, hi
        extr  x22, x10, x10, #32
        extr  x10, x10,  x9, #63
        and   w11, w19, w22, asr#31
        eor   x9,  x11,  x9, lsl#1
        fmov  \lo,  x9
        fmov  \hi, x10
.endm

_aes_hw_slothy_xts_decrypt:
aes_hw_slothy_xts_decrypt:
        // AARCH64_VALID_CALL_TARGET
        sub sp, sp, #STACK_SIZE_VREGS
        save_vregs
        save_regs

        cmp    x2,#16
        // Original input data size bigger than 16, jump to big size processing.
        b.lt    Lxts_dec_abort

.align 5
Lxts_dec_big_size:  // decrypt input size >= 16 bytes
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
        // add x7, x3, #32

// decryption
Lxts_dec:
        tst x21,#0xf
        b.eq Lxts_dec_begin
        subs x2,x2,#16
        cmp x2, #0
        b.lt Lxts_dec_done   // There is one block and a tail, go directy to cipher-stealing

Lxts_dec_begin:
        ld1 {v0.16b}, [x0], #16              // the first block
        cmp x2, #16
        orr  v29.16b,v0.16b,v0.16b
        b.lo Lxts_dec_tail1x   // when input = 1 with another block and a tail

        ld1  {v1.16b},[x0],#16  // the second block
        subs  x2,x2,#32           // bias
        orr  v28.16b,v0.16b,v0.16b
        orr  v29.16b,v1.16b,v1.16b
        b.lo  Lxts_dec_tail2x    // when input size  = 2 with another block and a tail

        // The iv for third block
        tweak d9,v9.d[1]

        orr  v27.16b,v0.16b,v0.16b
        orr  v28.16b,v1.16b,v1.16b
        ld1  {v24.16b},[x0],#16 // the third block
        orr  v29.16b,v24.16b,v24.16b
        cmp  x2,#16
        b.lo  Lxts_dec_tail3x // when input size  = 3 with another block and a tail

        // The iv for fourth block
        tweak d10,v10.d[1]

        orr  v3.16b,v0.16b,v0.16b
        orr  v27.16b,v1.16b,v1.16b
        orr  v28.16b,v24.16b,v24.16b
        ld1  {v25.16b},[x0],#16  // the fourth block
        orr  v29.16b,v25.16b,v25.16b
        subs x2,x2,#32
        b.lo  Lxts_dec_tail4x // when input size  = 4 with another block and a tail

        // The iv for fifth block
        tweak d11,v11.d[1]

        ld1  {v26.16b},[x0],#16    // the fifth block
        eor  v0.16b,v0.16b,v6.16b          // before decryption, xor with iv
        eor  v1.16b,v1.16b,v8.16b
        eor  v24.16b,v24.16b,v9.16b
        eor  v25.16b,v25.16b,v10.16b
        eor  v26.16b,v26.16b,v11.16b

.align  4
Loop5x_xts_dec:
        aesdr    v0.16b, v16.16b
        aesdr    v1.16b, v16.16b
        aesdr    v24.16b, v16.16b
        aesdr    v25.16b, v16.16b
        aesdr    v26.16b, v16.16b
        subs  x12,x2,#0x50         // because Lxts_dec_tail4x

        aesdr    v0.16b, v17.16b
        aesdr    v1.16b, v17.16b
        aesdr    v24.16b, v17.16b
        aesdr    v25.16b, v17.16b
        aesdr    v26.16b, v17.16b
        csel  x6,xzr,x12,gt    // borrow x6, w6, "gt" is not typo

        aesdr    v0.16b, v12.16b
        aesdr    v1.16b, v12.16b
        aesdr    v24.16b, v12.16b
        aesdr    v25.16b, v12.16b
        aesdr    v26.16b, v12.16b

        aesdr    v0.16b, v13.16b
        aesdr    v1.16b, v13.16b
        aesdr    v24.16b, v13.16b
        aesdr    v25.16b, v13.16b
        aesdr    v26.16b, v13.16b

        aesdr    v0.16b, v14.16b
        aesdr    v1.16b, v14.16b
        aesdr    v24.16b, v14.16b
        aesdr    v25.16b, v14.16b
        aesdr    v26.16b, v14.16b

        aesdr    v0.16b, v15.16b
        aesdr    v1.16b, v15.16b
        aesdr    v24.16b, v15.16b
        aesdr    v25.16b, v15.16b
        aesdr    v26.16b, v15.16b

        aesdr    v0.16b, v4.16b
        aesdr    v1.16b, v4.16b
        aesdr    v24.16b, v4.16b
        aesdr    v25.16b, v4.16b
        aesdr    v26.16b, v4.16b

        aesdr    v0.16b, v5.16b
        aesdr    v1.16b, v5.16b
        aesdr    v24.16b, v5.16b
        aesdr    v25.16b, v5.16b
        aesdr    v26.16b, v5.16b

        aesdr    v0.16b, v18.16b
        aesdr    v1.16b, v18.16b
        aesdr    v24.16b, v18.16b
        aesdr    v25.16b, v18.16b
        aesdr    v26.16b, v18.16b
        add  x0,x0,x6  // x0 is adjusted in such way that
                       // at exit from the loop v1.16b-v26.16b
                       // are loaded with last "words"

        aesdr    v0.16b, v19.16b
        aesdr    v1.16b, v19.16b
        aesdr    v24.16b, v19.16b
        aesdr    v25.16b, v19.16b
        aesdr    v26.16b, v19.16b

        aesdr    v0.16b, v20.16b
        aesdr    v1.16b, v20.16b
        aesdr    v24.16b, v20.16b
        aesdr    v25.16b, v20.16b
        aesdr    v26.16b, v20.16b

        aesdr    v0.16b, v21.16b
        aesdr    v1.16b, v21.16b
        aesdr    v24.16b, v21.16b
        aesdr    v25.16b, v21.16b
        aesdr    v26.16b, v21.16b

        aesdr    v0.16b, v22.16b
        aesdr    v1.16b, v22.16b
        aesdr    v24.16b, v22.16b
        aesdr    v25.16b, v22.16b
        aesdr    v26.16b, v22.16b

        aesd  v0.16b,v23.16b
        aesd  v1.16b,v23.16b
        aesd  v24.16b,v23.16b
        aesd  v25.16b,v23.16b
        aesd  v26.16b,v23.16b

        eor  v0.16b,v0.16b,v7.16b
        eor  v0.16b,v0.16b,v6.16b
        // The iv for first block of one iteration
        tweak d6,v6.d[1]
        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v8.16b
        ldp q2, q3, [x0], #0x50

        // The iv for second block
        tweak d8,v8.d[1]
        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v9.16b

        // The iv for third block
        tweak d9,v9.d[1]
        eor  v25.16b,v25.16b,v7.16b
        eor  v25.16b,v25.16b,v10.16b
        ldr q27, [x0, #-0x30]

        // The iv for fourth block
        tweak d10,v10.d[1]
        eor  v26.16b,v26.16b,v7.16b
        eor  v26.16b,v26.16b,v11.16b
        ldp  q28, q29,[x0, #-0x20]

        // The iv for fifth block
        tweak d11,v11.d[1]

        stp q0, q1, [x1], #0x50
        stp q24, q25, [x1, #-0x30]
        str  q26, [x1, #-0x10]
        eor  v0.16b,v2.16b,v6.16b
        eor  v1.16b,v3.16b,v8.16b
        eor  v24.16b,v27.16b,v9.16b
        eor  v25.16b,v28.16b,v10.16b
        eor  v26.16b,v29.16b,v11.16b

        subs x2,x2,#0x50
        b.hs  Loop5x_xts_dec

Loop5x_dec_after:
        cmn  x2,#0x10
        b.eq  Lxts_dec_tail4x  // 4 blocks left + 1block and a tail

        add  x2,x2,#0x50
        cbz  x2,Lxts_dec_done     // no blocks left + 1block and a tail

        subs  x2,x2,#0x20
        b.lo  Lxts_dec_tail1x    // 1 block left + 1block and a tail

        subs x2,x2,#0x10
        b.lo Lxts_dec_tail2x  // 2 blocks left + 1block and a tail

        b  Lxts_dec_tail3x  // 3 blocks left + 1block and a tail

.align  4
Lxts_dec_tail4x:
        eor  v1.16b,v6.16b,v3.16b
        eor  v24.16b,v27.16b,v8.16b
        eor  v25.16b,v28.16b,v9.16b
        eor  v26.16b,v29.16b,v10.16b

        aesdr    v1.16b, v16.16b
        aesdr    v24.16b, v16.16b
        aesdr    v25.16b, v16.16b
        aesdr    v26.16b, v16.16b

        aesdr    v1.16b, v17.16b
        aesdr    v24.16b, v17.16b
        aesdr    v25.16b, v17.16b
        aesdr    v26.16b, v17.16b

        aesdr    v1.16b, v12.16b
        aesdr    v24.16b, v12.16b
        aesdr    v25.16b, v12.16b
        aesdr    v26.16b, v12.16b

        aesdr    v1.16b, v13.16b
        aesdr    v24.16b, v13.16b
        aesdr    v25.16b, v13.16b
        aesdr    v26.16b, v13.16b

        aesdr    v1.16b, v14.16b
        aesdr    v24.16b, v14.16b
        aesdr    v25.16b, v14.16b
        aesdr    v26.16b, v14.16b

        aesdr    v1.16b, v15.16b
        aesdr    v24.16b, v15.16b
        aesdr    v25.16b, v15.16b
        aesdr    v26.16b, v15.16b

        aesdr    v1.16b, v4.16b
        aesdr    v24.16b, v4.16b
        aesdr    v25.16b, v4.16b
        aesdr    v26.16b, v4.16b

        aesdr    v1.16b, v5.16b
        aesdr    v24.16b, v5.16b
        aesdr    v25.16b, v5.16b
        aesdr    v26.16b, v5.16b

        aesdr    v1.16b, v18.16b
        aesdr    v24.16b, v18.16b
        aesdr    v25.16b, v18.16b
        aesdr    v26.16b, v18.16b

        aesdr    v1.16b, v19.16b
        aesdr    v24.16b, v19.16b
        aesdr    v25.16b, v19.16b
        aesdr    v26.16b, v19.16b

        aesdr    v1.16b, v20.16b
        aesdr    v24.16b, v20.16b
        aesdr    v25.16b, v20.16b
        aesdr    v26.16b, v20.16b

        aesdr    v1.16b, v21.16b
        aesdr    v24.16b, v21.16b
        aesdr    v25.16b, v21.16b
        aesdr    v26.16b, v21.16b

        aesdr    v1.16b, v22.16b
        aesdr    v24.16b, v22.16b
        aesdr    v25.16b, v22.16b
        aesdr    v26.16b, v22.16b

        aesd  v1.16b,v23.16b
        aesd  v24.16b,v23.16b
        aesd  v25.16b,v23.16b
        aesd  v26.16b,v23.16b

        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v6.16b

        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v8.16b

        eor  v25.16b,v25.16b,v7.16b
        eor  v25.16b,v25.16b,v9.16b

        eor  v26.16b,v26.16b,v7.16b
        eor  v26.16b,v26.16b,v10.16b
        // The iv for tail
        fmov  x9,d10
        fmov  x10,v10.d[1]
        tweak d6,v6.d[1]

        st1  {v1.16b},[x1],#16
        st1  {v24.16b,v25.16b},[x1],#32
        st1  {v26.16b},[x1],#16
        b  Lxts_dec_done

.align  4
Lxts_dec_tail3x:
        eor  v0.16b,v6.16b,v27.16b         // 3 blocks left
        eor  v1.16b,v8.16b,v28.16b
        eor  v24.16b,v29.16b,v9.16b

        // First round with v16
        aesdr    v0.16b, v16.16b
        aesdr    v1.16b, v16.16b
        aesdr    v24.16b, v16.16b

        // Second round with v17
        aesdr    v0.16b, v17.16b
        aesdr    v1.16b, v17.16b
        aesdr    v24.16b, v17.16b

        // Third round with v12
        aesdr    v0.16b, v12.16b
        aesdr    v1.16b, v12.16b
        aesdr    v24.16b, v12.16b

        // Fourth round with v13
        aesdr    v0.16b, v13.16b
        aesdr    v1.16b, v13.16b
        aesdr    v24.16b, v13.16b

        // Fifth round with v14
        aesdr    v0.16b, v14.16b
        aesdr    v1.16b, v14.16b
        aesdr    v24.16b, v14.16b

        // Sixth round with v15
        aesdr    v0.16b, v15.16b
        aesdr    v1.16b, v15.16b
        aesdr    v24.16b, v15.16b

        // Seventh round with v4
        aesdr    v0.16b, v4.16b
        aesdr    v1.16b, v4.16b
        aesdr    v24.16b, v4.16b

        // Eighth round with v5
        aesdr    v0.16b, v5.16b
        aesdr    v1.16b, v5.16b
        aesdr    v24.16b, v5.16b

        // 9th round with v18
        aesdr    v0.16b, v18.16b
        aesdr    v1.16b, v18.16b
        aesdr    v24.16b, v18.16b

        // 10th round with v19
        aesdr    v0.16b, v19.16b
        aesdr    v1.16b, v19.16b
        aesdr    v24.16b, v19.16b

        aesdr    v0.16b, v20.16b
        aesdr    v1.16b, v20.16b
        aesdr    v24.16b, v20.16b

        aesdr    v0.16b, v21.16b
        aesdr    v1.16b, v21.16b
        aesdr    v24.16b, v21.16b

        aesdr    v0.16b, v22.16b
        aesdr    v1.16b, v22.16b
        aesdr    v24.16b, v22.16b

        aesd  v0.16b,v23.16b
        aesd  v1.16b,v23.16b
        aesd  v24.16b,v23.16b

        eor  v0.16b,v0.16b,v7.16b
        eor  v0.16b,v0.16b,v6.16b
        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v8.16b
        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v9.16b

        // The iv for tail
        fmov  x9,d9
        fmov  x10,v9.d[1]
        tweak d6,v6.d[1]

        st1  {v0.16b,v1.16b},[x1],#32
        st1  {v24.16b},[x1],#16
        b Lxts_dec_done  // done processing three blocks

Lxts_dec_tail2x:
        eor  v1.16b,v28.16b,v6.16b
        eor  v24.16b,v29.16b,v8.16b

        // First round with v16
        aesdr    v1.16b, v16.16b
        aesdr    v24.16b, v16.16b

        // Second round with v17
        aesdr    v1.16b, v17.16b
        aesdr    v24.16b, v17.16b

        // Third round with v12
        aesdr    v1.16b, v12.16b
        aesdr    v24.16b, v12.16b

        // Fourth round with v13
        aesdr    v1.16b, v13.16b
        aesdr    v24.16b, v13.16b

        // Fifth round with v14
        aesdr    v1.16b, v14.16b
        aesdr    v24.16b, v14.16b

        // Sixth round with v15
        aesdr    v1.16b, v15.16b
        aesdr    v24.16b, v15.16b

        // Seventh round with v4
        aesdr    v1.16b, v4.16b
        aesdr    v24.16b, v4.16b

        // Eighth round with v5
        aesdr    v1.16b, v5.16b
        aesdr    v24.16b, v5.16b

        // 9th round with v18
        aesdr    v1.16b, v18.16b
        aesdr    v24.16b, v18.16b

        // 10th round with v19
        aesdr    v1.16b, v19.16b
        aesdr    v24.16b, v19.16b

        aesdr    v1.16b, v20.16b
        aesdr    v24.16b, v20.16b

        aesdr    v1.16b, v21.16b
        aesdr    v24.16b, v21.16b

        aesdr    v1.16b, v22.16b
        aesdr    v24.16b, v22.16b
        aesd  v1.16b,v23.16b
        aesd  v24.16b,v23.16b

        eor  v1.16b,v1.16b,v7.16b
        eor  v1.16b,v1.16b,v6.16b
        st1  {v1.16b},[x1],#16
        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v8.16b
        st1  {v24.16b},[x1],#16

        // The iv for tail
        fmov  x9,d8
        fmov  x10,v8.d[1]
        tweak d6,v6.d[1]
        b  Lxts_dec_done

Lxts_dec_tail1x:
        eor  v24.16b,v29.16b,v6.16b

        // First round with v16
        aesdr    v24.16b, v16.16b

        // Second round with v17
        aesdr    v24.16b, v17.16b

        // Third round with v12
        aesdr    v24.16b, v12.16b

        // Fourth round with v13
        aesdr    v24.16b, v13.16b

        // Fifth round with v14
        aesdr    v24.16b, v14.16b

        // Sixth round with v15
        aesdr    v24.16b, v15.16b

        // Seventh round with v4
        aesdr    v24.16b, v4.16b

        // Eighth round with v5
        aesdr    v24.16b, v5.16b

        // 9th round with v18
        aesdr    v24.16b, v18.16b

        // 10th round with v19
        aesdr    v24.16b, v19.16b

        aesdr    v24.16b, v20.16b
        aesdr    v24.16b, v21.16b
        aesdr    v24.16b, v22.16b
        aesd  v24.16b,v23.16b

        eor  v24.16b,v24.16b,v7.16b
        eor  v24.16b,v24.16b,v6.16b
        st1  {v24.16b},[x1],#16
        // tweak for tail
        fmov  x9,d6
        fmov  x10,v6.d[1]
        tweak d6,v6.d[1]
        b  Lxts_dec_done

Lxts_dec_done:
        tst    x21,#0xf
        b.eq    Lxts_dec_abort
        // Processing the last 1 block and a tail with cipher stealing.
        // At this point, we know there is 1 block+tail
        // We need two tweaks, one is already calculated and stored in v6
        // We use it to calculate v8
        mov    x7,x3

        fmov  x9,d6
        fmov  x10,v6.d[1]
        tweak d8,v8.d[1]

        ld1    {v0.4s},[x0],#16

// Decrypt the second to last block
.Lxts_dec_1st_done:
        eor    v26.16b,v0.16b,v8.16b
        ldr    w6,[x3,#240]
        ld1    {v0.4s},[x3],#16
        sub    w6,w6,#2
        ld1    {v1.4s},[x3],#16
.Loop_final_2nd_dec:
        aesd    v26.16b,v0.16b
        aesimc    v26.16b,v26.16b
        ld1    {v0.4s},[x3],#16     // load key schedule...
        subs    w6,w6,#2
        aesd    v26.16b,v1.16b
        aesimc    v26.16b,v26.16b
        ld1    {v1.4s},[x3],#16     // load key schedule...
        b.gt    .Loop_final_2nd_dec

        aesd    v26.16b,v0.16b
        aesimc    v26.16b,v26.16b
        ld1    {v0.4s},[x3]
        aesd    v26.16b,v1.16b
        eor    v26.16b,v26.16b,v0.16b
        eor    v26.16b,v26.16b,v8.16b
        st1    {v26.16b},[x1]

        mov    x20,x0
        add    x13,x1,#16

        // Composite the tailcnt "16 byte not aligned block" into the last second plain blocks
        // to get the last encrypted block.
.composite_dec_loop:
        subs    x21,x21,#1
        ldrb    w15,[x1,x21]
        ldrb    w14,[x20,x21]
        strb    w15,[x13,x21]
        strb    w14,[x1,x21]
        b.gt    .composite_dec_loop
.Lxts_dec_load_done:
        ld1    {v26.16b},[x1]
        eor    v26.16b,v26.16b,v6.16b

        // Decrypt the composite block to get the last second plain text block
        ldr    w6,[x7,#240]
        ld1    {v0.16b},[x7],#16
        sub    w6,w6,#2
        ld1    {v1.16b},[x7],#16
.Loop_final_dec:
        aesd    v26.16b,v0.16b
        aesimc    v26.16b,v26.16b
        ld1    {v0.4s},[x7],#16     // load key schedule...
        subs    w6,w6,#2
        aesd    v26.16b,v1.16b
        aesimc    v26.16b,v26.16b
        ld1    {v1.4s},[x7],#16     // load key schedule...
        b.gt    .Loop_final_dec

        aesd    v26.16b,v0.16b
        aesimc    v26.16b,v26.16b
        ld1    {v0.4s},[x7]
        aesd    v26.16b,v1.16b
        eor    v26.16b,v26.16b,v0.16b
        eor    v26.16b,v26.16b,v6.16b
        st1    {v26.16b},[x1]

Lxts_dec_abort:
        restore_vregs
        restore_regs
        add sp, sp, #STACK_SIZE_VREGS
        ret

#endif
#endif  // !OPENSSL_NO_ASM && defined(__AARCH64EL__) && defined(__APPLE__)
#if defined(__ELF__)
// See https://www.airs.com/blog/archives/518.
.section .note.GNU-stack,"",%progbits
#endif
