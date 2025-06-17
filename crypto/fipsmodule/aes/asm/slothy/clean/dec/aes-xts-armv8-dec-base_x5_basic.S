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
.globl	aes_hw_slothy_xts_decrypt
.hidden	aes_hw_slothy_xts_decrypt
.type	aes_hw_slothy_xts_decrypt,%function
#elif defined(__APPLE__)
#if defined(BORINGSSL_PREFIX)
#include <boringssl_prefix_symbols_asm.h>
#endif
#include <openssl/arm_arch.h>
.text
.globl	_aes_hw_slothy_xts_decrypt
.private_extern	_aes_hw_slothy_xts_decrypt
#else
#error Unknown configuration
#endif

#if __ARM_MAX_ARCH__ >= 8

.align	5

#define STACK_BASE_VREGS 0
#define STACK_SIZE_VREGS (4*16)

.macro save_vregs
    stp	d8,d9,[sp,#(STACK_BASE_VREGS + 16*0)]
	stp	d10,d11,[sp,#(STACK_BASE_VREGS + 16*1)]
.endm

.macro save_regs
    stp	x19,x20,[sp,#(STACK_BASE_VREGS + 16*2)]
	stp	x21,x22,[sp,#(STACK_BASE_VREGS + 16*3)]
.endm

.macro restore_vregs
	ldp	d8,d9,[sp,#(STACK_BASE_VREGS + 16*0)]
	ldp	d10,d11,[sp,#(STACK_BASE_VREGS + 16*1)]
.endm

.macro restore_regs
    ldp	x19,x20,[sp,#(STACK_BASE_VREGS + 16*2)]
    ldp	x21,x22,[sp,#(STACK_BASE_VREGS + 16*3)]
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

_aes_hw_slothy_xts_decrypt:
aes_hw_slothy_xts_decrypt:
	// AARCH64_VALID_CALL_TARGET
    sub sp, sp, #STACK_SIZE_VREGS
    save_vregs
	save_regs

	cmp	x2,#16
    // Original input data size bigger than 16, jump to big size processing.
	b.ne	.Lxts_dec_big_size
    // Encrypt the iv with key2, as the first XEX iv.
	ldr	w6,[x4,#240]
	ld1	{v0.16b},[x4],#16
	ld1	{v6.16b},[x5]
	sub	w6,w6,#2
	ld1	{v1.16b},[x4],#16

.Loop_dec_small_iv_enc:
	aesr	v6.16b,v0.16b
	ld1	{v0.4s},[x4],#16
	subs	w6,w6,#2
	aesr	v6.16b,v1.16b
	ld1	{v1.4s},[x4],#16
	b.gt	.Loop_dec_small_iv_enc

	aesr	v6.16b,v0.16b
	ld1	{v0.4s},[x4]
	aese	v6.16b,v1.16b
	eor	v6.16b,v6.16b,v0.16b

	ld1	{v0.16b},[x0]
	eor	v0.16b,v6.16b,v0.16b

	ldr	w6,[x3,#240]
	ld1	{v28.4s,v29.4s},[x3],#32       // load key schedule...

	aesdr	v0.16b,v28.16b
	ld1	{v16.4s,v17.4s},[x3],#32         // load key schedule...
	aesdr	v0.16b,v29.16b
	subs	w6,w6,#10         // bias
	// b.eq	.Lxts_128_dec
.Lxts_dec_round_loop:
	aesdr	v0.16b,v16.16b
	ld1	{v16.4s},[x3],#16            // load key schedule...
	aesdr	v0.16b,v17.16b
	ld1	{v17.4s},[x3],#16            // load key schedule...
	subs	w6,w6,#2          // bias
	b.gt	.Lxts_dec_round_loop
//.Lxts_128_dec:
	ld1	{v18.4s,v19.4s},[x3],#32       // load key schedule...
	aesdr	v0.16b,v16.16b
	aesdr	v0.16b,v17.16b
	ld1	{v20.4s,v21.4s},[x3],#32       // load key schedule...
	aesdr	v0.16b,v18.16b
	aesdr	v0.16b,v19.16b
	ld1	{v22.4s,v23.4s},[x3],#32       // load key schedule...
	aesdr	v0.16b,v20.16b
	aesdr	v0.16b,v21.16b
	ld1	{v7.4s},[x3]
	aesdr	v0.16b,v22.16b
	aesd	v0.16b,v23.16b
	eor	v0.16b,v0.16b,v7.16b
	eor	v0.16b,v6.16b,v0.16b
	st1	{v0.16b},[x1]
	b	.Lxts_dec_abort
.Lxts_dec_big_size:

	and	x21,x2,#0xf
	and	x2,x2,#-16
	subs	x2,x2,#16
	mov	x8,#16
	b.lo	.Lxts_dec_abort

    // Encrypt the iv with key2, as the first XEX iv
	ldr	w6,[x4,#240]
	ld1	{v0.16b},[x4],#16
	ld1	{v6.16b},[x5]
	sub	w6,w6,#2
	ld1	{v1.16b},[x4],#16

.Loop_dec_iv_enc:
	aesr	v6.16b,v0.16b
	ld1	{v0.4s},[x4],#16
	subs	w6,w6,#2
	aesr	v6.16b,v1.16b
	ld1	{v1.4s},[x4],#16
	b.gt	.Loop_dec_iv_enc

	aesr	v6.16b,v0.16b
	ld1	{v0.4s},[x4]
	aese	v6.16b,v1.16b
	eor	v6.16b,v6.16b,v0.16b

    // The iv for second block
    // x9- iv(low), x10 - iv(high)
    // the five ivs stored into, v6.16b,v8.16b,v9.16b,v10.16b,v11.16b
	fmov	x9,d6
	fmov	x10,v6.d[1]
	mov	w19,#0x87
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d8,x9
	fmov	v8.d[1],x10

	ldr	w5,[x3,#240]       // load rounds number

    // The iv for third block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d9,x9
	fmov	v9.d[1],x10

	ld1	{v16.4s,v17.4s},[x3]         // load key schedule...
	sub	w5,w5,#6
	add	x7,x3,x5,lsl#4  // pointer to last 7 round keys
	sub	w5,w5,#2
	ld1	{v18.4s,v19.4s},[x7],#32   // load key schedule...
	ld1	{v20.4s,v21.4s},[x7],#32
	ld1	{v22.4s,v23.4s},[x7],#32
	ld1	{v7.4s},[x7]

    // The iv for fourth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d10,x9
	fmov	v10.d[1],x10

	add	x7,x3,#32
	mov	w6,w5
	b	.Lxts_dec

    // Decryption
.align	5
.Lxts_dec:
	tst	x21,#0xf
	b.eq	.Lxts_dec_begin
	subs	x2,x2,#16
	csel	x8,xzr,x8,eq
	ld1	{v0.16b},[x0],#16
	b.lo	.Lxts_done
	sub	x0,x0,#16
.Lxts_dec_begin:
	ld1	{v0.16b},[x0],x8
	subs	x2,x2,#32           // bias
	add	w6,w5,#2
	orr	v3.16b,v0.16b,v0.16b
	orr	v1.16b,v0.16b,v0.16b
	orr	v28.16b,v0.16b,v0.16b
	ld1	{v24.16b},[x0],#16
	orr	v27.16b,v24.16b,v24.16b
	orr	v29.16b,v24.16b,v24.16b
	b.lo	.Lxts_inner_dec_tail
	eor	v0.16b,v0.16b,v6.16b          // before decryt, xor with iv
	eor	v24.16b,v24.16b,v8.16b

	orr	v1.16b,v24.16b,v24.16b
	ld1	{v24.16b},[x0],#16
	orr	v2.16b,v0.16b,v0.16b
	orr	v3.16b,v1.16b,v1.16b
	eor	v27.16b,v24.16b,v9.16b         // third block xox with third iv
	eor	v24.16b,v24.16b,v9.16b
	cmp	x2,#32
	b.lo	.Lxts_outer_dec_tail

	ld1	{v25.16b},[x0],#16

    // The iv for fifth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d11,x9
	fmov	v11.d[1],x10

	ld1	{v26.16b},[x0],#16
	eor	v25.16b,v25.16b,v10.16b        // the fourth block
	eor	v26.16b,v26.16b,v11.16b
	sub	x2,x2,#32           // bias
	mov	w6,w5
	b	.Loop5x_xts_dec

.align	4
.Loop5x_xts_dec:
	aesdr	v0.16b,v16.16b
	aesdr	v1.16b,v16.16b
	aesdr	v24.16b,v16.16b
	aesdr	v25.16b,v16.16b
	aesdr	v26.16b,v16.16b
	ld1	{v16.4s},[x7],#16        // load key schedule...
	subs	w6,w6,#2
	aesdr	v0.16b,v17.16b
	aesdr	v1.16b,v17.16b
	aesdr	v24.16b,v17.16b
	aesdr	v25.16b,v17.16b
	aesdr	v26.16b,v17.16b
	ld1	{v17.4s},[x7],#16        // load key schedule...
	b.gt	.Loop5x_xts_dec

	aesdr	v0.16b,v16.16b
	aesdr	v1.16b,v16.16b
	aesdr	v24.16b,v16.16b
	aesdr	v25.16b,v16.16b
	aesdr	v26.16b,v16.16b
	subs	x2,x2,#0x50         // because .Lxts_dec_tail4x

	aesdr	v0.16b,v17.16b
	aesdr	v1.16b,v17.16b
	aesdr	v24.16b,v17.16b
	aesdr	v25.16b,v17.16b
	aesdr	v26.16b,v17.16b
	csel	x6,xzr,x2,gt    // borrow x6, w6, "gt" is not typo
	mov	x7,x3

	aesdr	v0.16b,v18.16b
	aesdr	v1.16b,v18.16b
	aesdr	v24.16b,v18.16b
	aesdr	v25.16b,v18.16b
	aesdr	v26.16b,v18.16b
	add	x0,x0,x6  // x0 is adjusted in such way that
                                // at exit from the loop v1.16b-v26.16b
                                // are loaded with last "words"
	add	x6,x2,#0x60         // because .Lxts_dec_tail4x

	aesdr	v0.16b,v19.16b
	aesdr	v1.16b,v19.16b
	aesdr	v24.16b,v19.16b
	aesdr	v25.16b,v19.16b
	aesdr	v26.16b,v19.16b

	aesdr	v0.16b,v20.16b
	aesdr	v1.16b,v20.16b
	aesdr	v24.16b,v20.16b
	aesdr	v25.16b,v20.16b
	aesdr	v26.16b,v20.16b

	aesdr	v0.16b,v21.16b
	aesdr	v1.16b,v21.16b
	aesdr	v24.16b,v21.16b
	aesdr	v25.16b,v21.16b
	aesdr	v26.16b,v21.16b

	aesdr	v0.16b,v22.16b
	aesdr	v1.16b,v22.16b
	aesdr	v24.16b,v22.16b
	aesdr	v25.16b,v22.16b
	aesdr	v26.16b,v22.16b

	eor	v4.16b,v7.16b,v6.16b
	aesd	v0.16b,v23.16b
    // The iv for first block of next iteration.
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d6,x9
	fmov	v6.d[1],x10
	eor	v5.16b,v7.16b,v8.16b
	ld1	{v2.16b},[x0],#16
	aesd	v1.16b,v23.16b
    // The iv for second block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d8,x9
	fmov	v8.d[1],x10
	eor	v17.16b,v7.16b,v9.16b
	ld1	{v3.16b},[x0],#16
	aesd	v24.16b,v23.16b
    // The iv for third block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d9,x9
	fmov	v9.d[1],x10
	eor	v30.16b,v7.16b,v10.16b
	ld1	{v27.16b},[x0],#16
	aesd	v25.16b,v23.16b
    // The iv for fourth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d10,x9
	fmov	v10.d[1],x10
	eor	v31.16b,v7.16b,v11.16b
	ld1	{v28.16b},[x0],#16
	aesd	v26.16b,v23.16b

    // The iv for fifth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d11,x9
	fmov	v11.d[1],x10

	ld1	{v29.16b},[x0],#16
	cbz	x6,.Lxts_dec_tail4x
	ld1	{v16.4s},[x7],#16        // re-pre-load rndkey[0]
	eor	v4.16b,v4.16b,v0.16b
	eor	v0.16b,v2.16b,v6.16b
	eor	v5.16b,v5.16b,v1.16b
	eor	v1.16b,v3.16b,v8.16b
	eor	v17.16b,v17.16b,v24.16b
	eor	v24.16b,v27.16b,v9.16b
	eor	v30.16b,v30.16b,v25.16b
	eor	v25.16b,v28.16b,v10.16b
	eor	v31.16b,v31.16b,v26.16b
	st1	{v4.16b},[x1],#16
	eor	v26.16b,v29.16b,v11.16b
	st1	{v5.16b},[x1],#16
	mov	w6,w5
	st1	{v17.16b},[x1],#16
	ld1	{v17.4s},[x7],#16        // re-pre-load rndkey[1]
	st1	{v30.16b},[x1],#16
	st1	{v31.16b},[x1],#16
	b.hs	.Loop5x_xts_dec

	cmn	x2,#0x10
	b.ne	.Loop5x_dec_after
    // If x2(x2) equal to -0x10, the left blocks is 4.
    // After specially processing, utilize the five blocks processing again.
    // It will use the following IVs: v6.16b,v6.16b,v8.16b,v9.16b,v10.16b.
	orr	v11.16b,v10.16b,v10.16b
	orr	v10.16b,v9.16b,v9.16b
	orr	v9.16b,v8.16b,v8.16b
	orr	v8.16b,v6.16b,v6.16b
	fmov	x9,d11
	fmov	x10,v11.d[1]
	eor	v0.16b,v6.16b,v2.16b
	eor	v1.16b,v8.16b,v3.16b
	eor	v24.16b,v27.16b,v9.16b
	eor	v25.16b,v28.16b,v10.16b
	eor	v26.16b,v29.16b,v11.16b
	b.eq	.Loop5x_xts_dec

.Loop5x_dec_after:
	add	x2,x2,#0x50
	cbz	x2,.Lxts_done

	add	w6,w5,#2
	subs	x2,x2,#0x30
	b.lo	.Lxts_inner_dec_tail

	eor	v0.16b,v6.16b,v27.16b
	eor	v1.16b,v8.16b,v28.16b
	eor	v24.16b,v29.16b,v9.16b
	b	.Lxts_outer_dec_tail

.align	4
.Lxts_dec_tail4x:
	add	x0,x0,#16
	tst	x21,#0xf
	eor	v5.16b,v1.16b,v4.16b
	st1	{v5.16b},[x1],#16
	eor	v17.16b,v24.16b,v17.16b
	st1	{v17.16b},[x1],#16
	eor	v30.16b,v25.16b,v30.16b
	eor	v31.16b,v26.16b,v31.16b
	st1	{v30.16b,v31.16b},[x1],#32

	b.eq	.Lxts_dec_abort
	ld1	{v0.4s},[x0],#16
	b	.Lxts_done
.align	4
.Lxts_outer_dec_tail:
	aesdr	v0.16b,v16.16b
	aesdr	v1.16b,v16.16b
	aesdr	v24.16b,v16.16b
	ld1	{v16.4s},[x7],#16
	subs	w6,w6,#2
	aesdr	v0.16b,v17.16b
	aesdr	v1.16b,v17.16b
	aesdr	v24.16b,v17.16b
	ld1	{v17.4s},[x7],#16
	b.gt	.Lxts_outer_dec_tail

	aesdr	v0.16b,v16.16b
	aesdr	v1.16b,v16.16b
	aesdr	v24.16b,v16.16b
	eor	v4.16b,v6.16b,v7.16b
	subs	x2,x2,#0x30
    // The iv for first block
	fmov	x9,d9
	fmov	x10,v9.d[1]
	mov	w19,#0x87
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d6,x9
	fmov	v6.d[1],x10
	eor	v5.16b,v8.16b,v7.16b
	csel	x6,x2,x6,lo   // x6, w6, is zero at this point
	aesdr	v0.16b,v17.16b
	aesdr	v1.16b,v17.16b
	aesdr	v24.16b,v17.16b
	eor	v17.16b,v9.16b,v7.16b
    // The iv for second block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d8,x9
	fmov	v8.d[1],x10

	add	x6,x6,#0x20
	add	x0,x0,x6          // x0 is adjusted to the last data

	mov	x7,x3

    // The iv for third block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d9,x9
	fmov	v9.d[1],x10

	aesdr	v0.16b,v20.16b
	aesdr	v1.16b,v20.16b
	aesdr	v24.16b,v20.16b
	aesdr	v0.16b,v21.16b
	aesdr	v1.16b,v21.16b
	aesdr	v24.16b,v21.16b
	aesdr	v0.16b,v22.16b
	aesdr	v1.16b,v22.16b
	aesdr	v24.16b,v22.16b
	ld1	{v27.16b},[x0],#16
	aesd	v0.16b,v23.16b
	aesd	v1.16b,v23.16b
	aesd	v24.16b,v23.16b
	ld1	{v16.4s},[x7],#16        // re-pre-load rndkey[0]
	add	w6,w5,#2
	eor	v4.16b,v4.16b,v0.16b
	eor	v5.16b,v5.16b,v1.16b
	eor	v24.16b,v24.16b,v17.16b
	ld1	{v17.4s},[x7],#16        // re-pre-load rndkey[1]
	st1	{v4.16b},[x1],#16
	st1	{v5.16b},[x1],#16
	st1	{v24.16b},[x1],#16

	cmn	x2,#0x30
	add	x2,x2,#0x30
	b.eq	.Lxts_done
	sub	x2,x2,#0x30
	orr	v28.16b,v3.16b,v3.16b
	orr	v29.16b,v27.16b,v27.16b
	nop

.Lxts_inner_dec_tail:
    // x2 == -0x10 means two blocks left.
	cmn	x2,#0x10
	eor	v1.16b,v28.16b,v6.16b
	eor	v24.16b,v29.16b,v8.16b
	b.eq	.Lxts_dec_tail_loop
	eor	v24.16b,v29.16b,v6.16b
.Lxts_dec_tail_loop:
	aesdr	v1.16b,v16.16b
	aesdr	v24.16b,v16.16b
	ld1	{v16.4s},[x7],#16
	subs	w6,w6,#2
	aesdr	v1.16b,v17.16b
	aesdr	v24.16b,v17.16b
	ld1	{v17.4s},[x7],#16
	b.gt	.Lxts_dec_tail_loop

	aesdr	v1.16b,v16.16b
	aesdr	v24.16b,v16.16b
	aesdr	v1.16b,v17.16b
	aesdr	v24.16b,v17.16b
	aesdr	v1.16b,v20.16b
	aesdr	v24.16b,v20.16b
	cmn	x2,#0x20
	aesdr	v1.16b,v21.16b
	aesdr	v24.16b,v21.16b
	eor	v5.16b,v6.16b,v7.16b
	aesdr	v1.16b,v22.16b
	aesdr	v24.16b,v22.16b
	eor	v17.16b,v8.16b,v7.16b
	aesd	v1.16b,v23.16b
	aesd	v24.16b,v23.16b
	b.eq	.Lxts_dec_one
	eor	v5.16b,v5.16b,v1.16b
	eor	v17.16b,v17.16b,v24.16b
	orr	v6.16b,v9.16b,v9.16b
	orr	v8.16b,v10.16b,v10.16b
	st1	{v5.16b},[x1],#16
	st1	{v17.16b},[x1],#16
	add	x2,x2,#16
	b	.Lxts_done

.Lxts_dec_one:
	eor	v5.16b,v5.16b,v24.16b
	orr	v6.16b,v8.16b,v8.16b
	orr	v8.16b,v9.16b,v9.16b
	st1	{v5.16b},[x1],#16
	add	x2,x2,#32

.Lxts_done:
	tst	x21,#0xf
	b.eq	.Lxts_dec_abort
    // Processing the last two blocks with cipher stealing.
	mov	x7,x3
	cbnz	x2,.Lxts_dec_1st_done
	ld1	{v0.4s},[x0],#16

    // Decrypt the last secod block to get the last plain text block
.Lxts_dec_1st_done:
	eor	v26.16b,v0.16b,v8.16b
	ldr	w6,[x3,#240]
	ld1	{v0.4s},[x3],#16
	sub	w6,w6,#2
	ld1	{v1.4s},[x3],#16
.Loop_final_2nd_dec:
	aesdr	v26.16b,v0.16b
	ld1	{v0.4s},[x3],#16     // load key schedule...
	subs	w6,w6,#2
	aesdr	v26.16b,v1.16b
	ld1	{v1.4s},[x3],#16     // load key schedule...
	b.gt	.Loop_final_2nd_dec

	aesdr	v26.16b,v0.16b
	ld1	{v0.4s},[x3]
	aesd	v26.16b,v1.16b
	eor	v26.16b,v26.16b,v0.16b
	eor	v26.16b,v26.16b,v8.16b
	st1	{v26.16b},[x1]

	mov	x20,x0
	add	x13,x1,#16

    // Composite the tailcnt "16 byte not aligned block" into the last second plain blocks
    // to get the last encrypted block.
.composite_dec_loop:
	subs	x21,x21,#1
	ldrb	w15,[x1,x21]
	ldrb	w14,[x20,x21]
	strb	w15,[x13,x21]
	strb	w14,[x1,x21]
	b.gt	.composite_dec_loop
.Lxts_dec_load_done:
	ld1	{v26.16b},[x1]
	eor	v26.16b,v26.16b,v6.16b

    // Decrypt the composite block to get the last second plain text block
	ldr	w6,[x7,#240]
	ld1	{v0.16b},[x7],#16
	sub	w6,w6,#2
	ld1	{v1.16b},[x7],#16
.Loop_final_dec:
	aesdr	v26.16b,v0.16b
	ld1	{v0.4s},[x7],#16     // load key schedule...
	subs	w6,w6,#2
	aesdr	v26.16b,v1.16b
	ld1	{v1.4s},[x7],#16     // load key schedule...
	b.gt	.Loop_final_dec

	aesdr	v26.16b,v0.16b
	ld1	{v0.4s},[x7]
	aesd	v26.16b,v1.16b
	eor	v26.16b,v26.16b,v0.16b
	eor	v26.16b,v26.16b,v6.16b
	st1	{v26.16b},[x1]

.Lxts_dec_abort:
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
