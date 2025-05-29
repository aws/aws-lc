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

.align	4


#define STACK_BASE_VREGS 0
#define STACK_SIZE_VREGS (4*16)

.macro save_vregs
        stp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
        stp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
        stp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        stp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

.macro restore_vregs
        ldp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
        ldp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
        ldp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        ldp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

// A single AES round
// Prevent SLOTHY from unfolding because uArchs tend to fuse AESMC+AESE
.macro aesr data, key // @slothy:no-unfold
        aese  \data, \key
        aesmc \data, \data
.endm

_aes_hw_slothy_xts_encrypt:
aes_hw_slothy_xts_encrypt:
	# AARCH64_VALID_CALL_TARGET

    sub sp, sp, #STACK_SIZE_VREGS
    save_vregs

	cmp	x2,#16
    // Original input data size bigger than 16, jump to big size processing.
	b.ne	Lxts_enc_big_size
    // Encrypt the iv with key2, as the first XEX iv.
	ldr	w6,[x4,#240]
	ld1	{v0.16b},[x4],#16
	ld1	{v6.16b},[x5]
	sub	w6,w6,#2
	ld1	{v1.16b},[x4],#16

Loop_enc_iv_enc:
	aesr    v6.16b, v0.16b
	ld1	{v0.4s},[x4],#16
	aesr    v6.16b, v1.16b
	ld1	{v1.4s},[x4],#16
	subs	w6,w6,#2
	cbnz	w6,Loop_enc_iv_enc

	aesr    v6.16b, v0.16b
	ld1	{v0.4s},[x4]
	aese	v6.16b,v1.16b
	eor	v6.16b,v6.16b,v0.16b

	ld1	{v0.16b},[x0]
	eor	v0.16b,v6.16b,v0.16b

	ldr	w6,[x3,#240]
	ld1	{v28.4s,v29.4s},[x3],#32       // load key schedule...

	aesr    v0.16b, v28.16b
	ld1	{v16.4s,v17.4s},[x3],#32         // load key schedule...
	aesr    v0.16b, v29.16b
	subs	w6,w6,#10     //// if rounds==10, jump to aes-128-xts processing
//    b.eq    .Lxts_128_enc
Lxts_enc_round_loop:
	aesr    v0.16b, v16.16b
	ld1	{v16.4s},[x3],#16            // load key schedule...
	aesr    v0.16b, v17.16b
	ld1	{v17.4s},[x3],#16            // load key schedule...
	subs	w6,w6,#2          // bias
	b.gt	Lxts_enc_round_loop
//.Lxts_128_enc:
	ld1	{v18.4s,v19.4s},[x3],#32       // load key schedule...
	aesr    v0.16b, v16.16b
	aesr    v0.16b, v17.16b
	ld1	{v20.4s,v21.4s},[x3],#32       // load key schedule...
	aesr    v0.16b, v18.16b
	aesr    v0.16b, v19.16b
	ld1	{v22.4s,v23.4s},[x3],#32       // load key schedule...
	aesr    v0.16b, v20.16b
	aesr    v0.16b, v21.16b
	ld1	{v7.4s},[x3]
	aesr    v0.16b, v22.16b
	aese	v0.16b,v23.16b
	eor	v0.16b,v0.16b,v7.16b
	eor	v0.16b,v0.16b,v6.16b
	st1	{v0.16b},[x1]
	b	Lxts_enc_final_abort

.align	4
Lxts_enc_big_size:
   // Encrypt input size > 16 bytes
	stp	x19,x20,[sp,#-32]!
	stp	x21,x22,[sp,#16]

    // tailcnt store the tail value of length%16.
	and	x21,x2,#0xf
	and	x2,x2,#-16    // len &= 0x1..110000, now divisible by 16
	subs	x2,x2,#16
	mov	x8,#16
	b.lo	Lxts_abort         // if !(len > 16): error
	csel	x8,xzr,x8,eq  // if (len == 16): step = 0

    // Firstly, encrypt the iv with key2, as the first iv of XEX.
	ldr	w6,[x4,#240]
	ld1	{v0.4s},[x4],#16
	ld1	{v6.16b},[x5]
	sub	w6,w6,#2
	ld1	{v1.4s},[x4],#16

Loop_iv_enc:
	aesr    v6.16b, v0.16b
	ld1	{v0.4s},[x4],#16
	subs	w6,w6,#2
	aesr    v6.16b, v1.16b
	ld1	{v1.4s},[x4],#16
	b.gt	Loop_iv_enc

	aesr    v6.16b, v0.16b
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
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d8,x9
	fmov	v8.d[1],x10

	ldr	w5,[x3,#240]       // next starting point
	ld1	{v0.16b},[x0],x8

    mov x7, x3
	ld1	{v16.4s,v17.4s},[x7], #32         // load key schedule...
    ld1 {v12.4s,v13.4s},[x7], #32
	ld1	{v14.4s,v15.4s},[x7], #32
    ld1 {v4.4s,v5.4s},  [x7], #32
    ld1	{v18.4s,v19.4s},[x7], #32
	ld1	{v20.4s,v21.4s},[x7], #32
	ld1	{v22.4s,v23.4s},[x7], #32
	ld1	{v7.4s},        [x7]

	sub	w5,w5,#8
	add	x7,x3,#32
	mov	w6,w5

    // Encryption
Lxts_enc:
	ld1	{v24.16b},[x0],#16
	subs	x2,x2,#32           // bias
	add	w6,w5,#2
	orr	v28.16b,v0.16b,v0.16b
	orr	v29.16b,v24.16b,v24.16b
	b.lo	Lxts_inner_enc_tail    // when input size % 5 = 1 or 2
                                    // (with tail or not)
	eor	v0.16b,v0.16b,v6.16b          // before encryption, xor with iv
	eor	v24.16b,v24.16b,v8.16b

    // The iv for third block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d9,x9
	fmov	v9.d[1],x10


	orr	v1.16b,v24.16b,v24.16b
	ld1	{v24.16b},[x0],#16
	orr	v2.16b,v0.16b,v0.16b
	orr	v3.16b,v1.16b,v1.16b
	eor	v27.16b,v24.16b,v9.16b         // the third block
	eor	v24.16b,v24.16b,v9.16b
	cmp	x2,#32
	b.lo	Lxts_outer_enc_tail

    // The iv for fourth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d10,x9
	fmov	v10.d[1],x10

	ld1	{v25.16b},[x0],#16
    // The iv for fifth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d11,x9
	fmov	v11.d[1],x10

	ld1	{v26.16b},[x0],#16
	eor	v25.16b,v25.16b,v10.16b        // the fourth block
	eor	v26.16b,v26.16b,v11.16b
	sub	x2,x2,#32           // bias
	mov	w6,w5

.align	4
Loop5x_xts_enc:
    aesr    v0.16b, v16.16b
    aesr    v1.16b, v16.16b
	aesr    v24.16b, v16.16b
	aesr    v25.16b, v16.16b
	aesr    v26.16b, v16.16b
	subs	x12,x2,#0x50         // @slothy:core=True

	aesr    v0.16b, v17.16b
	aesr    v1.16b, v17.16b
	aesr    v24.16b, v17.16b
	aesr    v25.16b, v17.16b
	aesr    v26.16b, v17.16b
    // borrow x6, w6, "gt" is not typo
	csel	x6,xzr,x12,gt    // @slothy:core=True

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
	add	x0,x0,x6  // @slothy:core=True
                             // x0 is adjusted in such way that
                             // at exit from the loop v1.16b-v26.16b
                             // are loaded with last "words"

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

	aese	v0.16b,v23.16b
	aese	v1.16b,v23.16b
	aese	v24.16b,v23.16b
	aese	v25.16b,v23.16b
	aese	v26.16b,v23.16b

	eor	v0.16b,v0.16b,v7.16b
	eor	v0.16b,v0.16b,v6.16b
    // The iv for first block of one iteration
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d6,x9
	fmov	v6.d[1],x10
    eor	v1.16b,v1.16b,v7.16b
    eor	v1.16b,v1.16b,v8.16b
    ldp q2, q3, [x0], #0x50

    // The iv for second block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d8,x9
	fmov	v8.d[1],x10
    eor	v24.16b,v24.16b,v7.16b
    eor	v24.16b,v24.16b,v9.16b

    // The iv for third block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d9,x9
	fmov	v9.d[1],x10
    eor	v25.16b,v25.16b,v7.16b
    eor	v25.16b,v25.16b,v10.16b
    ldr q27, [x0, #-0x30]

    // The iv for fourth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d10,x9
	fmov	v10.d[1],x10
    eor	v26.16b,v26.16b,v7.16b
    eor	v26.16b,v26.16b,v11.16b
    ldp	q28, q29,[x0, #-0x20]

    // The iv for fifth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d11,x9
	fmov	v11.d[1],x10

    stp q0, q1, [x1], #0x50
    stp q24, q25, [x1, #-0x30]
    str	q26, [x1, #-0x10]
	eor	v0.16b,v2.16b,v6.16b
	eor	v1.16b,v3.16b,v8.16b
	eor	v24.16b,v27.16b,v9.16b
	eor	v25.16b,v28.16b,v10.16b
	eor	v26.16b,v29.16b,v11.16b

    subs x2,x2,#0x50
	b.hs	Loop5x_xts_enc


    // If left 4 blocks, continue from Lxts_enc_tail4x.
    // Otherwise, continue processing
    // 0, 1, 2 or 3 blocks (with or without tail) starting at
    // Loop5x_enc_after
	cmn	x2,#0x10
	b.ne	Loop5x_enc_after
    b.eq  Lxts_enc_tail4x

Loop5x_enc_after:
	add	x2,x2,#0x50
	cbz	x2,Lxts_enc_done     // no blocks left

	add	w6,w5,#2
	subs	x2,x2,#0x30
	b.lo	Lxts_inner_enc_tail    // 1 or 2 blocks left
                                    // (with tail or not)

	eor	v0.16b,v6.16b,v27.16b         // 3 blocks left
	eor	v1.16b,v8.16b,v28.16b
	eor	v24.16b,v29.16b,v9.16b
	b	Lxts_outer_enc_tail

.align	4
Lxts_enc_tail4x:
	orr	v11.16b,v10.16b,v10.16b
	orr	v10.16b,v9.16b,v9.16b
	orr	v9.16b,v8.16b,v8.16b
	orr	v8.16b,v6.16b,v6.16b
	fmov	x9,d11
	fmov	x10,v11.d[1]
	eor	v1.16b,v8.16b,v3.16b
	eor	v24.16b,v27.16b,v9.16b
	eor	v25.16b,v28.16b,v10.16b
	eor	v26.16b,v29.16b,v11.16b

	aesr    v1.16b, v16.16b
	aesr    v24.16b, v16.16b
	aesr    v25.16b, v16.16b
	aesr    v26.16b, v16.16b
	subs	x2,x2,#0x50         // because Lxts_enc_tail4x

	aesr    v1.16b, v17.16b
	aesr    v24.16b, v17.16b
	aesr    v25.16b, v17.16b
	aesr    v26.16b, v17.16b
	csel	x6,xzr,x2,gt    // borrow x6, w6, "gt" is not typo

	aesr    v1.16b, v12.16b
	aesr    v24.16b, v12.16b
	aesr    v25.16b, v12.16b
	aesr    v26.16b, v12.16b

	aesr    v1.16b, v13.16b
	aesr    v24.16b, v13.16b
	aesr    v25.16b, v13.16b
	aesr    v26.16b, v13.16b

	aesr    v1.16b, v14.16b
	aesr    v24.16b, v14.16b
	aesr    v25.16b, v14.16b
	aesr    v26.16b, v14.16b

	aesr    v1.16b, v15.16b
	aesr    v24.16b, v15.16b
	aesr    v25.16b, v15.16b
	aesr    v26.16b, v15.16b

	aesr    v1.16b, v4.16b
	aesr    v24.16b, v4.16b
	aesr    v25.16b, v4.16b
	aesr    v26.16b, v4.16b

	aesr    v1.16b, v5.16b
	aesr    v24.16b, v5.16b
	aesr    v25.16b, v5.16b
	aesr    v26.16b, v5.16b

	aesr    v1.16b, v18.16b
	aesr    v24.16b, v18.16b
	aesr    v25.16b, v18.16b
	aesr    v26.16b, v18.16b
	add	x0,x0,x6  // x0 is adjusted in such way that
                                // at exit from the loop v1.16b-v26.16b
                                // are loaded with last "words"

	aesr    v1.16b, v19.16b
	aesr    v24.16b, v19.16b
	aesr    v25.16b, v19.16b
	aesr    v26.16b, v19.16b

	aesr    v1.16b, v20.16b
	aesr    v24.16b, v20.16b
	aesr    v25.16b, v20.16b
	aesr    v26.16b, v20.16b

	aesr    v1.16b, v21.16b
	aesr    v24.16b, v21.16b
	aesr    v25.16b, v21.16b
	aesr    v26.16b, v21.16b

	aesr    v1.16b, v22.16b
	aesr    v24.16b, v22.16b
	aesr    v25.16b, v22.16b
	aesr    v26.16b, v22.16b

	aese	v1.16b,v23.16b
	aese	v24.16b,v23.16b
	aese	v25.16b,v23.16b
	aese	v26.16b,v23.16b

    // The iv for first block of one iteration
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d6,x9
	fmov	v6.d[1],x10
    eor	v1.16b,v1.16b,v7.16b
    eor	v1.16b,v1.16b,v8.16b
	ld1	{v2.16b},[x0],#16
    // The iv for second block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d8,x9
	fmov	v8.d[1],x10
    eor	v24.16b,v24.16b,v7.16b
    eor	v24.16b,v24.16b,v9.16b
    ld1	{v3.16b},[x0],#16
    // The iv for third block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d9,x9
	fmov	v9.d[1],x10
    eor	v25.16b,v25.16b,v7.16b
    eor	v25.16b,v25.16b,v10.16b
	ld1	{v27.16b},[x0],#16
    // The iv for fourth block
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d10,x9
	fmov	v10.d[1],x10
    eor	v26.16b,v26.16b,v7.16b
    eor	v26.16b,v26.16b,v11.16b
	ld1	{v28.16b},[x0],#16
	ld1	{v29.16b},[x0],#16

	add	x0,x0,#16
    st1  {v1.16b},[x1],#16
    st1	{v24.16b,v25.16b},[x1],#32
    st1  {v26.16b},[x1],#16
	b	Lxts_enc_done
.align	4
Lxts_outer_enc_tail:
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
	aese	v0.16b,v23.16b
	aese	v1.16b,v23.16b
	aese	v24.16b,v23.16b

	eor	v30.16b,v6.16b,v7.16b
	eor	v11.16b,v9.16b,v7.16b
	subs	x2,x2,#0x30
    // The iv for first block
	fmov	x9,d9
	fmov	x10,v9.d[1]
    //mov   w19,#0x87
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr#31
	eor	x9,x11,x9,lsl#1
	fmov	d6,x9
	fmov	v6.d[1],x10
	eor	v10.16b,v8.16b,v7.16b
	csel	x6,x2,x6,lo   // x6, w6, is zero at this point

	add	x6,x6,#0x20
	add	x0,x0,x6
	mov	x7,x3

	ld1	{v27.16b},[x0],#16
	add	w6,w5,#2
	eor	v30.16b,v30.16b,v0.16b
	eor	v31.16b,v10.16b,v1.16b
	eor	v24.16b,v24.16b,v11.16b
	ld1	{v16.4s,v17.4s},[x7],#32
	st1	{v30.16b,v31.16b},[x1],#32
	st1	{v24.16b},[x1],#16
	cmn	x2,#0x30
	b.eq	Lxts_enc_done
Lxts_encxor_one:
	orr	v28.16b,v3.16b,v3.16b
	orr	v29.16b,v27.16b,v27.16b
	nop

Lxts_inner_enc_tail:
	cmn	x2,#0x10
	eor	v1.16b,v28.16b,v6.16b
	eor	v24.16b,v29.16b,v8.16b
	b.eq	Lxts_enc_tail_loop
	eor	v24.16b,v29.16b,v6.16b
Lxts_enc_tail_loop:
		// First round with v16
		aesr    v1.16b, v16.16b
		aesr    v24.16b, v16.16b

		// Second round with v17
		aesr    v1.16b, v17.16b
		aesr    v24.16b, v17.16b

		// Third round with v12
		aesr    v1.16b, v12.16b
		aesr    v24.16b, v12.16b

		// Fourth round with v13
		aesr    v1.16b, v13.16b
		aesr    v24.16b, v13.16b

		// Fifth round with v14
		aesr    v1.16b, v14.16b
		aesr    v24.16b, v14.16b

		// Sixth round with v15
		aesr    v1.16b, v15.16b
		aesr    v24.16b, v15.16b

		// Seventh round with v4
		aesr    v1.16b, v4.16b
		aesr    v24.16b, v4.16b

		// Eighth round with v5
		aesr    v1.16b, v5.16b
		aesr    v24.16b, v5.16b

		// 9th round with v18
		aesr    v1.16b, v18.16b
		aesr    v24.16b, v18.16b

		// 10th round with v19
		aesr    v1.16b, v19.16b
		aesr    v24.16b, v19.16b

	aesr    v1.16b, v20.16b
	aesr    v24.16b, v20.16b
	cmn	x2,#0x20
	aesr    v1.16b, v21.16b
	aesr    v24.16b, v21.16b
	eor	v5.16b,v6.16b,v7.16b
	aesr    v1.16b, v22.16b
	aesr    v24.16b, v22.16b
	eor	v17.16b,v8.16b,v7.16b
	aese	v1.16b,v23.16b
	aese	v24.16b,v23.16b
	b.eq	Lxts_enc_one
	eor	v5.16b,v5.16b,v1.16b
	st1	{v5.16b},[x1],#16
	eor	v17.16b,v17.16b,v24.16b
	orr	v6.16b,v8.16b,v8.16b
	st1	{v17.16b},[x1],#16
	fmov	x9,d8
	fmov	x10,v8.d[1]
	mov	w19,#0x87
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d6,x9
	fmov	v6.d[1],x10
	b	Lxts_enc_done

Lxts_enc_one:
	eor	v5.16b,v5.16b,v24.16b
	orr	v6.16b,v6.16b,v6.16b
	st1	{v5.16b},[x1],#16
	fmov	x9,d6
	fmov	x10,v6.d[1]
	mov	w19,#0x87
	extr	x22,x10,x10,#32
	extr	x10,x10,x9,#63
	and	w11,w19,w22,asr #31
	eor	x9,x11,x9,lsl #1
	fmov	d6,x9
	fmov	v6.d[1],x10
	b	Lxts_enc_done
.align	5
Lxts_enc_done:
    // Process the tail block with cipher stealing.
	tst	x21,#0xf
	b.eq	Lxts_abort

	mov	x20,x0
	mov	x13,x1
	sub	x1,x1,#16
.composite_enc_loop:
	subs	x21,x21,#1
	ldrb	w15,[x1,x21]
	ldrb	w14,[x20,x21]
	strb	w15,[x13,x21]
	strb	w14,[x1,x21]
	b.gt	.composite_enc_loop
Lxts_enc_load_done:
	ld1	{v26.16b},[x1]
	eor	v26.16b,v26.16b,v6.16b

    // Encrypt the composite block to get the last second encrypted text block
	ldr	w6,[x3,#240]        // load key schedule...
	ld1	{v0.16b},[x3],#16
	sub	w6,w6,#2
	ld1	{v1.16b},[x3],#16     // load key schedule...
Loop_final_enc:
	aesr    v26.16b, v0.16b
	ld1	{v0.4s},[x3],#16
	subs	w6,w6,#2
	aesr    v26.16b, v1.16b
	ld1	{v1.4s},[x3],#16
	b.gt	Loop_final_enc

	aesr    v26.16b, v0.16b
	ld1	{v0.4s},[x3]
	aese	v26.16b,v1.16b
	eor	v26.16b,v26.16b,v0.16b
	eor	v26.16b,v26.16b,v6.16b
	st1	{v26.16b},[x1]

Lxts_abort:
	ldp	x21,x22,[sp,#16]
	ldp	x19,x20,[sp],#32
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
