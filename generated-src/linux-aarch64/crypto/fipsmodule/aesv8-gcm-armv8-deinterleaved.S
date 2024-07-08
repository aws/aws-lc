// This file is generated from a similarly-named Perl script in the BoringSSL
// source tree. Do not edit by hand.

#include <openssl/asm_base.h>

#if !defined(OPENSSL_NO_ASM) && defined(OPENSSL_AARCH64) && defined(__ELF__)
#include <openssl/arm_arch.h>
#if __ARM_MAX_ARCH__ >= 8

.arch	armv8-a+crypto
.text
.globl	aes_gcm_enc_kernel_deinterleaved
.hidden	aes_gcm_enc_kernel_deinterleaved
.type	aes_gcm_enc_kernel_deinterleaved,%function
.align	4
aes_gcm_enc_kernel_deinterleaved:
#ifdef BORINGSSL_DISPATCH_TEST

	adrp	x9,BORINGSSL_function_hit
	add	x9, x9, :lo12:BORINGSSL_function_hit
	mov	w10, #1
	strb	w10, [x9,#2] // kFlag_aes_gcm_enc_kernel_deinterleaved
#endif
	AARCH64_SIGN_LINK_REGISTER
	stp	x29, x30, [sp, #-128]!
	mov	x29, sp
	stp	x19, x20, [sp, #16]
	mov	x16, x4
	mov	x8, x5
	stp	x21, x22, [sp, #32]
	stp	x23, x24, [sp, #48]
	stp	d8, d9, [sp, #64]
	stp	d10, d11, [sp, #80]
	stp	d12, d13, [sp, #96]
	stp	d14, d15, [sp, #112]
	ldr	w17, [x8, #240]
	add	x19, x8, x17, lsl #4                   // borrow input_l1 for last key
	ldr	q18, [x8, #0]                                  // load rk0
	ldr	q19, [x8, #16]                                 // load rk1
	ldr	q20, [x8, #32]                                 // load rk2
	ldr	q21, [x8, #48]                                 // load rk3
	ldr	q22, [x8, #64]                                 // load rk4
	ldr	q23, [x8, #80]                                 // load rk5
	ldr	q24, [x8, #96]                                 // load rk6
	ldr	q25, [x8, #112]                                // load rk7
	ldr	q26, [x8, #128]                                // load rk8
	ldr	q27, [x8, #144]                                // load rk9
	ldr	q28, [x8, #160]                               // load rk10
	ldr	q29, [x8, #176]                               // load rk11
	ldr	q30, [x8, #192]                               // load rk12
	ldp	x13, x14, [x19]                       // load round N keys
	ldr	q31, [x19, #-16]                        // load round N-1 keys
	add	x4, x0, x1, lsr #3   // end_input_ptr
	lsr	x5, x1, #3              // byte_len
	mov	x15, x5
	ldp	x10, x11, [x16]              // ctr96_b64, ctr96_t32
	ld1	{ v0.16b}, [x16]                             // special case vector load initial counter so we can start first AES block as quickly as possible
	sub	x5, x5, #1      // byte_len - 1
	and	x5, x5, #0xffffffffffffffc0 // number of bytes to be processed in main loop (at least 1 byte must be handled by tail)
	add	x5, x5, x0
	lsr	x12, x11, #32
	orr	w11, w11, w11
	rev	w12, w12                                // rev_ctr32
	aese	v0.16b, v18.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 0
	add	w12, w12, #1                            // increment rev_ctr32
	fmov	d1, x10                               // CTR block 1
	rev	w9, w12                                 // CTR block 1
	orr	x9, x11, x9, lsl #32            // CTR block 1
	add	w12, w12, #1                            // CTR block 1
	fmov	v1.d[1], x9                               // CTR block 1
	rev	w9, w12                                 // CTR block 2
	fmov	d2, x10                               // CTR block 2
	add	w12, w12, #1                            // CTR block 2
	orr	x9, x11, x9, lsl #32            // CTR block 2
	fmov	v2.d[1], x9                               // CTR block 2
	fmov	d3, x10                               // CTR block 3
	rev	w9, w12                                 // CTR block 3
	orr	x9, x11, x9, lsl #32            // CTR block 3
	fmov	v3.d[1], x9                               // CTR block 3
	add	w12, w12, #1                            // CTR block 3
	aese	v0.16b, v19.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 1
	aese	v1.16b, v18.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 0
	aese	v0.16b, v20.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 2
	aese	v2.16b, v18.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 0
	aese	v1.16b, v19.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 1
	aese	v3.16b, v18.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 0
	aese	v2.16b, v19.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 1
	aese	v1.16b, v20.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 2
	aese	v3.16b, v19.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 1
	aese	v2.16b, v20.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 2
	aese	v1.16b, v21.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 3
	aese	v3.16b, v20.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 2
	aese	v2.16b, v21.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 3
	aese	v0.16b, v21.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 3
	aese	v3.16b, v21.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 3
	aese	v2.16b, v22.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 4
	aese	v0.16b, v22.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 4
	aese	v1.16b, v22.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 4
	aese	v3.16b, v22.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 4
	aese	v0.16b, v23.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 5
	aese	v1.16b, v23.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 5
	aese	v3.16b, v23.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 5
	aese	v2.16b, v23.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 5
	aese	v1.16b, v24.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 6
	aese	v3.16b, v24.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 6
	aese	v0.16b, v24.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 6
	aese	v2.16b, v24.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 6
	aese	v1.16b, v25.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 7
	aese	v0.16b, v25.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 7
	aese	v2.16b, v25.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 7
	aese	v3.16b, v25.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 7
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 8
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 8
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 8
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 8
	cmp	x17, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Lenc_finish_first_blocks                         // branch if AES-128

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 9
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 9
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 9
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 9
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 10
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 10
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 10
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 10
	b.eq	.Lenc_finish_first_blocks                         // branch if AES-192

	aese	v1.16b, v29.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 11
	aese	v2.16b, v29.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 11
	aese	v0.16b, v29.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 11
	aese	v3.16b, v29.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 11
	aese	v1.16b, v30.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 12
	aese	v2.16b, v30.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 12
	aese	v0.16b, v30.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 12
	aese	v3.16b, v30.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 12

.Lenc_finish_first_blocks:
	aese	v2.16b, v31.16b                                    // AES block 2 - round N-1
	aese	v1.16b, v31.16b                                    // AES block 1 - round N-1
	aese	v0.16b, v31.16b                                    // AES block 0 - round N-1
	aese	v3.16b, v31.16b                                    // AES block 3 - round N-1

	ldr	q12, [x6]                                   // load h1l | h1h
	ext	v12.16b, v12.16b, v12.16b, #8
	ldr	q14, [x6, #48]                              // load h3l | h3h
	ext	v14.16b, v14.16b, v14.16b, #8
	ldr	q13, [x6, #32]                              // load h2l | h2h
	ext	v13.16b, v13.16b, v13.16b, #8
	ldr	q15, [x6, #80]                              // load h4l | h4h
	ext	v15.16b, v15.16b, v15.16b, #8
	trn2	v17.2d,  v14.2d,    v15.2d                      // h4l | h3l
	trn1	v9.2d, v14.2d,    v15.2d                      // h4h | h3h
	trn2	v16.2d,  v12.2d,    v13.2d                      // h2l | h1l
	eor	v17.16b, v17.16b, v9.16b                  // h4k | h3k
	trn1	v8.2d,    v12.2d,    v13.2d                      // h2h | h1h
	eor	v16.16b, v16.16b, v8.16b                     // h2k | h1k

	ld1	{ v11.16b}, [x3]
	ext	v11.16b, v11.16b, v11.16b, #8
	rev64	v11.16b, v11.16b

        // At this point, have
        // - Computes N-1 rounds of AES, but not yet loaded+XOR'ed plaintext
        // - In consequence, not yet done any GHASH
        // - Not yet loaded CTR for next block

	cmp	x0, x5                   // check if we have <= 4 blocks
	b.ge	.Lenc_tail                                        // handle tail

	ldp	x6, x7, [x0, #0]            // AES block 0 - load plaintext
	eor	x6, x6, x13                      // AES block 0 - round N low
	eor	x7, x7, x14                      // AES block 0 - round N high
	fmov	d4, x6                               // AES block 0 - mov low
	fmov	v4.d[1], x7                           // AES block 0 - mov high
	eor	v4.16b, v4.16b, v0.16b                          // AES block 0 - result
	st1	{ v4.16b}, [x2], #16                     // AES block 0 - store result
	ldp	x19, x20, [x0, #16]           // AES block 1 - load plaintext
	eor	x19, x19, x13                      // AES block 1 - round N low
	eor	x20, x20, x14                      // AES block 1 - round N high
	fmov	d5, x19                               // AES block 1 - mov low
	fmov	v5.d[1], x20                           // AES block 1 - mov high
	eor	v5.16b, v5.16b, v1.16b                          // AES block 1 - result
	st1	{ v5.16b}, [x2], #16                     // AES block 1 - store result
	ldp	x21, x22, [x0, #32]           // AES block 2 - load plaintext
	eor	x21, x21, x13                      // AES block 2 - round N low
	fmov	d6, x21                               // AES block 2 - mov low
	eor	x22, x22, x14                      // AES block 2 - round N high
	fmov	v6.d[1], x22                           // AES block 2 - mov high
	eor	v6.16b, v6.16b, v2.16b                          // AES block 2 - result
	st1	{ v6.16b}, [x2], #16                     // AES block 2 - store result
	ldp	x23, x24, [x0, #48]           // AES block 3 - load plaintext
	eor	x24, x24, x14                      // AES block 3 - round N high
	eor	x23, x23, x13                      // AES block 3 - round N low
	fmov	d7, x23                               // AES block 3 - mov low
	fmov	v7.d[1], x24                           // AES block 3 - mov high
	eor	v7.16b, v7.16b, v3.16b                          // AES block 3 - result
	st1	{ v7.16b}, [x2], #16                     // AES block 3 - store result
	rev	w9, w12                                 // CTR block 4
	add	w12, w12, #1                            // CTR block 4
	orr	x9, x11, x9, lsl #32            // CTR block 4
	fmov	d0, x10                               // CTR block 4
	fmov	v0.d[1], x9                               // CTR block 4
	rev	w9, w12                                 // CTR block 5
	add	w12, w12, #1                            // CTR block 5
	fmov	d1, x10                               // CTR block 5
	orr	x9, x11, x9, lsl #32            // CTR block 5
	fmov	v1.d[1], x9                               // CTR block 5
	rev	w9, w12                                 // CTR block 6
	orr	x9, x11, x9, lsl #32            // CTR block 6
	add	w12, w12, #1                            // CTR block 6
	fmov	d2, x10                               // CTR block 6
	fmov	v2.d[1], x9                               // CTR block 6
	rev	w9, w12                                 // CTR block 7
	orr	x9, x11, x9, lsl #32            // CTR block 7
	add	x0, x0, #64                       // AES input_ptr update
	cmp	x0, x5                   // check if we have <= 8 blocks
	b.ge	.Lenc_prepretail                                  // do prepretail

        // At this point, we have
        // - Finalized and stored result of last x4-batched AES
        // - Prepared next 4 counters, except for 4k+3 (unclear why)
        // - Not yet done _any_ GHASH computation

.Lenc_main_loop:	//	main loop start
	fmov	d3, x10                               // CTR block 4k+3
	fmov	v3.d[1], x9                               // CTR block 4k+3
	add	w12, w12, #1                            // CTR block 4k+3
	rev64	v4.16b, v4.16b                                    // GHASH block 4k (only t0 is free)
	ext	v11.16b, v11.16b, v11.16b, #8                     // PRE 0
	eor	v4.16b, v4.16b, v11.16b                           // PRE 1
	mov	d10, v17.d[1]                               // GHASH block 4k - mid
	pmull2	v9.1q, v4.2d, v15.2d                       // GHASH block 4k - high
	mov	d8, v4.d[1]                                  // GHASH block 4k - mid
	rev64	v5.16b, v5.16b                                    // GHASH block 4k+1 (t0 and t1 free)
	pmull	v11.1q, v4.1d, v15.1d                       // GHASH block 4k - low
	eor	v8.8b, v8.8b, v4.8b                          // GHASH block 4k - mid
	rev64	v7.16b, v7.16b                                    // GHASH block 4k+3 (t0, t1, t2 and t3 free)
	pmull2	v4.1q, v5.2d, v14.2d                          // GHASH block 4k+1 - high
	pmull	v10.1q, v8.1d, v10.1d                      // GHASH block 4k - mid
	rev64	v6.16b, v6.16b                                    // GHASH block 4k+2 (t0, t1, and t2 free)
	pmull	v8.1q, v5.1d, v14.1d                          // GHASH block 4k+1 - low
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+1 - high
	mov	d4, v5.d[1]                                  // GHASH block 4k+1 - mid
	eor	v11.16b, v11.16b, v8.16b                         // GHASH block 4k+1 - low
	mov	d8, v6.d[1]                                  // GHASH block 4k+2 - mid
	eor	v4.8b, v4.8b, v5.8b                          // GHASH block 4k+1 - mid
	eor	v8.8b, v8.8b, v6.8b                          // GHASH block 4k+2 - mid
	pmull	v4.1q, v4.1d, v17.1d                          // GHASH block 4k+1 - mid
	ins	v8.d[1], v8.d[0]                                // GHASH block 4k+2 - mid
	eor	v10.16b, v10.16b, v4.16b                         // GHASH block 4k+1 - mid
	pmull2	v4.1q, v6.2d, v13.2d                          // GHASH block 4k+2 - high
	pmull	v5.1q, v6.1d, v13.1d                          // GHASH block 4k+2 - low
	pmull	v6.1q, v7.1d, v12.1d                          // GHASH block 4k+3 - low
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+2 - high
	mov	d4, v7.d[1]                                  // GHASH block 4k+3 - mid
	eor	v11.16b, v11.16b, v5.16b                         // GHASH block 4k+2 - low
	pmull2	v8.1q, v8.2d, v16.2d                          // GHASH block 4k+2 - mid
	pmull2	v5.1q, v7.2d, v12.2d                          // GHASH block 4k+3 - high
	eor	v4.8b, v4.8b, v7.8b                          // GHASH block 4k+3 - mid
	eor	v10.16b, v10.16b, v8.16b                         // GHASH block 4k+2 - mid
	movi	v8.8b, #0xc2
	pmull	v4.1q, v4.1d, v16.1d                          // GHASH block 4k+3 - mid
	eor	v9.16b, v9.16b, v5.16b                         // GHASH block 4k+3 - high
	eor	v11.16b, v11.16b, v6.16b                         // GHASH block 4k+3 - low
	eor	v10.16b, v10.16b, v4.16b                         // GHASH block 4k+3 - mid
	shl	d8, d8, #56               // mod_constant
	eor	v4.16b, v11.16b, v9.16b                         // MODULO - karatsuba tidy up
	pmull	v7.1q, v9.1d, v8.1d            // MODULO - top 64b align with mid
	ext	v9.16b, v9.16b, v9.16b, #8                     // MODULO - other top alignment
	eor	v10.16b, v10.16b, v4.16b                         // MODULO - karatsuba tidy up
	eor	v7.16b, v9.16b, v7.16b                   // MODULO - fold into mid
	eor	v10.16b, v10.16b, v7.16b                      // MODULO - fold into mid
	pmull	v9.1q, v10.1d, v8.1d            // MODULO - mid 64b align with low
	eor	v11.16b, v11.16b, v9.16b                         // MODULO - fold into low
	ext	v10.16b, v10.16b, v10.16b, #8                     // MODULO - other mid alignment
	eor	v11.16b, v11.16b, v10.16b                         // MODULO - fold into low
	aese	v0.16b, v18.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 0
	aese	v1.16b, v18.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 0
	aese	v2.16b, v18.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 0
	aese	v0.16b, v19.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 1
	aese	v1.16b, v19.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 1
	ldp	x23, x24, [x0, #48]           // AES block 4k+7 - load plaintext
	aese	v2.16b, v19.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 1
	ldp	x21, x22, [x0, #32]           // AES block 4k+6 - load plaintext
	aese	v0.16b, v20.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 2
	aese	v1.16b, v20.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 2
	aese	v3.16b, v18.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 0
	eor	x23, x23, x13                      // AES block 4k+7 - round N low
	aese	v0.16b, v21.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 3
	eor	x22, x22, x14                      // AES block 4k+6 - round N high
	aese	v3.16b, v19.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 1
	aese	v0.16b, v22.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 4
	aese	v2.16b, v20.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 2
	aese	v0.16b, v23.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 5
	aese	v1.16b, v21.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 3
	aese	v3.16b, v20.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 2
	aese	v2.16b, v21.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 3
	aese	v1.16b, v22.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 4
	aese	v3.16b, v21.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 3
	aese	v2.16b, v22.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 4
	aese	v0.16b, v24.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 6
	aese	v3.16b, v22.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 4
	aese	v0.16b, v25.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 7
	aese	v3.16b, v23.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 5
	aese	v1.16b, v23.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 5
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 8
	aese	v2.16b, v23.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 5
	aese	v1.16b, v24.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 6
	aese	v1.16b, v25.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 7
	aese	v3.16b, v24.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 6
	ldp	x19, x20, [x0, #16]           // AES block 4k+5 - load plaintext
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 8
	aese	v2.16b, v24.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 6
	aese	v2.16b, v25.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 7
	eor	x19, x19, x13                      // AES block 4k+5 - round N low
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 8
	aese	v3.16b, v25.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 7
	eor	x21, x21, x13                      // AES block 4k+6 - round N low
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 8
	cmp	x17, #12                                      // setup flags for AES-128/192/256 check
	fmov	d5, x19                               // AES block 4k+5 - mov low
	ldp	x6, x7, [x0, #0]            // AES block 4k+4 - load plaintext
	b.lt	.Lenc_main_loop_continue                          // branch if AES-128

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 9
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 9
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 9
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 9
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 10
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 10
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 10
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 10
	b.eq	.Lenc_main_loop_continue                          // branch if AES-192

	aese	v0.16b, v29.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 11
	aese	v1.16b, v29.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 11
	aese	v2.16b, v29.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 11
	aese	v3.16b, v29.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 11
	aese	v1.16b, v30.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 12
	aese	v0.16b, v30.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 12
	aese	v2.16b, v30.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 12
	aese	v3.16b, v30.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 12

.Lenc_main_loop_continue:
	eor	x6, x6, x13                      // AES block 4k+4 - round N low
	eor	x7, x7, x14                      // AES block 4k+4 - round N high
	fmov	d4, x6                               // AES block 4k+4 - mov low
	aese	v0.16b, v31.16b                                    // AES block 4k+4 - round N-1
	fmov	v4.d[1], x7                           // AES block 4k+4 - mov high
	eor	v4.16b, v4.16b, v0.16b                          // AES block 4k+4 - result
	st1	{ v4.16b}, [x2], #16                     // AES block 4k+4 - store result
	eor	x20, x20, x14                      // AES block 4k+5 - round N high
	aese	v1.16b, v31.16b                                    // AES block 4k+5 - round N-1
	fmov	v5.d[1], x20                           // AES block 4k+5 - mov high
	eor	v5.16b, v5.16b, v1.16b                          // AES block 4k+5 - result
	st1	{ v5.16b}, [x2], #16                     // AES block 4k+5 - store result
	fmov	d6, x21                               // AES block 4k+6 - mov low
	fmov	v6.d[1], x22                           // AES block 4k+6 - mov high
	aese	v2.16b, v31.16b                                    // AES block 4k+6 - round N-1
	eor	v6.16b, v6.16b, v2.16b                          // AES block 4k+6 - result
	st1	{ v6.16b}, [x2], #16                     // AES block 4k+6 - store result
	eor	x24, x24, x14                      // AES block 4k+7 - round N high
	fmov	d7, x23                               // AES block 4k+7 - mov low
	fmov	v7.d[1], x24                           // AES block 4k+7 - mov high
	aese	v3.16b, v31.16b                                    // AES block 4k+7 - round N-1
	eor	v7.16b, v7.16b, v3.16b                          // AES block 4k+7 - result
	st1	{ v7.16b}, [x2], #16                     // AES block 4k+7 - store result
	rev	w9, w12                                 // CTR block 4k+8
	orr	x9, x11, x9, lsl #32            // CTR block 4k+8
	add	w12, w12, #1                            // CTR block 4k+8
	fmov	d0, x10                               // CTR block 4k+8
	fmov	v0.d[1], x9                               // CTR block 4k+8
	rev	w9, w12                                 // CTR block 4k+9
	add	w12, w12, #1                            // CTR block 4k+9
	fmov	d1, x10                               // CTR block 4k+9
	orr	x9, x11, x9, lsl #32            // CTR block 4k+9
	fmov	v1.d[1], x9                               // CTR block 4k+9
	rev	w9, w12                                 // CTR block 4k+10
	orr	x9, x11, x9, lsl #32            // CTR block 4k+10
	add	w12, w12, #1                            // CTR block 4k+10
	fmov	d2, x10                               // CTR block 4k+10
	fmov	v2.d[1], x9                               // CTR block 4k+10
	rev	w9, w12                                 // CTR block 4k+11
	orr	x9, x11, x9, lsl #32            // CTR block 4k+11
	add	x0, x0, #64                       // AES input_ptr update
	cmp	x0, x5                   // .LOOP CONTROL
	b.lt	.Lenc_main_loop

.Lenc_prepretail:	//	PREPRETAIL
	fmov	d3, x10                               // CTR block 4k+3
	fmov	v3.d[1], x9                               // CTR block 4k+3
	add	w12, w12, #1                            // CTR block 4k+3
	rev64	v6.16b, v6.16b                                    // GHASH block 4k+2 (t0, t1, and t2 free)
	rev64	v4.16b, v4.16b                                    // GHASH block 4k (only t0 is free)
	rev64	v5.16b, v5.16b                                    // GHASH block 4k+1 (t0 and t1 free)
	mov	d10, v17.d[1]                               // GHASH block 4k - mid
	ext	v11.16b, v11.16b, v11.16b, #8                     // PRE 0
	eor	v4.16b, v4.16b, v11.16b                           // PRE 1
	pmull	v11.1q, v4.1d, v15.1d                       // GHASH block 4k - low
	mov	d8, v4.d[1]                                  // GHASH block 4k - mid
	pmull2	v9.1q, v4.2d, v15.2d                       // GHASH block 4k - high
	eor	v8.8b, v8.8b, v4.8b                          // GHASH block 4k - mid
	pmull	v10.1q, v8.1d, v10.1d                      // GHASH block 4k - mid
	pmull2	v4.1q, v5.2d, v14.2d                          // GHASH block 4k+1 - high
	pmull	v8.1q, v5.1d, v14.1d                          // GHASH block 4k+1 - low
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+1 - high
	mov	d4, v5.d[1]                                  // GHASH block 4k+1 - mid
	eor	v11.16b, v11.16b, v8.16b                         // GHASH block 4k+1 - low
	eor	v4.8b, v4.8b, v5.8b                          // GHASH block 4k+1 - mid
	mov	d8, v6.d[1]                                  // GHASH block 4k+2 - mid
	rev64	v7.16b, v7.16b                                    // GHASH block 4k+3 (t0, t1, t2 and t3 free)
	pmull	v4.1q, v4.1d, v17.1d                          // GHASH block 4k+1 - mid
	eor	v8.8b, v8.8b, v6.8b                          // GHASH block 4k+2 - mid
	pmull	v5.1q, v6.1d, v13.1d                          // GHASH block 4k+2 - low
	eor	v10.16b, v10.16b, v4.16b                         // GHASH block 4k+1 - mid
	pmull2	v4.1q, v6.2d, v13.2d                          // GHASH block 4k+2 - high
	eor	v11.16b, v11.16b, v5.16b                         // GHASH block 4k+2 - low
	ins	v8.d[1], v8.d[0]                                // GHASH block 4k+2 - mid
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+2 - high
	mov	d4, v7.d[1]                                  // GHASH block 4k+3 - mid
	pmull2	v8.1q, v8.2d, v16.2d                          // GHASH block 4k+2 - mid
	eor	v4.8b, v4.8b, v7.8b                          // GHASH block 4k+3 - mid
	pmull2	v5.1q, v7.2d, v12.2d                          // GHASH block 4k+3 - high
	pmull	v4.1q, v4.1d, v16.1d                          // GHASH block 4k+3 - mid
	eor	v10.16b, v10.16b, v8.16b                         // GHASH block 4k+2 - mid
	eor	v9.16b, v9.16b, v5.16b                         // GHASH block 4k+3 - high
	movi	v8.8b, #0xc2
	shl	d8, d8, #56               // mod_constant
	eor	v10.16b, v10.16b, v4.16b                         // GHASH block 4k+3 - mid
	pmull	v6.1q, v7.1d, v12.1d                          // GHASH block 4k+3 - low
	eor	v11.16b, v11.16b, v6.16b                         // GHASH block 4k+3 - low
	eor	v10.16b, v10.16b, v9.16b                         // karatsuba tidy up
	pmull	v4.1q, v9.1d, v8.1d
	ext	v9.16b, v9.16b, v9.16b, #8
	eor	v10.16b, v10.16b, v11.16b
	eor	v10.16b, v10.16b, v4.16b
	eor	v10.16b, v10.16b, v9.16b
	pmull	v4.1q, v10.1d, v8.1d
	ext	v10.16b, v10.16b, v10.16b, #8
	eor	v11.16b, v11.16b, v4.16b
	eor	v11.16b, v11.16b, v10.16b
	aese	v1.16b, v18.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 0
	aese	v2.16b, v18.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 0
	aese	v0.16b, v18.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 0
	aese	v2.16b, v19.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 1
	aese	v0.16b, v19.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 1
	aese	v2.16b, v20.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 2
	aese	v3.16b, v18.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 0
	aese	v1.16b, v19.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 1
	aese	v2.16b, v21.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 3
	aese	v1.16b, v20.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 2
	aese	v0.16b, v20.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 2
	aese	v3.16b, v19.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 1
	aese	v1.16b, v21.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 3
	aese	v3.16b, v20.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 2
	aese	v0.16b, v21.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 3
	aese	v3.16b, v21.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 3
	aese	v0.16b, v22.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 4
	aese	v3.16b, v22.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 4
	aese	v3.16b, v23.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 5
	aese	v2.16b, v22.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 4
	aese	v2.16b, v23.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 5
	aese	v1.16b, v22.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 4
	aese	v1.16b, v23.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 5
	aese	v0.16b, v23.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 5
	aese	v1.16b, v24.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 6
	aese	v2.16b, v24.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 6
	aese	v0.16b, v24.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 6
	aese	v3.16b, v24.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 6
	aese	v1.16b, v25.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 7
	aese	v0.16b, v25.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 7
	aese	v3.16b, v25.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 7
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 8
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 8
	cmp	x17, #12                                      // setup flags for AES-128/192/256 check
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 8
	aese	v2.16b, v25.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 7
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 8
	b.lt	.Lenc_finish_prepretail                           // branch if AES-128

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 9
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 9
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 9
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 9
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 10
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 10
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 10
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 10
	b.eq	.Lenc_finish_prepretail                           // branch if AES-192

	aese	v1.16b, v29.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 11
	aese	v0.16b, v29.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 11
	aese	v3.16b, v29.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 11
	aese	v2.16b, v29.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 11
	aese	v1.16b, v30.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 12
	aese	v0.16b, v30.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 12
	aese	v3.16b, v30.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 12
	aese	v2.16b, v30.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 12

.Lenc_finish_prepretail:
	aese	v1.16b, v31.16b                                    // AES block 4k+5 - round N-1
	aese	v3.16b, v31.16b                                    // AES block 4k+7 - round N-1
	aese	v0.16b, v31.16b                                    // AES block 4k+4 - round N-1
	aese	v2.16b, v31.16b                                    // AES block 4k+6 - round N-1

.Lenc_tail:	//	TAIL
	ext	v8.16b, v11.16b, v11.16b, #8                     // prepare final partial tag
	sub	x5, x4, x0   // main_end_input_ptr is number of bytes left to process
	ldp	x6, x7, [x0], #16           // AES block 4k+4 - load plaintext
	eor	x6, x6, x13                      // AES block 4k+4 - round N low
	eor	x7, x7, x14                      // AES block 4k+4 - round N high
	cmp	x5, #48
	fmov	d4, x6                               // AES block 4k+4 - mov low
	fmov	v4.d[1], x7                           // AES block 4k+4 - mov high
	eor	v5.16b, v4.16b, v0.16b                          // AES block 4k+4 - result
	b.gt	.Lenc_blocks_4_remaining
	cmp	x5, #32
	mov	v3.16b, v2.16b
	movi	v11.8b, #0
	movi	v9.8b, #0
	sub	w12, w12, #1
	mov	v2.16b, v1.16b
	movi	v10.8b, #0
	b.gt	.Lenc_blocks_3_remaining
	mov	v3.16b, v1.16b
	sub	w12, w12, #1
	cmp	x5, #16
	b.gt	.Lenc_blocks_2_remaining
	sub	w12, w12, #1
	b	.Lenc_blocks_1_remaining
.Lenc_blocks_4_remaining:	//	blocks left = 4
	st1	{ v5.16b}, [x2], #16                    // AES final-3 block  - store result
	rev64	v4.16b, v5.16b                                   // GHASH final-3 block
	eor	v4.16b, v4.16b, v8.16b                          // feed in partial tag
	mov	d22, v4.d[1]                                // GHASH final-3 block - mid
	eor	v22.8b, v22.8b, v4.8b                     // GHASH final-3 block - mid
	mov	d10, v17.d[1]                              // GHASH final-3 block - mid
	pmull	v11.1q, v4.1d, v15.1d                      // GHASH final-3 block - low
	pmull2	v9.1q, v4.2d, v15.2d                      // GHASH final-3 block - high
	pmull	v10.1q, v22.1d, v10.1d                   // GHASH final-3 block - mid
	movi	v8.8b, #0                                       // suppress further partial tag feed in
	ldp	x6, x7, [x0], #16          // AES final-2 block - load input low & high
	eor	x6, x6, x13                     // AES final-2 block - round N low
	eor	x7, x7, x14                     // AES final-2 block - round N high
	fmov	d5, x6                                // AES final-2 block - mov low
	fmov	v5.d[1], x7                            // AES final-2 block - mov high
	eor	v5.16b, v5.16b, v1.16b                           // AES final-2 block - result
.Lenc_blocks_3_remaining:	//	blocks left = 3
	st1	{ v5.16b}, [x2], #16                    // AES final-2 block - store result
	rev64	v4.16b, v5.16b                                   // GHASH final-2 block
	eor	v4.16b, v4.16b, v8.16b                          // feed in partial tag
	pmull2	v20.1q, v4.2d, v14.2d                         // GHASH final-2 block - high
	mov	d22, v4.d[1]                                // GHASH final-2 block - mid
	pmull	v21.1q, v4.1d, v14.1d                         // GHASH final-2 block - low
	eor	v22.8b, v22.8b, v4.8b                     // GHASH final-2 block - mid
	eor	v9.16b, v9.16b, v20.16b                           // GHASH final-2 block - high
	pmull	v22.1q, v22.1d, v17.1d                     // GHASH final-2 block - mid
	eor	v11.16b, v11.16b, v21.16b                           // GHASH final-2 block - low
	eor	v10.16b, v10.16b, v22.16b                      // GHASH final-2 block - mid
	movi	v8.8b, #0                                       // suppress further partial tag feed in
	ldp	x6, x7, [x0], #16          // AES final-1 block - load input low & high
	eor	x6, x6, x13                     // AES final-1 block - round N low
	fmov	d5, x6                                // AES final-1 block - mov low
	eor	x7, x7, x14                     // AES final-1 block - round N high
	fmov	v5.d[1], x7                            // AES final-1 block - mov high
	eor	v5.16b, v5.16b, v2.16b                           // AES final-1 block - result
.Lenc_blocks_2_remaining:	//	blocks left = 2
	st1	{ v5.16b}, [x2], #16                    // AES final-1 block - store result
	rev64	v4.16b, v5.16b                                   // GHASH final-1 block
	eor	v4.16b, v4.16b, v8.16b                          // feed in partial tag
	mov	d22, v4.d[1]                                // GHASH final-1 block - mid
	pmull2	v20.1q, v4.2d, v13.2d                         // GHASH final-1 block - high
	eor	v22.8b, v22.8b, v4.8b                     // GHASH final-1 block - mid
	eor	v9.16b, v9.16b, v20.16b                           // GHASH final-1 block - high
	ins	v22.d[1], v22.d[0]                           // GHASH final-1 block - mid
	pmull2	v22.1q, v22.2d, v16.2d                     // GHASH final-1 block - mid
	pmull	v21.1q, v4.1d, v13.1d                         // GHASH final-1 block - low
	eor	v10.16b, v10.16b, v22.16b                      // GHASH final-1 block - mid
	eor	v11.16b, v11.16b, v21.16b                           // GHASH final-1 block - low
	movi	v8.8b, #0                                       // suppress further partial tag feed in
	ldp	x6, x7, [x0], #16          // AES final block - load input low & high
	eor	x6, x6, x13                     // AES final block - round N low
	eor	x7, x7, x14                     // AES final block - round N high
	fmov	d5, x6                                // AES final block - mov low
	fmov	v5.d[1], x7                            // AES final block - mov high
	eor	v5.16b, v5.16b, v3.16b                           // AES final block - result
.Lenc_blocks_1_remaining:	//	blocks_left = 1
	rev64	v4.16b, v5.16b                                   // GHASH final block
	eor	v4.16b, v4.16b, v8.16b                          // feed in partial tag
	pmull2	v20.1q, v4.2d, v12.2d                         // GHASH final block - high
	mov	d8, v4.d[1]                                 // GHASH final block - mid
	pmull	v21.1q, v4.1d, v12.1d                         // GHASH final block - low
	eor	v9.16b, v9.16b, v20.16b                           // GHASH final block - high
	eor	v8.8b, v8.8b, v4.8b                         // GHASH final block - mid
	pmull	v8.1q, v8.1d, v16.1d                         // GHASH final block - mid
	eor	v11.16b, v11.16b, v21.16b                           // GHASH final block - low
	eor	v10.16b, v10.16b, v8.16b                        // GHASH final block - mid
	movi	v8.8b, #0xc2
	eor	v4.16b, v11.16b, v9.16b                        // MODULO - karatsuba tidy up
	shl	d8, d8, #56              // mod_constant
	eor	v10.16b, v10.16b, v4.16b                        // MODULO - karatsuba tidy up
	pmull	v7.1q, v9.1d, v8.1d           // MODULO - top 64b align with mid
	ext	v9.16b, v9.16b, v9.16b, #8                    // MODULO - other top alignment
	eor	v10.16b, v10.16b, v7.16b                     // MODULO - fold into mid
	eor	v10.16b, v10.16b, v9.16b                        // MODULO - fold into mid
	pmull	v9.1q, v10.1d, v8.1d           // MODULO - mid 64b align with low
	ext	v10.16b, v10.16b, v10.16b, #8                    // MODULO - other mid alignment
	eor	v11.16b, v11.16b, v9.16b                        // MODULO - fold into low
	eor	v11.16b, v11.16b, v10.16b                        // MODULO - fold into low
	ext	v11.16b, v11.16b, v11.16b, #8
	rev64	v11.16b, v11.16b

	rev	w9, w12
	str	w9, [x16, #12]                         // store the updated counter
	st1	{ v5.16b}, [x2]                         // store all 16B

	mov	x0, x15
	st1	{ v11.16b }, [x3]
	ldp	x19, x20, [sp, #16]
	ldp	x21, x22, [sp, #32]
	ldp	x23, x24, [sp, #48]
	ldp	d8, d9, [sp, #64]
	ldp	d10, d11, [sp, #80]
	ldp	d12, d13, [sp, #96]
	ldp	d14, d15, [sp, #112]
	ldp	x29, x30, [sp], #128
	AARCH64_VALIDATE_LINK_REGISTER
	ret
.size	aes_gcm_enc_kernel_deinterleaved,.-aes_gcm_enc_kernel_deinterleaved
.globl	aes_gcm_dec_kernel_deinterleaved
.hidden	aes_gcm_dec_kernel_deinterleaved
.type	aes_gcm_dec_kernel_deinterleaved,%function
.align	4
aes_gcm_dec_kernel_deinterleaved:
	AARCH64_SIGN_LINK_REGISTER
	stp	x29, x30, [sp, #-128]!
	mov	x29, sp
	stp	x19, x20, [sp, #16]
	mov	x16, x4
	mov	x8, x5
	stp	x21, x22, [sp, #32]
	stp	x23, x24, [sp, #48]
	stp	d8, d9, [sp, #64]
	stp	d10, d11, [sp, #80]
	stp	d12, d13, [sp, #96]
	stp	d14, d15, [sp, #112]
	ldr	w17, [x8, #240]
	add	x19, x8, x17, lsl #4                   // borrow input_l1 for last key
	ldp	x13, x14, [x19]                       // load round N keys
	ldr	q31, [x19, #-16]                        // load round N-1 keys
	lsr	x5, x1, #3              // byte_len
	mov	x15, x5
	ldp	x10, x11, [x16]              // ctr96_b64, ctr96_t32
	ldr	q18, [x8, #0]                                  // load rk0
	ldr	q19, [x8, #16]                                 // load rk1
	ldr	q20, [x8, #32]                                 // load rk2
	ldr	q21, [x8, #48]                                 // load rk3
	ldr	q22, [x8, #64]                                 // load rk4
	ldr	q23, [x8, #80]                                 // load rk5
	ldr	q24, [x8, #96]                                 // load rk6
	ldr	q25, [x8, #112]                                // load rk7
	ldr	q26, [x8, #128]                                // load rk8
	ldr	q27, [x8, #144]                                // load rk9
	ldr	q28, [x8, #160]                               // load rk10
	ldr	q29, [x8, #176]                               // load rk11
	ldr	q30, [x8, #192]                               // load rk12
	sub	x5, x5, #1      // byte_len - 1
	and	x5, x5, #0xffffffffffffffc0 // number of bytes to be processed in main loop (at least 1 byte must be handled by tail)
	add	x4, x0, x1, lsr #3   // end_input_ptr
	lsr	x12, x11, #32
	orr	w11, w11, w11
	add	x5, x5, x0
	rev	w12, w12                                // rev_ctr32
	add	w12, w12, #1                            // increment rev_ctr32
	fmov	d3, x10                               // CTR block 3
	rev	w9, w12                                 // CTR block 1
	add	w12, w12, #1                            // CTR block 1
	fmov	d1, x10                               // CTR block 1
	orr	x9, x11, x9, lsl #32            // CTR block 1
	ld1	{ v0.16b}, [x16]                             // special case vector load initial counter so we can start first AES block as quickly as possible
	fmov	v1.d[1], x9                               // CTR block 1
	rev	w9, w12                                 // CTR block 2
	add	w12, w12, #1                            // CTR block 2
	fmov	d2, x10                               // CTR block 2
	orr	x9, x11, x9, lsl #32            // CTR block 2
	fmov	v2.d[1], x9                               // CTR block 2
	rev	w9, w12                                 // CTR block 3
	orr	x9, x11, x9, lsl #32            // CTR block 3
	fmov	v3.d[1], x9                               // CTR block 3
	add	w12, w12, #1                            // CTR block 3

	aese	v0.16b, v18.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 0
	aese	v3.16b, v18.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 0
	aese	v1.16b, v18.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 0
	aese	v2.16b, v18.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 0
	aese	v0.16b, v19.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 1
	aese	v1.16b, v19.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 1
	aese	v2.16b, v19.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 1
	aese	v3.16b, v19.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 1
	aese	v0.16b, v20.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 2
	aese	v2.16b, v20.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 2
	aese	v3.16b, v20.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 2
	aese	v0.16b, v21.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 3
	aese	v1.16b, v20.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 2
	aese	v3.16b, v21.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 3
	aese	v0.16b, v22.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 4
	aese	v2.16b, v21.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 3
	aese	v1.16b, v21.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 3
	aese	v3.16b, v22.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 4
	aese	v2.16b, v22.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 4
	aese	v1.16b, v22.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 4
	aese	v3.16b, v23.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 5
	aese	v0.16b, v23.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 5
	aese	v1.16b, v23.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 5
	aese	v2.16b, v23.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 5
	aese	v0.16b, v24.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 6
	aese	v3.16b, v24.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 6
	cmp	x17, #12                                      // setup flags for AES-128/192/256 check
	aese	v1.16b, v24.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 6
	aese	v2.16b, v24.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 6
	aese	v0.16b, v25.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 7
	aese	v1.16b, v25.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 7
	aese	v3.16b, v25.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 7
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 8
	aese	v2.16b, v25.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 7
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 8
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 8
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 8
	b.lt	.Ldec_finish_first_blocks                         // branch if AES-128

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 9
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 9
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 9
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 9
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 10
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 10
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 10
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 10
	b.eq	.Ldec_finish_first_blocks                         // branch if AES-192

	aese	v0.16b, v29.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 11
	aese	v3.16b, v29.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 11
	aese	v1.16b, v29.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 11
	aese	v2.16b, v29.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 11
	aese	v1.16b, v30.16b
	aesmc	v1.16b, v1.16b          // AES block 1 - round 12
	aese	v0.16b, v30.16b
	aesmc	v0.16b, v0.16b          // AES block 0 - round 12
	aese	v2.16b, v30.16b
	aesmc	v2.16b, v2.16b          // AES block 2 - round 12
	aese	v3.16b, v30.16b
	aesmc	v3.16b, v3.16b          // AES block 3 - round 12

.Ldec_finish_first_blocks:

	aese	v1.16b, v31.16b                                    // AES block 1 - round N-1
	aese	v2.16b, v31.16b                                    // AES block 2 - round N-1
	aese	v3.16b, v31.16b                                    // AES block 3 - round N-1
	aese	v0.16b, v31.16b                                    // AES block 0 - round N-1

	ldr	q12, [x6]                                   // load h1l | h1h
	ext	v12.16b, v12.16b, v12.16b, #8
	ldr	q13, [x6, #32]                              // load h2l | h2h
	ext	v13.16b, v13.16b, v13.16b, #8
	ldr	q14, [x6, #48]                              // load h3l | h3h
	ext	v14.16b, v14.16b, v14.16b, #8
	ldr	q15, [x6, #80]                              // load h4l | h4h
	ext	v15.16b, v15.16b, v15.16b, #8

	trn1	v9.2d, v14.2d,    v15.2d                      // h4h | h3h
	trn2	v17.2d,  v14.2d,    v15.2d                      // h4l | h3l
	trn1	v8.2d,    v12.2d,    v13.2d                      // h2h | h1h
	trn2	v16.2d,  v12.2d,    v13.2d                      // h2l | h1l
	eor	v17.16b, v17.16b, v9.16b                  // h4k | h3k
	eor	v16.16b, v16.16b, v8.16b                     // h2k | h1k

	ld1	{ v11.16b}, [x3]
	ext	v11.16b, v11.16b, v11.16b, #8
	rev64	v11.16b, v11.16b

	cmp	x0, x5                   // check if we have <= 4 blocks
	b.ge	.Ldec_tail                                        // handle tail

	ldr	q4, [x0, #0]                          // AES block 0 - load ciphertext
	eor	v0.16b, v4.16b, v0.16b                            // AES block 0 - result
	mov	x7, v0.d[1]                            // AES block 0 - mov high
	mov	x6, v0.d[0]                            // AES block 0 - mov low
	eor	x7, x7, x14                    // AES block 0 - round N high
	eor	x6, x6, x13                    // AES block 0 - round N low
	stp	x6, x7, [x2], #16        // AES block 0 - store result
	ldr	q5, [x0, #16]                         // AES block 1 - load ciphertext
	eor	v1.16b, v5.16b, v1.16b                            // AES block 1 - result
	mov	x19, v1.d[0]                            // AES block 1 - mov low
	mov	x20, v1.d[1]                            // AES block 1 - mov high
	eor	x19, x19, x13                    // AES block 1 - round N low
	eor	x20, x20, x14                    // AES block 1 - round N high
	stp	x19, x20, [x2], #16        // AES block 1 - store result
	ldr	q6, [x0, #32]                         // AES block 2 - load ciphertext
	eor	v2.16b, v6.16b, v2.16b                            // AES block 2 - result
	ldr	q7, [x0, #48]                         // AES block 3 - load ciphertext

	add	x0, x0, #64                       // AES input_ptr update

	rev64	v4.16b, v4.16b                                    // GHASH block 0
	rev64	v5.16b, v5.16b                                    // GHASH block 1

	rev	w9, w12                                 // CTR block 4
	add	w12, w12, #1                            // CTR block 4
	fmov	d0, x10                               // CTR block 4
	orr	x9, x11, x9, lsl #32            // CTR block 4
	fmov	v0.d[1], x9                               // CTR block 4
	rev	w9, w12                                 // CTR block 5
	add	w12, w12, #1                            // CTR block 5
	orr	x9, x11, x9, lsl #32            // CTR block 5
	fmov	d1, x10                               // CTR block 5
	fmov	v1.d[1], x9                               // CTR block 5
	rev	w9, w12                                 // CTR block 6
	add	w12, w12, #1                            // CTR block 6
	orr	x9, x11, x9, lsl #32            // CTR block 6

	cmp	x0, x5                   // check if we have <= 8 blocks
	b.ge	.Ldec_prepretail                                  // do prepretail

.Ldec_main_loop:	//	main loop start
	mov	x21, v2.d[0]                            // AES block 4k+2 - mov low
	mov	x22, v2.d[1]                            // AES block 4k+2 - mov high
	eor	x22, x22, x14                    // AES block 4k+2 - round N high
	eor	x21, x21, x13                    // AES block 4k+2 - round N low
	stp	x21, x22, [x2], #16        // AES block 4k+2 - store result
	eor	v3.16b, v7.16b, v3.16b                            // AES block 4k+3 - result
	mov	x24, v3.d[1]                            // AES block 4k+3 - mov high
	mov	x23, v3.d[0]                            // AES block 4k+3 - mov low

	ext	v11.16b, v11.16b, v11.16b, #8                     // PRE 0
	eor	v4.16b, v4.16b, v11.16b                           // PRE 1
	pmull2	v9.1q, v4.2d, v15.2d                       // GHASH block 4k - high
	mov	d8, v4.d[1]                                  // GHASH block 4k - mid
	eor	v8.8b, v8.8b, v4.8b                          // GHASH block 4k - mid
	mov	d10, v17.d[1]                               // GHASH block 4k - mid
	rev64	v6.16b, v6.16b                                    // GHASH block 4k+2
	pmull	v11.1q, v4.1d, v15.1d                       // GHASH block 4k - low
	pmull2	v4.1q, v5.2d, v14.2d                          // GHASH block 4k+1 - high
	rev64	v7.16b, v7.16b                                    // GHASH block 4k+3
	pmull	v10.1q, v8.1d, v10.1d                      // GHASH block 4k - mid
	pmull	v8.1q, v5.1d, v14.1d                          // GHASH block 4k+1 - low
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+1 - high
	mov	d4, v5.d[1]                                  // GHASH block 4k+1 - mid
	eor	v11.16b, v11.16b, v8.16b                         // GHASH block 4k+1 - low
	mov	d8, v6.d[1]                                  // GHASH block 4k+2 - mid
	eor	v4.8b, v4.8b, v5.8b                          // GHASH block 4k+1 - mid
	pmull	v5.1q, v6.1d, v13.1d                          // GHASH block 4k+2 - low
	eor	v8.8b, v8.8b, v6.8b                          // GHASH block 4k+2 - mid
	eor	v11.16b, v11.16b, v5.16b                         // GHASH block 4k+2 - low
	pmull	v4.1q, v4.1d, v17.1d                          // GHASH block 4k+1 - mid
	ins	v8.d[1], v8.d[0]                                // GHASH block 4k+2 - mid
	eor	v10.16b, v10.16b, v4.16b                         // GHASH block 4k+1 - mid
	pmull2	v4.1q, v6.2d, v13.2d                          // GHASH block 4k+2 - high
	mov	d6, v7.d[1]                                  // GHASH block 4k+3 - mid
	pmull2	v8.1q, v8.2d, v16.2d                          // GHASH block 4k+2 - mid
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+2 - high
	pmull	v4.1q, v7.1d, v12.1d                          // GHASH block 4k+3 - low
	eor	v10.16b, v10.16b, v8.16b                         // GHASH block 4k+2 - mid
	pmull2	v5.1q, v7.2d, v12.2d                          // GHASH block 4k+3 - high
	eor	v6.8b, v6.8b, v7.8b                          // GHASH block 4k+3 - mid
	eor	v9.16b, v9.16b, v5.16b                         // GHASH block 4k+3 - high
	pmull	v6.1q, v6.1d, v16.1d                          // GHASH block 4k+3 - mid
	movi	v8.8b, #0xc2
	eor	v11.16b, v11.16b, v4.16b                         // GHASH block 4k+3 - low
	shl	d8, d8, #56               // mod_constant
	eor	v10.16b, v10.16b, v6.16b                         // GHASH block 4k+3 - mid
	pmull	v7.1q, v9.1d, v8.1d            // MODULO - top 64b align with mid
	eor	v6.16b, v11.16b, v9.16b                         // MODULO - karatsuba tidy up
	ext	v9.16b, v9.16b, v9.16b, #8                     // MODULO - other top alignment
	eor	v10.16b, v10.16b, v6.16b                         // MODULO - karatsuba tidy up
	eor	v10.16b, v10.16b, v7.16b                      // MODULO - fold into mid
	eor	v10.16b, v10.16b, v9.16b                         // MODULO - fold into mid
	pmull	v8.1q, v10.1d, v8.1d     // MODULO - mid 64b align with low
	eor	v11.16b, v11.16b, v8.16b               // MODULO - fold into low
	ext	v10.16b, v10.16b, v10.16b, #8                     // MODULO - other mid alignment
	eor	v11.16b, v11.16b, v10.16b                         // MODULO - fold into low

	fmov	d2, x10                               // CTR block 4k+6
	fmov	v2.d[1], x9                               // CTR block 4k+6
	rev	w9, w12                                 // CTR block 4k+7
	fmov	d3, x10                               // CTR block 4k+7
	orr	x9, x11, x9, lsl #32            // CTR block 4k+7
	fmov	v3.d[1], x9                               // CTR block 4k+7
	add	w12, w12, #1                            // CTR block 4k+7

	aese	v0.16b, v18.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 0
	aese	v1.16b, v18.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 0
	aese	v0.16b, v19.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 1
	aese	v1.16b, v19.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 1
	aese	v0.16b, v20.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 2
	aese	v2.16b, v18.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 0
	aese	v1.16b, v20.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 2
	aese	v0.16b, v21.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 3
	aese	v2.16b, v19.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 1
	aese	v1.16b, v21.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 3
	aese	v3.16b, v18.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 0
	aese	v2.16b, v20.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 2
	aese	v2.16b, v21.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 3
	eor	x23, x23, x13                    // AES block 4k+3 - round N low
	eor	x24, x24, x14                    // AES block 4k+3 - round N high
	aese	v2.16b, v22.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 4
	aese	v3.16b, v19.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 1
	aese	v0.16b, v22.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 4
	aese	v2.16b, v23.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 5
	aese	v3.16b, v20.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 2
	aese	v1.16b, v22.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 4
	aese	v3.16b, v21.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 3
	aese	v1.16b, v23.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 5
	aese	v0.16b, v23.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 5
	aese	v1.16b, v24.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 6
	aese	v0.16b, v24.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 6
	aese	v3.16b, v22.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 4
	aese	v1.16b, v25.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 7
	aese	v0.16b, v25.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 7
	aese	v3.16b, v23.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 5
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 8
	aese	v3.16b, v24.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 6
	cmp	x17, #12                                      // setup flags for AES-128/192/256 check
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 8
	aese	v2.16b, v24.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 6
	aese	v2.16b, v25.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 7
	aese	v3.16b, v25.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 7
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 8
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 8
	b.lt	.Ldec_main_loop_continue                          // branch if AES-128

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 9
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 9
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 9
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 9
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 10
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 10
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 10
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 10
	b.eq	.Ldec_main_loop_continue                          // branch if AES-192

	aese	v0.16b, v29.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 11
	aese	v1.16b, v29.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 11
	aese	v2.16b, v29.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 11
	aese	v3.16b, v29.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 11
	aese	v0.16b, v30.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 12
	aese	v1.16b, v30.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 12
	aese	v2.16b, v30.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 12
	aese	v3.16b, v30.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 12

.Ldec_main_loop_continue:

	ldr	q4, [x0, #0]                          // AES block 4k+4 - load ciphertext
	aese	v0.16b, v31.16b                                    // AES block 4k+4 - round N-1
	ldr	q5, [x0, #16]                         // AES block 4k+5 - load ciphertext
	eor	v0.16b, v4.16b, v0.16b                            // AES block 4k+4 - result
	stp	x23, x24, [x2], #16        // AES block 4k+3 - store result
	ldr	q7, [x0, #48]                         // AES block 4k+7 - load ciphertext
	ldr	q6, [x0, #32]                         // AES block 4k+6 - load ciphertext
	mov	x7, v0.d[1]                            // AES block 4k+4 - mov high
	aese	v1.16b, v31.16b                                    // AES block 4k+5 - round N-1
	add	x0, x0, #64                       // AES input_ptr update
	mov	x6, v0.d[0]                            // AES block 4k+4 - mov low
	eor	v1.16b, v5.16b, v1.16b                            // AES block 4k+5 - result
	aese	v2.16b, v31.16b                                    // AES block 4k+6 - round N-1
	eor	x6, x6, x13                    // AES block 4k+4 - round N low
	eor	x7, x7, x14                    // AES block 4k+4 - round N high
	mov	x20, v1.d[1]                            // AES block 4k+5 - mov high
	eor	v2.16b, v6.16b, v2.16b                            // AES block 4k+6 - result
	mov	x19, v1.d[0]                            // AES block 4k+5 - mov low
	aese	v3.16b, v31.16b                                    // AES block 4k+7 - round N-1
	eor	x20, x20, x14                    // AES block 4k+5 - round N high
	stp	x6, x7, [x2], #16        // AES block 4k+4 - store result
	eor	x19, x19, x13                    // AES block 4k+5 - round N low
	stp	x19, x20, [x2], #16        // AES block 4k+5 - store result

	rev64	v5.16b, v5.16b                                    // GHASH block 4k+5
	rev64	v4.16b, v4.16b                                    // GHASH block 4k+4

	rev	w9, w12                                 // CTR block 4k+8
	add	w12, w12, #1                            // CTR block 4k+8
	orr	x9, x11, x9, lsl #32            // CTR block 4k+8
	fmov	d0, x10                               // CTR block 4k+8
	fmov	v0.d[1], x9                               // CTR block 4k+8
	rev	w9, w12                                 // CTR block 4k+9
	orr	x9, x11, x9, lsl #32            // CTR block 4k+9
	add	w12, w12, #1                            // CTR block 4k+9
	fmov	d1, x10                               // CTR block 4k+9
	fmov	v1.d[1], x9                               // CTR block 4k+9
	rev	w9, w12                                 // CTR block 4k+10
	add	w12, w12, #1                            // CTR block 4k+10
	orr	x9, x11, x9, lsl #32            // CTR block 4k+10

	cmp	x0, x5                   // .LOOP CONTROL
	b.lt	.Ldec_main_loop

.Ldec_prepretail:	//	PREPRETAIL

	mov	x21, v2.d[0]                            // AES block 4k+2 - mov low
	mov	x22, v2.d[1]                            // AES block 4k+2 - mov high
	eor	x22, x22, x14                    // AES block 4k+2 - round N high
	eor	x21, x21, x13                    // AES block 4k+2 - round N low
	stp	x21, x22, [x2], #16        // AES block 4k+2 - store result
	eor	v3.16b, v7.16b, v3.16b                            // AES block 4k+3 - result
	mov	x23, v3.d[0]                            // AES block 4k+3 - mov low
	mov	x24, v3.d[1]                            // AES block 4k+3 - mov high
	eor	x23, x23, x13                    // AES block 4k+3 - round N low
	eor	x24, x24, x14                    // AES block 4k+3 - round N high
	stp	x23, x24, [x2], #16        // AES block 4k+3 - store result

	ext	v11.16b, v11.16b, v11.16b, #8                     // PRE 0
	eor	v4.16b, v4.16b, v11.16b                           // PRE 1
	rev64	v6.16b, v6.16b                                    // GHASH block 4k+2
	pmull	v11.1q, v4.1d, v15.1d                       // GHASH block 4k - low
	mov	d8, v4.d[1]                                  // GHASH block 4k - mid
	pmull2	v9.1q, v4.2d, v15.2d                       // GHASH block 4k - high
	mov	d10, v17.d[1]                               // GHASH block 4k - mid
	eor	v8.8b, v8.8b, v4.8b                          // GHASH block 4k - mid
	pmull2	v4.1q, v5.2d, v14.2d                          // GHASH block 4k+1 - high
	rev64	v7.16b, v7.16b                                    // GHASH block 4k+3
	pmull	v10.1q, v8.1d, v10.1d                      // GHASH block 4k - mid
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+1 - high
	pmull	v8.1q, v5.1d, v14.1d                          // GHASH block 4k+1 - low
	mov	d4, v5.d[1]                                  // GHASH block 4k+1 - mid
	eor	v11.16b, v11.16b, v8.16b                         // GHASH block 4k+1 - low
	mov	d8, v6.d[1]                                  // GHASH block 4k+2 - mid
	eor	v4.8b, v4.8b, v5.8b                          // GHASH block 4k+1 - mid
	pmull	v5.1q, v6.1d, v13.1d                          // GHASH block 4k+2 - low
	eor	v8.8b, v8.8b, v6.8b                          // GHASH block 4k+2 - mid
	pmull	v4.1q, v4.1d, v17.1d                          // GHASH block 4k+1 - mid
	eor	v11.16b, v11.16b, v5.16b                         // GHASH block 4k+2 - low
	pmull2	v5.1q, v7.2d, v12.2d                          // GHASH block 4k+3 - high
	eor	v10.16b, v10.16b, v4.16b                         // GHASH block 4k+1 - mid
	pmull2	v4.1q, v6.2d, v13.2d                          // GHASH block 4k+2 - high
	ins	v8.d[1], v8.d[0]                                // GHASH block 4k+2 - mid
	eor	v9.16b, v9.16b, v4.16b                         // GHASH block 4k+2 - high
	pmull	v4.1q, v7.1d, v12.1d                          // GHASH block 4k+3 - low
	mov	d6, v7.d[1]                                  // GHASH block 4k+3 - mid
	pmull2	v8.1q, v8.2d, v16.2d                          // GHASH block 4k+2 - mid
	eor	v6.8b, v6.8b, v7.8b                          // GHASH block 4k+3 - mid
	eor	v10.16b, v10.16b, v8.16b                         // GHASH block 4k+2 - mid
	eor	v11.16b, v11.16b, v4.16b                         // GHASH block 4k+3 - low
	pmull	v6.1q, v6.1d, v16.1d                          // GHASH block 4k+3 - mid
	eor	v9.16b, v9.16b, v5.16b                         // GHASH block 4k+3 - high
	eor	v10.16b, v10.16b, v6.16b                         // GHASH block 4k+3 - mid
	eor	v6.16b, v11.16b, v9.16b                         // MODULO - karatsuba tidy up
	movi	v8.8b, #0xc2
	shl	d8, d8, #56               // mod_constant
	eor	v10.16b, v10.16b, v6.16b                         // MODULO - karatsuba tidy up
	pmull	v7.1q, v9.1d, v8.1d            // MODULO - top 64b align with mid
	ext	v9.16b, v9.16b, v9.16b, #8                     // MODULO - other top alignment
	eor	v10.16b, v10.16b, v7.16b                      // MODULO - fold into mid
	eor	v10.16b, v10.16b, v9.16b                         // MODULO - fold into mid
	pmull	v8.1q, v10.1d, v8.1d     // MODULO - mid 64b align with low
	ext	v10.16b, v10.16b, v10.16b, #8                     // MODULO - other mid alignment
	eor	v11.16b, v11.16b, v8.16b               // MODULO - fold into low
	eor	v11.16b, v11.16b, v10.16b                         // MODULO - fold into low

	fmov	d2, x10                               // CTR block 4k+6
	fmov	v2.d[1], x9                               // CTR block 4k+6
	rev	w9, w12                                 // CTR block 4k+7
	orr	x9, x11, x9, lsl #32            // CTR block 4k+7
	fmov	d3, x10                               // CTR block 4k+7
	fmov	v3.d[1], x9                               // CTR block 4k+7
	add	w12, w12, #1                            // CTR block 4k+7

	aese	v0.16b, v18.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 0
	aese	v0.16b, v19.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 1
	aese	v1.16b, v18.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 0
	aese	v1.16b, v19.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 1
	aese	v2.16b, v18.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 0
	aese	v2.16b, v19.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 1
	aese	v3.16b, v18.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 0
	aese	v3.16b, v19.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 1
	aese	v0.16b, v20.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 2
	aese	v1.16b, v20.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 2
	aese	v2.16b, v20.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 2
	aese	v0.16b, v21.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 3
	aese	v3.16b, v20.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 2
	aese	v0.16b, v22.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 4
	aese	v3.16b, v21.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 3
	aese	v0.16b, v23.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 5
	aese	v3.16b, v22.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 4
	aese	v3.16b, v23.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 5
	aese	v2.16b, v21.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 3
	aese	v1.16b, v21.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 3
	aese	v2.16b, v22.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 4
	aese	v1.16b, v22.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 4
	aese	v2.16b, v23.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 5
	aese	v1.16b, v23.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 5
	aese	v3.16b, v24.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 6
	aese	v2.16b, v24.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 6
	aese	v0.16b, v24.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 6
	aese	v1.16b, v24.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 6
	aese	v3.16b, v25.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 7
	aese	v1.16b, v25.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 7
	aese	v0.16b, v25.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 7
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 8
	aese	v2.16b, v25.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 7
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 8
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 8
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 8

	cmp	x17, #12                                      // setup flags for AES-128/192/256 check
	b.lt	.Ldec_finish_prepretail                           // branch if AES-128

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 9
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 9
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 9
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 9
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 10
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 10
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 10
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 10
	b.eq	.Ldec_finish_prepretail                           // branch if AES-192

	aese	v2.16b, v29.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 11
	aese	v0.16b, v29.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 11
	aese	v1.16b, v29.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 11
	aese	v2.16b, v30.16b
	aesmc	v2.16b, v2.16b          // AES block 4k+6 - round 12
	aese	v3.16b, v29.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 11
	aese	v1.16b, v30.16b
	aesmc	v1.16b, v1.16b          // AES block 4k+5 - round 12
	aese	v0.16b, v30.16b
	aesmc	v0.16b, v0.16b          // AES block 4k+4 - round 12
	aese	v3.16b, v30.16b
	aesmc	v3.16b, v3.16b          // AES block 4k+7 - round 12

.Ldec_finish_prepretail:
	aese	v1.16b, v31.16b                                    // AES block 4k+5 - round N-1
	aese	v0.16b, v31.16b                                    // AES block 4k+4 - round N-1
	aese	v3.16b, v31.16b                                    // AES block 4k+7 - round N-1
	aese	v2.16b, v31.16b                                    // AES block 4k+6 - round N-1

.Ldec_tail:	//	TAIL
	sub	x5, x4, x0   // main_end_input_ptr is number of bytes left to process
	ld1	{ v5.16b}, [x0], #16                      // AES block 4k+4 - load ciphertext
	eor	v0.16b, v5.16b, v0.16b                            // AES block 4k+4 - result
	mov	x6, v0.d[0]                            // AES block 4k+4 - mov low
	mov	x7, v0.d[1]                            // AES block 4k+4 - mov high
	ext	v8.16b, v11.16b, v11.16b, #8                     // prepare final partial tag
	eor	x6, x6, x13                    // AES block 4k+4 - round N low
	eor	x7, x7, x14                    // AES block 4k+4 - round N high

	cmp	x5, #48
	b.gt	.Ldec_blocks_4_remaining
	sub	w12, w12, #1
	mov	v3.16b, v2.16b
	movi	v10.8b, #0
	movi	v11.8b, #0
	cmp	x5, #32
	movi	v9.8b, #0
	mov	v2.16b, v1.16b
	b.gt	.Ldec_blocks_3_remaining
	sub	w12, w12, #1
	mov	v3.16b, v1.16b
	cmp	x5, #16
	b.gt	.Ldec_blocks_2_remaining
	sub	w12, w12, #1
	b	.Ldec_blocks_1_remaining
.Ldec_blocks_4_remaining:	//	blocks left = 4
	stp	x6, x7, [x2], #16       // AES final-3 block  - store result
	rev64	v4.16b, v5.16b                                   // GHASH final-3 block
	mov	d10, v17.d[1]                              // GHASH final-3 block - mid
	eor	v4.16b, v4.16b, v8.16b                          // feed in partial tag
	mov	d22, v4.d[1]                                // GHASH final-3 block - mid
	eor	v22.8b, v22.8b, v4.8b                     // GHASH final-3 block - mid
	movi	v8.8b, #0                                       // suppress further partial tag feed in
	pmull2	v9.1q, v4.2d, v15.2d                      // GHASH final-3 block - high
	pmull	v10.1q, v22.1d, v10.1d                   // GHASH final-3 block - mid
	pmull	v11.1q, v4.1d, v15.1d                      // GHASH final-3 block - low

	ld1	{ v5.16b}, [x0], #16                     // AES final-2 block - load ciphertext
	eor	v0.16b, v5.16b, v1.16b                           // AES final-2 block - result
	mov	x6, v0.d[0]                           // AES final-2 block - mov low
	mov	x7, v0.d[1]                           // AES final-2 block - mov high
	eor	x6, x6, x13                   // AES final-2 block - round N low
	eor	x7, x7, x14                   // AES final-2 block - round N high
.Ldec_blocks_3_remaining:	//	blocks left = 3
	stp	x6, x7, [x2], #16       // AES final-2 block  - store result
	rev64	v4.16b, v5.16b                                   // GHASH final-2 block
	eor	v4.16b, v4.16b, v8.16b                          // feed in partial tag
	mov	d22, v4.d[1]                                // GHASH final-2 block - mid
	pmull	v21.1q, v4.1d, v14.1d                         // GHASH final-2 block - low
	pmull2	v20.1q, v4.2d, v14.2d                         // GHASH final-2 block - high
	eor	v22.8b, v22.8b, v4.8b                     // GHASH final-2 block - mid
	eor	v11.16b, v11.16b, v21.16b                           // GHASH final-2 block - low
	movi	v8.8b, #0                                       // suppress further partial tag feed in
	pmull	v22.1q, v22.1d, v17.1d                     // GHASH final-2 block - mid
	eor	v9.16b, v9.16b, v20.16b                           // GHASH final-2 block - high
	eor	v10.16b, v10.16b, v22.16b                      // GHASH final-2 block - mid
	ld1	{ v5.16b}, [x0], #16                     // AES final-1 block - load ciphertext
	eor	v0.16b, v5.16b, v2.16b                           // AES final-1 block - result
	mov	x6, v0.d[0]                           // AES final-1 block - mov low
	mov	x7, v0.d[1]                           // AES final-1 block - mov high
	eor	x6, x6, x13                   // AES final-1 block - round N low
	eor	x7, x7, x14                   // AES final-1 block - round N high
.Ldec_blocks_2_remaining:	//	blocks left = 2
	stp	x6, x7, [x2], #16       // AES final-1 block  - store result
	rev64	v4.16b, v5.16b                                   // GHASH final-1 block
	eor	v4.16b, v4.16b, v8.16b                          // feed in partial tag
	movi	v8.8b, #0                                       // suppress further partial tag feed in
	mov	d22, v4.d[1]                                // GHASH final-1 block - mid
	pmull2	v20.1q, v4.2d, v13.2d                         // GHASH final-1 block - high
	eor	v22.8b, v22.8b, v4.8b                     // GHASH final-1 block - mid
	pmull	v21.1q, v4.1d, v13.1d                         // GHASH final-1 block - low
	ins	v22.d[1], v22.d[0]                           // GHASH final-1 block - mid
	pmull2	v22.1q, v22.2d, v16.2d                     // GHASH final-1 block - mid
	eor	v11.16b, v11.16b, v21.16b                           // GHASH final-1 block - low
	eor	v9.16b, v9.16b, v20.16b                           // GHASH final-1 block - high
	eor	v10.16b, v10.16b, v22.16b                      // GHASH final-1 block - mid
	ld1	{ v5.16b}, [x0], #16                     // AES final block - load ciphertext
	eor	v0.16b, v5.16b, v3.16b                           // AES final block - result
	mov	x6, v0.d[0]                           // AES final block - mov low
	mov	x7, v0.d[1]                           // AES final block - mov high
	eor	x6, x6, x13                   // AES final block - round N low
	eor	x7, x7, x14                   // AES final block - round N high
.Ldec_blocks_1_remaining:	//	blocks_left = 1
	rev	w9, w12
	rev64	v4.16b, v5.16b                                    // GHASH final block
	eor	v4.16b, v4.16b, v8.16b                           // feed in partial tag
	pmull	v21.1q, v4.1d, v12.1d                          // GHASH final block - low
	mov	d8, v4.d[1]                                  // GHASH final block - mid
	eor	v8.8b, v8.8b, v4.8b                          // GHASH final block - mid
	pmull2	v20.1q, v4.2d, v12.2d                          // GHASH final block - high
	pmull	v8.1q, v8.1d, v16.1d                          // GHASH final block - mid
	eor	v9.16b, v9.16b, v20.16b                            // GHASH final block - high
	eor	v11.16b, v11.16b, v21.16b                            // GHASH final block - low
	eor	v10.16b, v10.16b, v8.16b                         // GHASH final block - mid
	movi	v8.8b, #0xc2
	eor	v6.16b, v11.16b, v9.16b                         // MODULO - karatsuba tidy up
	shl	d8, d8, #56               // mod_constant
	eor	v10.16b, v10.16b, v6.16b                         // MODULO - karatsuba tidy up
	pmull	v7.1q, v9.1d, v8.1d            // MODULO - top 64b align with mid
	ext	v9.16b, v9.16b, v9.16b, #8                     // MODULO - other top alignment
	eor	v10.16b, v10.16b, v7.16b                      // MODULO - fold into mid
	eor	v10.16b, v10.16b, v9.16b                         // MODULO - fold into mid
	pmull	v8.1q, v10.1d, v8.1d     // MODULO - mid 64b align with low
	ext	v10.16b, v10.16b, v10.16b, #8                     // MODULO - other mid alignment
	eor	v11.16b, v11.16b, v8.16b               // MODULO - fold into low
	stp	x6, x7, [x2]
	str	w9, [x16, #12]                          // store the updated counter
	eor	v11.16b, v11.16b, v10.16b                         // MODULO - fold into low
	ext	v11.16b, v11.16b, v11.16b, #8
	rev64	v11.16b, v11.16b
	mov	x0, x15
	st1	{ v11.16b }, [x3]
	ldp	x19, x20, [sp, #16]
	ldp	x21, x22, [sp, #32]
	ldp	x23, x24, [sp, #48]
	ldp	d8, d9, [sp, #64]
	ldp	d10, d11, [sp, #80]
	ldp	d12, d13, [sp, #96]
	ldp	d14, d15, [sp, #112]
	ldp	x29, x30, [sp], #128
	AARCH64_VALIDATE_LINK_REGISTER
	ret
.size	aes_gcm_dec_kernel_deinterleaved,.-aes_gcm_dec_kernel_deinterleaved
#endif
#endif  // !OPENSSL_NO_ASM && defined(OPENSSL_AARCH64) && defined(__ELF__)
