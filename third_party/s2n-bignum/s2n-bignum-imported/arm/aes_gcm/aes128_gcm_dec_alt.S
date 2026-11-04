// Copyright (c) 2020-2022 The OpenSSL Project Authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Written by Xiaokang Qian <xiaokang.qian@arm.com> for the OpenSSL project,
// derived from https://github.com/ARM-software/AArch64cryptolib, original
// author Samuel Lee <Samuel.Lee@arm.com>.

// ----------------------------------------------------------------------------
// AES-128-GCM bulk decryption, 8 blocks at a time: counter-mode decryption of
// whole blocks with the GHASH tag update
// Inputs in[len_bits/8], len_bits, tag[2], ivec[16], key[176], htable[24];
// outputs out[len_bits/8], tag[2], ivec[16], returns bytes processed
//
//    extern uint64_t aes128_gcm_dec_alt(const uint8_t *in, uint64_t len_bits,
//                                       uint8_t *out, uint64_t *tag,
//                                       uint8_t *ivec,
//                                       const s2n_bignum_AES_KEY *key,
//                                       const uint64_t *htable);
//
// Processes the input "in" of "len_bits" bits under AES-128 in GCM mode: each
// 16-byte block is decrypted in counter mode using the counter block "ivec"
// and the AES round keys "key", the result is written to "out", and the
// running GHASH authenticator "tag" is updated over the INPUT (ciphertext)
// using the precomputed table of H-powers "htable". On return the updated
// counter is written back to "ivec", the updated authenticator to "tag", and
// the number of bytes processed, len_bits/8, is returned. "tag" and "ivec"
// are the Xi and Yi blocks of AWS-LC's GCM context.
//
// Whole blocks only: "len_bits" must be a multiple of 128. For any other
// value nothing is processed: the function returns 0 without reading or
// writing memory, as it also does for len_bits = 0. A partial final block is
// the caller's responsibility, as in AWS-LC's GCM layer, whose
// crypto/fipsmodule/modes/gcm.c passes whole blocks only.
//
// The table "htable" is the twelve 16-byte entries (192 bytes) that
// gcm_init_v8 writes at the start of its Htable, derived from the subkey
// H = AES_K(0^128). They hold, in order, H, m(H,H^2), H^2, H^3, m(H^3,H^4),
// H^4, H^5, m(H^5,H^6), H^6, H^7, m(H^7,H^8), H^8, where the powers are in
// the bit-reflected ("twisted") representation that gcm_init_v8 uses and
// m(A,B) packs the Karatsuba middle terms A.lo ^ A.hi (low 64 bits) and
// B.lo ^ B.hi (high 64 bits) of two neighbouring powers into one entry. The
// reference implementation in tests/ref_aes_gcm.c (ref_gcm_init_htable)
// constructs the same table independently.
// Of "key" only the 11 round keys (176 bytes) are read, not key->rounds, and
// of "htable" only these 192 bytes.
//
// The input must satisfy in + len_bits/8 < 2^63, because the loop control
// compares the input pointer with the main-loop end pointer as signed
// integers (cmp x0, x5 followed by b.ge or b.lt). The buffers written ("out",
// "tag" and "ivec") must not overlap each other, "in", "key" or "htable"; in
// particular, in-place operation (out == in) is not covered by the proof.
//
// This is an alternative to aes128_gcm_dec with the same arguments, for
// processors with FEAT_SHA3, whose eor3 it uses. Unlike aes128_gcm_dec it
// reads the whole 192-byte table, not just its first 96 bytes, it requires
// in + len_bits/8 < 2^63, and when len_bits is not a multiple of 128 it
// returns 0 without touching memory, where aes128_gcm_dec processes the
// whole blocks.
//
// This routine does not enforce the NIST GCM message limit.
// Callers must ensure the cumulative message length does not exceed 2^36 - 32 bytes (2^39 - 256 bits).
//
// Standard ARM ABI: X0 = in, X1 = len_bits, X2 = out, X3 = tag, X4 = ivec,
//                   X5 = key, X6 = htable, returns X0
// ----------------------------------------------------------------------------

// Origin: derived from AWS-LC's aesv8_gcm_8x_dec_128, the linux64 output of
// crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-unroll8.pl at AWS-LC commit
// f3e723d851ec034216c4a3c273c3ad5644249946, keeping its AES-128 ten-round
// schedule and instruction stream, with these changes:
//  - s2n-bignum symbol, visibility, CFI and local-label conventions.
//  - Entry: the whole-blocks guard (tst x1, #127; b.ne) follows the
//    zero-length check and precedes the d8-d15 saves, so the reject path
//    needs no epilogue. All four saves come before the argument moves, so the
//    core correctness theorem, which like the other theorems is about the
//    code of a -DNO_IBT build, starts at pc + 0x1c with the C arguments still
//    in X0-X6.
//  - Final block: the partial-block handling at L128_dec_blocks_less_than_1
//    is removed, namely the len_bits % 128 mask, the load of the 16 output
//    bytes the last block will occupy, the masking of the GHASH input and the
//    bif blend of the output. The last block is stored and hashed whole, and
//    the output buffer is never read.
//  - Counter setup: the counter blocks 1 to 7 are the reversed base counter
//    plus the increments 1 to 7, each one add and one rev32 (the increments
//    2 to 7 are built from the increment 1 first), instead of one serial
//    add/rev32 chain through v30.
//  - GHASH tail: the nine Karatsuba middle-term lane moves are
//    ext vD.16b, vN.16b, vN.16b, #8 instead of ins vD.d[0], vN.d[1]. Only
//    lane 0 of vD is consumed, and ext writes the whole register, so the
//    moves no longer wait for the previous writer of vD.
//  - Exactly 8 blocks left: the tail's first b.gt goes to the straight-line
//    drain L128_dec_exact8_drain, placed after the return stub, instead of
//    L128_dec_blocks_more_than_7, which is no longer reached but stays in
//    place. The drain feeds the partial tag into its first block only,
//    defers the products of three blocks to v13-v15 and folds each into the
//    next block's accumulations with eor3, and rejoins the shared reduction
//    at L128_dec_reduce.
//  - One to four blocks: after the prologue, cmp x9, #64; b.le sends them to
//    L128_dec_w5r_small, placed after the drain (the small-message path of
//    aes256_gcm_dec_alt with the AES-128 round keys). It seeds the GHASH
//    accumulator with Xi' * H^nblk, decrypts the blocks one at a time,
//    folding block j in with H^(nblk-j), reduces once, and rejoins the
//    epilogue at L128_dec_frame_restore.
// The drain and the small-message path follow the return stub, so the entry
// guard's branches to the stub stay short. There is no alignment directive
// in the function, so that a -DNO_IBT build is exactly this code without the
// bti c landing pad, as the proofs require.
// Proofs: arm/proofs/aes128_gcm_dec_alt.ml.
#include "_internal_s2n_bignum_arm.h"

        .arch armv8.2-a+crypto+sha3
        .text

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes128_gcm_dec_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes128_gcm_dec_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes128_gcm_dec_alt)
.align	4
S2N_BN_SYMBOL(aes128_gcm_dec_alt):
	CFI_START
	AARCH64_VALID_CALL_TARGET
	cbz	x1, L128_dec_ret
	tst	x1, #127				//whole blocks only: len_bits % 128 == 0
	b.ne	L128_dec_ret			//otherwise process nothing, return 0
	CFI_PUSH2N(d8,d9,80)
	CFI_STACKSAVE2X(d10,d11,16,24)
	CFI_STACKSAVE2X(d12,d13,32,40)
	CFI_STACKSAVE2X(d14,d15,48,56)
	lsr	x9, x1, #3
	mov	x16, x4
	mov	x11, x5
	mov	x5, #0xc200000000000000
	stp	x5, xzr, [sp, #64]
	add	x10, sp, #64

	cmp	x9, #64				//nblk <= 4 ?
	b.le	L128_dec_w5r_small

	mov	x5, x9
	ld1	{ v0.16b}, [x16]					//CTR block 0

	ldp	q26, q27, [x11, #0]				 	//load rk0, rk1
	sub	x5, x5, #1		//byte_len - 1

	mov	x15, #0x100000000				//set up counter increment
	movi	v31.16b, #0x0
	mov	v31.d[1], x15
	add	v8.4s, v31.4s, v31.4s		//+2 increment
	add	v9.4s, v8.4s, v31.4s		//+3 increment
	add	v10.4s, v8.4s, v8.4s		//+4 increment
	add	v11.4s, v10.4s, v31.4s		//+5 increment
	add	v12.4s, v10.4s, v8.4s		//+6 increment
	add	v13.4s, v10.4s, v9.4s		//+7 increment
	ld1	{ v19.16b}, [x3]
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b

	rev32	v14.16b, v0.16b				//set up reversed counter (base)

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 0

	add	v15.4s, v14.4s, v31.4s		//CTR block 1 = base + 1
	add	v16.4s, v14.4s, v8.4s		//CTR block 2 = base + 2
	add	v17.4s, v14.4s, v9.4s		//CTR block 3 = base + 3
	add	v18.4s, v14.4s, v10.4s		//CTR block 4 = base + 4
	add	v20.4s, v14.4s, v11.4s		//CTR block 5 = base + 5
	add	v21.4s, v14.4s, v12.4s		//CTR block 6 = base + 6
	add	v30.4s, v14.4s, v13.4s		//CTR block 7 = base + 7
	rev32	v1.16b, v15.16b				//CTR block 1
	rev32	v2.16b, v16.16b				//CTR block 2
	rev32	v3.16b, v17.16b				//CTR block 3
	rev32	v4.16b, v18.16b				//CTR block 4
	rev32	v5.16b, v20.16b				//CTR block 5
	rev32	v6.16b, v21.16b				//CTR block 6
	rev32	v7.16b, v30.16b				//CTR block 7

	and	x5, x5, #0xffffffffffffff80	//number of bytes to be processed in main loop (at least 1 byte must be handled by tail)

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 0

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 1

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 0

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 0

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 0

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 0
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 1

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 0

	ldp	q28, q26, [x11, #32]				//load rk2, rk3

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 1

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 1
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 1

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 2
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 2
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 1

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 2
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 2

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 2
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 2

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 3
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 3

	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 3

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 3
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 3

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 3
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 3

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 4
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 4
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 3

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 4
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 4
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 4

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 4

	ldp	q26, q27, [x11, #96]				//load rk6, rk7
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 5
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 5

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 5
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 5

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 5
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 5

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 5

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 6
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 6
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 5

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 6

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 6
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 6

	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 7
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 7

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 7
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 7
	ldp	q28, q26, [x11, #128]				//load rk8, rk9

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 7
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 7
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 7

	add	x5, x5, x0
	add	v30.4s, v30.4s, v31.4s		//CTR block 7

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 8
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 8

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 8
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 8
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 8

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 8
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 8
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 8

	aese	v0.16b, v26.16b						//AES block 0 - round 9
	aese	v1.16b, v26.16b						//AES block 1 - round 9
	aese	v6.16b, v26.16b						//AES block 6 - round 9

	ldr	q27, [x11, #160]					//load rk10
	aese	v4.16b, v26.16b						//AES block 4 - round 9
	aese	v3.16b, v26.16b						//AES block 3 - round 9

	aese	v2.16b, v26.16b						//AES block 2 - round 9
	aese	v5.16b, v26.16b						//AES block 5 - round 9
	aese	v7.16b, v26.16b						//AES block 7 - round 9

	add	x4, x0, x1, lsr #3		//end_input_ptr
	cmp	x0, x5				//check if we have <= 8 blocks
	b.ge	L128_dec_tail						//handle tail

	ldp	q8, q9, [x0], #32			//AES block 0, 1 - load ciphertext

	eor3	v0.16b, v8.16b, v0.16b, v27.16b	//AES block 0 - result
	eor3	v1.16b, v9.16b, v1.16b, v27.16b	//AES block 1 - result
	stp	q0, q1, [x2], #32			//AES block 0, 1 - store result

	rev32	v0.16b, v30.16b				//CTR block 8
	add	v30.4s, v30.4s, v31.4s		//CTR block 8
	ldp	q10, q11, [x0], #32			//AES block 2, 3 - load ciphertext

	ldp	q12, q13, [x0], #32			//AES block 4, 5 - load ciphertext

	rev32	v1.16b, v30.16b				//CTR block 9
	add	v30.4s, v30.4s, v31.4s		//CTR block 9
	ldp	q14, q15, [x0], #32			//AES block 6, 7 - load ciphertext

	eor3	v3.16b, v11.16b, v3.16b, v27.16b	//AES block 3 - result
	eor3	v2.16b, v10.16b, v2.16b, v27.16b	//AES block 2 - result
	stp	q2, q3, [x2], #32			//AES block 2, 3 - store result

	rev32	v2.16b, v30.16b				//CTR block 10
	add	v30.4s, v30.4s, v31.4s		//CTR block 10

	eor3	v6.16b, v14.16b, v6.16b, v27.16b	//AES block 6 - result

	rev32	v3.16b, v30.16b				//CTR block 11
	add	v30.4s, v30.4s, v31.4s		//CTR block 11

	eor3	v4.16b, v12.16b, v4.16b, v27.16b	//AES block 4 - result
	eor3	v5.16b, v13.16b, v5.16b, v27.16b	//AES block 5 - result
	stp	q4, q5, [x2], #32			//AES block 4, 5 - store result

	eor3	v7.16b, v15.16b, v7.16b, v27.16b	//AES block 7 - result
	stp	q6, q7, [x2], #32			//AES block 6, 7 - store result
	rev32	v4.16b, v30.16b				//CTR block 12

	cmp	x0, x5				//check if we have <= 8 blocks
	add	v30.4s, v30.4s, v31.4s		//CTR block 12
	b.ge	L128_dec_prepretail					//do prepretail

L128_dec_main_loop:	//main	loop start
	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h

	rev64	v9.16b, v9.16b						//GHASH block 8k+1
	rev64	v8.16b, v8.16b						//GHASH block 8k
	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0

	rev64	v14.16b, v14.16b						//GHASH block 8k+6
	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h

	eor	v8.16b, v8.16b, v19.16b				 	//PRE 1
	rev32	v5.16b, v30.16b				//CTR block 8k+13
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13

	rev64	v10.16b, v10.16b						//GHASH block 8k+2
	rev64	v12.16b, v12.16b						//GHASH block 8k+4
	ldp	q26, q27, [x11, #0]				 	//load rk0, rk1

	rev32	v6.16b, v30.16b				//CTR block 8k+14
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14
	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k

	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high
	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high
	rev64	v11.16b, v11.16b						//GHASH block 8k+3

	rev32	v7.16b, v30.16b				//CTR block 8k+15
	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	rev64	v13.16b, v13.16b						//GHASH block 8k+5

	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid

	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0
	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0
	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1
	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low
	eor3	v17.16b, v17.16b, v29.16b, v9.16b	//GHASH block 8k+2, 8k+3 - high

	ldp	q28, q26, [x11, #32]				//load rk2, rk3
	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1

	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low
	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k	- mid

	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h
	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1
	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low

	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2
	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//GHASH block 8k+2, 8k+3 - low

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2
	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid
	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h

	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2

	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2
	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3
	rev64	v15.16b, v15.16b						//GHASH block 8k+7
	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high

	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low
	eor3	v18.16b, v18.16b, v21.16b, v29.16b	//GHASH block 8k+2, 8k+3 - mid

	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3

	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low
	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high

	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4

	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid
	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid

	ldp	q26, q27, [x11, #96]				//load rk6, rk7
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5
	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5

	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5

	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high
	eor3	v18.16b, v18.16b, v24.16b, v16.16b	//GHASH block 8k+4, 8k+5 - mid
	eor3	v19.16b, v19.16b, v25.16b, v23.16b	//GHASH block 8k+4, 8k+5 - low

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6
	eor3	v17.16b, v17.16b, v8.16b, v10.16b	//GHASH block 8k+4, 8k+5 - high
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6
	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6
	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low

	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15

	eor3	v17.16b, v17.16b, v11.16b, v12.16b	//GHASH block 8k+6, 8k+7 - high
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6
	ldp	q28, q26, [x11, #128]				//load rk8, rk9

	ldr	d16, [x10]			//MODULO - load modulo constant
	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//GHASH block 8k+6, 8k+7 - low
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7

	rev32	v20.16b, v30.16b					//CTR block 8k+16
	eor3	v18.16b, v18.16b, v21.16b, v13.16b	//GHASH block 8k+6, 8k+7 - mid
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+16

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7
	rev32	v22.16b, v30.16b					//CTR block 8k+17

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7
	ext	v21.16b, v17.16b, v17.16b, #8			 	//MODULO - other top alignment
	pmull	v29.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid

	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//MODULO - karatsuba tidy up
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+17

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8
	ldp	q8, q9, [x0], #32			//AES block 8k+8, 8k+9 - load ciphertext

	ldp	q10, q11, [x0], #32			//AES block 8k+10, 8k+11 - load ciphertext
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8
	rev32	v23.16b, v30.16b					//CTR block 8k+18

	ldp	q12, q13, [x0], #32			//AES block 8k+12, 8k+13 - load ciphertext
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8
	eor3	v18.16b, v18.16b, v29.16b, v21.16b	//MODULO - fold into mid

	ldp	q14, q15, [x0], #32			//AES block 8k+14, 8k+15 - load ciphertext
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+18

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8

	aese	v0.16b, v26.16b						//AES block 8k+8 - round 9
	aese	v1.16b, v26.16b						//AES block 8k+9 - round 9
	ldr	q27, [x11, #160]					//load rk10

	aese	v6.16b, v26.16b						//AES block 8k+14 - round 9
	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v2.16b, v26.16b						//AES block 8k+10 - round 9

	aese	v7.16b, v26.16b						//AES block 8k+15 - round 9
	aese	v4.16b, v26.16b						//AES block 8k+12 - round 9
	ext	v21.16b, v18.16b, v18.16b, #8			 	//MODULO - other mid alignment

	rev32	v25.16b, v30.16b					//CTR block 8k+19
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+19

	aese	v3.16b, v26.16b						//AES block 8k+11 - round 9
	aese	v5.16b, v26.16b						//AES block 8k+13 - round 9
	eor3	v1.16b, v9.16b, v1.16b, v27.16b	//AES block 8k+9 - result

	eor3	v0.16b, v8.16b, v0.16b, v27.16b	//AES block 8k+8 - result
	eor3	v7.16b, v15.16b, v7.16b, v27.16b	//AES block 8k+15 - result
	eor3	v6.16b, v14.16b, v6.16b, v27.16b	//AES block 8k+14 - result

	eor3	v2.16b, v10.16b, v2.16b, v27.16b	//AES block 8k+10 - result
	stp	q0, q1, [x2], #32			//AES block 8k+8, 8k+9 - store result
	mov	v1.16b, v22.16b					//CTR block 8k+17

	eor3	v4.16b, v12.16b, v4.16b, v27.16b	//AES block 8k+12 - result
	eor3	v19.16b, v19.16b, v17.16b, v21.16b	//MODULO - fold into low
	mov	v0.16b, v20.16b					//CTR block 8k+16

	eor3	v3.16b, v11.16b, v3.16b, v27.16b	//AES block 8k+11 - result
	cmp	x0, x5				//LOOP CONTROL
	stp	q2, q3, [x2], #32			//AES block 8k+10, 8k+11 - store result

	eor3	v5.16b, v13.16b, v5.16b, v27.16b	//AES block 8k+13 - result
	mov	v2.16b, v23.16b					//CTR block 8k+18

	stp	q4, q5, [x2], #32			//AES block 8k+12, 8k+13 - store result
	rev32	v4.16b, v30.16b				//CTR block 8k+20
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+20

	stp	q6, q7, [x2], #32			//AES block 8k+14, 8k+15 - store result
	mov	v3.16b, v25.16b					//CTR block 8k+19
	b.lt	L128_dec_main_loop

L128_dec_prepretail:	//PREPRETAIL
	rev64	v11.16b, v11.16b						//GHASH block 8k+3
	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0
	rev64	v8.16b, v8.16b						//GHASH block 8k

	rev64	v10.16b, v10.16b						//GHASH block 8k+2
	rev32	v5.16b, v30.16b				//CTR block 8k+13
	ldp	q26, q27, [x11, #0]				 	//load rk0, rk1

	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h
	eor	v8.16b, v8.16b, v19.16b				 	//PRE 1
	rev64	v9.16b, v9.16b						//GHASH block 8k+1

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13
	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h
	rev64	v13.16b, v13.16b						//GHASH block 8k+5

	rev64	v12.16b, v12.16b						//GHASH block 8k+4

	rev64	v14.16b, v14.16b						//GHASH block 8k+6

	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k
	rev32	v6.16b, v30.16b				//CTR block 8k+14
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14

	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low
	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high

	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high

	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low
	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0

	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid

	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low
	rev32	v7.16b, v30.16b				//CTR block 8k+15
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0

	eor3	v17.16b, v17.16b, v29.16b, v9.16b	//GHASH block 8k+2, 8k+3 - high
	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0

	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k - mid
	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0

	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low
	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid
	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1

	ldp	q28, q26, [x11, #32]				//load rk2, rk3
	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//GHASH block 8k+2, 8k+3 - low
	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid

	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid

	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1

	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h
	eor3	v18.16b, v18.16b, v21.16b, v29.16b	//GHASH block 8k+2, 8k+3 - mid

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2
	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2

	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low
	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	rev64	v15.16b, v15.16b						//GHASH block 8k+7
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3

	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3
	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid

	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high
	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3
	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid

	eor3	v17.16b, v17.16b, v8.16b, v10.16b	//GHASH block 8k+4, 8k+5 - high
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4

	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4
	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4
	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid

	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high
	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid

	ldp	q26, q27, [x11, #96]				//load rk6, rk7
	eor3	v18.16b, v18.16b, v24.16b, v16.16b	//GHASH block 8k+4, 8k+5 - mid
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5

	ldr	d16, [x10]			//MODULO - load modulo constant
	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low
	eor3	v19.16b, v19.16b, v25.16b, v23.16b	//GHASH block 8k+4, 8k+5 - low

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5
	eor3	v18.16b, v18.16b, v21.16b, v13.16b	//GHASH block 8k+6, 8k+7 - mid
	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//GHASH block 8k+6, 8k+7 - low

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6

	eor3	v17.16b, v17.16b, v11.16b, v12.16b	//GHASH block 8k+6, 8k+7 - high
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7
	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//MODULO - karatsuba tidy up
	ldp	q28, q26, [x11, #128]				//load rk8, rk9

	pmull	v29.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7
	ext	v21.16b, v17.16b, v17.16b, #8			 	//MODULO - other top alignment

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7

	eor3	v18.16b, v18.16b, v29.16b, v21.16b	//MODULO - fold into mid
	ldr	q27, [x11, #160]					//load rk10

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8
	ext	v21.16b, v18.16b, v18.16b, #8			 	//MODULO - other mid alignment

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8

	aese	v6.16b, v26.16b						//AES block 8k+14 - round 9
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8

	eor3	v19.16b, v19.16b, v17.16b, v21.16b	//MODULO - fold into low
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15
	aese	v2.16b, v26.16b						//AES block 8k+10 - round 9

	aese	v3.16b, v26.16b						//AES block 8k+11 - round 9
	aese	v5.16b, v26.16b						//AES block 8k+13 - round 9
	aese	v0.16b, v26.16b						//AES block 8k+8 - round 9

	aese	v4.16b, v26.16b						//AES block 8k+12 - round 9
	aese	v1.16b, v26.16b						//AES block 8k+9 - round 9
	aese	v7.16b, v26.16b						//AES block 8k+15 - round 9

L128_dec_tail:	//TAIL

	mov	v29.16b, v27.16b
	sub	x5, x4, x0 	//main_end_input_ptr is number of bytes left to process

	cmp	x5, #112

	ldp	q24, q25, [x6, #160]			//load h8k | h7k
	ldr	q9, [x0], #16				//AES block 8k+8 - load ciphertext

	ldp	q20, q21, [x6, #96]			//load h5l | h5h
	ext	v16.16b, v19.16b, v19.16b, #8				//prepare final partial tag

	ldp	q22, q23, [x6, #128]			//load h6l | h6h

	eor3	v12.16b, v9.16b, v0.16b, v29.16b	//AES block 8k+8 - result
	b.gt	L128_dec_exact8_drain			//exactly 8 blocks left: dedicated drain

	cmp	x5, #96
	mov	v7.16b, v6.16b
	movi	v19.8b, #0

	movi	v17.8b, #0
	mov	v6.16b, v5.16b
	mov	v5.16b, v4.16b

	mov	v4.16b, v3.16b
	mov	v3.16b, v2.16b
	mov	v2.16b, v1.16b

	movi	v18.8b, #0
	sub	v30.4s, v30.4s, v31.4s
	b.gt	L128_dec_blocks_more_than_6

	cmp	x5, #80
	sub	v30.4s, v30.4s, v31.4s

	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b
	mov	v5.16b, v4.16b

	mov	v4.16b, v3.16b
	mov	v3.16b, v1.16b
	b.gt	L128_dec_blocks_more_than_5

	cmp	x5, #64

	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b
	mov	v5.16b, v4.16b

	mov	v4.16b, v1.16b
	sub	v30.4s, v30.4s, v31.4s
	b.gt	L128_dec_blocks_more_than_4

	sub	v30.4s, v30.4s, v31.4s
	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b

	mov	v5.16b, v1.16b
	cmp	x5, #48
	b.gt	L128_dec_blocks_more_than_3

	sub	v30.4s, v30.4s, v31.4s
	mov	v7.16b, v6.16b
	cmp	x5, #32

	ldr	q24, [x6, #64]				//load h4k | h3k
	mov	v6.16b, v1.16b
	b.gt	L128_dec_blocks_more_than_2

	cmp	x5, #16

	mov	v7.16b, v1.16b
	sub	v30.4s, v30.4s, v31.4s
	b.gt	L128_dec_blocks_more_than_1

	sub	v30.4s, v30.4s, v31.4s
	ldr	q21, [x6, #16]				//load h2k | h1k
	b	L128_dec_blocks_less_than_1
L128_dec_blocks_more_than_7:	//blocks	left >  7
	rev64	v8.16b, v9.16b						//GHASH final-7 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ext	v18.16b, v24.16b, v24.16b, #8			//GHASH final-7 block - mid

	pmull	v19.1q, v8.1d, v25.1d				//GHASH final-7 block - low
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-7 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in
	ldr	q9, [x0], #16				//AES final-6 block - load ciphertext

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-7 block - mid

	pmull2	v17.1q, v8.2d, v25.2d				//GHASH final-7 block - high
	st1	{ v12.16b}, [x2], #16			 	//AES final-7 block  - store result
	eor3	v12.16b, v9.16b, v1.16b, v29.16b	//AES final-6 block - result

	pmull	v18.1q, v27.1d, v18.1d			 	//GHASH final-7 block - mid
L128_dec_blocks_more_than_6:	//blocks	left >  6

	rev64	v8.16b, v9.16b						//GHASH final-6 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-6 block - mid

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-6 block - mid

	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-6 block - low
	ldr	q9, [x0], #16				//AES final-5 block - load ciphertext
	movi	v16.8b, #0						//supress further partial tag feed in

	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-6 block - mid
	st1	{ v12.16b}, [x2], #16			 	//AES final-6 block - store result
	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-6 block - high

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-6 block - low
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-6 block - high

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-6 block - mid
	eor3	v12.16b, v9.16b, v2.16b, v29.16b	//AES final-5 block - result
L128_dec_blocks_more_than_5:	//blocks	left >  5

	rev64	v8.16b, v9.16b						//GHASH final-5 block

	ldr	q9, [x0], #16				//AES final-4 block - load ciphertext
	st1	{ v12.16b}, [x2], #16			 	//AES final-5 block - store result

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-5 block - mid

	eor3	v12.16b, v9.16b, v3.16b, v29.16b	//AES final-4 block - result

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-5 block - mid

	ins	v27.d[1], v27.d[0]					//GHASH final-5 block - mid
	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-5 block - low
	movi	v16.8b, #0						//supress further partial tag feed in

	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-5 block - mid
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-5 block - high
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-5 block - low

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-5 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-5 block - high
L128_dec_blocks_more_than_4:	//blocks	left >  4

	rev64	v8.16b, v9.16b						//GHASH final-4 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	ldr	q9, [x0], #16				//AES final-3 block - load ciphertext

	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-4 block - mid
	movi	v16.8b, #0						//supress further partial tag feed in
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final-4 block - high

	pmull	v26.1q, v8.1d, v20.1d				//GHASH final-4 block - low

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-4 block - high

	st1	{ v12.16b}, [x2], #16			 	//AES final-4 block - store result
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-4 block - mid

	eor3	v12.16b, v9.16b, v4.16b, v29.16b	//AES final-3 block - result
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-4 block - low

	pmull	v27.1q, v27.1d, v21.1d				//GHASH final-4 block - mid

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-4 block - mid
L128_dec_blocks_more_than_3:	//blocks	left >  3

	st1	{ v12.16b}, [x2], #16			 	//AES final-3 block - store result
	rev64	v8.16b, v9.16b						//GHASH final-3 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-3 block - mid

	ldr	q25, [x6, #80]				//load h4l | h4h
	ldr	q24, [x6, #64]				//load h4k | h3k

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-3 block - mid

	ldr	q9, [x0], #16				//AES final-2 block - load ciphertext

	ins	v27.d[1], v27.d[0]					//GHASH final-3 block - mid
	pmull	v26.1q, v8.1d, v25.1d				//GHASH final-3 block - low
	pmull2	v28.1q, v8.2d, v25.2d				//GHASH final-3 block - high

	movi	v16.8b, #0						//supress further partial tag feed in
	eor3	v12.16b, v9.16b, v5.16b, v29.16b	//AES final-2 block - result
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-3 block - low

	pmull2	v27.1q, v27.2d, v24.2d				//GHASH final-3 block - mid

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-3 block - high
	eor	v18.16b, v18.16b, v27.16b				//GHASH final-3 block - mid
L128_dec_blocks_more_than_2:	//blocks	left >  2

	rev64	v8.16b, v9.16b						//GHASH final-2 block

	st1	{ v12.16b}, [x2], #16			 	//AES final-2 block - store result

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	ldr	q23, [x6, #48]				//load h3l | h3h
	movi	v16.8b, #0						//supress further partial tag feed in

	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-2 block - mid

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-2 block - mid

	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-2 block - low

	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-2 block - high
	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-2 block - mid
	ldr	q9, [x0], #16				//AES final-1 block - load ciphertext

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-2 block - mid

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-2 block - low

	eor3	v12.16b, v9.16b, v6.16b, v29.16b	//AES final-1 block - result
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-2 block - high
L128_dec_blocks_more_than_1:	//blocks	left >  1

	st1	{ v12.16b}, [x2], #16			 	//AES final-1 block - store result
	rev64	v8.16b, v9.16b						//GHASH final-1 block

	ldr	q22, [x6, #32]				//load h2l | h2h

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	movi	v16.8b, #0						//supress further partial tag feed in

	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-1 block - mid

	ldr	q9, [x0], #16				//AES final block - load ciphertext
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-1 block - high

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-1 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-1 block - high
	ldr	q21, [x6, #16]				//load h2k | h1k

	ins	v27.d[1], v27.d[0]					//GHASH final-1 block - mid
	eor3	v12.16b, v9.16b, v7.16b, v29.16b	//AES final block - result

	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-1 block - low

	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-1 block - mid

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-1 block - low

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-1 block - mid
L128_dec_blocks_less_than_1:	//final block, always whole: stored and hashed as 16 bytes

	ldr	q20, [x6]				//load h1l | h1h

	rev64	v8.16b, v9.16b						//GHASH final block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final block - high
	ext	v16.16b, v8.16b, v8.16b, #8			//GHASH final block - mid

	eor	v17.16b, v17.16b, v28.16b					//GHASH final block - high
	eor	v16.8b, v16.8b, v8.8b				//GHASH final block - mid

	pmull	v16.1q, v16.1d, v21.1d				//GHASH final block - mid
	st1	{ v12.16b}, [x2]				//store all 16B

	pmull	v26.1q, v8.1d, v20.1d				//GHASH final block - low

	eor	v18.16b, v18.16b, v16.16b				//GHASH final block - mid
L128_dec_reduce:	//cascade and exact-8 drain converge here
	ldr	d16, [x10]			//MODULO - load modulo constant

	eor	v19.16b, v19.16b, v26.16b					//GHASH final block - low

	eor	v14.16b, v17.16b, v19.16b				//MODULO - karatsuba tidy up

	pmull	v21.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid
	ext	v17.16b, v17.16b, v17.16b, #8				//MODULO - other top alignment

	eor	v18.16b, v18.16b, v14.16b				//MODULO - karatsuba tidy up

	eor3	v18.16b, v18.16b, v17.16b, v21.16b	//MODULO - fold into mid

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	ext	v18.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment

	eor3	v19.16b, v19.16b, v18.16b, v17.16b	//MODULO - fold into low
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]
	rev32	v30.16b, v30.16b

	str	q30, [x16]					//store the updated counter

L128_dec_frame_restore:	//the main epilogue; the 1-4 block path rejoins here
	mov	x0, x9
	.cfi_remember_state
	CFI_STACKLOAD2(d10,d11,16)
	CFI_STACKLOAD2(d12,d13,32)
	CFI_STACKLOAD2(d14,d15,48)
	CFI_POP2N(d8,d9,80)
	ret

L128_dec_ret:	//reached only from the entry guard, before any save
	.cfi_def_cfa_offset 0
	.cfi_restore d8
	.cfi_restore d9
	.cfi_restore d10
	.cfi_restore d11
	.cfi_restore d12
	.cfi_restore d13
	.cfi_restore d14
	.cfi_restore d15
	mov	w0, #0x0
	ret
	.cfi_restore_state			//the code below still runs with the frame live

L128_dec_exact8_drain:	//exact-8 GHASH drain: partial-tag feed only in the first block
	// ---- exact-8 drain: final-7 block ----
	rev64	v8.16b, v9.16b						//GHASH final-7 block
	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	ext	v18.16b, v24.16b, v24.16b, #8			//GHASH final-7 block - mid
	pmull	v19.1q, v8.1d, v25.1d				//GHASH final-7 block - low
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-7 block - mid
	ldr	q9, [x0], #16				//AES final-6 block - load ciphertext
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-7 block - mid
	pmull2	v17.1q, v8.2d, v25.2d				//GHASH final-7 block - high
	st1	{ v12.16b}, [x2], #16			 	//AES final-7 block  - store result
	eor3	v12.16b, v9.16b, v1.16b, v29.16b	//AES final-6 block - result
	pmull	v18.1q, v27.1d, v18.1d			 	//GHASH final-7 block - mid
	// ---- exact-8 drain: final-6 block ----
	rev64	v8.16b, v9.16b						//GHASH final-6 block
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-6 block - mid
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-6 block - mid
	pmull	v14.1q, v8.1d, v23.1d				//GHASH final-6 block - low (deferred to v14)
	ldr	q9, [x0], #16				//AES final-5 block - load ciphertext
	pmull	v15.1q, v27.1d, v24.1d				//GHASH final-6 block - mid (deferred to v15)
	st1	{ v12.16b}, [x2], #16			 	//AES final-6 block - store result
	pmull2	v13.1q, v8.2d, v23.2d				//GHASH final-6 block - high (deferred to v13)
	eor3	v12.16b, v9.16b, v2.16b, v29.16b	//AES final-5 block - result
	// ---- exact-8 drain: final-5 block ----
	rev64	v8.16b, v9.16b						//GHASH final-5 block
	ldr	q9, [x0], #16				//AES final-4 block - load ciphertext
	st1	{ v12.16b}, [x2], #16			 	//AES final-5 block - store result
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-5 block - mid
	eor3	v12.16b, v9.16b, v3.16b, v29.16b	//AES final-4 block - result
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-5 block - mid
	ins	v27.d[1], v27.d[0]					//GHASH final-5 block - mid
	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-5 block - low
	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-5 block - mid
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-5 block - high
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//GHASH final-6,5 blocks - low
	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//GHASH final-6,5 blocks - mid
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//GHASH final-6,5 blocks - high
	// ---- exact-8 drain: final-4 block ----
	rev64	v8.16b, v9.16b						//GHASH final-4 block
	ldr	q9, [x0], #16				//AES final-3 block - load ciphertext
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-4 block - mid
	pmull2	v13.1q, v8.2d, v20.2d				//GHASH final-4 block - high (deferred to v13)
	pmull	v14.1q, v8.1d, v20.1d				//GHASH final-4 block - low (deferred to v14)
	st1	{ v12.16b}, [x2], #16			 	//AES final-4 block - store result
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-4 block - mid
	eor3	v12.16b, v9.16b, v4.16b, v29.16b	//AES final-3 block - result
	pmull	v15.1q, v27.1d, v21.1d				//GHASH final-4 block - mid (deferred to v15)
	// ---- exact-8 drain: final-3 block ----
	st1	{ v12.16b}, [x2], #16			 	//AES final-3 block - store result
	rev64	v8.16b, v9.16b						//GHASH final-3 block
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-3 block - mid
	ldr	q25, [x6, #80]				//load h4l | h4h
	ldr	q24, [x6, #64]				//load h4k | h3k
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-3 block - mid
	ldr	q9, [x0], #16				//AES final-2 block - load ciphertext
	ins	v27.d[1], v27.d[0]					//GHASH final-3 block - mid
	pmull	v26.1q, v8.1d, v25.1d				//GHASH final-3 block - low
	pmull2	v28.1q, v8.2d, v25.2d				//GHASH final-3 block - high
	eor3	v12.16b, v9.16b, v5.16b, v29.16b	//AES final-2 block - result
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//GHASH final-4,3 blocks - low
	pmull2	v27.1q, v27.2d, v24.2d				//GHASH final-3 block - mid
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//GHASH final-4,3 blocks - high
	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//GHASH final-4,3 blocks - mid
	// ---- exact-8 drain: final-2 block ----
	rev64	v8.16b, v9.16b						//GHASH final-2 block
	st1	{ v12.16b}, [x2], #16			 	//AES final-2 block - store result
	ldr	q23, [x6, #48]				//load h3l | h3h
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-2 block - mid
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-2 block - mid
	pmull	v14.1q, v8.1d, v23.1d				//GHASH final-2 block - low (deferred to v14)
	pmull2	v13.1q, v8.2d, v23.2d				//GHASH final-2 block - high (deferred to v13)
	pmull	v15.1q, v27.1d, v24.1d				//GHASH final-2 block - mid (deferred to v15)
	ldr	q9, [x0], #16				//AES final-1 block - load ciphertext
	eor3	v12.16b, v9.16b, v6.16b, v29.16b	//AES final-1 block - result
	// ---- exact-8 drain: final-1 block ----
	st1	{ v12.16b}, [x2], #16			 	//AES final-1 block - store result
	rev64	v8.16b, v9.16b						//GHASH final-1 block
	ldr	q22, [x6, #32]				//load h2l | h2h
	ext	v27.16b, v8.16b, v8.16b, #8			//GHASH final-1 block - mid
	ldr	q9, [x0], #16				//AES final block - load ciphertext
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-1 block - high
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-1 block - mid
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//GHASH final-2,1 blocks - high
	ldr	q21, [x6, #16]				//load h2k | h1k
	ins	v27.d[1], v27.d[0]					//GHASH final-1 block - mid
	eor3	v12.16b, v9.16b, v7.16b, v29.16b	//AES final block - result
	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-1 block - low
	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-1 block - mid
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//GHASH final-2,1 blocks - low
	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//GHASH final-2,1 blocks - mid
	// ---- exact-8 drain: final-0 block ----
	ldr	q20, [x6]				//load h1l | h1h
	rev64	v8.16b, v9.16b						//GHASH final block
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final block - high
	ext	v16.16b, v8.16b, v8.16b, #8			//GHASH final block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final block - high
	eor	v16.8b, v16.8b, v8.8b				//GHASH final block - mid
	pmull	v16.1q, v16.1d, v21.1d				//GHASH final block - mid
	st1	{ v12.16b}, [x2]				//store all 16B
	pmull	v26.1q, v8.1d, v20.1d				//GHASH final block - low
	eor	v18.16b, v18.16b, v16.16b				//GHASH final block - mid
	b	L128_dec_reduce

L128_dec_w5r_small:	//nblk <= 4: seed Xi' * H^nblk, then fall through one block per step
	ld1	{ v30.16b}, [x16]				//CTR block 0 (raw)
	ld1	{ v19.16b}, [x3]				//load Xi
	mov	x15, #0x100000000			//counter increment
	movi	v31.16b, #0x0
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	mov	v31.d[1], x15				//+1
	ext	v16.16b, v19.16b, v19.16b, #8		//partial-tag feed Xi'
	rev32	v29.16b, v30.16b			//reversed counter base
	ldp	q1, q2, [x11, #0]			//rk0, rk1
	ldp	q3, q4, [x11, #32]			//rk2, rk3
	ldp	q5, q6, [x11, #64]			//rk4, rk5
	ldp	q7, q8, [x11, #96]			//rk6, rk7
	ldp	q9, q10, [x11, #128]			//rk8, rk9
	ldr	q11, [x11, #160]			//rk10
	cmp	x9, #32
	b.gt	L128_dec_w5r_h1
	cmp	x9, #16
	b.eq	L128_dec_w5r_stub_1
	b	L128_dec_w5r_stub_2
L128_dec_w5r_h1:
	cmp	x9, #48
	b.eq	L128_dec_w5r_stub_3
	b	L128_dec_w5r_stub_4

L128_dec_w5r_stub_4:	//entry for nblk=4: seed acc = Xi' * H^4
	ldr	q24, [x6, #80]				//h4l | h4h
	ldr	d25, [x6, #72]				//h4k (64-bit)
	ext	v21.16b, v16.16b, v16.16b, #8		//Xi' mid
	eor	v21.8b, v21.8b, v16.8b			//Xi' mid
	pmull2	v17.1q, v16.2d, v24.2d			//Xi' high
	pmull	v19.1q, v16.1d, v24.1d			//Xi' low
	pmull	v18.1q, v21.1d, v25.1d			//Xi' mid
	b	L128_dec_w5r_g4

L128_dec_w5r_stub_3:	//entry for nblk=3: seed acc = Xi' * H^3
	ldr	q24, [x6, #48]				//h3l | h3h
	ldr	d25, [x6, #64]				//h3k (64-bit)
	ext	v21.16b, v16.16b, v16.16b, #8		//Xi' mid
	eor	v21.8b, v21.8b, v16.8b			//Xi' mid
	pmull2	v17.1q, v16.2d, v24.2d			//Xi' high
	pmull	v19.1q, v16.1d, v24.1d			//Xi' low
	pmull	v18.1q, v21.1d, v25.1d			//Xi' mid
	b	L128_dec_w5r_g3

L128_dec_w5r_stub_2:	//entry for nblk=2: seed acc = Xi' * H^2
	ldr	q24, [x6, #32]				//h2l | h2h
	ldr	d25, [x6, #24]				//h2k (64-bit)
	ext	v21.16b, v16.16b, v16.16b, #8		//Xi' mid
	eor	v21.8b, v21.8b, v16.8b			//Xi' mid
	pmull2	v17.1q, v16.2d, v24.2d			//Xi' high
	pmull	v19.1q, v16.1d, v24.1d			//Xi' low
	pmull	v18.1q, v21.1d, v25.1d			//Xi' mid
	b	L128_dec_w5r_g2

L128_dec_w5r_stub_1:	//entry for nblk=1: seed acc = Xi' * H^1
	ldr	q24, [x6, #0]				//h1l | h1h
	ldr	d25, [x6, #16]				//h1k (64-bit)
	ext	v21.16b, v16.16b, v16.16b, #8		//Xi' mid
	eor	v21.8b, v21.8b, v16.8b			//Xi' mid
	pmull2	v17.1q, v16.2d, v24.2d			//Xi' high
	pmull	v19.1q, v16.1d, v24.1d			//Xi' low
	pmull	v18.1q, v21.1d, v25.1d			//Xi' mid
	b	L128_dec_w5r_g1

L128_dec_w5r_g4:	//one block, GHASH with H^4
	ldr	q26, [x0], #16				//ciphertext 0
	rev32	v0.16b, v29.16b			//CTR block 0
	add	v29.4s, v29.4s, v31.4s
	aese	v0.16b, v1.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 0
	ldr	q24, [x6, #80]				//h4l | h4h
	ldr	d25, [x6, #72]				//h4k (64-bit)
	rev64	v20.16b, v26.16b				//GHASH H^4 block
	ext	v21.16b, v20.16b, v20.16b, #8		//H^4 mid
	aese	v0.16b, v2.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 1
	aese	v0.16b, v3.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 2
	aese	v0.16b, v4.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 3
	aese	v0.16b, v5.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 4
	eor	v21.8b, v21.8b, v20.8b			//H^4 mid
	pmull2	v22.1q, v20.2d, v24.2d			//H^4 high
	pmull	v23.1q, v20.1d, v24.1d			//H^4 low
	pmull	v30.1q, v21.1d, v25.1d			//H^4 mid
	aese	v0.16b, v6.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 5
	aese	v0.16b, v7.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 6
	aese	v0.16b, v8.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 7
	aese	v0.16b, v9.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 8
	eor	v17.16b, v17.16b, v22.16b			//fold high
	eor	v19.16b, v19.16b, v23.16b			//fold low
	eor	v18.16b, v18.16b, v30.16b			//fold mid
	aese	v0.16b, v10.16b				//blk 0 - round 9
	eor3	v0.16b, v26.16b, v0.16b, v11.16b	//H^4 block - result
	str	q0, [x2], #16

L128_dec_w5r_g3:	//one block, GHASH with H^3
	ldr	q26, [x0], #16				//ciphertext 0
	rev32	v0.16b, v29.16b			//CTR block 0
	add	v29.4s, v29.4s, v31.4s
	aese	v0.16b, v1.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 0
	ldr	q24, [x6, #48]				//h3l | h3h
	ldr	d25, [x6, #64]				//h3k (64-bit)
	rev64	v20.16b, v26.16b				//GHASH H^3 block
	ext	v21.16b, v20.16b, v20.16b, #8		//H^3 mid
	aese	v0.16b, v2.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 1
	aese	v0.16b, v3.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 2
	aese	v0.16b, v4.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 3
	aese	v0.16b, v5.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 4
	eor	v21.8b, v21.8b, v20.8b			//H^3 mid
	pmull2	v22.1q, v20.2d, v24.2d			//H^3 high
	pmull	v23.1q, v20.1d, v24.1d			//H^3 low
	pmull	v30.1q, v21.1d, v25.1d			//H^3 mid
	aese	v0.16b, v6.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 5
	aese	v0.16b, v7.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 6
	aese	v0.16b, v8.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 7
	aese	v0.16b, v9.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 8
	eor	v17.16b, v17.16b, v22.16b			//fold high
	eor	v19.16b, v19.16b, v23.16b			//fold low
	eor	v18.16b, v18.16b, v30.16b			//fold mid
	aese	v0.16b, v10.16b				//blk 0 - round 9
	eor3	v0.16b, v26.16b, v0.16b, v11.16b	//H^3 block - result
	str	q0, [x2], #16

L128_dec_w5r_g2:	//one block, GHASH with H^2
	ldr	q26, [x0], #16				//ciphertext 0
	rev32	v0.16b, v29.16b			//CTR block 0
	add	v29.4s, v29.4s, v31.4s
	aese	v0.16b, v1.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 0
	ldr	q24, [x6, #32]				//h2l | h2h
	ldr	d25, [x6, #24]				//h2k (64-bit)
	rev64	v20.16b, v26.16b				//GHASH H^2 block
	ext	v21.16b, v20.16b, v20.16b, #8		//H^2 mid
	aese	v0.16b, v2.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 1
	aese	v0.16b, v3.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 2
	aese	v0.16b, v4.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 3
	aese	v0.16b, v5.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 4
	eor	v21.8b, v21.8b, v20.8b			//H^2 mid
	pmull2	v22.1q, v20.2d, v24.2d			//H^2 high
	pmull	v23.1q, v20.1d, v24.1d			//H^2 low
	pmull	v30.1q, v21.1d, v25.1d			//H^2 mid
	aese	v0.16b, v6.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 5
	aese	v0.16b, v7.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 6
	aese	v0.16b, v8.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 7
	aese	v0.16b, v9.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 8
	eor	v17.16b, v17.16b, v22.16b			//fold high
	eor	v19.16b, v19.16b, v23.16b			//fold low
	eor	v18.16b, v18.16b, v30.16b			//fold mid
	aese	v0.16b, v10.16b				//blk 0 - round 9
	eor3	v0.16b, v26.16b, v0.16b, v11.16b	//H^2 block - result
	str	q0, [x2], #16

L128_dec_w5r_g1:	//one block, GHASH with H^1
	ldr	q26, [x0], #16				//ciphertext 0
	rev32	v0.16b, v29.16b			//CTR block 0
	add	v29.4s, v29.4s, v31.4s
	aese	v0.16b, v1.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 0
	ldr	q24, [x6, #0]				//h1l | h1h
	ldr	d25, [x6, #16]				//h1k (64-bit)
	rev64	v20.16b, v26.16b				//GHASH H^1 block
	ext	v21.16b, v20.16b, v20.16b, #8		//H^1 mid
	aese	v0.16b, v2.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 1
	eor	v21.8b, v21.8b, v20.8b			//H^1 mid
	pmull2	v22.1q, v20.2d, v24.2d			//H^1 high
	pmull	v23.1q, v20.1d, v24.1d			//H^1 low
	pmull	v30.1q, v21.1d, v25.1d			//H^1 mid
	aese	v0.16b, v3.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 2
	aese	v0.16b, v4.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 3
	eor	v17.16b, v17.16b, v22.16b			//fold high
	eor	v19.16b, v19.16b, v23.16b			//fold low
	eor	v18.16b, v18.16b, v30.16b			//fold mid
	aese	v0.16b, v5.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 4
	aese	v0.16b, v6.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 5
	ldr	d16, [x10]				//MODULO - load modulo constant
	pmull	v22.1q, v17.1d, v16.1d			//MODULO - top 64b align with mid
	aese	v0.16b, v7.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 6
	eor	v23.16b, v17.16b, v19.16b		//MODULO - karatsuba tidy up
	ext	v17.16b, v17.16b, v17.16b, #8		//MODULO - other top alignment
	aese	v0.16b, v8.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 7
	eor	v18.16b, v18.16b, v23.16b		//MODULO - karatsuba tidy up
	eor	v22.16b, v17.16b, v22.16b		//MODULO - fold into mid
	aese	v0.16b, v9.16b
	aesmc	v0.16b, v0.16b			//blk 0 - round 8
	eor	v18.16b, v18.16b, v22.16b		//MODULO - fold into mid
	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	ext	v18.16b, v18.16b, v18.16b, #8		//MODULO - other mid alignment
	eor	v19.16b, v19.16b, v17.16b		//MODULO - fold into low
	eor	v19.16b, v19.16b, v18.16b		//MODULO - fold into low
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]				//store the tag
	rev32	v30.16b, v29.16b			//counter after the last block
	aese	v0.16b, v10.16b				//blk 0 - round 9
	str	q30, [x16]				//store the updated counter
	eor3	v0.16b, v26.16b, v0.16b, v11.16b	//H^1 block - result
	str	q0, [x2], #16

L128_dec_w5r_done:	//rejoin the one epilogue: single `ret` for nblk >= 1
	b	L128_dec_frame_restore
	.cfi_endproc

S2N_BN_SIZE_DIRECTIVE(aes128_gcm_dec_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
