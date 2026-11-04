// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// AES-256-GCM bulk encryption, 8 blocks at a time: counter-mode encryption of
// whole blocks with the GHASH tag update
// Inputs in[len_bits/8], len_bits, tag[2], ivec[16], key[240], htable[24];
// outputs out[len_bits/8], tag[2], ivec[16], returns bytes processed
//
//    extern uint64_t aes256_gcm_enc_alt(const uint8_t *in, uint64_t len_bits,
//                                            uint8_t *out, uint64_t *tag,
//                                            uint8_t *ivec,
//                                            const s2n_bignum_AES_KEY *key,
//                                            const uint64_t *htable);
//
// Processes the input "in" of "len_bits" bits under AES-256 in GCM mode: each
// 16-byte block is encrypted in counter mode using the counter block "ivec"
// and the AES round keys "key", the result is written to "out", and the
// running GHASH authenticator "tag" is updated over the OUTPUT (ciphertext)
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
// Of "key" only the 15 round keys (240 bytes) are read, not key->rounds, and
// of "htable" only these 192 bytes.
//
// The input must satisfy in + len_bits/8 < 2^63, because the loop control
// compares the input pointer with the main-loop end pointer as signed
// integers (cmp x0, x5 followed by b.ge or b.lt). The buffers written ("out",
// "tag" and "ivec") must not overlap each other, "in", "key" or "htable"; in
// particular, in-place operation (out == in) is not covered by the proof.
//
// This routine does not enforce the NIST GCM message limit.
// Callers must ensure the cumulative message length does not exceed 2^36 - 32 bytes (2^39 - 256 bits).
//
// Standard ARM ABI: X0 = in, X1 = len_bits, X2 = out, X3 = tag, X4 = ivec,
//                   X5 = key, X6 = htable, returns X0
// ----------------------------------------------------------------------------

// Origin: derived from AWS-LC's aesv8_gcm_8x_enc_256
// (crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-unroll8.pl, flavor linux64),
// with these changes:
//  - Entry: a whole-blocks guard (tst x1, #127; b.ne L256_enc_ret) follows
//    the zero-length check (cbz x1, L256_enc_ret) and precedes the d8-d15
//    saves, so the reject path returns 0 having touched no memory unless
//    len_bits is a nonzero multiple of 128.
//  - Final block: the partial-block masking machinery at
//    L256_enc_blocks_less_than_1 is removed as dead under the whole-blocks
//    contract, including the ld1 that reads existing output bytes (a 16-byte
//    overread of the output buffer) and the read-modify-write bif blend. The
//    final block is a plain full block, and the output buffer is never read.
//    The AWS-LC caller already satisfies the contract: its
//    crypto/fipsmodule/modes/gcm.c masks the length to whole blocks.
//  - The body has since been rescheduled for speed, so it is not a verbatim
//    copy of the generator's output.
#include "_internal_s2n_bignum_arm.h"

        .arch	armv8.2-a+crypto+sha3
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes256_gcm_enc_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes256_gcm_enc_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes256_gcm_enc_alt)
        .text
        .balign 4

#define STACK_SIZE 80 // 4*16 (d8-d15) + 16 (modulo constant scratch)

S2N_BN_SYMBOL(aes256_gcm_enc_alt):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        cbz	x1, L256_enc_ret
        tst	x1, #127				//whole-blocks contract: bit_len % 128 == 0
        b.ne	L256_enc_ret				//not whole blocks: process nothing, return 0

        CFI_DEC_SP(STACK_SIZE)
        CFI_STACKSAVE2X(d8,d9,0,8)
        lsr	x9, x1, #3
        mov	x16, x4
        mov	x11, x5
        CFI_STACKSAVE2X(d10,d11,16,24)
        CFI_STACKSAVE2X(d12,d13,32,40)
        CFI_STACKSAVE2X(d14,d15,48,56)
        mov	x5, #0xc200000000000000
        stp	x5, xzr, [sp, #64]
        add	x10, sp, #64

// -- BEGIN derived generator body (aesv8_gcm_8x_enc_256) --
	ld1	{ v0.16b}, [x16]					//CTR block 0

	mov	x5, x9

	mov	x15, #0x100000000			//set up counter increment
	movi	v31.16b, #0x0
	mov	v31.d[1], x15
	cmp	x9, #64		//nb <= 4 (<=64B)? -> ONE fused short path (single entry test)
	b.le	L256_enc_small
	add	v28.4s, v31.4s, v31.4s		//+2 increment (hoisted, load shadow)
	add	v10.4s, v28.4s, v31.4s		//+3 increment
	add	v11.4s, v28.4s, v28.4s		//+4 increment
	add	v12.4s, v11.4s, v31.4s		//+5 increment
	add	v13.4s, v11.4s, v28.4s		//+6 increment
	add	v14.4s, v11.4s, v10.4s		//+7 increment
	sub	x5, x5, #1		//byte_len - 1

	and	x5, x5, #0xffffffffffffff80	//number of bytes to be processed in main loop (at least 1 byte must be handled by tail)

	add	x5, x5, x0

	rev32	v29.16b, v0.16b				//set up reversed counter (base = v30_0)
	add	v8.4s, v29.4s, v31.4s		//CTR block 1 = base + 1
	add	v9.4s, v29.4s, v28.4s		//CTR block 2 = base + 2
	add	v15.4s, v29.4s, v10.4s		//CTR block 3 = base + 3
	add	v16.4s, v29.4s, v11.4s		//CTR block 4 = base + 4
	add	v17.4s, v29.4s, v12.4s		//CTR block 5 = base + 5
	add	v18.4s, v29.4s, v13.4s		//CTR block 6 = base + 6
	add	v30.4s, v29.4s, v14.4s		//CTR block 7 = base + 7
	rev32	v1.16b, v8.16b		//CTR block 1 (rev32)
	rev32	v2.16b, v9.16b		//CTR block 2 (rev32)
	rev32	v3.16b, v15.16b		//CTR block 3 (rev32)
	rev32	v4.16b, v16.16b		//CTR block 4 (rev32)
	rev32	v5.16b, v17.16b		//CTR block 5 (rev32)
	rev32	v6.16b, v18.16b		//CTR block 6 (rev32)
	rev32	v7.16b, v30.16b		//CTR block 7 (rev32)
	// SETUP AES rewritten round-major, keystream blocks 0,1 issued FIRST each round so
	// the g=0 tail (which consumes v0,v1) sees them complete before the 6 wasted blocks 2-7.
	// Pure permutation of the generator's 112 aese/104 aesmc + 8 key loads (same .o multiset).
	ldp	q26, q27, [x11, #0]			//load rk0, rk1
	ld1	{ v19.16b}, [x3]				//load tag
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	add	v30.4s, v30.4s, v31.4s		//CTR block 8 (advance for tail)


	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 0
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 0
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 0
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 0
	ldp	q28, q26, [x11, #32]			//load rk2, rk3

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 1
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 1
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 1
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 1
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 1
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 1

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 2
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 2
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 2
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 2
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 2
	ldp	q27, q28, [x11, #64]			//load rk4, rk5

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 3
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 3
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 3
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 3
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 3
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 3
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 3
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 3

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 4
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 4
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 4
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 4
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 4
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 4
	ldp	q26, q27, [x11, #96]			//load rk6, rk7

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 5
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 5
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 5
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 5
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 5
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 5
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 5

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 6
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 6
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 6
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 6
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 6
	ldp	q28, q26, [x11, #128]			//load rk8, rk9

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 7
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 7
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 7
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 7
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 7
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 7

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 8
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 8
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 8
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 8
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 8
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 8
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 8
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 8
	ldp	q27, q28, [x11, #160]			//load rk10, rk11

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 9
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 9
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 9
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 9
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 9
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 9
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 9

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 10
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 10
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 10
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 10
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 10
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 10
	ldp	q26, q27, [x11, #192]			//load rk12, rk13

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 11
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 11
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 11
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 11
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 11
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 11
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 11
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 11
	ldr	q28, [x11, #224]				//load rk14

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 12
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 12
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 12
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 12
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 12
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 12
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 12
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 12

	aese	v0.16b, v27.16b			//AES block 0 - round 13
	aese	v1.16b, v27.16b			//AES block 1 - round 13
	aese	v2.16b, v27.16b			//AES block 2 - round 13
	aese	v3.16b, v27.16b			//AES block 3 - round 13
	aese	v4.16b, v27.16b			//AES block 4 - round 13
	aese	v5.16b, v27.16b			//AES block 5 - round 13
	aese	v6.16b, v27.16b			//AES block 6 - round 13
	aese	v7.16b, v27.16b			//AES block 7 - round 13

	add	x4, x0, x1, lsr #3		//end_input_ptr
	cmp	x0, x5				//check if we have <= 8 blocks
	b.ge	L256_enc_tail						//handle tail

	ldp	q8, q9, [x0], #32			//AES block 0, 1 - load plaintext

	ldp	q10, q11, [x0], #32			//AES block 2, 3 - load plaintext

	eor3	v8.16b, v8.16b, v0.16b, v28.16b				//AES block 0 - result
	rev32	v0.16b, v30.16b				//CTR block 8
	add	v30.4s, v30.4s, v31.4s		//CTR block 8

	eor3	v9.16b, v9.16b, v1.16b, v28.16b				//AES block 1 - result
	eor3	v11.16b, v11.16b, v3.16b, v28.16b				//AES block 3 - result

	rev32	v1.16b, v30.16b				//CTR block 9
	add	v30.4s, v30.4s, v31.4s		//CTR block 9
	ldp	q12, q13, [x0], #32			//AES block 4, 5 - load plaintext

	ldp	q14, q15, [x0], #32			//AES block 6, 7 - load plaintext
	eor3	v10.16b, v10.16b, v2.16b, v28.16b				//AES block 2 - result
	cmp	x0, x5				//check if we have <= 8 blocks

	rev32	v2.16b, v30.16b				//CTR block 10
	add	v30.4s, v30.4s, v31.4s		//CTR block 10
	stp	q8, q9, [x2], #32			//AES block 0, 1 - store result

	stp	q10, q11, [x2], #32			//AES block 2, 3 - store result

	rev32	v3.16b, v30.16b				//CTR block 11
	add	v30.4s, v30.4s, v31.4s		//CTR block 11

	eor3	v12.16b, v12.16b, v4.16b, v28.16b				//AES block 4 - result

	eor3	v15.16b, v15.16b, v7.16b, v28.16b				//AES block 7 - result
	eor3	v14.16b, v14.16b, v6.16b, v28.16b				//AES block 6 - result
	eor3	v13.16b, v13.16b, v5.16b, v28.16b				//AES block 5 - result

	stp	q12, q13, [x2], #32			//AES block 4, 5 - store result
	rev32	v4.16b, v30.16b				//CTR block 12

	stp	q14, q15, [x2], #32			//AES block 6, 7 - store result
	add	v30.4s, v30.4s, v31.4s		//CTR block 12
	b.ge	L256_enc_prepretail					//do prepretail

L256_enc_main_loop:	//main	loop start
	ldp	q26, q27, [x11, #0]					//load rk0, rk1

	rev32	v5.16b, v30.16b				//CTR block 8k+13
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13
	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k

	rev64	v11.16b, v11.16b						//GHASH block 8k+3
	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h
	rev64	v9.16b, v9.16b						//GHASH block 8k+1

	rev32	v6.16b, v30.16b				//CTR block 8k+14
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14
	rev64	v8.16b, v8.16b						//GHASH block 8k

	rev64	v12.16b, v12.16b						//GHASH block 8k+4
	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0
	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0
	rev32	v7.16b, v30.16b				//CTR block 8k+15

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0

	ldp	q28, q26, [x11, #32]				//load rk2, rk3
	eor	v8.16b, v8.16b, v19.16b				 	//PRE 1
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1

	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low
	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high

	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2
	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	rev64	v14.16b, v14.16b						//GHASH block 8k+6
	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3
	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	rev64	v10.16b, v10.16b						//GHASH block 8k+2

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3

	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high
	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high
	rev64	v13.16b, v13.16b						//GHASH block 8k+5

	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low
	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low
	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h

	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
	eor3	v17.16b, v17.16b, v29.16b, v9.16b			//GHASH block 8k+2, 8k+3 - high
	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4

	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4

	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid
	ldp	q26, q27, [x11, #96]				//load rk6, rk7

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5

	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
	rev64	v15.16b, v15.16b						//GHASH block 8k+7

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5

	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid
	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k	- mid
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5

	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6

	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6

	eor3	v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+2, 8k+3 - low
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6

	ldp	q28, q26, [x11, #128]				//load rk8, rk9
	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7

	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7
	eor3	v18.16b, v18.16b, v21.16b, v29.16b			//GHASH block 8k+2, 8k+3 - mid

	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low

	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7

	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8

	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low
	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 9
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8

	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid
	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high
	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8

	eor3	v18.16b, v18.16b, v24.16b, v16.16b			//GHASH block 8k+4, 8k+5 - mid
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 9

	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 9
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 9

	ldp	q27, q28, [x11, #160]				//load rk10, rk11
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 9
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 9

	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high
	eor3	v19.16b, v19.16b, v25.16b, v23.16b			//GHASH block 8k+4, 8k+5 - low
	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low

	ldr	d16, [x10]			//MODULO - load modulo constant
	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 9

	eor3	v18.16b, v18.16b, v21.16b, v13.16b			//GHASH block 8k+6, 8k+7 - mid
	eor3	v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+6, 8k+7 - low
	eor3	v17.16b, v17.16b, v8.16b, v10.16b			//GHASH block 8k+4, 8k+5 - high

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 10
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 10

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 10
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 10
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 10
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 10

	eor3	v17.16b, v17.16b, v11.16b, v12.16b			//GHASH block 8k+6, 8k+7 - high

	ldp	q26, q27, [x11, #192]				//load rk12, rk13
	rev32	v20.16b, v30.16b					//CTR block 8k+16

	ext	v21.16b, v17.16b, v17.16b, #8			 	//MODULO - other top alignment
	ldp	q8, q9, [x0], #32			//AES block 8k+8, 8k+9 - load plaintext
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 11

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 11
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+16
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 11

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 11
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 11

	pmull	v29.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 11

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 12
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 11

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 12
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 12
	rev32	v22.16b, v30.16b					//CTR block 8k+17

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+17
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 11
	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//MODULO - karatsuba tidy up

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 12
	ldr	q28, [x11, #224]					//load rk14
	aese	v7.16b, v27.16b						//AES block 8k+15 - round 13

	ldp	q10, q11, [x0], #32			//AES block 8k+10, 8k+11 - load plaintext
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 12
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 12

	eor3	v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 12
	ldp	q12, q13, [x0], #32			//AES block 4, 5 - load plaintext

	ldp	q14, q15, [x0], #32			//AES block 6, 7 - load plaintext
	aese	v2.16b, v27.16b						//AES block 8k+10 - round 13
	aese	v4.16b, v27.16b						//AES block 8k+12 - round 13

	rev32	v23.16b, v30.16b					//CTR block 8k+18
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+18
	aese	v5.16b, v27.16b						//AES block 8k+13 - round 13

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 12
	aese	v3.16b, v27.16b						//AES block 8k+11 - round 13
	cmp	x0, x5				//.LOOP CONTROL

	eor3	v10.16b, v10.16b, v2.16b, v28.16b				//AES block 8k+10 - result
	rev32	v25.16b, v30.16b					//CTR block 8k+19
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+19

	aese	v0.16b, v27.16b						//AES block 8k+8 - round 13
	aese	v6.16b, v27.16b						//AES block 8k+14 - round 13
	eor3	v13.16b, v13.16b, v5.16b, v28.16b				//AES block 5 - result

	ext	v21.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment
	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v1.16b, v27.16b						//AES block 8k+9 - round 13

	eor3	v12.16b, v12.16b, v4.16b, v28.16b				//AES block 4 - result
	rev32	v4.16b, v30.16b				//CTR block 8k+20
	eor3	v11.16b, v11.16b, v3.16b, v28.16b				//AES block 8k+11 - result

	mov	v3.16b, v25.16b					//CTR block 8k+19
	eor3	v9.16b, v9.16b, v1.16b, v28.16b				//AES block 8k+9 - result
	eor3	v8.16b, v8.16b, v0.16b, v28.16b				//AES block 8k+8 - result

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+20
	stp	q8, q9, [x2], #32			//AES block 8k+8, 8k+9 - store result
	mov	v2.16b, v23.16b					//CTR block 8k+18

	eor3	v15.16b, v15.16b, v7.16b, v28.16b				//AES block 7 - result
	eor3	v19.16b, v19.16b, v21.16b, v17.16b	//MODULO - fold into low
	stp	q10, q11, [x2], #32			//AES block 8k+10, 8k+11 - store result

	eor3	v14.16b, v14.16b, v6.16b, v28.16b				//AES block 6 - result
	mov	v1.16b, v22.16b					//CTR block 8k+17
	stp	q12, q13, [x2], #32			//AES block 4, 5 - store result

	stp	q14, q15, [x2], #32			//AES block 6, 7 - store result
	mov	v0.16b, v20.16b					//CTR block 8k+16
	b.lt	L256_enc_main_loop

L256_enc_prepretail:	//PREPRETAIL
	rev32	v5.16b, v30.16b				//CTR block 8k+13
	ldp	q26, q27, [x11, #0]					//load rk0, rk1
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13

	rev64	v10.16b, v10.16b						//GHASH block 8k+2

	rev32	v6.16b, v30.16b				//CTR block 8k+14
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14

	rev64	v13.16b, v13.16b						//GHASH block 8k+5
	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k

	rev32	v7.16b, v30.16b				//CTR block 8k+15

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0

	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0
	rev64	v8.16b, v8.16b						//GHASH block 8k
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1

	rev64	v9.16b, v9.16b						//GHASH block 8k+1
	ldp	q28, q26, [x11, #32]				//load rk2, rk3
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1

	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1

	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	eor	v8.16b, v8.16b, v19.16b					//PRE 1

	rev64	v11.16b, v11.16b						//GHASH block 8k+3
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2

	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high

	rev64	v14.16b, v14.16b						//GHASH block 8k+6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid

	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3
	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high

	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low
	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3

	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5
	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k	- mid
	eor3	v17.16b, v17.16b, v29.16b, v9.16b			//GHASH block 8k+2, 8k+3 - high

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4
	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4
	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4

	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low
	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid

	rev64	v12.16b, v12.16b						//GHASH block 8k+4
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5
	ldp	q26, q27, [x11, #96]				//load rk6, rk7

	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h
	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid

	eor3	v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+2, 8k+3 - low
	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5
	rev64	v15.16b, v15.16b						//GHASH block 8k+7
	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
	eor3	v18.16b, v18.16b, v21.16b, v29.16b			//GHASH block 8k+2, 8k+3 - mid

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6

	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6

	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low
	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h

	ldp	q28, q26, [x11, #128]				//load rk8, rk9
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7

	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7
	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7
	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid

	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high
	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7

	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8
	eor3	v19.16b, v19.16b, v25.16b, v23.16b			//GHASH block 8k+4, 8k+5 - low
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8

	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid
	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8

	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high
	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid

	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low
	eor3	v18.16b, v18.16b, v24.16b, v16.16b			//GHASH block 8k+4, 8k+5 - mid
	eor3	v17.16b, v17.16b, v8.16b, v10.16b			//GHASH block 8k+4, 8k+5 - high

	ldp	q27, q28, [x11, #160]				//load rk10, rk11
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 9
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 9

	eor3	v17.16b, v17.16b, v11.16b, v12.16b			//GHASH block 8k+6, 8k+7 - high
	eor3	v18.16b, v18.16b, v21.16b, v13.16b			//GHASH block 8k+6, 8k+7 - mid
	ldr	d16, [x10]			//MODULO - load modulo constant

	eor3	v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+6, 8k+7 - low

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 9
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 9

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 9
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 9

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 10
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 10
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 9

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 10

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 10
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 10
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 10

	pmull	v29.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid
	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//MODULO - karatsuba tidy up
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 11

	ldp	q26, q27, [x11, #192]				//load rk12, rk13
	ext	v21.16b, v17.16b, v17.16b, #8			 	//MODULO - other top alignment
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 11

	eor3	v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 11
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 11

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 11
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 11
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 11

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 11
	ldr	q28, [x11, #224]					//load rk14

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 12
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 12
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 12

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 12
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 12
	ext	v21.16b, v18.16b, v18.16b, #8			 	//MODULO - other mid alignment

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 12
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 12
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 12
	aese	v0.16b, v27.16b						//AES block 8k+8 - round 13

	eor3	v19.16b, v19.16b, v21.16b, v17.16b	//MODULO - fold into low
	aese	v5.16b, v27.16b						//AES block 8k+13 - round 13
	aese	v1.16b, v27.16b						//AES block 8k+9 - round 13

	aese	v3.16b, v27.16b						//AES block 8k+11 - round 13
	aese	v4.16b, v27.16b						//AES block 8k+12 - round 13
	aese	v7.16b, v27.16b						//AES block 8k+15 - round 13

	aese	v2.16b, v27.16b						//AES block 8k+10 - round 13
	aese	v6.16b, v27.16b						//AES block 8k+14 - round 13
L256_enc_tail:	//TAIL

	ldp	q24, q25, [x6, #160]			//load h8l | h8h
	sub	x5, x4, x0		//main_end_input_ptr is number of bytes left to process

	ldr	q8, [x0], #16				//AES block 8k+8 - load plaintext

	ldp	q20, q21, [x6, #96]			//load h5l | h5h

	ext	v16.16b, v19.16b, v19.16b, #8				//prepare final partial tag
	ldp	q22, q23, [x6, #128]			//load h6l | h6h
	mov	v29.16b, v28.16b

	cmp	x5, #112
	eor3	v9.16b, v8.16b, v0.16b, v29.16b				//AES block 8k+8 - result
	b	L256_enc_tail_dispatch	//peel rem=8 (inline exact8) and rem=2 before the slides

L256_enc_tail_slides:		//rem in {1,3,4,5,6,7} rejoin here (addresses unchanged)
	movi	v19.8b, #0
	mov	v7.16b, v6.16b
	movi	v17.8b, #0

	mov	v6.16b, v5.16b
	mov	v5.16b, v4.16b
	mov	v4.16b, v3.16b

	mov	v3.16b, v2.16b
	sub	v30.4s, v30.4s, v31.4s
	mov	v2.16b, v1.16b

	movi	v18.8b, #0
	cmp	x5, #96
	b.gt	L256_enc_blocks_more_than_6

	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b
	cmp	x5, #80

	mov	v5.16b, v4.16b
	mov	v4.16b, v3.16b
	mov	v3.16b, v1.16b

	sub	v30.4s, v30.4s, v31.4s
	b.gt	L256_enc_blocks_more_than_5

	mov	v7.16b, v6.16b
	sub	v30.4s, v30.4s, v31.4s

	mov	v6.16b, v5.16b
	mov	v5.16b, v4.16b

	cmp	x5, #64
	mov	v4.16b, v1.16b
	b.gt	L256_enc_blocks_more_than_4

	cmp	x5, #48
	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b

	mov	v5.16b, v1.16b
	sub	v30.4s, v30.4s, v31.4s
	b.gt	L256_enc_rem4_drain	//rem=4 (64B/192B) -> dedicated eor3-fused drain

	cmp	x5, #32
	mov	v7.16b, v6.16b
	ldr	q24, [x6, #64]				//load h4k | h3k

	mov	v6.16b, v1.16b
	sub	v30.4s, v30.4s, v31.4s
	b.gt	L256_enc_blocks_more_than_2

	mov	v7.16b, v1.16b

	sub	v30.4s, v30.4s, v31.4s
	cmp	x5, #16
	b.gt	L256_enc_blocks_more_than_1

	sub	v30.4s, v30.4s, v31.4s
	ldr	q21, [x6, #16]				//load h2k | h1k
	b	L256_enc_blocks_less_than_1
L256_enc_blocks_more_than_6:	//blocks	left >  6

	st1	{ v9.16b}, [x2], #16				//AES final-6 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-6 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-6 block - low
	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-6 block - mid
	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-6 block - high

	ldr	q9, [x0], #16				//AES final-5 block - load plaintext

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-6 block - low

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-6 block - mid

	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-6 block - mid
	eor3	v9.16b, v9.16b, v2.16b, v29.16b			//AES final-5 block - result

	movi	v16.8b, #0						//supress further partial tag feed in

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-6 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-6 block - high
L256_enc_blocks_more_than_5:	//blocks	left >  5

	st1	{ v9.16b}, [x2], #16				//AES final-5 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-5 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-5 block - mid

	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-5 block - high

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-5 block - high
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-5 block - mid

	ext	v12.16b, v21.16b, v21.16b, #8			//[R2c] h5k(hi lane) to low lane

	ldr	q9, [x0], #16				//AES final-4 block - load plaintext
	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-5 block - low

	pmull	v27.1q, v27.1d, v12.1d				//[R2c] final-5 mid (pmull low, h5k in v12)
	movi	v16.8b, #0						//supress further partial tag feed in
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-5 block - low

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-5 block - mid
	eor3	v9.16b, v9.16b, v3.16b, v29.16b			//AES final-4 block - result
L256_enc_blocks_more_than_4:	//blocks	left >  4

	st1	{ v9.16b}, [x2], #16				//AES final-4 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-4 block

	ldr	q9, [x0], #16				//AES final-3 block - load plaintext

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-4 block - mid
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final-4 block - high

	eor3	v9.16b, v9.16b, v4.16b, v29.16b			//AES final-3 block - result
	pmull	v26.1q, v8.1d, v20.1d				//GHASH final-4 block - low

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-4 block - mid
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-4 block - low

	pmull	v27.1q, v27.1d, v21.1d				//GHASH final-4 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-4 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-4 block - high
L256_enc_blocks_more_than_3:	//blocks	left >  3
	b	L256_enc_rem4_drain	//rem 5/6/7 finish on the shared eor3-fused rem4 drain
L256_enc_blocks_more_than_2:	//blocks	left >  2

	ldr	q23, [x6, #48]				//load h3l | h3h

	st1	{ v9.16b}, [x2], #16			 	//AES final-2 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-2 block
	ldr	q9, [x0], #16				//AES final-1 block - load plaintext

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-2 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in

	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-2 block - high
	eor3	v9.16b, v9.16b, v6.16b, v29.16b			//AES final-1 block - result

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-2 block - mid

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-2 block - high

	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-2 block - mid
	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-2 block - low

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-2 block - mid
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-2 block - low
L256_enc_blocks_more_than_1:	//blocks	left >  1

	st1	{ v9.16b}, [x2], #16				//AES final-1 block - store result

	ldr	q22, [x6, #32]				//load h2l | h2h
	rev64	v8.16b, v9.16b						//GHASH final-1 block
	ldr	q9, [x0], #16				//AES final block - load plaintext

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	movi	v16.8b, #0						//supress further partial tag feed in

	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-1 block - mid
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-1 block - high

	eor3	v9.16b, v9.16b, v7.16b, v29.16b			//AES final block - result
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-1 block - high

	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-1 block - low
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-1 block - mid

	ldr	q21, [x6, #16]				//load h2k | h1k
	ext	v10.16b, v21.16b, v21.16b, #8			//[R2] h2k(hi lane) to low lane

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-1 block - low
	// [R2] ins v27.d[1] removed (pmull low lane, h2k in v10)

	pmull	v27.1q, v27.1d, v10.1d				//[R2] final-1 mid (pmull low, h2k in v10)

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-1 block - mid
L256_enc_blocks_less_than_1:	//final whole block (whole-blocks contract: never partial)

	ldr	q20, [x6]				//load h1l | h1h

	rev64	v8.16b, v9.16b						//GHASH final block

	rev32	v30.16b, v30.16b
	str	q30, [x16]					//store the updated counter

	eor	v8.16b, v8.16b, v16.16b					//feed in tag
	st1	{ v9.16b}, [x2]				//store all 16B

	ins	v16.d[0], v8.d[1]					//GHASH final block - mid
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final block - high
	pmull	v26.1q, v8.1d, v20.1d				//GHASH final block - low

	eor	v17.16b, v17.16b, v28.16b					//GHASH final block - high
	eor	v19.16b, v19.16b, v26.16b					//GHASH final block - low

	eor	v16.8b, v16.8b, v8.8b				//GHASH final block - mid

	pmull	v16.1q, v16.1d, v21.1d				//GHASH final block - mid

	eor	v18.16b, v18.16b, v16.16b				//GHASH final block - mid
	ldr	d16, [x10]			//MODULO - load modulo constant

	ext	v21.16b, v17.16b, v17.16b, #8				//MODULO - other top alignment

	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//MODULO - karatsuba tidy up
	pmull	v29.1q, v17.1d, v16.1d			//MODULO - top 64b align with mid

	eor3	v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	ext	v21.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment

	eor3	v19.16b, v19.16b, v17.16b, v21.16b	//MODULO - fold into low
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]
L256_enc_epilogue:  //both paths converge here
	mov	x0, x9					//return sizes
// -- END derived generator body --

        .cfi_remember_state
        CFI_STACKLOAD2(d10,d11,16)
        CFI_STACKLOAD2(d12,d13,32)
        CFI_STACKLOAD2(d14,d15,48)
        CFI_STACKLOAD2(d8,d9,0)
        CFI_INC_SP(STACK_SIZE)
        ret
        .cfi_restore_state

// Frameless return for the entry guards, reached before the frame is set up.
L256_enc_ret:
        .cfi_remember_state
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
        .cfi_restore_state


L256_enc_exact8_drain:  //dedicated exact-8 GHASH drain (no no-op tag eors)
	st1	{ v9.16b}, [x2], #16				//AES final-7 block  - store result

	rev64	v8.16b, v9.16b						//GHASH final-7 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ldr	q9, [x0], #16				//AES final-6 block - load plaintext

	pmull2	v17.1q, v8.2d, v25.2d				//GHASH final-7 block - high
	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-7 block - mid
	ins	v18.d[0], v24.d[1]					//GHASH final-7 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-7 block - mid
	eor3	v9.16b, v9.16b, v1.16b, v29.16b			//AES final-6 block - result

	pmull	v18.1q, v27.1d, v18.1d				//GHASH final-7 block - mid
	pmull	v19.1q, v8.1d, v25.1d				//GHASH final-7 block - low

	st1	{ v9.16b}, [x2], #16				//AES final-6 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-6 block


	pmull	v14.1q, v8.1d, v23.1d				//final-6 low -> v14
	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-6 block - mid
	pmull2	v13.1q, v8.2d, v23.2d				//final-6 high -> v13

	ldr	q9, [x0], #16				//AES final-5 block - load plaintext


	eor	v27.8b, v27.8b, v8.8b				//GHASH final-6 block - mid

	pmull	v15.1q, v27.1d, v24.1d				//final-6 mid -> v15
	eor3	v9.16b, v9.16b, v2.16b, v29.16b			//AES final-5 block - result



	st1	{ v9.16b}, [x2], #16				//AES final-5 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-5 block


	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-5 block - mid

	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-5 block - high

	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//fused high (pair)
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-5 block - mid

	ext	v12.16b, v21.16b, v21.16b, #8			//[R2c] h5k(hi lane) to low lane

	ldr	q9, [x0], #16				//AES final-4 block - load plaintext
	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-5 block - low

	pmull	v27.1q, v27.1d, v12.1d				//[R2c] final-5 mid (pmull low, h5k in v12)
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//fused low (pair)

	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//fused mid (pair)
	eor3	v9.16b, v9.16b, v3.16b, v29.16b			//AES final-4 block - result

	st1	{ v9.16b}, [x2], #16				//AES final-4 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-4 block

	ldr	q9, [x0], #16				//AES final-3 block - load plaintext


	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-4 block - mid
	pmull2	v13.1q, v8.2d, v20.2d				//final-4 high -> v13

	eor3	v9.16b, v9.16b, v4.16b, v29.16b			//AES final-3 block - result
	pmull	v14.1q, v8.1d, v20.1d				//final-4 low -> v14

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-4 block - mid

	pmull	v15.1q, v27.1d, v21.1d				//final-4 mid -> v15



	st1	{ v9.16b}, [x2], #16				//AES final-3 block - store result

	ldr	q25, [x6, #80]				//load h4l | h4h
	rev64	v8.16b, v9.16b						//GHASH final-3 block


	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-3 block - mid
	pmull2	v28.1q, v8.2d, v25.2d				//GHASH final-3 block - high

	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//fused high (pair)
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-3 block - mid
	ldr	q24, [x6, #64]				//load h4k | h3k
	ext	v11.16b, v24.16b, v24.16b, #8			//[R2b] h3k(hi lane) to low lane

	// [R2b] ins v27.d[1] removed (final-3, pmull low, h3k in v11)
	ldr	q9, [x0], #16				//AES final-2 block - load plaintext

	pmull	v27.1q, v27.1d, v11.1d				//[R2b] final-3 mid (pmull low, h3k in v11)
	pmull	v26.1q, v8.1d, v25.1d				//GHASH final-3 block - low

	eor3	v9.16b, v9.16b, v5.16b, v29.16b			//AES final-2 block - result

	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//fused mid (pair)
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//fused low (pair)

	ldr	q23, [x6, #48]				//load h3l | h3h

	st1	{ v9.16b}, [x2], #16			 	//AES final-2 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-2 block
	ldr	q9, [x0], #16				//AES final-1 block - load plaintext


	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-2 block - mid


	pmull2	v13.1q, v8.2d, v23.2d				//final-2 high -> v13
	eor3	v9.16b, v9.16b, v6.16b, v29.16b			//AES final-1 block - result

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-2 block - mid


	pmull	v15.1q, v27.1d, v24.1d				//final-2 mid -> v15
	pmull	v14.1q, v8.1d, v23.1d				//final-2 low -> v14


	st1	{ v9.16b}, [x2], #16				//AES final-1 block - store result

	ldr	q22, [x6, #32]				//load h2l | h2h
	rev64	v8.16b, v9.16b						//GHASH final-1 block
	ldr	q9, [x0], #16				//AES final block - load plaintext


	ext	v27.16b, v8.16b, v8.16b, #8					//GHASH final-1 block - mid
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-1 block - high

	eor3	v9.16b, v9.16b, v7.16b, v29.16b			//AES final block - result
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//fused high (pair)

	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-1 block - low
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-1 block - mid

	ldr	q21, [x6, #16]				//load h2k | h1k
	ext	v10.16b, v21.16b, v21.16b, #8			//[R2] h2k(hi lane) to low lane

	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//fused low (pair)
	// [R2] ins v27.d[1] removed (pmull low lane, h2k in v10)

	pmull	v27.1q, v27.1d, v10.1d				//[R2] final-1 mid (pmull low, h2k in v10)

	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//fused mid (pair)

	ldr	q20, [x6]				//load h1l | h1h

	rev64	v8.16b, v9.16b						//GHASH final block

	rev32	v30.16b, v30.16b
	str	q30, [x16]					//store the updated counter

	st1	{ v9.16b}, [x2]				//store all 16B

	ins	v16.d[0], v8.d[1]					//GHASH final block - mid
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final block - high
	pmull	v26.1q, v8.1d, v20.1d				//GHASH final block - low

	eor	v17.16b, v17.16b, v28.16b					//GHASH final block - high
	eor	v19.16b, v19.16b, v26.16b					//GHASH final block - low

	eor	v16.8b, v16.8b, v8.8b				//GHASH final block - mid

	pmull	v16.1q, v16.1d, v21.1d				//GHASH final block - mid

	eor	v18.16b, v18.16b, v16.16b				//GHASH final block - mid
	ldr	d16, [x10]			//MODULO - load modulo constant

	ext	v21.16b, v17.16b, v17.16b, #8				//MODULO - other top alignment

	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//MODULO - karatsuba tidy up
	pmull	v29.1q, v17.1d, v16.1d			//MODULO - top 64b align with mid

	eor3	v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	ext	v21.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment

	eor3	v19.16b, v19.16b, v17.16b, v21.16b	//MODULO - fold into low
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]
	b	L256_enc_epilogue

L256_enc_rem4_drain:  //dedicated rem=4 (192B only; 64B routes to L256_enc_small) GHASH drain, eor3-fused
	// entry (shuffled by tail, x5=64): v9=ct(v0 block final-3), v5/v6/v7=keystreams for
	// final-2/-1/final, v16=partial tag, v17/v18/v19=0, v29=rk14, v30=base+4, x0/x2/x3 positioned.
	// pair (final-3,final-2) and (final-1,final): A-block products to free v13/v14/v15, B fuses.
	// --- block final-3 (A): products -> v13(hi)/v14(lo)/v15(mid) ---
	st1	{ v9.16b}, [x2], #16
	ldr	q25, [x6, #80]			//h4l | h4h
	rev64	v8.16b, v9.16b
	eor	v8.16b, v8.16b, v16.16b		//feed in partial tag
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v13.1q, v8.2d, v25.2d		//final-3 high -> v13
	ldr	q24, [x6, #64]			//h4k | h3k
	ext	v11.16b, v24.16b, v24.16b, #8	//[R2b] mid key hi->lo lane
	eor	v27.8b, v27.8b, v8.8b
	ldr	q9, [x0], #16			//final-2 - load plaintext
	pmull	v15.1q, v27.1d, v11.1d		//final-3 mid -> v15
	pmull	v14.1q, v8.1d, v25.1d		//final-3 low -> v14
	eor3	v9.16b, v9.16b, v5.16b, v29.16b		//final-2 - result
	// --- block final-2 (B): products -> v28/v26/v27, fuse pair-1 ---
	// dropped no-op `eor v8,v8,v16` (v16=0) + dead `movi v16` here and below
	st1	{ v9.16b}, [x2], #16
	ldr	q23, [x6, #48]			//h3l | h3h
	rev64	v8.16b, v9.16b
	ldr	q9, [x0], #16			//final-1 - load plaintext
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v28.1q, v8.2d, v23.2d		//final-2 high
	eor3	v9.16b, v9.16b, v6.16b, v29.16b		//final-1 - result
	eor	v27.8b, v27.8b, v8.8b
	pmull	v26.1q, v8.1d, v23.1d		//final-2 low
	pmull	v27.1q, v27.1d, v24.1d		//final-2 mid
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//fused high (pair-1)
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//fused low (pair-1)
	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//fused mid (pair-1)
	// --- block final-1 (A): products -> v13(hi)/v14(lo)/v15(mid) ---
	st1	{ v9.16b}, [x2], #16
	ldr	q22, [x6, #32]			//h2l | h2h
	rev64	v8.16b, v9.16b
	ldr	q9, [x0], #16			//final - load plaintext
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v13.1q, v8.2d, v22.2d		//final-1 high -> v13
	eor3	v9.16b, v9.16b, v7.16b, v29.16b		//final - result
	pmull	v14.1q, v8.1d, v22.1d		//final-1 low -> v14
	eor	v27.8b, v27.8b, v8.8b
	ldr	q21, [x6, #16]			//h2k | h1k
	ext	v10.16b, v21.16b, v21.16b, #8	//h2k hi->lo lane
	pmull	v15.1q, v27.1d, v10.1d		//final-1 mid -> v15
	// --- block final (B): products -> v28/v26/v16, fuse pair-2, then MODULO ---
	ldr	q20, [x6]			//h1l | h1h
	rev64	v8.16b, v9.16b
	rev32	v30.16b, v30.16b
	str	q30, [x16]			//store the updated counter
	st1	{ v9.16b}, [x2]			//store all 16B
	ins	v16.d[0], v8.d[1]		//final mid (v16 lane1 dead: only .d[0]/.8b read below)
	pmull2	v28.1q, v8.2d, v20.2d		//final high
	pmull	v26.1q, v8.1d, v20.1d		//final low
	eor	v16.8b, v16.8b, v8.8b		//final mid
	pmull	v16.1q, v16.1d, v21.1d		//final mid (h1k)
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//fused high (pair-2)
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//fused low (pair-2)
	eor3	v18.16b, v18.16b, v16.16b, v15.16b	//fused mid (pair-2)
	ldr	d16, [x10]			//MODULO - load modulo constant
	ext	v21.16b, v17.16b, v17.16b, #8			//MODULO - other top alignment
	eor3	v18.16b, v18.16b, v17.16b, v19.16b		//MODULO - karatsuba tidy up
	pmull	v29.1q, v17.1d, v16.1d			//MODULO - top 64b align with mid
	eor3	v18.16b, v18.16b, v29.16b, v21.16b		//MODULO - fold into mid
	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	ext	v21.16b, v18.16b, v18.16b, #8			//MODULO - other mid alignment
	eor3	v19.16b, v19.16b, v17.16b, v21.16b		//MODULO - fold into low
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]
	b	L256_enc_epilogue

L256_enc_tail_dispatch:  //flags still hold (x5 vs #112) from the tail-entry cmp
	b.gt	L256_enc_exact8_drain	//rem=8 (x5>112): inline exact-8 drain (unchanged)
	cmp	x5, #32			//rem=2 (32B)?
	b.eq	L256_enc_rem2_drain
	b	L256_enc_tail_slides	//rem in {1,3,4,5,6,7}: rejoin the slide cascade

L256_enc_rem2_drain:  //rem=2: eor3-fused 2-block drain (block1 products -> v13/14/15, fused accum)
	sub	v30.4s, v30.4s, v31.4s
	ldr	q22, [x6, #32]			//h2l|h2h
	sub	v30.4s, v30.4s, v31.4s
	ldr	q21, [x6, #16]			//h2k|h1k
	sub	v30.4s, v30.4s, v31.4s
	ldr	q20, [x6]			//h1l|h1h
	sub	v30.4s, v30.4s, v31.4s
	st1	{ v9.16b}, [x2], #16		//block1 ct
	sub	v30.4s, v30.4s, v31.4s
	rev64	v8.16b, v9.16b
	sub	v30.4s, v30.4s, v31.4s
	eor	v8.16b, v8.16b, v16.16b		//feed tag
	ldr	q9, [x0], #16			//block2 PT
	ext	v27.16b, v8.16b, v8.16b, #8
	ext	v10.16b, v21.16b, v21.16b, #8	//h2k hi->lo
	pmull2	v13.1q, v8.2d, v22.2d		//block1 hi -> v13
	eor	v27.8b, v27.8b, v8.8b
	pmull	v14.1q, v8.1d, v22.1d		//block1 lo -> v14
	eor3	v9.16b, v9.16b, v1.16b, v29.16b
	pmull	v15.1q, v27.1d, v10.1d		//block1 mid -> v15
	st1	{ v9.16b}, [x2]			//block2 ct
	rev64	v8.16b, v9.16b
	ins	v16.d[0], v8.d[1]		//block2 mid prep
	pmull2	v28.1q, v8.2d, v20.2d		//block2 hi
	pmull	v26.1q, v8.1d, v20.1d		//block2 lo
	eor	v16.8b, v16.8b, v8.8b
	pmull	v16.1q, v16.1d, v21.1d		//block2 mid (h1k)
	eor	v17.16b, v13.16b, v28.16b	//fused hi
	eor	v19.16b, v14.16b, v26.16b	//fused lo
	eor	v18.16b, v15.16b, v16.16b	//fused mid
	rev32	v30.16b, v30.16b
	str	q30, [x16]			//ivec store
	ldr	d16, [x10]			//modulo const
	ext	v21.16b, v17.16b, v17.16b, #8
	eor3	v18.16b, v18.16b, v17.16b, v19.16b
	pmull	v29.1q, v17.1d, v16.1d
	eor3	v18.16b, v18.16b, v29.16b, v21.16b
	pmull	v17.1q, v18.1d, v16.1d
	ext	v21.16b, v18.16b, v18.16b, #8
	eor3	v19.16b, v19.16b, v17.16b, v21.16b
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]		//tag store
	b	L256_enc_epilogue

L256_enc_small:  //fused nb<=4 short path (single entry test cmp x9,#64/b.le).
	// shared self-load prefix (skips the 8-block counter build); then internal nb dispatch.
	rev32	v29.16b, v0.16b
	ldp	q26, q27, [x11, #0]
	ld1	{ v19.16b}, [x3]
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	add	v28.4s, v31.4s, v31.4s	//+2
	add	v10.4s, v28.4s, v31.4s	//+3
	add	v11.4s, v28.4s, v28.4s	//+4
	// each small_N body builds its final counter directly
	// reversal index synthesized ONCE in the shared prefix (route B);
	// Q12 lives across dispatch.
	movz	x7, #0x0e0f
	movk	x7, #0x0c0d, lsl #16
	movk	x7, #0x0a0b, lsl #32
	movk	x7, #0x0809, lsl #48
	movz	x8, #0x0607
	movk	x8, #0x0405, lsl #16
	movk	x8, #0x0203, lsl #32
	movk	x8, #0x0001, lsl #48
	fmov	d12, x7
	mov	v12.d[1], x8
	cmp	x9, #16
	b.eq	L256_enc_small_1
	cmp	x9, #32
	b.eq	L256_enc_small_2
	cmp	x9, #48
	b.eq	L256_enc_small_3
L256_enc_small_4:  //nb==4 (64B): 4-block AES + fast4 eor3-fused drain (tbl v12)
	add	v30.4s, v29.4s, v11.4s	//final counter = base+4 = ctr(c+nb), direct
	add	v8.4s, v29.4s, v31.4s	//counter1
	rev32	v1.16b, v8.16b
	add	v9.4s, v29.4s, v28.4s	//counter2
	rev32	v2.16b, v9.16b
	add	v15.4s, v29.4s, v10.4s	//counter3
	rev32	v3.16b, v15.16b
	// index synth hoisted to shared prefix (Q12 already set on entry)
	mov	x12, x11			//AES re-roll: walking round-key pointer (rk0)
	mov	w13, #13
L256_enc_small_4_aesloop:
	ld1	{ v26.16b }, [x12], #16
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b
	subs	w13, w13, #1
	b.ne	L256_enc_small_4_aesloop
	ld1	{ v26.16b }, [x12], #16		//rk13 (no aesmc)
	aese	v0.16b, v26.16b
	aese	v1.16b, v26.16b
	aese	v2.16b, v26.16b
	aese	v3.16b, v26.16b
	ldr	q28, [x12]			//rk14 -> v28 (drain: mov v29,v28)
	ldr	q8, [x0], #16			//block0 PT (x0 -> block1 PT)
	ext	v16.16b, v19.16b, v19.16b, #8	//partial tag
	mov	v29.16b, v28.16b		//v29 = rk14
	// dropped mov v5/6/7 <- v1/2/3; fast4_drain reads v1/v2/v3 directly
	movi	v17.8b, #0
	movi	v18.8b, #0
	movi	v19.8b, #0
	eor3	v9.16b, v8.16b, v0.16b, v29.16b
	st1	{ v9.16b}, [x2], #16
	ldr	q25, [x6, #80]			//h4l | h4h
	rev64	v8.16b, v9.16b
	eor	v8.16b, v8.16b, v16.16b		//feed in partial tag
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v13.1q, v8.2d, v25.2d		//final-3 high -> v13
	ldr	q24, [x6, #64]			//h4k | h3k
	ext	v11.16b, v24.16b, v24.16b, #8	//mid key hi->lo lane
	eor	v27.8b, v27.8b, v8.8b
	ldr	q9, [x0], #16			//final-2 - load plaintext
	pmull	v15.1q, v27.1d, v11.1d		//final-3 mid -> v15
	pmull	v14.1q, v8.1d, v25.1d		//final-3 low -> v14
	eor3	v9.16b, v9.16b, v1.16b, v29.16b	//final-2 - result
	st1	{ v9.16b}, [x2], #16
	ldr	q23, [x6, #48]			//h3l | h3h
	rev64	v8.16b, v9.16b			//byteswap ct block for GHASH fold
	ldr	q9, [x0], #16			//final-1 - load plaintext
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v28.1q, v8.2d, v23.2d		//final-2 high
	eor3	v9.16b, v9.16b, v2.16b, v29.16b	//final-1 - result
	eor	v27.8b, v27.8b, v8.8b
	pmull	v26.1q, v8.1d, v23.1d		//final-2 low
	pmull	v27.1q, v27.1d, v24.1d		//final-2 mid
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//fused high (pair-1)
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//fused low (pair-1)
	eor3	v18.16b, v18.16b, v27.16b, v15.16b	//fused mid (pair-1)
	st1	{ v9.16b}, [x2], #16
	ldr	q22, [x6, #32]			//h2l | h2h
	rev64	v8.16b, v9.16b			//byteswap ct block for GHASH fold
	ldr	q9, [x0], #16			//final - load plaintext
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v13.1q, v8.2d, v22.2d		//final-1 high -> v13
	eor3	v9.16b, v9.16b, v3.16b, v29.16b	//final - result
	pmull	v14.1q, v8.1d, v22.1d		//final-1 low -> v14
	eor	v27.8b, v27.8b, v8.8b
	ldr	q21, [x6, #16]			//h2k | h1k
	ext	v10.16b, v21.16b, v21.16b, #8	//h2k hi->lo lane
	pmull	v15.1q, v27.1d, v10.1d		//final-1 mid -> v15
	ldr	q20, [x6]			//h1l | h1h
	rev64	v8.16b, v9.16b
	rev32	v30.16b, v30.16b
	str	q30, [x16]			//store the updated counter
	st1	{ v9.16b}, [x2]			//store all 16B no-op tag eor removed
	ins	v16.d[0], v8.d[1]		//final mid
	pmull2	v28.1q, v8.2d, v20.2d		//final high
	pmull	v26.1q, v8.1d, v20.1d		//final low
	eor	v16.8b, v16.8b, v8.8b		//final mid
	pmull	v16.1q, v16.1d, v21.1d		//final mid (h1k)
	eor3	v17.16b, v17.16b, v28.16b, v13.16b	//fused high (pair-2)
	eor3	v19.16b, v19.16b, v26.16b, v14.16b	//fused low (pair-2)
	eor3	v18.16b, v18.16b, v16.16b, v15.16b	//fused mid (pair-2)
	b	L256_enc_small_reduce
L256_enc_small_3:  //nb==3 (48B): 3-block AES + 3-block drain (tbl v12)
	add	v30.4s, v29.4s, v10.4s	//final counter = base+3 = ctr(c+nb), direct
	add	v8.4s, v29.4s, v31.4s	//counter1
	rev32	v1.16b, v8.16b
	add	v9.4s, v29.4s, v28.4s	//counter2
	rev32	v2.16b, v9.16b
	// index synth hoisted to shared prefix (Q12 already set on entry)
	// v26=rk0, v27=rk1 loaded. v30=base+3 (=ctr(c+nb), built directly), v31=incr, v19=folded tag.
	mov	x12, x11			//AES re-roll walking rk ptr
	mov	w13, #13
L256_enc_small_3_aesloop:
	ld1	{ v26.16b }, [x12], #16
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b
	subs	w13, w13, #1
	b.ne	L256_enc_small_3_aesloop
	ld1	{ v26.16b }, [x12], #16		//rk13 (no aesmc)
	aese	v0.16b, v26.16b
	aese	v1.16b, v26.16b
	aese	v2.16b, v26.16b
	ldr	q28, [x12]			//rk14 -> v28
	ldr	q8, [x0], #16			//block0 PT (x0 -> block1 PT)
	ext	v16.16b, v19.16b, v19.16b, #8	//partial tag
	mov	v29.16b, v28.16b		//v29 = rk14
	eor3	v9.16b, v8.16b, v0.16b, v29.16b
	// --- block0 (A): H^3, feed tag, products -> v13(hi)/v14(lo)/v15(mid) ---
	st1	{ v9.16b}, [x2], #16		//block0 ct
	ldr	q23, [x6, #48]			//h3l | h3h
	rev64	v8.16b, v9.16b
	eor	v8.16b, v8.16b, v16.16b		//feed in partial tag
	ldr	q24, [x6, #64]			//h4k | h3k (h3k = low lane)
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v13.1q, v8.2d, v23.2d		//block0 hi -> v13 (H^3)
	eor	v27.8b, v27.8b, v8.8b
	ldr	q9, [x0], #16			//block1 PT
	pmull	v14.1q, v8.1d, v23.1d		//block0 lo -> v14
	pmull	v15.1q, v27.1d, v24.1d		//block0 mid -> v15 (h3k, v24 low lane, no ext)
	eor3	v9.16b, v9.16b, v1.16b, v29.16b	//block1 ct
	// --- block1 (B): H^2, products, fuse pair into v17/18/19 (first accum: plain eor) ---
	st1	{ v9.16b}, [x2], #16		//block1 ct
	ldr	q22, [x6, #32]			//h2l | h2h
	rev64	v8.16b, v9.16b
	ldr	q9, [x0], #16			//block2 PT
	ext	v27.16b, v8.16b, v8.16b, #8
	pmull2	v3.1q, v8.2d, v22.2d		//block1 hi (H^2) -> v3 (stage for 3-way eor3)
	eor3	v9.16b, v9.16b, v2.16b, v29.16b	//block2 ct
	eor	v27.8b, v27.8b, v8.8b
	pmull	v4.1q, v8.1d, v22.1d		//block1 lo -> v4
	ldr	q21, [x6, #16]			//h2k | h1k
	ext	v10.16b, v21.16b, v21.16b, #8	//h2k hi->lo lane
	pmull	v5.1q, v27.1d, v10.1d		//block1 mid (h2k) -> v5
	// pairwise (blk1^blk0) fuse deleted; folded into block2's 3-way eor3 below
	// --- block2 (lone): H^1, final products + accumulate + MODULO ---
	ldr	q20, [x6]			//h1l | h1h
	rev64	v8.16b, v9.16b
	rev32	v30.16b, v30.16b
	str	q30, [x16]			//store the updated counter
	st1	{ v9.16b}, [x2]			//block2 ct (16B, no inc)
	ins	v16.d[0], v8.d[1]		//final mid prep
	pmull2	v28.1q, v8.2d, v20.2d		//block2 hi (H^1)
	pmull	v26.1q, v8.1d, v20.1d		//block2 lo
	eor	v16.8b, v16.8b, v8.8b		//final mid
	pmull	v16.1q, v16.1d, v21.1d		//final mid (h1k low lane)
	eor3	v17.16b, v28.16b, v3.16b, v13.16b	//hi = blk2^blk1^blk0 (accum depth 2->1)
	eor3	v19.16b, v26.16b, v4.16b, v14.16b	//lo
	eor3	v18.16b, v16.16b, v5.16b, v15.16b	//mid
	b	L256_enc_small_reduce
L256_enc_small_2:  //nb==2 (32B): 2-block AES + eor3-fused 2-block drain (tbl v12)
	add	v30.4s, v29.4s, v28.4s	//final counter = base+2 = ctr(c+nb), direct
	add	v8.4s, v29.4s, v31.4s	//counter1
	rev32	v1.16b, v8.16b
	// index synth hoisted to shared prefix (Q12 already set on entry)
	mov	x12, x11			//AES re-roll walking rk ptr
	mov	w13, #13
L256_enc_small_2_aesloop:
	ld1	{ v26.16b }, [x12], #16
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b
	subs	w13, w13, #1
	b.ne	L256_enc_small_2_aesloop
	ld1	{ v26.16b }, [x12], #16		//rk13 (no aesmc)
	aese	v0.16b, v26.16b
	aese	v1.16b, v26.16b
	ldr	q28, [x12]			//rk14 -> v28
	ldr	q8, [x0], #16			//block1 PT (x0 -> block2 PT)
	ext	v16.16b, v19.16b, v19.16b, #8	//tag prep
	mov	v29.16b, v28.16b		//v29 = rk14
	eor3	v9.16b, v8.16b, v0.16b, v29.16b
	ldr	q22, [x6, #32]			//h2l|h2h
	ldr	q21, [x6, #16]			//h2k|h1k
	ldr	q20, [x6]			//h1l|h1h
	st1	{ v9.16b}, [x2], #16		//block1 ct
	rev64	v8.16b, v9.16b
	eor	v8.16b, v8.16b, v16.16b		//feed tag
	ldr	q9, [x0], #16			//block2 PT
	ext	v27.16b, v8.16b, v8.16b, #8
	ext	v10.16b, v21.16b, v21.16b, #8	//h2k hi->lo
	pmull2	v13.1q, v8.2d, v22.2d		//block1 hi -> v13
	eor	v27.8b, v27.8b, v8.8b
	pmull	v14.1q, v8.1d, v22.1d		//block1 lo -> v14
	eor3	v9.16b, v9.16b, v1.16b, v29.16b
	pmull	v15.1q, v27.1d, v10.1d		//block1 mid -> v15
	st1	{ v9.16b}, [x2]			//block2 ct
	rev64	v8.16b, v9.16b
	ins	v16.d[0], v8.d[1]		//block2 mid prep
	pmull2	v28.1q, v8.2d, v20.2d		//block2 hi
	pmull	v26.1q, v8.1d, v20.1d		//block2 lo
	eor	v16.8b, v16.8b, v8.8b
	pmull	v16.1q, v16.1d, v21.1d		//block2 mid (h1k)
	eor	v17.16b, v13.16b, v28.16b	//fused hi
	eor	v19.16b, v14.16b, v26.16b	//fused lo
	eor	v18.16b, v15.16b, v16.16b	//fused mid
	rev32	v30.16b, v30.16b
	str	q30, [x16]			//ivec store
	b	L256_enc_small_reduce
L256_enc_small_1:  //nb==1 (16B): 1-block AES + single-block drain (tbl v12)
	add	v30.4s, v29.4s, v31.4s	//final counter = base+1 = ctr(c+nb), direct
	// index synth hoisted to shared prefix (Q12 already set on entry)
	// v26=rk0, v27=rk1 loaded (before dispatch). v30=base+1 (=ctr(c+nb), built directly), v31=incr, v19=folded tag.
	mov	x12, x11			//AES re-roll walking rk ptr
	mov	w13, #13
L256_enc_small_1_aesloop:
	ld1	{ v26.16b }, [x12], #16
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	subs	w13, w13, #1
	b.ne	L256_enc_small_1_aesloop
	ld1	{ v26.16b }, [x12], #16		//rk13 (no aesmc)
	aese	v0.16b, v26.16b
	ldr	q28, [x12]			//rk14 -> v28
	ldr	q8, [x0]			//block0 PT
	ext	v16.16b, v19.16b, v19.16b, #8	//partial tag
	mov	v29.16b, v28.16b		//v29 = rk14
	eor3	v9.16b, v8.16b, v0.16b, v29.16b
	// v30 = base+1 = ctr(c+nb), built directly above; counter store interleaved w/ loads
	ldr	q20, [x6]			//h1l | h1h
	ldr	q21, [x6, #16]			//h2k | h1k
	rev64	v8.16b, v9.16b			//GHASH block
	eor	v8.16b, v8.16b, v16.16b		//feed in tag
	st1	{ v9.16b}, [x2]			//store all 16B
	ins	v16.d[0], v8.d[1]		//mid prep
	pmull2	v17.1q, v8.2d, v20.2d		//high -> v17
	pmull	v19.1q, v8.1d, v20.1d		//low -> v19
	eor	v16.8b, v16.8b, v8.8b		//mid
	pmull	v18.1q, v16.1d, v21.1d		//mid -> v18 (h1k low lane)
	rev32	v30.16b, v30.16b
	str	q30, [x16]			//store the updated counter (base+1 = ctr(c+nb))
L256_enc_small_reduce:  //shared final GHASH reduction + tbl(v12) reverse + tag store
	ldr	d16, [x10]			//MODULO - load modulo constant
	ext	v21.16b, v17.16b, v17.16b, #8	//MODULO - other top alignment
	eor3	v18.16b, v18.16b, v17.16b, v19.16b		//MODULO - karatsuba tidy up
	pmull	v29.1q, v17.1d, v16.1d		//MODULO - top 64b align with mid
	eor3	v18.16b, v18.16b, v29.16b, v21.16b		//MODULO - fold into mid
	pmull	v17.1q, v18.1d, v16.1d		//MODULO - mid 64b align with low
	ext	v21.16b, v18.16b, v18.16b, #8	//MODULO - other mid alignment
	eor3	v19.16b, v19.16b, v17.16b, v21.16b		//MODULO - fold into low
	tbl	v19.16b, {v19.16b}, v12.16b	//ext+rev64 -> tbl (16B reverse)
	st1	{ v19.16b }, [x3]
	b	L256_enc_epilogue
        .cfi_endproc


S2N_BN_SIZE_DIRECTIVE(aes256_gcm_enc_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
