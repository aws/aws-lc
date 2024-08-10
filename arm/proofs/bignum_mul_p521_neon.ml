(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_521.                                              *)
(* ========================================================================= *)

needs "arm/proofs/bignum_mul_p521.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to the core parts of
   bignum_mul_p521 and bignum_mul_p521_neon. This is a vectorized
   version of core of bignum_mul_p521 but instructions are unscheduled. *)

let bignum_mul_p521_interm1_ops:int list = [
  0xa940542f; (* ldp	x15, x21, [x1] *)
  0xa941442a; (* ldp	x10, x17, [x1, #16] *)
  0xa940404d; (* ldp	x13, x16, [x2] *)
  0x3dc00032; (* ldr	q18, [x1] *)
  0x3dc0005c; (* ldr	q28, [x2] *)
  0xa9415045; (* ldp	x5, x20, [x2, #16] *)
  0x6f00e5f0; (* movi	v16.2d, #0xffffffff *)
  0x4e9c5b87; (* uzp2	v7.4s, v28.4s, v28.4s *)
  0x0ea12a44; (* xtn	v4.2s, v18.2d *)
  0x0ea12b81; (* xtn	v1.2s, v28.2d *)
  0x4ea00b9b; (* rev64	v27.4s, v28.4s *)
  0x2ea1c095; (* umull	v21.2d, v4.2s, v1.2s *)
  0x2ea7c09c; (* umull	v28.2d, v4.2s, v7.2s *)
  0x4e925a45; (* uzp2	v5.4s, v18.4s, v18.4s *)
  0x4eb29f72; (* mul	v18.4s, v27.4s, v18.4s *)
  0x6f6016bc; (* usra	v28.2d, v21.2d, #32 *)
  0x2ea7c0bd; (* umull	v29.2d, v5.2s, v7.2s *)
  0x6ea02a52; (* uaddlp	v18.2d, v18.4s *)
  0x4e301f90; (* and	v16.16b, v28.16b, v16.16b *)
  0x2ea180b0; (* umlal	v16.2d, v5.2s, v1.2s *)
  0x4f605652; (* shl	v18.2d, v18.2d, #32 *)
  0x6f60179d; (* usra	v29.2d, v28.2d, #32 *)
  0x2ea18092; (* umlal	v18.2d, v4.2s, v1.2s *)
  0x6f60161d; (* usra	v29.2d, v16.2d, #32 *)
  0x4e083e48; (* mov	x8, v18.d[0] *)
  0x4e183e49; (* mov	x9, v18.d[1] *)
  0x9b057d46; (* mul	x6, x10, x5 *)
  0x9b147e33; (* mul	x19, x17, x20 *)
  0x4e083fae; (* mov	x14, v29.d[0] *)
  0xab0e0129; (* adds	x9, x9, x14 *)
  0x4e183fae; (* mov	x14, v29.d[1] *)
  0xba0e00c6; (* adcs	x6, x6, x14 *)
  0x9bc57d4e; (* umulh	x14, x10, x5 *)
  0xba0e0273; (* adcs	x19, x19, x14 *)
  0x9bd47e2e; (* umulh	x14, x17, x20 *)
  0x9a1f01ce; (* adc	x14, x14, xzr *)
  0xab08012b; (* adds	x11, x9, x8 *)
  0xba0900c9; (* adcs	x9, x6, x9 *)
  0xba060266; (* adcs	x6, x19, x6 *)
  0xba1301d3; (* adcs	x19, x14, x19 *)
  0x9a0e03ee; (* adc	x14, xzr, x14 *)
  0xab080123; (* adds	x3, x9, x8 *)
  0xba0b00d8; (* adcs	x24, x6, x11 *)
  0xba090269; (* adcs	x9, x19, x9 *)
  0xba0601c6; (* adcs	x6, x14, x6 *)
  0xba1303f3; (* adcs	x19, xzr, x19 *)
  0x9a0e03ee; (* adc	x14, xzr, x14 *)
  0xeb110144; (* subs	x4, x10, x17 *)
  0xda842484; (* cneg	x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm	x7, cc  // cc = lo, ul, last *)
  0xeb050297; (* subs	x23, x20, x5 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul	x22, x4, x23 *)
  0x9bd77c84; (* umulh	x4, x4, x23 *)
  0xda8720e7; (* cinv	x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn	x7, #0x1 *)
  0xca0702d7; (* eor	x23, x22, x7 *)
  0xba1700c6; (* adcs	x6, x6, x23 *)
  0xca070084; (* eor	x4, x4, x7 *)
  0xba040273; (* adcs	x19, x19, x4 *)
  0x9a0701ce; (* adc	x14, x14, x7 *)
  0xeb1501e4; (* subs	x4, x15, x21 *)
  0xda842484; (* cneg	x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm	x7, cc  // cc = lo, ul, last *)
  0xeb0d0217; (* subs	x23, x16, x13 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul	x22, x4, x23 *)
  0x9bd77c84; (* umulh	x4, x4, x23 *)
  0xda8720e7; (* cinv	x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn	x7, #0x1 *)
  0xca0702d7; (* eor	x23, x22, x7 *)
  0xba17016b; (* adcs	x11, x11, x23 *)
  0xca070084; (* eor	x4, x4, x7 *)
  0xba040063; (* adcs	x3, x3, x4 *)
  0xba070318; (* adcs	x24, x24, x7 *)
  0xba070129; (* adcs	x9, x9, x7 *)
  0xba0700c6; (* adcs	x6, x6, x7 *)
  0xba070273; (* adcs	x19, x19, x7 *)
  0x9a0701ce; (* adc	x14, x14, x7 *)
  0xeb1102a4; (* subs	x4, x21, x17 *)
  0xda842484; (* cneg	x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm	x7, cc  // cc = lo, ul, last *)
  0xeb100297; (* subs	x23, x20, x16 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul	x22, x4, x23 *)
  0x9bd77c84; (* umulh	x4, x4, x23 *)
  0xda8720e7; (* cinv	x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn	x7, #0x1 *)
  0xca0702d7; (* eor	x23, x22, x7 *)
  0xba170129; (* adcs	x9, x9, x23 *)
  0xca070084; (* eor	x4, x4, x7 *)
  0xba0400c6; (* adcs	x6, x6, x4 *)
  0xba070273; (* adcs	x19, x19, x7 *)
  0x9a0701ce; (* adc	x14, x14, x7 *)
  0xeb0a01e4; (* subs	x4, x15, x10 *)
  0xda842484; (* cneg	x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm	x7, cc  // cc = lo, ul, last *)
  0xeb0d00b7; (* subs	x23, x5, x13 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul	x22, x4, x23 *)
  0x9bd77c84; (* umulh	x4, x4, x23 *)
  0xda8720e7; (* cinv	x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn	x7, #0x1 *)
  0xca0702d7; (* eor	x23, x22, x7 *)
  0xba170063; (* adcs	x3, x3, x23 *)
  0xca070084; (* eor	x4, x4, x7 *)
  0xba040318; (* adcs	x24, x24, x4 *)
  0xba070129; (* adcs	x9, x9, x7 *)
  0xba0700c6; (* adcs	x6, x6, x7 *)
  0xba070273; (* adcs	x19, x19, x7 *)
  0x9a0701ce; (* adc	x14, x14, x7 *)
  0xeb1101f1; (* subs	x17, x15, x17 *)
  0xda912631; (* cneg	x17, x17, cc  // cc = lo, ul, last *)
  0xda9f23e4; (* csetm	x4, cc  // cc = lo, ul, last *)
  0xeb0d028d; (* subs	x13, x20, x13 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e34; (* mul	x20, x17, x13 *)
  0x9bcd7e31; (* umulh	x17, x17, x13 *)
  0xda84208d; (* cinv	x13, x4, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn	x13, #0x1 *)
  0xca0d0294; (* eor	x20, x20, x13 *)
  0xba140314; (* adcs	x20, x24, x20 *)
  0xca0d0231; (* eor	x17, x17, x13 *)
  0xba110131; (* adcs	x17, x9, x17 *)
  0xba0d00c9; (* adcs	x9, x6, x13 *)
  0xba0d0266; (* adcs	x6, x19, x13 *)
  0x9a0d01cd; (* adc	x13, x14, x13 *)
  0xeb0a02b5; (* subs	x21, x21, x10 *)
  0xda9526b5; (* cneg	x21, x21, cc  // cc = lo, ul, last *)
  0xda9f23ea; (* csetm	x10, cc  // cc = lo, ul, last *)
  0xeb1000b0; (* subs	x16, x5, x16 *)
  0xda902610; (* cneg	x16, x16, cc  // cc = lo, ul, last *)
  0x9b107ea5; (* mul	x5, x21, x16 *)
  0x9bd07eb5; (* umulh	x21, x21, x16 *)
  0xda8a214a; (* cinv	x10, x10, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn	x10, #0x1 *)
  0xca0a00b0; (* eor	x16, x5, x10 *)
  0xba100290; (* adcs	x16, x20, x16 *)
  0xca0a02b5; (* eor	x21, x21, x10 *)
  0xba150235; (* adcs	x21, x17, x21 *)
  0xba0a0131; (* adcs	x17, x9, x10 *)
  0xba0a00c5; (* adcs	x5, x6, x10 *)
  0x9a0a01aa; (* adc	x10, x13, x10 *)
  0xd377d90d; (* lsl	x13, x8, #9 *)
  0x93c8dd74; (* extr	x20, x11, x8, #55 *)
  0x93cbdc68; (* extr	x8, x3, x11, #55 *)
  0x93c3de09; (* extr	x9, x16, x3, #55 *)
  0xd377fe10; (* lsr	x16, x16, #55 *)
  0xa90047f5; (* stp	x21, x17, [sp] *)
  0xa9012be5; (* stp	x5, x10, [sp, #16] *)
  0xa90253ed; (* stp	x13, x20, [sp, #32] *)
  0xa90327e8; (* stp	x8, x9, [sp, #48] *)
  0xf90023f0; (* str	x16, [sp, #64] *)
  0xa9422835; (* ldp	x21, x10, [x1, #32] *)
  0xa9433431; (* ldp	x17, x13, [x1, #48] *)
  0xa9421450; (* ldp	x16, x5, [x2, #32] *)
  0x3dc00832; (* ldr	q18, [x1, #32] *)
  0x3dc0085c; (* ldr	q28, [x2, #32] *)
  0xa9432054; (* ldp	x20, x8, [x2, #48] *)
  0x6f00e5f0; (* movi	v16.2d, #0xffffffff *)
  0x4e9c5b87; (* uzp2	v7.4s, v28.4s, v28.4s *)
  0x0ea12a44; (* xtn	v4.2s, v18.2d *)
  0x0ea12b81; (* xtn	v1.2s, v28.2d *)
  0x4ea00b9c; (* rev64	v28.4s, v28.4s *)
  0x2ea1c09b; (* umull	v27.2d, v4.2s, v1.2s *)
  0x2ea7c09d; (* umull	v29.2d, v4.2s, v7.2s *)
  0x4e925a55; (* uzp2	v21.4s, v18.4s, v18.4s *)
  0x4eb29f9c; (* mul	v28.4s, v28.4s, v18.4s *)
  0x6f60177d; (* usra	v29.2d, v27.2d, #32 *)
  0x2ea7c2b2; (* umull	v18.2d, v21.2s, v7.2s *)
  0x6ea02b9c; (* uaddlp	v28.2d, v28.4s *)
  0x4e301fb0; (* and	v16.16b, v29.16b, v16.16b *)
  0x2ea182b0; (* umlal	v16.2d, v21.2s, v1.2s *)
  0x4f60579c; (* shl	v28.2d, v28.2d, #32 *)
  0x6f6017b2; (* usra	v18.2d, v29.2d, #32 *)
  0x2ea1809c; (* umlal	v28.2d, v4.2s, v1.2s *)
  0x6f601612; (* usra	v18.2d, v16.2d, #32 *)
  0x4e083f89; (* mov	x9, v28.d[0] *)
  0x4e183f86; (* mov	x6, v28.d[1] *)
  0x9b147e33; (* mul	x19, x17, x20 *)
  0x9b087dae; (* mul	x14, x13, x8 *)
  0x4e083e4b; (* mov	x11, v18.d[0] *)
  0xab0b00c6; (* adds	x6, x6, x11 *)
  0x4e183e4b; (* mov	x11, v18.d[1] *)
  0xba0b0273; (* adcs	x19, x19, x11 *)
  0x9bd47e2b; (* umulh	x11, x17, x20 *)
  0xba0b01ce; (* adcs	x14, x14, x11 *)
  0x9bc87dab; (* umulh	x11, x13, x8 *)
  0x9a1f016b; (* adc	x11, x11, xzr *)
  0xab0900c3; (* adds	x3, x6, x9 *)
  0xba060266; (* adcs	x6, x19, x6 *)
  0xba1301d3; (* adcs	x19, x14, x19 *)
  0xba0e016e; (* adcs	x14, x11, x14 *)
  0x9a0b03eb; (* adc	x11, xzr, x11 *)
  0xab0900d8; (* adds	x24, x6, x9 *)
  0xba030264; (* adcs	x4, x19, x3 *)
  0xba0601c6; (* adcs	x6, x14, x6 *)
  0xba130173; (* adcs	x19, x11, x19 *)
  0xba0e03ee; (* adcs	x14, xzr, x14 *)
  0x9a0b03eb; (* adc	x11, xzr, x11 *)
  0xeb0d0227; (* subs	x7, x17, x13 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm	x23, cc  // cc = lo, ul, last *)
  0xeb140116; (* subs	x22, x8, x20 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul	x12, x7, x22 *)
  0x9bd67ce7; (* umulh	x7, x7, x22 *)
  0xda9722f7; (* cinv	x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn	x23, #0x1 *)
  0xca170196; (* eor	x22, x12, x23 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0xca1700e7; (* eor	x7, x7, x23 *)
  0xba0701ce; (* adcs	x14, x14, x7 *)
  0x9a17016b; (* adc	x11, x11, x23 *)
  0xeb0a02a7; (* subs	x7, x21, x10 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm	x23, cc  // cc = lo, ul, last *)
  0xeb1000b6; (* subs	x22, x5, x16 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul	x12, x7, x22 *)
  0x9bd67ce7; (* umulh	x7, x7, x22 *)
  0xda9722f7; (* cinv	x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn	x23, #0x1 *)
  0xca170196; (* eor	x22, x12, x23 *)
  0xba160063; (* adcs	x3, x3, x22 *)
  0xca1700e7; (* eor	x7, x7, x23 *)
  0xba070318; (* adcs	x24, x24, x7 *)
  0xba170084; (* adcs	x4, x4, x23 *)
  0xba1700c6; (* adcs	x6, x6, x23 *)
  0xba170273; (* adcs	x19, x19, x23 *)
  0xba1701ce; (* adcs	x14, x14, x23 *)
  0x9a17016b; (* adc	x11, x11, x23 *)
  0xeb0d0147; (* subs	x7, x10, x13 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm	x23, cc  // cc = lo, ul, last *)
  0xeb050116; (* subs	x22, x8, x5 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul	x12, x7, x22 *)
  0x9bd67ce7; (* umulh	x7, x7, x22 *)
  0xda9722f7; (* cinv	x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn	x23, #0x1 *)
  0xca170196; (* eor	x22, x12, x23 *)
  0xba1600c6; (* adcs	x6, x6, x22 *)
  0xca1700e7; (* eor	x7, x7, x23 *)
  0xba070273; (* adcs	x19, x19, x7 *)
  0xba1701ce; (* adcs	x14, x14, x23 *)
  0x9a17016b; (* adc	x11, x11, x23 *)
  0xeb1102a7; (* subs	x7, x21, x17 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm	x23, cc  // cc = lo, ul, last *)
  0xeb100296; (* subs	x22, x20, x16 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul	x12, x7, x22 *)
  0x9bd67ce7; (* umulh	x7, x7, x22 *)
  0xda9722f7; (* cinv	x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn	x23, #0x1 *)
  0xca170196; (* eor	x22, x12, x23 *)
  0xba160318; (* adcs	x24, x24, x22 *)
  0xca1700e7; (* eor	x7, x7, x23 *)
  0xba070084; (* adcs	x4, x4, x7 *)
  0xba1700c6; (* adcs	x6, x6, x23 *)
  0xba170273; (* adcs	x19, x19, x23 *)
  0xba1701ce; (* adcs	x14, x14, x23 *)
  0x9a17016b; (* adc	x11, x11, x23 *)
  0xeb0d02a7; (* subs	x7, x21, x13 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm	x23, cc  // cc = lo, ul, last *)
  0xeb100116; (* subs	x22, x8, x16 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul	x12, x7, x22 *)
  0x9bd67ce7; (* umulh	x7, x7, x22 *)
  0xda9722f7; (* cinv	x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn	x23, #0x1 *)
  0xca170196; (* eor	x22, x12, x23 *)
  0xba160084; (* adcs	x4, x4, x22 *)
  0xca1700e7; (* eor	x7, x7, x23 *)
  0xba0700c6; (* adcs	x6, x6, x7 *)
  0xba170273; (* adcs	x19, x19, x23 *)
  0xba1701ce; (* adcs	x14, x14, x23 *)
  0x9a17016b; (* adc	x11, x11, x23 *)
  0xeb110147; (* subs	x7, x10, x17 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm	x23, cc  // cc = lo, ul, last *)
  0xeb050296; (* subs	x22, x20, x5 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul	x12, x7, x22 *)
  0x9bd67ce7; (* umulh	x7, x7, x22 *)
  0xda9722f7; (* cinv	x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn	x23, #0x1 *)
  0xca170196; (* eor	x22, x12, x23 *)
  0xba160084; (* adcs	x4, x4, x22 *)
  0xca1700e7; (* eor	x7, x7, x23 *)
  0xba0700c6; (* adcs	x6, x6, x7 *)
  0xba170273; (* adcs	x19, x19, x23 *)
  0xba1701ce; (* adcs	x14, x14, x23 *)
  0x9a17016b; (* adc	x11, x11, x23 *)
  0xa9405fe7; (* ldp	x7, x23, [sp] *)
  0xab070129; (* adds	x9, x9, x7 *)
  0xba170063; (* adcs	x3, x3, x23 *)
  0xa9000fe9; (* stp	x9, x3, [sp] *)
  0xa9410fe9; (* ldp	x9, x3, [sp, #16] *)
  0xba090309; (* adcs	x9, x24, x9 *)
  0xba030083; (* adcs	x3, x4, x3 *)
  0xa9010fe9; (* stp	x9, x3, [sp, #16] *)
  0xa9420fe9; (* ldp	x9, x3, [sp, #32] *)
  0xba0900c9; (* adcs	x9, x6, x9 *)
  0xba030266; (* adcs	x6, x19, x3 *)
  0xa9021be9; (* stp	x9, x6, [sp, #32] *)
  0xa9431be9; (* ldp	x9, x6, [sp, #48] *)
  0xba0901c9; (* adcs	x9, x14, x9 *)
  0xba060166; (* adcs	x6, x11, x6 *)
  0xa9031be9; (* stp	x9, x6, [sp, #48] *)
  0xf94023e9; (* ldr	x9, [sp, #64] *)
  0x9a1f0129; (* adc	x9, x9, xzr *)
  0xf90023e9; (* str	x9, [sp, #64] *)
  0xa9401829; (* ldp	x9, x6, [x1] *)
  0xeb0902b5; (* subs	x21, x21, x9 *)
  0xfa06014a; (* sbcs	x10, x10, x6 *)
  0xa9411829; (* ldp	x9, x6, [x1, #16] *)
  0xfa090231; (* sbcs	x17, x17, x9 *)
  0xfa0601ad; (* sbcs	x13, x13, x6 *)
  0xda9f23e9; (* csetm	x9, cc  // cc = lo, ul, last *)
  0xa9404c46; (* ldp	x6, x19, [x2] *)
  0xeb1000d0; (* subs	x16, x6, x16 *)
  0xfa050265; (* sbcs	x5, x19, x5 *)
  0xa9414c46; (* ldp	x6, x19, [x2, #16] *)
  0xfa1400d4; (* sbcs	x20, x6, x20 *)
  0xfa080268; (* sbcs	x8, x19, x8 *)
  0xda9f23e6; (* csetm	x6, cc  // cc = lo, ul, last *)
  0xca0902b5; (* eor	x21, x21, x9 *)
  0xeb0902b5; (* subs	x21, x21, x9 *)
  0xca09014a; (* eor	x10, x10, x9 *)
  0xfa09014a; (* sbcs	x10, x10, x9 *)
  0xca090231; (* eor	x17, x17, x9 *)
  0xfa090231; (* sbcs	x17, x17, x9 *)
  0xca0901ad; (* eor	x13, x13, x9 *)
  0xda0901ad; (* sbc	x13, x13, x9 *)
  0xca060210; (* eor	x16, x16, x6 *)
  0xeb060210; (* subs	x16, x16, x6 *)
  0xca0600a5; (* eor	x5, x5, x6 *)
  0xfa0600a5; (* sbcs	x5, x5, x6 *)
  0xca060294; (* eor	x20, x20, x6 *)
  0xfa060294; (* sbcs	x20, x20, x6 *)
  0xca060108; (* eor	x8, x8, x6 *)
  0xda060108; (* sbc	x8, x8, x6 *)
  0xca0900c9; (* eor	x9, x6, x9 *)
  0x9b107ea6; (* mul	x6, x21, x16 *)
  0x9b057d53; (* mul	x19, x10, x5 *)
  0x9b147e2e; (* mul	x14, x17, x20 *)
  0x9b087dab; (* mul	x11, x13, x8 *)
  0x9bd07ea3; (* umulh	x3, x21, x16 *)
  0xab030273; (* adds	x19, x19, x3 *)
  0x9bc57d43; (* umulh	x3, x10, x5 *)
  0xba0301ce; (* adcs	x14, x14, x3 *)
  0x9bd47e23; (* umulh	x3, x17, x20 *)
  0xba03016b; (* adcs	x11, x11, x3 *)
  0x9bc87da3; (* umulh	x3, x13, x8 *)
  0x9a1f0063; (* adc	x3, x3, xzr *)
  0xab060278; (* adds	x24, x19, x6 *)
  0xba1301d3; (* adcs	x19, x14, x19 *)
  0xba0e016e; (* adcs	x14, x11, x14 *)
  0xba0b006b; (* adcs	x11, x3, x11 *)
  0x9a0303e3; (* adc	x3, xzr, x3 *)
  0xab060264; (* adds	x4, x19, x6 *)
  0xba1801c7; (* adcs	x7, x14, x24 *)
  0xba130173; (* adcs	x19, x11, x19 *)
  0xba0e006e; (* adcs	x14, x3, x14 *)
  0xba0b03eb; (* adcs	x11, xzr, x11 *)
  0x9a0303e3; (* adc	x3, xzr, x3 *)
  0xeb0d0237; (* subs	x23, x17, x13 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb14010c; (* subs	x12, x8, x20 *)
  0xda8c258c; (* cneg	x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul	x15, x23, x12 *)
  0x9bcc7ef7; (* umulh	x23, x23, x12 *)
  0xda9622d6; (* cinv	x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn	x22, #0x1 *)
  0xca1601ec; (* eor	x12, x15, x22 *)
  0xba0c01ce; (* adcs	x14, x14, x12 *)
  0xca1602f7; (* eor	x23, x23, x22 *)
  0xba17016b; (* adcs	x11, x11, x23 *)
  0x9a160063; (* adc	x3, x3, x22 *)
  0xeb0a02b7; (* subs	x23, x21, x10 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb1000ac; (* subs	x12, x5, x16 *)
  0xda8c258c; (* cneg	x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul	x15, x23, x12 *)
  0x9bcc7ef7; (* umulh	x23, x23, x12 *)
  0xda9622d6; (* cinv	x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn	x22, #0x1 *)
  0xca1601ec; (* eor	x12, x15, x22 *)
  0xba0c0318; (* adcs	x24, x24, x12 *)
  0xca1602f7; (* eor	x23, x23, x22 *)
  0xba170084; (* adcs	x4, x4, x23 *)
  0xba1600e7; (* adcs	x7, x7, x22 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0xba1601ce; (* adcs	x14, x14, x22 *)
  0xba16016b; (* adcs	x11, x11, x22 *)
  0x9a160063; (* adc	x3, x3, x22 *)
  0xeb0d0157; (* subs	x23, x10, x13 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb05010c; (* subs	x12, x8, x5 *)
  0xda8c258c; (* cneg	x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul	x15, x23, x12 *)
  0x9bcc7ef7; (* umulh	x23, x23, x12 *)
  0xda9622d6; (* cinv	x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn	x22, #0x1 *)
  0xca1601ec; (* eor	x12, x15, x22 *)
  0xba0c0273; (* adcs	x19, x19, x12 *)
  0xca1602f7; (* eor	x23, x23, x22 *)
  0xba1701ce; (* adcs	x14, x14, x23 *)
  0xba16016b; (* adcs	x11, x11, x22 *)
  0x9a160063; (* adc	x3, x3, x22 *)
  0xeb1102b7; (* subs	x23, x21, x17 *)
  0xda9726f7; (* cneg	x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb10028c; (* subs	x12, x20, x16 *)
  0xda8c258c; (* cneg	x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul	x15, x23, x12 *)
  0x9bcc7ef7; (* umulh	x23, x23, x12 *)
  0xda9622d6; (* cinv	x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn	x22, #0x1 *)
  0xca1601ec; (* eor	x12, x15, x22 *)
  0xba0c0084; (* adcs	x4, x4, x12 *)
  0xca1602f7; (* eor	x23, x23, x22 *)
  0xba1700e7; (* adcs	x7, x7, x23 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0xba1601ce; (* adcs	x14, x14, x22 *)
  0xba16016b; (* adcs	x11, x11, x22 *)
  0x9a160063; (* adc	x3, x3, x22 *)
  0xeb0d02b5; (* subs	x21, x21, x13 *)
  0xda9526b5; (* cneg	x21, x21, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm	x13, cc  // cc = lo, ul, last *)
  0xeb100110; (* subs	x16, x8, x16 *)
  0xda902610; (* cneg	x16, x16, cc  // cc = lo, ul, last *)
  0x9b107ea8; (* mul	x8, x21, x16 *)
  0x9bd07eb5; (* umulh	x21, x21, x16 *)
  0xda8d21ad; (* cinv	x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn	x13, #0x1 *)
  0xca0d0110; (* eor	x16, x8, x13 *)
  0xba1000f0; (* adcs	x16, x7, x16 *)
  0xca0d02b5; (* eor	x21, x21, x13 *)
  0xba150275; (* adcs	x21, x19, x21 *)
  0xba0d01c8; (* adcs	x8, x14, x13 *)
  0xba0d0173; (* adcs	x19, x11, x13 *)
  0x9a0d006d; (* adc	x13, x3, x13 *)
  0xeb11014a; (* subs	x10, x10, x17 *)
  0xda8a254a; (* cneg	x10, x10, cc  // cc = lo, ul, last *)
  0xda9f23f1; (* csetm	x17, cc  // cc = lo, ul, last *)
  0xeb050285; (* subs	x5, x20, x5 *)
  0xda8524a5; (* cneg	x5, x5, cc  // cc = lo, ul, last *)
  0x9b057d54; (* mul	x20, x10, x5 *)
  0x9bc57d4a; (* umulh	x10, x10, x5 *)
  0xda912231; (* cinv	x17, x17, cc  // cc = lo, ul, last *)
  0xb100063f; (* cmn	x17, #0x1 *)
  0xca110285; (* eor	x5, x20, x17 *)
  0xba050210; (* adcs	x16, x16, x5 *)
  0xca11014a; (* eor	x10, x10, x17 *)
  0xba0a02b5; (* adcs	x21, x21, x10 *)
  0xba11010a; (* adcs	x10, x8, x17 *)
  0xba110265; (* adcs	x5, x19, x17 *)
  0x9a1101b1; (* adc	x17, x13, x17 *)
  0xa94053ed; (* ldp	x13, x20, [sp] *)
  0xa9414fe8; (* ldp	x8, x19, [sp, #16] *)
  0xca0900c6; (* eor	x6, x6, x9 *)
  0xab0d00c6; (* adds	x6, x6, x13 *)
  0xca09030e; (* eor	x14, x24, x9 *)
  0xba1401ce; (* adcs	x14, x14, x20 *)
  0xca09008b; (* eor	x11, x4, x9 *)
  0xba08016b; (* adcs	x11, x11, x8 *)
  0xca090210; (* eor	x16, x16, x9 *)
  0xba130210; (* adcs	x16, x16, x19 *)
  0xca0902b5; (* eor	x21, x21, x9 *)
  0xa94263e3; (* ldp	x3, x24, [sp, #32] *)
  0xa9431fe4; (* ldp	x4, x7, [sp, #48] *)
  0xf94023f7; (* ldr	x23, [sp, #64] *)
  0xba0302b5; (* adcs	x21, x21, x3 *)
  0xca09014a; (* eor	x10, x10, x9 *)
  0xba18014a; (* adcs	x10, x10, x24 *)
  0xca0900a5; (* eor	x5, x5, x9 *)
  0xba0400a5; (* adcs	x5, x5, x4 *)
  0xca090231; (* eor	x17, x17, x9 *)
  0xba070231; (* adcs	x17, x17, x7 *)
  0x9a1f02f6; (* adc	x22, x23, xzr *)
  0xab0d02b5; (* adds	x21, x21, x13 *)
  0xba14014a; (* adcs	x10, x10, x20 *)
  0xba0800ad; (* adcs	x13, x5, x8 *)
  0xba130231; (* adcs	x17, x17, x19 *)
  0x92402125; (* and	x5, x9, #0x1ff *)
  0xd377d8d4; (* lsl	x20, x6, #9 *)
  0xaa050285; (* orr	x5, x20, x5 *)
  0xba050065; (* adcs	x5, x3, x5 *)
  0x93c6ddd4; (* extr	x20, x14, x6, #55 *)
  0xba140314; (* adcs	x20, x24, x20 *)
  0x93cedd68; (* extr	x8, x11, x14, #55 *)
  0xba080088; (* adcs	x8, x4, x8 *)
  0x93cbde09; (* extr	x9, x16, x11, #55 *)
  0xba0900e9; (* adcs	x9, x7, x9 *)
  0xd377fe10; (* lsr	x16, x16, #55 *)
  0x9a170210; (* adc	x16, x16, x23 *)
  0xf9402046; (* ldr	x6, [x2, #64] *)
  0xa9403833; (* ldp	x19, x14, [x1] *)
  0x9240ce6b; (* and	x11, x19, #0xfffffffffffff *)
  0x9b0b7ccb; (* mul	x11, x6, x11 *)
  0xf9402023; (* ldr	x3, [x1, #64] *)
  0xa9401058; (* ldp	x24, x4, [x2] *)
  0x9240cf07; (* and	x7, x24, #0xfffffffffffff *)
  0x9b077c67; (* mul	x7, x3, x7 *)
  0x8b07016b; (* add	x11, x11, x7 *)
  0x93d3d1d3; (* extr	x19, x14, x19, #52 *)
  0x9240ce73; (* and	x19, x19, #0xfffffffffffff *)
  0x9b137cd3; (* mul	x19, x6, x19 *)
  0x93d8d098; (* extr	x24, x4, x24, #52 *)
  0x9240cf18; (* and	x24, x24, #0xfffffffffffff *)
  0x9b187c78; (* mul	x24, x3, x24 *)
  0x8b180273; (* add	x19, x19, x24 *)
  0xd374fd78; (* lsr	x24, x11, #52 *)
  0x8b180273; (* add	x19, x19, x24 *)
  0xd374cd6b; (* lsl	x11, x11, #12 *)
  0x93cb326b; (* extr	x11, x19, x11, #12 *)
  0xab0b02b5; (* adds	x21, x21, x11 *)
  0xa941602b; (* ldp	x11, x24, [x1, #16] *)
  0xa9415c47; (* ldp	x7, x23, [x2, #16] *)
  0x93cea16e; (* extr	x14, x11, x14, #40 *)
  0x9240cdce; (* and	x14, x14, #0xfffffffffffff *)
  0x9b0e7cce; (* mul	x14, x6, x14 *)
  0x93c4a0e4; (* extr	x4, x7, x4, #40 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047c64; (* mul	x4, x3, x4 *)
  0x8b0401ce; (* add	x14, x14, x4 *)
  0xd374fe64; (* lsr	x4, x19, #52 *)
  0x8b0401ce; (* add	x14, x14, x4 *)
  0xd374ce73; (* lsl	x19, x19, #12 *)
  0x93d361d3; (* extr	x19, x14, x19, #24 *)
  0xba13014a; (* adcs	x10, x10, x19 *)
  0x93cb7313; (* extr	x19, x24, x11, #28 *)
  0x9240ce73; (* and	x19, x19, #0xfffffffffffff *)
  0x9b137cd3; (* mul	x19, x6, x19 *)
  0x93c772eb; (* extr	x11, x23, x7, #28 *)
  0x9240cd6b; (* and	x11, x11, #0xfffffffffffff *)
  0x9b0b7c6b; (* mul	x11, x3, x11 *)
  0x8b0b0273; (* add	x19, x19, x11 *)
  0xd374fdcb; (* lsr	x11, x14, #52 *)
  0x8b0b0273; (* add	x19, x19, x11 *)
  0xd374cdce; (* lsl	x14, x14, #12 *)
  0x93ce926e; (* extr	x14, x19, x14, #36 *)
  0xba0e01ad; (* adcs	x13, x13, x14 *)
  0x8a0d014e; (* and	x14, x10, x13 *)
  0xa942102b; (* ldp	x11, x4, [x1, #32] *)
  0xa9423047; (* ldp	x7, x12, [x2, #32] *)
  0x93d84178; (* extr	x24, x11, x24, #16 *)
  0x9240cf18; (* and	x24, x24, #0xfffffffffffff *)
  0x9b187cd8; (* mul	x24, x6, x24 *)
  0x93d740f7; (* extr	x23, x7, x23, #16 *)
  0x9240cef7; (* and	x23, x23, #0xfffffffffffff *)
  0x9b177c77; (* mul	x23, x3, x23 *)
  0x8b170318; (* add	x24, x24, x23 *)
  0xd3503ed7; (* lsl	x23, x22, #48 *)
  0x8b170318; (* add	x24, x24, x23 *)
  0xd374fe77; (* lsr	x23, x19, #52 *)
  0x8b170318; (* add	x24, x24, x23 *)
  0xd374ce73; (* lsl	x19, x19, #12 *)
  0x93d3c313; (* extr	x19, x24, x19, #48 *)
  0xba130231; (* adcs	x17, x17, x19 *)
  0x8a1101d3; (* and	x19, x14, x17 *)
  0xd344fd6e; (* lsr	x14, x11, #4 *)
  0x9240cdce; (* and	x14, x14, #0xfffffffffffff *)
  0x9b0e7cce; (* mul	x14, x6, x14 *)
  0xd344fcf7; (* lsr	x23, x7, #4 *)
  0x9240cef7; (* and	x23, x23, #0xfffffffffffff *)
  0x9b177c77; (* mul	x23, x3, x23 *)
  0x8b1701ce; (* add	x14, x14, x23 *)
  0xd374ff17; (* lsr	x23, x24, #52 *)
  0x8b1701ce; (* add	x14, x14, x23 *)
  0xd374cf18; (* lsl	x24, x24, #12 *)
  0x93d8f1d8; (* extr	x24, x14, x24, #60 *)
  0x93cbe08b; (* extr	x11, x4, x11, #56 *)
  0x9240cd6b; (* and	x11, x11, #0xfffffffffffff *)
  0x9b0b7ccb; (* mul	x11, x6, x11 *)
  0x93c7e187; (* extr	x7, x12, x7, #56 *)
  0x9240cce7; (* and	x7, x7, #0xfffffffffffff *)
  0x9b077c67; (* mul	x7, x3, x7 *)
  0x8b07016b; (* add	x11, x11, x7 *)
  0xd374fdce; (* lsr	x14, x14, #52 *)
  0x8b0e016e; (* add	x14, x11, x14 *)
  0xd378df0b; (* lsl	x11, x24, #8 *)
  0x93cb21cb; (* extr	x11, x14, x11, #8 *)
  0xba0b00a5; (* adcs	x5, x5, x11 *)
  0x8a050273; (* and	x19, x19, x5 *)
  0xa943602b; (* ldp	x11, x24, [x1, #48] *)
  0xa9431c42; (* ldp	x2, x7, [x2, #48] *)
  0x93c4b164; (* extr	x4, x11, x4, #44 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cc4; (* mul	x4, x6, x4 *)
  0x93ccb057; (* extr	x23, x2, x12, #44 *)
  0x9240cef7; (* and	x23, x23, #0xfffffffffffff *)
  0x9b177c77; (* mul	x23, x3, x23 *)
  0x8b170084; (* add	x4, x4, x23 *)
  0xd374fdd7; (* lsr	x23, x14, #52 *)
  0x8b170084; (* add	x4, x4, x23 *)
  0xd374cdce; (* lsl	x14, x14, #12 *)
  0x93ce508e; (* extr	x14, x4, x14, #20 *)
  0xba0e0294; (* adcs	x20, x20, x14 *)
  0x8a140273; (* and	x19, x19, x20 *)
  0x93cb830e; (* extr	x14, x24, x11, #32 *)
  0x9240cdce; (* and	x14, x14, #0xfffffffffffff *)
  0x9b0e7cce; (* mul	x14, x6, x14 *)
  0x93c280e2; (* extr	x2, x7, x2, #32 *)
  0x9240cc42; (* and	x2, x2, #0xfffffffffffff *)
  0x9b027c62; (* mul	x2, x3, x2 *)
  0x8b0201c2; (* add	x2, x14, x2 *)
  0xd374fc8e; (* lsr	x14, x4, #52 *)
  0x8b0e0042; (* add	x2, x2, x14 *)
  0xd374cc8e; (* lsl	x14, x4, #12 *)
  0x93ce804e; (* extr	x14, x2, x14, #32 *)
  0xba0e0108; (* adcs	x8, x8, x14 *)
  0x8a080273; (* and	x19, x19, x8 *)
  0xd354ff0e; (* lsr	x14, x24, #20 *)
  0x9b0e7cce; (* mul	x14, x6, x14 *)
  0xd354fceb; (* lsr	x11, x7, #20 *)
  0x9b0b7c6b; (* mul	x11, x3, x11 *)
  0x8b0b01ce; (* add	x14, x14, x11 *)
  0xd374fc4b; (* lsr	x11, x2, #52 *)
  0x8b0b01ce; (* add	x14, x14, x11 *)
  0xd374cc42; (* lsl	x2, x2, #12 *)
  0x93c2b1c2; (* extr	x2, x14, x2, #44 *)
  0xba020129; (* adcs	x9, x9, x2 *)
  0x8a090262; (* and	x2, x19, x9 *)
  0x9b037cc6; (* mul	x6, x6, x3 *)
  0xd36cfdd3; (* lsr	x19, x14, #44 *)
  0x8b1300c6; (* add	x6, x6, x19 *)
  0x9a060210; (* adc	x16, x16, x6 *)
  0xd349fe06; (* lsr	x6, x16, #9 *)
  0xb277da10; (* orr	x16, x16, #0xfffffffffffffe00 *)
  0xeb1f03ff; (* cmp	xzr, xzr *)
  0xba0602bf; (* adcs	xzr, x21, x6 *)
  0xba1f005f; (* adcs	xzr, x2, xzr *)
  0xba1f021f; (* adcs	xzr, x16, xzr *)
  0xba0602b5; (* adcs	x21, x21, x6 *)
  0xba1f014a; (* adcs	x10, x10, xzr *)
  0xba1f01ad; (* adcs	x13, x13, xzr *)
  0xba1f0231; (* adcs	x17, x17, xzr *)
  0xba1f00a5; (* adcs	x5, x5, xzr *)
  0xba1f0294; (* adcs	x20, x20, xzr *)
  0xba1f0108; (* adcs	x8, x8, xzr *)
  0xba1f0129; (* adcs	x9, x9, xzr *)
  0x9a1f0210; (* adc	x16, x16, xzr *)
  0x924022a2; (* and	x2, x21, #0x1ff *)
  0x93d52555; (* extr	x21, x10, x21, #9 *)
  0x93ca25aa; (* extr	x10, x13, x10, #9 *)
  0xa9002815; (* stp	x21, x10, [x0] *)
  0x93cd2635; (* extr	x21, x17, x13, #9 *)
  0x93d124aa; (* extr	x10, x5, x17, #9 *)
  0xa9012815; (* stp	x21, x10, [x0, #16] *)
  0x93c52695; (* extr	x21, x20, x5, #9 *)
  0x93d4250a; (* extr	x10, x8, x20, #9 *)
  0xa9022815; (* stp	x21, x10, [x0, #32] *)
  0x93c82535; (* extr	x21, x9, x8, #9 *)
  0x93c9260a; (* extr	x10, x16, x9, #9 *)
  0xa9032815; (* stp	x21, x10, [x0, #48] *)
  0xf9002002; (* str	x2, [x0, #64] *)
];;

let bignum_mul_p521_interm1_core_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_mul_p521_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_mul_p521_interm1_core_mc" (term_of_bytes byte_list);;

let BIGNUM_MUL_P521_INTERM1_CORE_EXEC =
  ARM_MK_EXEC_RULE bignum_mul_p521_interm1_core_mc;;

let mul_p521_eqin = new_definition
  `!s1 s1' x y z stackpointer.
    (mul_p521_eqin:(armstate#armstate)->int64->int64->int64->int64->bool)
        (s1,s1') x y z stackpointer <=>
    (C_ARGUMENTS [z; x; y] s1 /\
     C_ARGUMENTS [z; x; y] s1' /\
     read SP s1 = stackpointer /\
     read SP s1' = stackpointer /\
     ?a. bignum_from_memory (x,9) s1 = a /\
         bignum_from_memory (x,9) s1' = a /\
     (?b. bignum_from_memory (y,9) s1 = b /\
          bignum_from_memory (y,9) s1' = b))`;;

let mul_p521_eqout = new_definition
  `!s1 s1' z stackpointer.
    (mul_p521_eqout:(armstate#armstate)->int64->int64->bool)
        (s1,s1') z stackpointer <=>
    (?a.
      read SP s1 = stackpointer /\
      read SP s1' = stackpointer /\
      bignum_from_memory (z,9) s1 = a /\
      bignum_from_memory (z,9) s1' = a)`;;

let actions = [
  ("equal", 0, 3, 0, 3);
  ("insert", 3, 3, 3, 5);
  ("equal", 3, 4, 5, 6);
  ("replace", 4, 6, 6, 26);
  ("equal", 6, 8, 26, 28);
  ("replace", 8, 9, 28, 29);
  ("equal", 9, 10, 29, 30);
  ("replace", 10, 11, 30, 31);
  ("equal", 11, 136, 31, 156);
  ("insert", 136, 136, 156, 158);
  ("equal", 136, 137, 158, 159);
  ("replace", 137, 139, 159, 179);
  ("equal", 139, 141, 179, 181);
  ("replace", 141, 142, 181, 182);
  ("equal", 142, 143, 182, 183);
  ("replace", 143, 144, 183, 184);
  ("equal", 144, 624, 184, 664);
];;

let equiv_goal1 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_mul_p521_core_mc);
        (word pc2,LENGTH bignum_mul_p521_interm1_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_mul_p521_core_mc);
        (word pc2,LENGTH bignum_mul_p521_interm1_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    mul_p521_eqin
    mul_p521_eqout
    bignum_mul_p521_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_mul_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
                       WORD_SQR64_HI; WORD_SQR128_DIGIT0]]
  @ (!extra_word_CONV);;

let BIGNUM_MUL_P521_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MUL_P521_CORE_EXEC;
    fst BIGNUM_MUL_P521_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC mul_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MUL_P521_CORE_EXEC
    BIGNUM_MUL_P521_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[mul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,9) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange left **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0':armstate` (concl th)) THEN
    MONOTONE_MAYCHANGE_TAC;

    (** SUBGOAL 3. Maychange right **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0:armstate` (concl th)) THEN
    MONOTONE_MAYCHANGE_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV;;



(******************************************************************************
  The second program equivalence between the core part of intermediate
  program and fully optimized program
******************************************************************************)

let bignum_mul_p521_neon_mc =
  define_from_elf "bignum_mul_p521_neon_mc"
    "arm/p521/bignum_mul_p521_neon.o";;

let BIGNUM_MUL_P521_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_mul_p521_neon_mc;;

let bignum_mul_p521_neon_core_mc_def,
    bignum_mul_p521_neon_core_mc,
    BIGNUM_MUL_P521_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_mul_p521_neon_core_mc"
    bignum_mul_p521_neon_mc
    (`20`,`LENGTH bignum_mul_p521_neon_mc - 44`)
    (fst BIGNUM_MUL_P521_NEON_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_mul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_mul_p521_neon_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_mul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_mul_p521_neon_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    mul_p521_eqin
    mul_p521_eqout
    bignum_mul_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_mul_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;


(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws. *)

let inst_map = [5;2;4;158;6;157;7;8;11;1;10;9;48;15;50;164;163;3;27;161;18;49;62;162;168;21;28;12;14;13;167;63;64;35;16;171;65;23;66;174;165;166;69;67;176;17;68;169;51;19;55;26;52;22;20;53;170;160;73;172;24;33;175;173;29;54;31;177;30;25;32;34;36;37;38;39;57;40;71;41;59;42;43;44;45;46;47;56;58;60;61;80;81;82;83;84;87;70;72;85;74;75;86;76;77;78;145;79;112;114;113;115;144;89;116;118;119;95;97;151;96;117;98;99;102;100;128;130;129;131;101;135;132;88;90;91;92;121;93;133;104;94;103;105;159;106;107;134;155;108;109;110;123;180;111;120;122;124;188;125;126;137;127;136;138;139;179;140;147;186;184;148;141;182;142;153;146;143;201;152;150;203;202;181;204;149;154;208;205;178;207;183;156;185;187;189;190;191;206;192;193;212;194;215;217;216;218;219;222;195;210;196;220;197;198;221;199;200;209;211;224;213;214;233;234;235;226;236;240;237;223;225;238;227;228;239;229;230;242;231;232;244;248;249;250;251;255;252;241;243;253;245;246;247;254;265;257;266;267;268;269;272;256;259;258;270;260;261;262;271;263;264;274;276;273;275;323;326;277;278;279;280;324;316;325;319;327;328;329;317;338;318;340;344;320;321;322;281;282;283;284;332;285;342;330;288;286;339;341;334;343;336;345;331;287;333;335;292;290;355;337;289;291;293;297;294;351;295;296;298;346;299;300;301;353;305;302;350;303;309;306;304;348;307;308;313;310;311;349;314;312;352;315;357;354;356;347;358;370;371;372;373;377;374;359;360;375;361;362;376;363;364;379;365;366;367;368;381;369;384;385;386;387;391;388;378;380;389;382;383;402;390;403;404;393;395;392;394;396;397;398;399;400;401;417;418;419;405;406;409;434;435;436;407;437;441;408;438;420;421;424;411;410;413;412;422;414;415;470;416;423;450;451;426;452;453;454;457;425;439;428;427;492;429;440;472;468;430;431;432;433;455;442;505;443;456;444;445;446;459;447;513;506;448;514;449;458;460;461;466;462;474;476;467;463;481;477;464;465;504;469;493;483;494;485;471;507;478;473;475;480;479;496;482;484;498;486;487;488;500;502;489;515;490;509;508;491;495;497;499;510;525;501;516;503;511;517;527;528;539;526;518;540;512;561;520;522;529;530;519;541;521;542;552;531;523;543;524;532;554;555;544;553;533;580;556;569;557;545;558;581;534;559;570;535;536;546;537;538;548;547;582;560;549;550;565;562;563;594;564;571;583;566;584;611;593;612;576;585;598;572;573;599;608;595;574;609;578;596;623;597;567;586;575;621;577;579;600;587;588;589;590;604;613;591;610;551;568;601;602;624;603;605;617;606;592;614;607;622;625;632;615;616;626;618;628;627;619;629;620;633;630;634;635;636;638;631;637;639;640;641;642;651;643;652;664;644;653;645;655;654;646;656;647;658;657;648;659;649;660;661;650;662;663];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MUL_P521_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MUL_P521_INTERM1_CORE_EXEC;
    fst BIGNUM_MUL_P521_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC mul_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_MUL_P521_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_MUL_P521_NEON_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[mul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,9) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange left **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0':armstate` (concl th)) THEN
    MONOTONE_MAYCHANGE_TAC;

    (** SUBGOAL 3. Maychange right **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0:armstate` (concl th)) THEN
    MONOTONE_MAYCHANGE_TAC
  ]);;


(******************************************************************************
  Use transitivity of two program equivalences to prove end-to-end
  correctness
******************************************************************************)

let equiv_goal = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_mul_p521_core_mc);
        (word pc2,LENGTH bignum_mul_p521_neon_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_mul_p521_core_mc);
        (word pc2,LENGTH bignum_mul_p521_neon_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    mul_p521_eqin
    mul_p521_eqout
    bignum_mul_p521_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_mul_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;

let mul_p521_eqout_TRANS = prove(
  `!s s2 s' z stackpointer.
    mul_p521_eqout (s,s') z stackpointer/\
    mul_p521_eqout (s',s2) z stackpointer
    ==> mul_p521_eqout (s,s2) z stackpointer`,
  MESON_TAC[mul_p521_eqout]);;

let BIGNUM_MUL_P521_CORE_EQUIV = time prove(equiv_goal,
  REPEAT STRIP_TAC THEN
  (* To prove the goal, show that there exists an empty slot in the memory
     which can locate bignum_mul_p521_interm1_core_mc. *)
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc:int64,LENGTH bignum_mul_p521_core_mc);
        (word pc3:int64,LENGTH bignum_mul_p521_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc3:int64,LENGTH bignum_mul_p521_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_mul_p521_neon_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_mul_p521_interm1_core_mc))
        [x,8 * 9; y,8 * 9; stackpointer,80] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    REPEAT (FIRST_X_ASSUM MP_TAC) THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MUL_P521_INTERM1_CORE_EXEC;
       fst BIGNUM_MUL_P521_NEON_CORE_EXEC;
       fst BIGNUM_MUL_P521_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MUL_P521_CORE_EQUIV1,BIGNUM_MUL_P521_CORE_EQUIV2)
    (mul_p521_eqin,mul_p521_eqout_TRANS)
    (BIGNUM_MUL_P521_CORE_EXEC,BIGNUM_MUL_P521_INTERM1_CORE_EXEC,
     BIGNUM_MUL_P521_NEON_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MUL_P521_NEON_SUBROUTINE_CORRECT
          from BIGNUM_MUL_P521_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MUL_P521_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `ALL (nonoverlapping
      (word pc:int64, LENGTH
        (APPEND bignum_mul_p521_core_mc barrier_inst_bytes)))
      [(z:int64,8 * 9); (stackpointer:int64,80)] /\
     aligned 16 stackpointer`
    [`z:int64`;`x:int64`;`y:int64`] bignum_mul_p521_core_mc
    `\s0. C_ARGUMENTS [z;x;y] s0 /\ read SP s0 = stackpointer`;;

let BIGNUM_MUL_P521_EVENTUALLY_N_AT_PC = time prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MUL_P521_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_mul_p521_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              fst BIGNUM_MUL_P521_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MUL_P521_CORE_EXEC]
    THEN CONV_TAC NUM_DIVIDES_CONV
    THEN NO_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MUL_P521_CORE_EXEC);;


let BIGNUM_MUL_P521_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MUL_P521_EXEC
    BIGNUM_MUL_P521_CORE_EXEC
    BIGNUM_MUL_P521_CORE_CORRECT
    BIGNUM_MUL_P521_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_MUL_P521_CORE_CORRECT with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_mul_p521_core_mc replaced with
    bignum_mul_p521_neon_core_m
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_MUL_P521_NEON_CORE_CORRECT = prove
 (`!z x y a b pc2 stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc2,LENGTH bignum_mul_p521_neon_core_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc2,LENGTH bignum_mul_p521_neon_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_mul_p521_neon_core_mc /\
                  read PC s = word(pc2) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc2 + LENGTH bignum_mul_p521_neon_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,9);
                          memory :> bytes(stackpointer,80)])`,
  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      ALL (nonoverlapping (word pc,
        LENGTH (APPEND bignum_mul_p521_core_mc barrier_inst_bytes)))
      [(stackpointer:int64,80);(z:int64,8*9);(x:int64,8 * 9);(y:int64,8 * 9)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MUL_P521_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    time FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MUL_P521_CORE_EQUIV BIGNUM_MUL_P521_CORE_CORRECT_N
    (BIGNUM_MUL_P521_CORE_EXEC,BIGNUM_MUL_P521_NEON_CORE_EXEC)
    (mul_p521_eqin,mul_p521_eqout));;


let BIGNUM_MUL_P521_NEON_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_mul_p521_neon_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_mul_p521_neon_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p521_neon_mc /\
                  read PC s = word(pc+20) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + (20 + LENGTH bignum_mul_p521_neon_core_mc)) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,9);
                          memory :> bytes(stackpointer,80)])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MUL_P521_NEON_CORE_CORRECT
      bignum_mul_p521_neon_core_mc_def
      [fst BIGNUM_MUL_P521_NEON_EXEC;
       fst BIGNUM_MUL_P521_NEON_CORE_EXEC]);;


let BIGNUM_MUL_P521_NEON_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_mul_p521_neon_mc) /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [(word pc,LENGTH bignum_mul_p521_neon_mc); (x,8 * 9); (y,8 * 9);
             (z,8 * 9)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p521_neon_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = returnaddress /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 144),144)])`,
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)
    (REWRITE_RULE [fst BIGNUM_MUL_P521_NEON_CORE_EXEC;
                   fst BIGNUM_MUL_P521_NEON_EXEC]
     BIGNUM_MUL_P521_NEON_CORRECT) in
  REWRITE_TAC[fst BIGNUM_MUL_P521_NEON_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_P521_NEON_EXEC th
   `[X19;X20;X21;X22;X23;X24;X25;X26]` 144);;
