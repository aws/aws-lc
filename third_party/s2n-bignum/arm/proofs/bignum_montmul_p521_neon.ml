(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-unscheduled program
******************************************************************************)

needs "arm/proofs/bignum_montmul_p521.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to both
   bignum_montmul_p521 and bignum_montmul_p521_neon. This is a vectorized
   version of bignum_montmul_p521 but instructions are unscheduled. *)

let bignum_montmul_p521_interm1_ops:int list = [
  0xa9401c2e; (* ldp	x14, x7, [x1] *)
  0xa9416423; (* ldp	x3, x25, [x1, #16] *)
  0xa940604a; (* ldp	x10, x24, [x2] *)
  0x3dc00020; (* ldr	q0, [x1] *)
  0x3dc00059; (* ldr	q25, [x2] *)
  0xa941184c; (* ldp	x12, x6, [x2, #16] *)
  0x6f00e5f2; (* movi	v18.2d, #0xffffffff *)
  0x4e995b23; (* uzp2	v3.4s, v25.4s, v25.4s *)
  0x0ea1281a; (* xtn	v26.2s, v0.2d *)
  0x0ea12b36; (* xtn	v22.2s, v25.2d *)
  0x4ea00b38; (* rev64	v24.4s, v25.4s *)
  0x2eb6c353; (* umull	v19.2d, v26.2s, v22.2s *)
  0x2ea3c359; (* umull	v25.2d, v26.2s, v3.2s *)
  0x4e805814; (* uzp2	v20.4s, v0.4s, v0.4s *)
  0x4ea09f00; (* mul	v0.4s, v24.4s, v0.4s *)
  0x6f601679; (* usra	v25.2d, v19.2d, #32 *)
  0x2ea3c286; (* umull	v6.2d, v20.2s, v3.2s *)
  0x6ea02800; (* uaddlp	v0.2d, v0.4s *)
  0x4e321f32; (* and	v18.16b, v25.16b, v18.16b *)
  0x2eb68292; (* umlal	v18.2d, v20.2s, v22.2s *)
  0x4f605400; (* shl	v0.2d, v0.2d, #32 *)
  0x6f601726; (* usra	v6.2d, v25.2d, #32 *)
  0x2eb68340; (* umlal	v0.2d, v26.2s, v22.2s *)
  0x6f601646; (* usra	v6.2d, v18.2d, #32 *)
  0x4e083c17; (* mov	x23, v0.d[0] *)
  0x4e183c10; (* mov	x16, v0.d[1] *)
  0x9b0c7c65; (* mul	x5, x3, x12 *)
  0x9b067f35; (* mul	x21, x25, x6 *)
  0x4e083cd3; (* mov	x19, v6.d[0] *)
  0xab130210; (* adds	x16, x16, x19 *)
  0x4e183cd3; (* mov	x19, v6.d[1] *)
  0xba1300a5; (* adcs	x5, x5, x19 *)
  0x9bcc7c73; (* umulh	x19, x3, x12 *)
  0xba1302b5; (* adcs	x21, x21, x19 *)
  0x9bc67f33; (* umulh	x19, x25, x6 *)
  0x9a1f0273; (* adc	x19, x19, xzr *)
  0xab170208; (* adds	x8, x16, x23 *)
  0xba1000b0; (* adcs	x16, x5, x16 *)
  0xba0502a5; (* adcs	x5, x21, x5 *)
  0xba150275; (* adcs	x21, x19, x21 *)
  0x9a1303f3; (* adc	x19, xzr, x19 *)
  0xab17020b; (* adds	x11, x16, x23 *)
  0xba0800af; (* adcs	x15, x5, x8 *)
  0xba1002b0; (* adcs	x16, x21, x16 *)
  0xba050265; (* adcs	x5, x19, x5 *)
  0xba1503f5; (* adcs	x21, xzr, x21 *)
  0x9a1303f3; (* adc	x19, xzr, x19 *)
  0xeb190074; (* subs	x20, x3, x25 *)
  0xda942694; (* cneg	x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm	x9, cc  // cc = lo, ul, last *)
  0xeb0c00cd; (* subs	x13, x6, x12 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul	x26, x20, x13 *)
  0x9bcd7e94; (* umulh	x20, x20, x13 *)
  0xda892129; (* cinv	x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn	x9, #0x1 *)
  0xca09034d; (* eor	x13, x26, x9 *)
  0xba0d00a5; (* adcs	x5, x5, x13 *)
  0xca090294; (* eor	x20, x20, x9 *)
  0xba1402b5; (* adcs	x21, x21, x20 *)
  0x9a090273; (* adc	x19, x19, x9 *)
  0xeb0701d4; (* subs	x20, x14, x7 *)
  0xda942694; (* cneg	x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm	x9, cc  // cc = lo, ul, last *)
  0xeb0a030d; (* subs	x13, x24, x10 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul	x26, x20, x13 *)
  0x9bcd7e94; (* umulh	x20, x20, x13 *)
  0xda892129; (* cinv	x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn	x9, #0x1 *)
  0xca09034d; (* eor	x13, x26, x9 *)
  0xba0d0108; (* adcs	x8, x8, x13 *)
  0xca090294; (* eor	x20, x20, x9 *)
  0xba14016b; (* adcs	x11, x11, x20 *)
  0xba0901ef; (* adcs	x15, x15, x9 *)
  0xba090210; (* adcs	x16, x16, x9 *)
  0xba0900a5; (* adcs	x5, x5, x9 *)
  0xba0902b5; (* adcs	x21, x21, x9 *)
  0x9a090273; (* adc	x19, x19, x9 *)
  0xeb1900f4; (* subs	x20, x7, x25 *)
  0xda942694; (* cneg	x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm	x9, cc  // cc = lo, ul, last *)
  0xeb1800cd; (* subs	x13, x6, x24 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul	x26, x20, x13 *)
  0x9bcd7e94; (* umulh	x20, x20, x13 *)
  0xda892129; (* cinv	x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn	x9, #0x1 *)
  0xca09034d; (* eor	x13, x26, x9 *)
  0xba0d0210; (* adcs	x16, x16, x13 *)
  0xca090294; (* eor	x20, x20, x9 *)
  0xba1400a5; (* adcs	x5, x5, x20 *)
  0xba0902b5; (* adcs	x21, x21, x9 *)
  0x9a090273; (* adc	x19, x19, x9 *)
  0xeb0301d4; (* subs	x20, x14, x3 *)
  0xda942694; (* cneg	x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm	x9, cc  // cc = lo, ul, last *)
  0xeb0a018d; (* subs	x13, x12, x10 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul	x26, x20, x13 *)
  0x9bcd7e94; (* umulh	x20, x20, x13 *)
  0xda892129; (* cinv	x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn	x9, #0x1 *)
  0xca09034d; (* eor	x13, x26, x9 *)
  0xba0d016b; (* adcs	x11, x11, x13 *)
  0xca090294; (* eor	x20, x20, x9 *)
  0xba1401ef; (* adcs	x15, x15, x20 *)
  0xba090210; (* adcs	x16, x16, x9 *)
  0xba0900a5; (* adcs	x5, x5, x9 *)
  0xba0902b5; (* adcs	x21, x21, x9 *)
  0x9a090273; (* adc	x19, x19, x9 *)
  0xeb1901d9; (* subs	x25, x14, x25 *)
  0xda992739; (* cneg	x25, x25, cc  // cc = lo, ul, last *)
  0xda9f23f4; (* csetm	x20, cc  // cc = lo, ul, last *)
  0xeb0a00ca; (* subs	x10, x6, x10 *)
  0xda8a254a; (* cneg	x10, x10, cc  // cc = lo, ul, last *)
  0x9b0a7f26; (* mul	x6, x25, x10 *)
  0x9bca7f39; (* umulh	x25, x25, x10 *)
  0xda94228a; (* cinv	x10, x20, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn	x10, #0x1 *)
  0xca0a00c6; (* eor	x6, x6, x10 *)
  0xba0601e6; (* adcs	x6, x15, x6 *)
  0xca0a0339; (* eor	x25, x25, x10 *)
  0xba190219; (* adcs	x25, x16, x25 *)
  0xba0a00b0; (* adcs	x16, x5, x10 *)
  0xba0a02a5; (* adcs	x5, x21, x10 *)
  0x9a0a026a; (* adc	x10, x19, x10 *)
  0xeb0300e7; (* subs	x7, x7, x3 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23e3; (* csetm	x3, cc  // cc = lo, ul, last *)
  0xeb180198; (* subs	x24, x12, x24 *)
  0xda982718; (* cneg	x24, x24, cc  // cc = lo, ul, last *)
  0x9b187cec; (* mul	x12, x7, x24 *)
  0x9bd87ce7; (* umulh	x7, x7, x24 *)
  0xda832063; (* cinv	x3, x3, cc  // cc = lo, ul, last *)
  0xb100047f; (* cmn	x3, #0x1 *)
  0xca030198; (* eor	x24, x12, x3 *)
  0xba1800d8; (* adcs	x24, x6, x24 *)
  0xca0300e7; (* eor	x7, x7, x3 *)
  0xba070327; (* adcs	x7, x25, x7 *)
  0xba030219; (* adcs	x25, x16, x3 *)
  0xba0300ac; (* adcs	x12, x5, x3 *)
  0x9a030143; (* adc	x3, x10, x3 *)
  0xd377daea; (* lsl	x10, x23, #9 *)
  0x93d7dd06; (* extr	x6, x8, x23, #55 *)
  0x93c8dd77; (* extr	x23, x11, x8, #55 *)
  0x93cbdf10; (* extr	x16, x24, x11, #55 *)
  0xd377ff18; (* lsr	x24, x24, #55 *)
  0xa90067e7; (* stp	x7, x25, [sp] *)
  0xa9010fec; (* stp	x12, x3, [sp, #16] *)
  0xa9021bea; (* stp	x10, x6, [sp, #32] *)
  0xa90343f7; (* stp	x23, x16, [sp, #48] *)
  0xf90023f8; (* str	x24, [sp, #64] *)
  0xa9420c27; (* ldp	x7, x3, [x1, #32] *)
  0x3dc00820; (* ldr	q0, [x1, #32] *)
  0xa9432839; (* ldp	x25, x10, [x1, #48] *)
  0xa9423058; (* ldp	x24, x12, [x2, #32] *)
  0x3dc00859; (* ldr	q25, [x2, #32] *)
  0xa9435c46; (* ldp	x6, x23, [x2, #48] *)
  0x3dc00c32; (* ldr	q18, [x1, #48] *)
  0x3dc00c43; (* ldr	q3, [x2, #48] *)
  0x4e801b3a; (* uzp1	v26.4s, v25.4s, v0.4s *)
  0x4ea00b39; (* rev64	v25.4s, v25.4s *)
  0x4e801816; (* uzp1	v22.4s, v0.4s, v0.4s *)
  0x4ea09f20; (* mul	v0.4s, v25.4s, v0.4s *)
  0x6ea02800; (* uaddlp	v0.2d, v0.4s *)
  0x4f605400; (* shl	v0.2d, v0.2d, #32 *)
  0x2eba82c0; (* umlal	v0.2d, v22.2s, v26.2s *)
  0x4e083c10; (* mov	x16, v0.d[0] *)
  0x4e183c05; (* mov	x5, v0.d[1] *)
  0x6f00e5e0; (* movi	v0.2d, #0xffffffff *)
  0x4e835879; (* uzp2	v25.4s, v3.4s, v3.4s *)
  0x0ea12a5a; (* xtn	v26.2s, v18.2d *)
  0x0ea12876; (* xtn	v22.2s, v3.2d *)
  0x4ea00878; (* rev64	v24.4s, v3.4s *)
  0x2eb6c353; (* umull	v19.2d, v26.2s, v22.2s *)
  0x2eb9c343; (* umull	v3.2d, v26.2s, v25.2s *)
  0x4e925a54; (* uzp2	v20.4s, v18.4s, v18.4s *)
  0x4eb29f12; (* mul	v18.4s, v24.4s, v18.4s *)
  0x6f601663; (* usra	v3.2d, v19.2d, #32 *)
  0x2eb9c286; (* umull	v6.2d, v20.2s, v25.2s *)
  0x6ea02a59; (* uaddlp	v25.2d, v18.4s *)
  0x4e201c60; (* and	v0.16b, v3.16b, v0.16b *)
  0x2eb68280; (* umlal	v0.2d, v20.2s, v22.2s *)
  0x4f605739; (* shl	v25.2d, v25.2d, #32 *)
  0x6f601466; (* usra	v6.2d, v3.2d, #32 *)
  0x2eb68359; (* umlal	v25.2d, v26.2s, v22.2s *)
  0x6f601406; (* usra	v6.2d, v0.2d, #32 *)
  0x4e083f35; (* mov	x21, v25.d[0] *)
  0x4e183f33; (* mov	x19, v25.d[1] *)
  0x9bd87ce8; (* umulh	x8, x7, x24 *)
  0xab0800a5; (* adds	x5, x5, x8 *)
  0x9bcc7c68; (* umulh	x8, x3, x12 *)
  0xba0802b5; (* adcs	x21, x21, x8 *)
  0x4e083cc8; (* mov	x8, v6.d[0] *)
  0xba080273; (* adcs	x19, x19, x8 *)
  0x4e183cc8; (* mov	x8, v6.d[1] *)
  0x9a1f0108; (* adc	x8, x8, xzr *)
  0xab1000ab; (* adds	x11, x5, x16 *)
  0xba0502a5; (* adcs	x5, x21, x5 *)
  0xba150275; (* adcs	x21, x19, x21 *)
  0xba130113; (* adcs	x19, x8, x19 *)
  0x9a0803e8; (* adc	x8, xzr, x8 *)
  0xab1000af; (* adds	x15, x5, x16 *)
  0xba0b02b4; (* adcs	x20, x21, x11 *)
  0xba050265; (* adcs	x5, x19, x5 *)
  0xba150115; (* adcs	x21, x8, x21 *)
  0xba1303f3; (* adcs	x19, xzr, x19 *)
  0x9a0803e8; (* adc	x8, xzr, x8 *)
  0xeb0a0329; (* subs	x9, x25, x10 *)
  0xda892529; (* cneg	x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm	x13, cc  // cc = lo, ul, last *)
  0xeb0602fa; (* subs	x26, x23, x6 *)
  0xda9a275a; (* cneg	x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul	x22, x9, x26 *)
  0x9bda7d29; (* umulh	x9, x9, x26 *)
  0xda8d21ad; (* cinv	x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn	x13, #0x1 *)
  0xca0d02da; (* eor	x26, x22, x13 *)
  0xba1a02b5; (* adcs	x21, x21, x26 *)
  0xca0d0129; (* eor	x9, x9, x13 *)
  0xba090273; (* adcs	x19, x19, x9 *)
  0x9a0d0108; (* adc	x8, x8, x13 *)
  0xeb0300e9; (* subs	x9, x7, x3 *)
  0xda892529; (* cneg	x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm	x13, cc  // cc = lo, ul, last *)
  0xeb18019a; (* subs	x26, x12, x24 *)
  0xda9a275a; (* cneg	x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul	x22, x9, x26 *)
  0x9bda7d29; (* umulh	x9, x9, x26 *)
  0xda8d21ad; (* cinv	x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn	x13, #0x1 *)
  0xca0d02da; (* eor	x26, x22, x13 *)
  0xba1a016b; (* adcs	x11, x11, x26 *)
  0xca0d0129; (* eor	x9, x9, x13 *)
  0xba0901ef; (* adcs	x15, x15, x9 *)
  0xba0d0294; (* adcs	x20, x20, x13 *)
  0xba0d00a5; (* adcs	x5, x5, x13 *)
  0xba0d02b5; (* adcs	x21, x21, x13 *)
  0xba0d0273; (* adcs	x19, x19, x13 *)
  0x9a0d0108; (* adc	x8, x8, x13 *)
  0xeb0a0069; (* subs	x9, x3, x10 *)
  0xda892529; (* cneg	x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm	x13, cc  // cc = lo, ul, last *)
  0xeb0c02fa; (* subs	x26, x23, x12 *)
  0xda9a275a; (* cneg	x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul	x22, x9, x26 *)
  0x9bda7d29; (* umulh	x9, x9, x26 *)
  0xda8d21ad; (* cinv	x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn	x13, #0x1 *)
  0xca0d02da; (* eor	x26, x22, x13 *)
  0xba1a00a5; (* adcs	x5, x5, x26 *)
  0xca0d0129; (* eor	x9, x9, x13 *)
  0xba0902ae; (* adcs	x14, x21, x9 *)
  0xba0d0275; (* adcs	x21, x19, x13 *)
  0x9a0d0113; (* adc	x19, x8, x13 *)
  0xeb1900e9; (* subs	x9, x7, x25 *)
  0xda892528; (* cneg	x8, x9, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm	x9, cc  // cc = lo, ul, last *)
  0xeb1800cd; (* subs	x13, x6, x24 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7d1a; (* mul	x26, x8, x13 *)
  0x9bcd7d08; (* umulh	x8, x8, x13 *)
  0xda892129; (* cinv	x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn	x9, #0x1 *)
  0xca09034d; (* eor	x13, x26, x9 *)
  0xba0d01ef; (* adcs	x15, x15, x13 *)
  0xca090108; (* eor	x8, x8, x9 *)
  0xba080288; (* adcs	x8, x20, x8 *)
  0xba0900a5; (* adcs	x5, x5, x9 *)
  0xba0901d4; (* adcs	x20, x14, x9 *)
  0xba0902b5; (* adcs	x21, x21, x9 *)
  0x9a090273; (* adc	x19, x19, x9 *)
  0xeb0a00e9; (* subs	x9, x7, x10 *)
  0xda892529; (* cneg	x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm	x13, cc  // cc = lo, ul, last *)
  0xeb1802fa; (* subs	x26, x23, x24 *)
  0xda9a275a; (* cneg	x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul	x22, x9, x26 *)
  0x9bda7d29; (* umulh	x9, x9, x26 *)
  0xda8d21ad; (* cinv	x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn	x13, #0x1 *)
  0xca0d02da; (* eor	x26, x22, x13 *)
  0xba1a0108; (* adcs	x8, x8, x26 *)
  0xca0d0129; (* eor	x9, x9, x13 *)
  0xba0900a5; (* adcs	x5, x5, x9 *)
  0xba0d0294; (* adcs	x20, x20, x13 *)
  0xba0d02b5; (* adcs	x21, x21, x13 *)
  0x9a0d0273; (* adc	x19, x19, x13 *)
  0xeb190069; (* subs	x9, x3, x25 *)
  0xda892529; (* cneg	x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm	x13, cc  // cc = lo, ul, last *)
  0xeb0c00da; (* subs	x26, x6, x12 *)
  0xda9a275a; (* cneg	x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul	x22, x9, x26 *)
  0x9bda7d29; (* umulh	x9, x9, x26 *)
  0xda8d21ad; (* cinv	x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn	x13, #0x1 *)
  0xca0d02da; (* eor	x26, x22, x13 *)
  0xba1a0108; (* adcs	x8, x8, x26 *)
  0xca0d0129; (* eor	x9, x9, x13 *)
  0xba0900a5; (* adcs	x5, x5, x9 *)
  0xba0d0294; (* adcs	x20, x20, x13 *)
  0xba0d02b5; (* adcs	x21, x21, x13 *)
  0x9a0d0273; (* adc	x19, x19, x13 *)
  0xa94037e9; (* ldp	x9, x13, [sp] *)
  0xab090210; (* adds	x16, x16, x9 *)
  0xba0d016b; (* adcs	x11, x11, x13 *)
  0xa9002ff0; (* stp	x16, x11, [sp] *)
  0xa9412ff0; (* ldp	x16, x11, [sp, #16] *)
  0xba1001f0; (* adcs	x16, x15, x16 *)
  0xba0b0108; (* adcs	x8, x8, x11 *)
  0xa90123f0; (* stp	x16, x8, [sp, #16] *)
  0xa94223f0; (* ldp	x16, x8, [sp, #32] *)
  0xba1000b0; (* adcs	x16, x5, x16 *)
  0xba080285; (* adcs	x5, x20, x8 *)
  0xa90217f0; (* stp	x16, x5, [sp, #32] *)
  0xa94317f0; (* ldp	x16, x5, [sp, #48] *)
  0xba1002b0; (* adcs	x16, x21, x16 *)
  0xba050265; (* adcs	x5, x19, x5 *)
  0xa90317f0; (* stp	x16, x5, [sp, #48] *)
  0xf94023f0; (* ldr	x16, [sp, #64] *)
  0x9a1f0210; (* adc	x16, x16, xzr *)
  0xf90023f0; (* str	x16, [sp, #64] *)
  0xa9401430; (* ldp	x16, x5, [x1] *)
  0xeb1000e7; (* subs	x7, x7, x16 *)
  0xfa050063; (* sbcs	x3, x3, x5 *)
  0xa9411430; (* ldp	x16, x5, [x1, #16] *)
  0xfa100339; (* sbcs	x25, x25, x16 *)
  0xfa05014a; (* sbcs	x10, x10, x5 *)
  0xda9f23f0; (* csetm	x16, cc  // cc = lo, ul, last *)
  0xa9405445; (* ldp	x5, x21, [x2] *)
  0xeb1800b8; (* subs	x24, x5, x24 *)
  0xfa0c02ac; (* sbcs	x12, x21, x12 *)
  0xa9414c45; (* ldp	x5, x19, [x2, #16] *)
  0xfa0600a6; (* sbcs	x6, x5, x6 *)
  0xfa170277; (* sbcs	x23, x19, x23 *)
  0xda9f23e5; (* csetm	x5, cc  // cc = lo, ul, last *)
  0xca1000e7; (* eor	x7, x7, x16 *)
  0xeb1000e7; (* subs	x7, x7, x16 *)
  0xca100063; (* eor	x3, x3, x16 *)
  0xfa100063; (* sbcs	x3, x3, x16 *)
  0xca100339; (* eor	x25, x25, x16 *)
  0xfa100339; (* sbcs	x25, x25, x16 *)
  0xca10014a; (* eor	x10, x10, x16 *)
  0xda10014a; (* sbc	x10, x10, x16 *)
  0xca050318; (* eor	x24, x24, x5 *)
  0xeb050318; (* subs	x24, x24, x5 *)
  0xca05018c; (* eor	x12, x12, x5 *)
  0xfa05018c; (* sbcs	x12, x12, x5 *)
  0xca0500c6; (* eor	x6, x6, x5 *)
  0xfa0500c6; (* sbcs	x6, x6, x5 *)
  0xca0502f7; (* eor	x23, x23, x5 *)
  0xda0502f7; (* sbc	x23, x23, x5 *)
  0xca1000b0; (* eor	x16, x5, x16 *)
  0x9b187cf5; (* mul	x21, x7, x24 *)
  0x9b0c7c65; (* mul	x5, x3, x12 *)
  0x9b067f33; (* mul	x19, x25, x6 *)
  0x9b177d48; (* mul	x8, x10, x23 *)
  0x9bd87ceb; (* umulh	x11, x7, x24 *)
  0xab0b00a5; (* adds	x5, x5, x11 *)
  0x9bcc7c6b; (* umulh	x11, x3, x12 *)
  0xba0b0273; (* adcs	x19, x19, x11 *)
  0x9bc67f2b; (* umulh	x11, x25, x6 *)
  0xba0b0108; (* adcs	x8, x8, x11 *)
  0x9bd77d4b; (* umulh	x11, x10, x23 *)
  0x9a1f016b; (* adc	x11, x11, xzr *)
  0xab1500af; (* adds	x15, x5, x21 *)
  0xba050265; (* adcs	x5, x19, x5 *)
  0xba130113; (* adcs	x19, x8, x19 *)
  0xba080168; (* adcs	x8, x11, x8 *)
  0x9a0b03eb; (* adc	x11, xzr, x11 *)
  0xab1500b4; (* adds	x20, x5, x21 *)
  0xba0f0269; (* adcs	x9, x19, x15 *)
  0xba050105; (* adcs	x5, x8, x5 *)
  0xba130173; (* adcs	x19, x11, x19 *)
  0xba0803e8; (* adcs	x8, xzr, x8 *)
  0x9a0b03eb; (* adc	x11, xzr, x11 *)
  0xeb0a032d; (* subs	x13, x25, x10 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm	x26, cc  // cc = lo, ul, last *)
  0xeb0602f6; (* subs	x22, x23, x6 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul	x4, x13, x22 *)
  0x9bd67dad; (* umulh	x13, x13, x22 *)
  0xda9a235a; (* cinv	x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn	x26, #0x1 *)
  0xca1a0096; (* eor	x22, x4, x26 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0xca1a01ad; (* eor	x13, x13, x26 *)
  0xba0d0108; (* adcs	x8, x8, x13 *)
  0x9a1a016b; (* adc	x11, x11, x26 *)
  0xeb0300ed; (* subs	x13, x7, x3 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm	x26, cc  // cc = lo, ul, last *)
  0xeb180196; (* subs	x22, x12, x24 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul	x4, x13, x22 *)
  0x9bd67dad; (* umulh	x13, x13, x22 *)
  0xda9a235a; (* cinv	x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn	x26, #0x1 *)
  0xca1a0096; (* eor	x22, x4, x26 *)
  0xba1601ef; (* adcs	x15, x15, x22 *)
  0xca1a01ad; (* eor	x13, x13, x26 *)
  0xba0d0294; (* adcs	x20, x20, x13 *)
  0xba1a0129; (* adcs	x9, x9, x26 *)
  0xba1a00a5; (* adcs	x5, x5, x26 *)
  0xba1a0273; (* adcs	x19, x19, x26 *)
  0xba1a0108; (* adcs	x8, x8, x26 *)
  0x9a1a016b; (* adc	x11, x11, x26 *)
  0xeb0a006d; (* subs	x13, x3, x10 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm	x26, cc  // cc = lo, ul, last *)
  0xeb0c02f6; (* subs	x22, x23, x12 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul	x4, x13, x22 *)
  0x9bd67dad; (* umulh	x13, x13, x22 *)
  0xda9a235a; (* cinv	x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn	x26, #0x1 *)
  0xca1a0096; (* eor	x22, x4, x26 *)
  0xba1600a5; (* adcs	x5, x5, x22 *)
  0xca1a01ad; (* eor	x13, x13, x26 *)
  0xba0d0273; (* adcs	x19, x19, x13 *)
  0xba1a0108; (* adcs	x8, x8, x26 *)
  0x9a1a016b; (* adc	x11, x11, x26 *)
  0xeb1900ed; (* subs	x13, x7, x25 *)
  0xda8d25ad; (* cneg	x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm	x26, cc  // cc = lo, ul, last *)
  0xeb1800d6; (* subs	x22, x6, x24 *)
  0xda9626d6; (* cneg	x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul	x4, x13, x22 *)
  0x9bd67dad; (* umulh	x13, x13, x22 *)
  0xda9a235a; (* cinv	x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn	x26, #0x1 *)
  0xca1a0096; (* eor	x22, x4, x26 *)
  0xba160294; (* adcs	x20, x20, x22 *)
  0xca1a01ad; (* eor	x13, x13, x26 *)
  0xba0d0129; (* adcs	x9, x9, x13 *)
  0xba1a00a5; (* adcs	x5, x5, x26 *)
  0xba1a0273; (* adcs	x19, x19, x26 *)
  0xba1a0108; (* adcs	x8, x8, x26 *)
  0x9a1a016b; (* adc	x11, x11, x26 *)
  0xeb0a00e7; (* subs	x7, x7, x10 *)
  0xda8724e7; (* cneg	x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23ea; (* csetm	x10, cc  // cc = lo, ul, last *)
  0xeb1802f8; (* subs	x24, x23, x24 *)
  0xda982718; (* cneg	x24, x24, cc  // cc = lo, ul, last *)
  0x9b187cf7; (* mul	x23, x7, x24 *)
  0x9bd87ce7; (* umulh	x7, x7, x24 *)
  0xda8a214a; (* cinv	x10, x10, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn	x10, #0x1 *)
  0xca0a02f8; (* eor	x24, x23, x10 *)
  0xba180138; (* adcs	x24, x9, x24 *)
  0xca0a00e7; (* eor	x7, x7, x10 *)
  0xba0700a7; (* adcs	x7, x5, x7 *)
  0xba0a0277; (* adcs	x23, x19, x10 *)
  0xba0a0105; (* adcs	x5, x8, x10 *)
  0x9a0a016a; (* adc	x10, x11, x10 *)
  0xeb190063; (* subs	x3, x3, x25 *)
  0xda832463; (* cneg	x3, x3, cc  // cc = lo, ul, last *)
  0xda9f23f9; (* csetm	x25, cc  // cc = lo, ul, last *)
  0xeb0c00cc; (* subs	x12, x6, x12 *)
  0xda8c258c; (* cneg	x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7c66; (* mul	x6, x3, x12 *)
  0x9bcc7c63; (* umulh	x3, x3, x12 *)
  0xda992339; (* cinv	x25, x25, cc  // cc = lo, ul, last *)
  0xb100073f; (* cmn	x25, #0x1 *)
  0xca1900cc; (* eor	x12, x6, x25 *)
  0xba0c0318; (* adcs	x24, x24, x12 *)
  0xca190063; (* eor	x3, x3, x25 *)
  0xba0300e7; (* adcs	x7, x7, x3 *)
  0xba1902e3; (* adcs	x3, x23, x25 *)
  0xba1900ac; (* adcs	x12, x5, x25 *)
  0x9a190159; (* adc	x25, x10, x25 *)
  0xa9401bea; (* ldp	x10, x6, [sp] *)
  0xa94117f7; (* ldp	x23, x5, [sp, #16] *)
  0xca1002b5; (* eor	x21, x21, x16 *)
  0xab0a02b5; (* adds	x21, x21, x10 *)
  0xca1001f3; (* eor	x19, x15, x16 *)
  0xba060273; (* adcs	x19, x19, x6 *)
  0xca100288; (* eor	x8, x20, x16 *)
  0xba170108; (* adcs	x8, x8, x23 *)
  0xca100318; (* eor	x24, x24, x16 *)
  0xba050318; (* adcs	x24, x24, x5 *)
  0xca1000e7; (* eor	x7, x7, x16 *)
  0xa9423feb; (* ldp	x11, x15, [sp, #32] *)
  0xa94327f4; (* ldp	x20, x9, [sp, #48] *)
  0xf94023ed; (* ldr	x13, [sp, #64] *)
  0xba0b00e7; (* adcs	x7, x7, x11 *)
  0xca100063; (* eor	x3, x3, x16 *)
  0xba0f0063; (* adcs	x3, x3, x15 *)
  0xca10018c; (* eor	x12, x12, x16 *)
  0xba14018c; (* adcs	x12, x12, x20 *)
  0xca100339; (* eor	x25, x25, x16 *)
  0xba090339; (* adcs	x25, x25, x9 *)
  0x9a1f01ba; (* adc	x26, x13, xzr *)
  0xab0a00e7; (* adds	x7, x7, x10 *)
  0xba060063; (* adcs	x3, x3, x6 *)
  0xba17018a; (* adcs	x10, x12, x23 *)
  0xba050339; (* adcs	x25, x25, x5 *)
  0x9240220c; (* and	x12, x16, #0x1ff *)
  0xd377daa6; (* lsl	x6, x21, #9 *)
  0xaa0c00cc; (* orr	x12, x6, x12 *)
  0xba0c016c; (* adcs	x12, x11, x12 *)
  0x93d5de66; (* extr	x6, x19, x21, #55 *)
  0xba0601e6; (* adcs	x6, x15, x6 *)
  0x93d3dd17; (* extr	x23, x8, x19, #55 *)
  0xba170297; (* adcs	x23, x20, x23 *)
  0x93c8df10; (* extr	x16, x24, x8, #55 *)
  0xba100130; (* adcs	x16, x9, x16 *)
  0xd377ff18; (* lsr	x24, x24, #55 *)
  0x9a0d0318; (* adc	x24, x24, x13 *)
  0xf9402045; (* ldr	x5, [x2, #64] *)
  0xa9404c35; (* ldp	x21, x19, [x1] *)
  0x9240cea8; (* and	x8, x21, #0xfffffffffffff *)
  0x9b087ca8; (* mul	x8, x5, x8 *)
  0xf940202b; (* ldr	x11, [x1, #64] *)
  0xa940504f; (* ldp	x15, x20, [x2] *)
  0x9240cde9; (* and	x9, x15, #0xfffffffffffff *)
  0x9b097d69; (* mul	x9, x11, x9 *)
  0x8b090108; (* add	x8, x8, x9 *)
  0x93d5d275; (* extr	x21, x19, x21, #52 *)
  0x9240ceb5; (* and	x21, x21, #0xfffffffffffff *)
  0x9b157cb5; (* mul	x21, x5, x21 *)
  0x93cfd28f; (* extr	x15, x20, x15, #52 *)
  0x9240cdef; (* and	x15, x15, #0xfffffffffffff *)
  0x9b0f7d6f; (* mul	x15, x11, x15 *)
  0x8b0f02b5; (* add	x21, x21, x15 *)
  0xd374fd0f; (* lsr	x15, x8, #52 *)
  0x8b0f02b5; (* add	x21, x21, x15 *)
  0xd374cd08; (* lsl	x8, x8, #12 *)
  0x93c832a8; (* extr	x8, x21, x8, #12 *)
  0xab0800e7; (* adds	x7, x7, x8 *)
  0xa9413c28; (* ldp	x8, x15, [x1, #16] *)
  0xa9413449; (* ldp	x9, x13, [x2, #16] *)
  0x93d3a113; (* extr	x19, x8, x19, #40 *)
  0x9240ce73; (* and	x19, x19, #0xfffffffffffff *)
  0x9b137cb3; (* mul	x19, x5, x19 *)
  0x93d4a134; (* extr	x20, x9, x20, #40 *)
  0x9240ce94; (* and	x20, x20, #0xfffffffffffff *)
  0x9b147d74; (* mul	x20, x11, x20 *)
  0x8b140273; (* add	x19, x19, x20 *)
  0xd374feb4; (* lsr	x20, x21, #52 *)
  0x8b140273; (* add	x19, x19, x20 *)
  0xd374ceb5; (* lsl	x21, x21, #12 *)
  0x93d56275; (* extr	x21, x19, x21, #24 *)
  0xba150063; (* adcs	x3, x3, x21 *)
  0x93c871f5; (* extr	x21, x15, x8, #28 *)
  0x9240ceb5; (* and	x21, x21, #0xfffffffffffff *)
  0x9b157cb5; (* mul	x21, x5, x21 *)
  0x93c971a8; (* extr	x8, x13, x9, #28 *)
  0x9240cd08; (* and	x8, x8, #0xfffffffffffff *)
  0x9b087d68; (* mul	x8, x11, x8 *)
  0x8b0802b5; (* add	x21, x21, x8 *)
  0xd374fe68; (* lsr	x8, x19, #52 *)
  0x8b0802b5; (* add	x21, x21, x8 *)
  0xd374ce73; (* lsl	x19, x19, #12 *)
  0x93d392b3; (* extr	x19, x21, x19, #36 *)
  0xba13014a; (* adcs	x10, x10, x19 *)
  0x8a0a0073; (* and	x19, x3, x10 *)
  0xa9425028; (* ldp	x8, x20, [x1, #32] *)
  0xa9425849; (* ldp	x9, x22, [x2, #32] *)
  0x93cf410f; (* extr	x15, x8, x15, #16 *)
  0x9240cdef; (* and	x15, x15, #0xfffffffffffff *)
  0x9b0f7ca4; (* mul	x4, x5, x15 *)
  0x93cd412f; (* extr	x15, x9, x13, #16 *)
  0x9240cdef; (* and	x15, x15, #0xfffffffffffff *)
  0x9b0f7d6f; (* mul	x15, x11, x15 *)
  0x8b0f008f; (* add	x15, x4, x15 *)
  0xd3503f4d; (* lsl	x13, x26, #48 *)
  0x8b0d01ef; (* add	x15, x15, x13 *)
  0xd374fead; (* lsr	x13, x21, #52 *)
  0x8b0d01ef; (* add	x15, x15, x13 *)
  0xd374ceb5; (* lsl	x21, x21, #12 *)
  0x93d5c1f5; (* extr	x21, x15, x21, #48 *)
  0xba150339; (* adcs	x25, x25, x21 *)
  0x8a190275; (* and	x21, x19, x25 *)
  0xd344fd13; (* lsr	x19, x8, #4 *)
  0x9240ce73; (* and	x19, x19, #0xfffffffffffff *)
  0x9b137cb3; (* mul	x19, x5, x19 *)
  0xd344fd3a; (* lsr	x26, x9, #4 *)
  0x9240cf4d; (* and	x13, x26, #0xfffffffffffff *)
  0x9b0d7d7a; (* mul	x26, x11, x13 *)
  0x8b1a0273; (* add	x19, x19, x26 *)
  0xd374fded; (* lsr	x13, x15, #52 *)
  0x8b0d0273; (* add	x19, x19, x13 *)
  0xd374cdef; (* lsl	x15, x15, #12 *)
  0x93cff26f; (* extr	x15, x19, x15, #60 *)
  0x93c8e288; (* extr	x8, x20, x8, #56 *)
  0x9240cd08; (* and	x8, x8, #0xfffffffffffff *)
  0x9b087ca8; (* mul	x8, x5, x8 *)
  0x93c9e2c9; (* extr	x9, x22, x9, #56 *)
  0x9240cd29; (* and	x9, x9, #0xfffffffffffff *)
  0x9b097d69; (* mul	x9, x11, x9 *)
  0x8b090108; (* add	x8, x8, x9 *)
  0xd374fe73; (* lsr	x19, x19, #52 *)
  0x8b130113; (* add	x19, x8, x19 *)
  0xd378dde8; (* lsl	x8, x15, #8 *)
  0x93c82268; (* extr	x8, x19, x8, #8 *)
  0xba08018c; (* adcs	x12, x12, x8 *)
  0x8a0c02b5; (* and	x21, x21, x12 *)
  0xa9432021; (* ldp	x1, x8, [x1, #48] *)
  0xa9433c42; (* ldp	x2, x15, [x2, #48] *)
  0x93d4b034; (* extr	x20, x1, x20, #44 *)
  0x9240ce94; (* and	x20, x20, #0xfffffffffffff *)
  0x9b147cb4; (* mul	x20, x5, x20 *)
  0x93d6b049; (* extr	x9, x2, x22, #44 *)
  0x9240cd29; (* and	x9, x9, #0xfffffffffffff *)
  0x9b097d69; (* mul	x9, x11, x9 *)
  0x8b090294; (* add	x20, x20, x9 *)
  0xd374fe69; (* lsr	x9, x19, #52 *)
  0x8b090296; (* add	x22, x20, x9 *)
  0xd374ce73; (* lsl	x19, x19, #12 *)
  0x93d352d3; (* extr	x19, x22, x19, #20 *)
  0xba1300c6; (* adcs	x6, x6, x19 *)
  0x8a0602b5; (* and	x21, x21, x6 *)
  0x93c18101; (* extr	x1, x8, x1, #32 *)
  0x9240cc21; (* and	x1, x1, #0xfffffffffffff *)
  0x9b017ca1; (* mul	x1, x5, x1 *)
  0x93c281e2; (* extr	x2, x15, x2, #32 *)
  0x9240cc42; (* and	x2, x2, #0xfffffffffffff *)
  0x9b027d62; (* mul	x2, x11, x2 *)
  0x8b020022; (* add	x2, x1, x2 *)
  0xd374fec1; (* lsr	x1, x22, #52 *)
  0x8b010042; (* add	x2, x2, x1 *)
  0xd374cec1; (* lsl	x1, x22, #12 *)
  0x93c18041; (* extr	x1, x2, x1, #32 *)
  0xba0102f7; (* adcs	x23, x23, x1 *)
  0x8a1702b5; (* and	x21, x21, x23 *)
  0xd354fd01; (* lsr	x1, x8, #20 *)
  0x9b017ca1; (* mul	x1, x5, x1 *)
  0xd354fdf3; (* lsr	x19, x15, #20 *)
  0x9b137d73; (* mul	x19, x11, x19 *)
  0x8b130021; (* add	x1, x1, x19 *)
  0xd374fc53; (* lsr	x19, x2, #52 *)
  0x8b130033; (* add	x19, x1, x19 *)
  0xd374cc42; (* lsl	x2, x2, #12 *)
  0x93c2b262; (* extr	x2, x19, x2, #44 *)
  0xba020210; (* adcs	x16, x16, x2 *)
  0x8a1002a2; (* and	x2, x21, x16 *)
  0x9b0b7ca5; (* mul	x5, x5, x11 *)
  0xd36cfe61; (* lsr	x1, x19, #44 *)
  0x8b0100a5; (* add	x5, x5, x1 *)
  0x9a050318; (* adc	x24, x24, x5 *)
  0xd349ff05; (* lsr	x5, x24, #9 *)
  0xb277db18; (* orr	x24, x24, #0xfffffffffffffe00 *)
  0xeb1f03ff; (* cmp	xzr, xzr *)
  0xba0500ff; (* adcs	xzr, x7, x5 *)
  0xba1f005f; (* adcs	xzr, x2, xzr *)
  0xba1f031f; (* adcs	xzr, x24, xzr *)
  0xba0500e7; (* adcs	x7, x7, x5 *)
  0xba1f0062; (* adcs	x2, x3, xzr *)
  0xba1f014a; (* adcs	x10, x10, xzr *)
  0xba1f0339; (* adcs	x25, x25, xzr *)
  0xba1f018c; (* adcs	x12, x12, xzr *)
  0xba1f00c6; (* adcs	x6, x6, xzr *)
  0xba1f02f7; (* adcs	x23, x23, xzr *)
  0xba1f0210; (* adcs	x16, x16, xzr *)
  0x9a1f0303; (* adc	x3, x24, xzr *)
  0xa9002802; (* stp	x2, x10, [x0] *)
  0xa9013019; (* stp	x25, x12, [x0, #16] *)
  0xa9025c06; (* stp	x6, x23, [x0, #32] *)
  0xd377d8f9; (* lsl	x25, x7, #9 *)
  0x92402063; (* and	x3, x3, #0x1ff *)
  0xaa190063; (* orr	x3, x3, x25 *)
  0xa9030c10; (* stp	x16, x3, [x0, #48] *)
  0xd377fcee; (* lsr	x14, x7, #55 *)
  0xf900200e; (* str	x14, [x0, #64] *)
];;

let bignum_montmul_p521_interm1_core_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_montmul_p521_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_montmul_p521_interm1_core_mc" (term_of_bytes byte_list);;

let BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC =
  ARM_MK_EXEC_RULE bignum_montmul_p521_interm1_core_mc;;

let montmul_p521_eqin = new_definition
  `!s1 s1' x y z stackpointer.
    (montmul_p521_eqin:(armstate#armstate)->int64->int64->int64->int64->bool)
        (s1,s1') x y z stackpointer <=>
    (C_ARGUMENTS [z; x; y] s1 /\
     C_ARGUMENTS [z; x; y] s1' /\
     read SP s1 = stackpointer /\
     read SP s1' = stackpointer /\
     ?a. bignum_from_memory (x,9) s1 = a /\
         bignum_from_memory (x,9) s1' = a /\
     (?b. bignum_from_memory (y,9) s1 = b /\
          bignum_from_memory (y,9) s1' = b))`;;

let montmul_p521_eqout = new_definition
  `!s1 s1' z stackpointer.
    (montmul_p521_eqout:(armstate#armstate)->int64->int64->bool)
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
  ("equal", 11, 134, 31, 154);
  ("insert", 134, 134, 154, 155);
  ("equal", 134, 136, 155, 157);
  ("insert", 136, 136, 157, 158);
  ("equal", 136, 137, 158, 159);
  ("replace", 137, 141, 159, 190);
  ("equal", 141, 145, 190, 194);
  ("replace", 145, 146, 194, 195);
  ("equal", 146, 147, 195, 196);
  ("replace", 147, 148, 196, 197);
  ("equal", 148, 619, 197, 668);
];;

let equiv_goal1 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montmul_p521_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_interm1_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_montmul_p521_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_interm1_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    montmul_p521_eqin
    montmul_p521_eqout
    bignum_montmul_p521_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_montmul_p521_interm1_core_mc
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

let BIGNUM_MONTMUL_P521_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P521_CORE_EXEC;
    fst BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTMUL_P521_CORE_EXEC
    BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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

let bignum_montmul_p521_neon_mc =
  define_from_elf "bignum_montmul_p521_neon_mc"
    "arm/p521/bignum_montmul_p521_neon.o";;

let BIGNUM_MONTMUL_P521_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p521_neon_mc;;

let bignum_montmul_p521_neon_core_mc_def,
    bignum_montmul_p521_neon_core_mc,
    BIGNUM_MONTMUL_P521_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p521_neon_core_mc"
    bignum_montmul_p521_neon_mc
    (`20`,`LENGTH bignum_montmul_p521_neon_mc - 44`)
    (fst BIGNUM_MONTMUL_P521_NEON_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montmul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_neon_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_montmul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_neon_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    montmul_p521_eqin
    montmul_p521_eqout
    bignum_montmul_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_montmul_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;


(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws. *)

let inst_map = [5;4;161;2;7;6;8;9;1;11;10;48;13;175;49;12;160;50;28;15;14;51;174;55;52;172;17;53;16;179;22;18;54;57;19;182;62;21;173;63;185;20;23;178;35;177;181;24;27;59;158;176;3;64;26;155;187;25;33;31;29;180;163;30;162;171;32;164;165;34;36;37;183;186;38;39;184;40;166;41;42;43;167;44;188;45;168;46;47;65;66;67;68;69;56;58;71;60;61;80;81;82;83;87;84;70;86;73;72;74;75;76;77;85;78;79;95;97;96;98;102;99;89;112;100;114;113;115;116;119;101;91;128;129;104;130;88;106;90;118;144;92;93;94;131;132;135;103;117;145;105;107;123;108;121;195;109;146;133;110;151;156;111;120;189;134;122;137;124;154;125;157;139;126;127;210;212;211;136;191;138;140;147;141;159;193;142;143;224;149;170;226;150;225;213;190;214;197;217;192;215;152;148;194;169;153;196;198;216;219;227;231;228;221;199;200;229;201;202;230;203;204;233;205;206;207;208;209;235;218;220;222;223;242;244;243;245;246;249;232;234;247;236;237;248;251;238;239;240;241;257;258;259;260;264;261;250;253;252;262;254;255;256;274;263;275;276;277;278;281;279;266;265;268;267;283;269;328;280;270;271;272;273;282;284;285;286;325;287;288;289;290;291;292;326;327;332;329;330;331;293;294;297;333;334;343;335;345;296;339;341;336;337;295;338;340;347;342;353;344;301;349;346;348;299;350;351;352;362;354;298;300;302;306;303;356;304;305;307;366;308;310;309;355;357;311;314;358;312;313;318;364;315;322;316;317;319;360;320;323;321;379;381;380;324;359;393;394;395;382;383;386;361;363;385;365;367;396;400;384;390;397;368;388;399;369;370;371;372;373;398;374;477;375;376;377;378;387;389;391;404;392;402;411;412;413;414;415;418;401;403;416;405;417;406;420;407;408;409;410;426;427;428;429;430;433;443;431;422;444;432;445;446;447;435;450;419;479;421;423;424;437;425;459;460;461;434;436;448;438;481;439;440;449;441;514;442;462;463;454;452;464;466;451;453;522;465;523;455;468;456;515;470;457;458;467;469;501;475;471;472;476;490;473;474;478;502;492;486;503;483;480;482;485;487;494;484;513;489;488;491;493;495;496;497;516;498;505;499;534;509;500;504;524;518;506;548;536;507;549;508;517;525;519;550;510;526;535;520;539;540;521;511;527;551;537;538;529;531;528;512;562;530;552;532;570;541;542;543;566;567;553;544;555;545;546;533;561;547;592;568;554;556;578;557;558;579;563;580;593;559;564;565;581;582;589;574;590;583;572;603;569;571;560;594;573;584;575;602;607;585;591;632;595;617;618;620;633;586;630;621;608;604;609;576;605;587;577;606;596;597;588;613;598;619;599;611;610;600;601;612;622;614;624;631;626;623;615;625;635;641;616;634;637;636;627;642;638;643;628;639;629;644;647;646;645;648;640;649;650;651;663;667;668;652;653;660;654;655;661;656;657;658;662;659;664;665;666];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTMUL_P521_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTMUL_P521_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_MONTMUL_P521_NEON_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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
       [(word pc,LENGTH bignum_montmul_p521_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_neon_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_montmul_p521_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_neon_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    montmul_p521_eqin
    montmul_p521_eqout
    bignum_montmul_p521_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_montmul_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;

let montmul_p521_eqout_TRANS = prove(
  `!s s2 s' z stackpointer.
    montmul_p521_eqout (s,s') z stackpointer/\
    montmul_p521_eqout (s',s2) z stackpointer
    ==> montmul_p521_eqout (s,s2) z stackpointer`,
  MESON_TAC[montmul_p521_eqout]);;

let BIGNUM_MONTMUL_P521_CORE_EQUIV = time prove(equiv_goal,
  REPEAT STRIP_TAC THEN
  (* To prove the goal, show that there exists an empty slot in the memory
     which can locate bignum_montmul_p521_interm1_core_mc. *)
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc:int64,LENGTH bignum_montmul_p521_core_mc);
        (word pc3:int64,LENGTH bignum_montmul_p521_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc3:int64,LENGTH bignum_montmul_p521_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montmul_p521_neon_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montmul_p521_interm1_core_mc))
        [x,8 * 9; y,8 * 9; stackpointer,80] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    REPEAT (FIRST_X_ASSUM MP_TAC) THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTMUL_P521_NEON_CORE_EXEC;
       fst BIGNUM_MONTMUL_P521_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTMUL_P521_CORE_EQUIV1,BIGNUM_MONTMUL_P521_CORE_EQUIV2)
    (montmul_p521_eqin,montmul_p521_eqout_TRANS)
    (BIGNUM_MONTMUL_P521_CORE_EXEC,BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC,
     BIGNUM_MONTMUL_P521_NEON_CORE_EXEC));;



(******************************************************************************
          Inducing BIGNUM_MONTMUL_P521_NEON_SUBROUTINE_CORRECT
          from BIGNUM_MONTMUL_P521_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTMUL_P521_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `ALL (nonoverlapping
      (word pc:int64, LENGTH
        (APPEND bignum_montmul_p521_core_mc barrier_inst_bytes)))
      [(z:int64,8 * 9); (stackpointer:int64,80)] /\
     aligned 16 stackpointer`
    [`z:int64`;`x:int64`;`y:int64`] bignum_montmul_p521_core_mc
    `\s0. C_ARGUMENTS [z;x;y] s0 /\ read SP s0 = stackpointer`;;

let BIGNUM_MONTMUL_P521_EVENTUALLY_N_AT_PC = time prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTMUL_P521_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montmul_p521_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              fst BIGNUM_MONTMUL_P521_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P521_CORE_EXEC]
    THEN CONV_TAC NUM_DIVIDES_CONV
    THEN NO_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTMUL_P521_CORE_EXEC);;


let BIGNUM_MONTMUL_P521_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTMUL_P521_EXEC
    BIGNUM_MONTMUL_P521_CORE_EXEC
    BIGNUM_MONTMUL_P521_CORE_CORRECT
    BIGNUM_MONTMUL_P521_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_MONTMUL_P521_CORE_CORRECT with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montmul_p521_core_mc replaced with
    bignum_montmul_p521_neon_core_m
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_MONTMUL_P521_NEON_CORE_CORRECT = prove
 (`!z x y a b pc2 stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc2,LENGTH bignum_montmul_p521_neon_core_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc2,LENGTH bignum_montmul_p521_neon_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p521_neon_core_mc /\
                  read PC s = word(pc2) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p521_neon_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
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
        LENGTH (APPEND bignum_montmul_p521_core_mc barrier_inst_bytes)))
      [(stackpointer:int64,80);(z:int64,8*9);(x:int64,8 * 9);(y:int64,8 * 9)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P521_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    time FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P521_CORE_EQUIV BIGNUM_MONTMUL_P521_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P521_CORE_EXEC,BIGNUM_MONTMUL_P521_NEON_CORE_EXEC)
    (montmul_p521_eqin,montmul_p521_eqout));;


let BIGNUM_MONTMUL_P521_NEON_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_montmul_p521_neon_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_montmul_p521_neon_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_neon_mc /\
                  read PC s = word(pc+20) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + (20 + LENGTH bignum_montmul_p521_neon_core_mc)) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,9);
                          memory :> bytes(stackpointer,80)])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P521_NEON_CORE_CORRECT
      bignum_montmul_p521_neon_core_mc_def
      [fst BIGNUM_MONTMUL_P521_NEON_EXEC;
       fst BIGNUM_MONTMUL_P521_NEON_CORE_EXEC]);;


let BIGNUM_MONTMUL_P521_NEON_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_montmul_p521_neon_mc) /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [(word pc,LENGTH bignum_montmul_p521_neon_mc); (x,8 * 9); (y,8 * 9);
             (z,8 * 9)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_neon_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = returnaddress /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 144),144)])`,
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)
    (REWRITE_RULE [fst BIGNUM_MONTMUL_P521_NEON_CORE_EXEC;
                   fst BIGNUM_MONTMUL_P521_NEON_EXEC]
     BIGNUM_MONTMUL_P521_NEON_CORRECT) in
  REWRITE_TAC[fst BIGNUM_MONTMUL_P521_NEON_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P521_NEON_EXEC th
   `[X19;X20;X21;X22;X23;X24;X25;X26]` 144);;
