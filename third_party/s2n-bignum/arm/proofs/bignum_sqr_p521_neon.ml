(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squaring modulo p_521, the field characteristic for the NIST P-521 curve. *)
(* ========================================================================= *)

needs "arm/proofs/bignum_sqr_p521.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to the core parts of
   bignum_sqr_p521 and bignum_sqr_p521_neon. This is a vectorized
   version of core of bignum_sqr_p521 but instructions are unscheduled. *)

let bignum_sqr_p521_interm1_ops:int list = [
  0xa9404c34; (* ldp	x20, x19, [x1] *)
  0x3dc00037; (* ldr	q23, [x1] *)
  0x3dc00021; (* ldr	q1, [x1] *)
  0x3dc00030; (* ldr	q16, [x1] *)
  0xa941302e; (* ldp	x14, x12, [x1, #16] *)
  0x3dc0043c; (* ldr	q28, [x1, #16] *)
  0x3dc0043f; (* ldr	q31, [x1, #16] *)
  0xa9420829; (* ldp	x9, x2, [x1, #32] *)
  0x3dc0083d; (* ldr	q29, [x1, #32] *)
  0x3dc00824; (* ldr	q4, [x1, #32] *)
  0x3dc00025; (* ldr	q5, [x1] *)
  0x3dc00822; (* ldr	q2, [x1, #32] *)
  0xa9433426; (* ldp	x6, x13, [x1, #48] *)
  0x3dc00c38; (* ldr	q24, [x1, #48] *)
  0x3dc00c3b; (* ldr	q27, [x1, #48] *)
  0x3dc00420; (* ldr	q0, [x1, #16] *)
  0x3dc00c3e; (* ldr	q30, [x1, #48] *)
  0x9b067d31; (* mul	x17, x9, x6 *)
  0x9b0d7c4a; (* mul	x10, x2, x13 *)
  0x9bc67d38; (* umulh	x24, x9, x6 *)
  0xeb020124; (* subs	x4, x9, x2 *)
  0xda842484; (* cneg	x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23f0; (* csetm	x16, cc  // cc = lo, ul, last *)
  0xeb0601a3; (* subs	x3, x13, x6 *)
  0xda832477; (* cneg	x23, x3, cc  // cc = lo, ul, last *)
  0x9b177c83; (* mul	x3, x4, x23 *)
  0x9bd77c84; (* umulh	x4, x4, x23 *)
  0xda902216; (* cinv	x22, x16, cc  // cc = lo, ul, last *)
  0xca160077; (* eor	x23, x3, x22 *)
  0xca160090; (* eor	x16, x4, x22 *)
  0xab180223; (* adds	x3, x17, x24 *)
  0x9a1f0318; (* adc	x24, x24, xzr *)
  0x9bcd7c44; (* umulh	x4, x2, x13 *)
  0xab0a0063; (* adds	x3, x3, x10 *)
  0xba040318; (* adcs	x24, x24, x4 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab0a0318; (* adds	x24, x24, x10 *)
  0x9a1f008a; (* adc	x10, x4, xzr *)
  0xb10006df; (* cmn	x22, #0x1 *)
  0xba170064; (* adcs	x4, x3, x23 *)
  0xba100318; (* adcs	x24, x24, x16 *)
  0x9a16014a; (* adc	x10, x10, x22 *)
  0xab110228; (* adds	x8, x17, x17 *)
  0xba040096; (* adcs	x22, x4, x4 *)
  0xba180305; (* adcs	x5, x24, x24 *)
  0xba0a014b; (* adcs	x11, x10, x10 *)
  0x9a1f03f7; (* adc	x23, xzr, xzr *)
  0x6f00e5f9; (* movi	v25.2d, #0xffffffff *)
  0x4e845893; (* uzp2	v19.4s, v4.4s, v4.4s *)
  0x0ea12bba; (* xtn	v26.2s, v29.2d *)
  0x0ea12896; (* xtn	v22.2s, v4.2d *)
  0x4ea00884; (* rev64	v4.4s, v4.4s *)
  0x2eb6c347; (* umull	v7.2d, v26.2s, v22.2s *)
  0x2eb3c355; (* umull	v21.2d, v26.2s, v19.2s *)
  0x4e9d5bb1; (* uzp2	v17.4s, v29.4s, v29.4s *)
  0x4ebd9c84; (* mul	v4.4s, v4.4s, v29.4s *)
  0x6f6014f5; (* usra	v21.2d, v7.2d, #32 *)
  0x2eb3c232; (* umull	v18.2d, v17.2s, v19.2s *)
  0x6ea02884; (* uaddlp	v4.2d, v4.4s *)
  0x4e391ea7; (* and	v7.16b, v21.16b, v25.16b *)
  0x2eb68227; (* umlal	v7.2d, v17.2s, v22.2s *)
  0x4f605484; (* shl	v4.2d, v4.2d, #32 *)
  0x6f6016b2; (* usra	v18.2d, v21.2d, #32 *)
  0x2eb68344; (* umlal	v4.2d, v26.2s, v22.2s *)
  0x6f6014f2; (* usra	v18.2d, v7.2d, #32 *)
  0x4e083c8f; (* mov	x15, v4.d[0] *)
  0x4e183c90; (* mov	x16, v4.d[1] *)
  0x9b027d23; (* mul	x3, x9, x2 *)
  0x4e083e4a; (* mov	x10, v18.d[0] *)
  0x4e183e51; (* mov	x17, v18.d[1] *)
  0x9bc27d24; (* umulh	x4, x9, x2 *)
  0xab030158; (* adds	x24, x10, x3 *)
  0xba04020a; (* adcs	x10, x16, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab030307; (* adds	x7, x24, x3 *)
  0xba04014a; (* adcs	x10, x10, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab0a0108; (* adds	x8, x8, x10 *)
  0xba1102d6; (* adcs	x22, x22, x17 *)
  0xba1f00b5; (* adcs	x21, x5, xzr *)
  0xba1f0165; (* adcs	x5, x11, xzr *)
  0x9a1f02eb; (* adc	x11, x23, xzr *)
  0x6f00e5f9; (* movi	v25.2d, #0xffffffff *)
  0x4e9b5b73; (* uzp2	v19.4s, v27.4s, v27.4s *)
  0x0ea12b1a; (* xtn	v26.2s, v24.2d *)
  0x0ea12b76; (* xtn	v22.2s, v27.2d *)
  0x4ea00b64; (* rev64	v4.4s, v27.4s *)
  0x2eb6c347; (* umull	v7.2d, v26.2s, v22.2s *)
  0x2eb3c355; (* umull	v21.2d, v26.2s, v19.2s *)
  0x4e985b11; (* uzp2	v17.4s, v24.4s, v24.4s *)
  0x4eb89c84; (* mul	v4.4s, v4.4s, v24.4s *)
  0x6f6014f5; (* usra	v21.2d, v7.2d, #32 *)
  0x2eb3c232; (* umull	v18.2d, v17.2s, v19.2s *)
  0x6ea02884; (* uaddlp	v4.2d, v4.4s *)
  0x4e391ea7; (* and	v7.16b, v21.16b, v25.16b *)
  0x2eb68227; (* umlal	v7.2d, v17.2s, v22.2s *)
  0x4f605484; (* shl	v4.2d, v4.2d, #32 *)
  0x6f6016b2; (* usra	v18.2d, v21.2d, #32 *)
  0x2eb68344; (* umlal	v4.2d, v26.2s, v22.2s *)
  0x6f6014f2; (* usra	v18.2d, v7.2d, #32 *)
  0x4e083c97; (* mov	x23, v4.d[0] *)
  0x4e183c90; (* mov	x16, v4.d[1] *)
  0x9b0d7cc3; (* mul	x3, x6, x13 *)
  0x4e083e4a; (* mov	x10, v18.d[0] *)
  0x4e183e51; (* mov	x17, v18.d[1] *)
  0x9bcd7cc4; (* umulh	x4, x6, x13 *)
  0xab030158; (* adds	x24, x10, x3 *)
  0xba04020a; (* adcs	x10, x16, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab030318; (* adds	x24, x24, x3 *)
  0xba04014a; (* adcs	x10, x10, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab1502f7; (* adds	x23, x23, x21 *)
  0xba050310; (* adcs	x16, x24, x5 *)
  0xba0b0143; (* adcs	x3, x10, x11 *)
  0x9a1f0235; (* adc	x21, x17, xzr *)
  0xf9402031; (* ldr	x17, [x1, #64] *)
  0x8b110225; (* add	x5, x17, x17 *)
  0x9b117e2b; (* mul	x11, x17, x17 *)
  0x9240ce91; (* and	x17, x20, #0xfffffffffffff *)
  0x9b117ca4; (* mul	x4, x5, x17 *)
  0x93d4d271; (* extr	x17, x19, x20, #52 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374fc91; (* lsr	x17, x4, #52 *)
  0x8b110158; (* add	x24, x10, x17 *)
  0xd374cc91; (* lsl	x17, x4, #12 *)
  0x93d13311; (* extr	x17, x24, x17, #12 *)
  0xab1101ef; (* adds	x15, x15, x17 *)
  0x93d3a1d1; (* extr	x17, x14, x19, #40 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374ff11; (* lsr	x17, x24, #52 *)
  0x8b110144; (* add	x4, x10, x17 *)
  0xd374cf11; (* lsl	x17, x24, #12 *)
  0x93d16091; (* extr	x17, x4, x17, #24 *)
  0xba1100e7; (* adcs	x7, x7, x17 *)
  0x93ce7191; (* extr	x17, x12, x14, #28 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374fc91; (* lsr	x17, x4, #52 *)
  0x8b110158; (* add	x24, x10, x17 *)
  0xd374cc91; (* lsl	x17, x4, #12 *)
  0x93d19311; (* extr	x17, x24, x17, #36 *)
  0xba110108; (* adcs	x8, x8, x17 *)
  0x93cc4131; (* extr	x17, x9, x12, #16 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374ff11; (* lsr	x17, x24, #52 *)
  0x8b110144; (* add	x4, x10, x17 *)
  0xd374cf11; (* lsl	x17, x24, #12 *)
  0x93d1c091; (* extr	x17, x4, x17, #48 *)
  0xba1102d6; (* adcs	x22, x22, x17 *)
  0xd344fd31; (* lsr	x17, x9, #4 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374fc91; (* lsr	x17, x4, #52 *)
  0x8b110158; (* add	x24, x10, x17 *)
  0xd374cc91; (* lsl	x17, x4, #12 *)
  0x93d1f304; (* extr	x4, x24, x17, #60 *)
  0x93c9e051; (* extr	x17, x2, x9, #56 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374ff11; (* lsr	x17, x24, #52 *)
  0x8b110158; (* add	x24, x10, x17 *)
  0xd378dc91; (* lsl	x17, x4, #8 *)
  0x93d12311; (* extr	x17, x24, x17, #8 *)
  0xba1102f7; (* adcs	x23, x23, x17 *)
  0x93c2b0d1; (* extr	x17, x6, x2, #44 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374ff11; (* lsr	x17, x24, #52 *)
  0x8b110144; (* add	x4, x10, x17 *)
  0xd374cf11; (* lsl	x17, x24, #12 *)
  0x93d15091; (* extr	x17, x4, x17, #20 *)
  0xba110210; (* adcs	x16, x16, x17 *)
  0x93c681b1; (* extr	x17, x13, x6, #32 *)
  0x9240ce31; (* and	x17, x17, #0xfffffffffffff *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374fc91; (* lsr	x17, x4, #52 *)
  0x8b110158; (* add	x24, x10, x17 *)
  0xd374cc91; (* lsl	x17, x4, #12 *)
  0x93d18311; (* extr	x17, x24, x17, #32 *)
  0xba110063; (* adcs	x3, x3, x17 *)
  0xd354fdb1; (* lsr	x17, x13, #20 *)
  0x9b117caa; (* mul	x10, x5, x17 *)
  0xd374ff11; (* lsr	x17, x24, #52 *)
  0x8b11014a; (* add	x10, x10, x17 *)
  0xd374cf11; (* lsl	x17, x24, #12 *)
  0x93d1b151; (* extr	x17, x10, x17, #44 *)
  0xba1102a4; (* adcs	x4, x21, x17 *)
  0xd36cfd51; (* lsr	x17, x10, #44 *)
  0x9a110178; (* adc	x24, x11, x17 *)
  0x93cf24ea; (* extr	x10, x7, x15, #9 *)
  0x93c72511; (* extr	x17, x8, x7, #9 *)
  0xa900440a; (* stp	x10, x17, [x0] *)
  0x93c826ca; (* extr	x10, x22, x8, #9 *)
  0x93d626f1; (* extr	x17, x23, x22, #9 *)
  0xa901440a; (* stp	x10, x17, [x0, #16] *)
  0x93d7260a; (* extr	x10, x16, x23, #9 *)
  0x93d02471; (* extr	x17, x3, x16, #9 *)
  0xa902440a; (* stp	x10, x17, [x0, #32] *)
  0x93c3248a; (* extr	x10, x4, x3, #9 *)
  0x93c42711; (* extr	x17, x24, x4, #9 *)
  0xa903440a; (* stp	x10, x17, [x0, #48] *)
  0x924021ea; (* and	x10, x15, #0x1ff *)
  0xd349ff11; (* lsr	x17, x24, #9 *)
  0x8b110151; (* add	x17, x10, x17 *)
  0xf9002011; (* str	x17, [x0, #64] *)
  0x4e971b91; (* uzp1	v17.4s, v28.4s, v23.4s *)
  0x4ea00b84; (* rev64	v4.4s, v28.4s *)
  0x4e971ae7; (* uzp1	v7.4s, v23.4s, v23.4s *)
  0x4eb79c84; (* mul	v4.4s, v4.4s, v23.4s *)
  0x6ea02884; (* uaddlp	v4.2d, v4.4s *)
  0x4f605484; (* shl	v4.2d, v4.2d, #32 *)
  0x2eb180e4; (* umlal	v4.2d, v7.2s, v17.2s *)
  0x4e083c88; (* mov	x8, v4.d[0] *)
  0x4e183c96; (* mov	x22, v4.d[1] *)
  0x9bce7e97; (* umulh	x23, x20, x14 *)
  0xeb130291; (* subs	x17, x20, x19 *)
  0xda912624; (* cneg	x4, x17, cc  // cc = lo, ul, last *)
  0xda9f23f8; (* csetm	x24, cc  // cc = lo, ul, last *)
  0xeb0e0191; (* subs	x17, x12, x14 *)
  0xda912631; (* cneg	x17, x17, cc  // cc = lo, ul, last *)
  0x9b117c8a; (* mul	x10, x4, x17 *)
  0x9bd17c91; (* umulh	x17, x4, x17 *)
  0xda982310; (* cinv	x16, x24, cc  // cc = lo, ul, last *)
  0xca100143; (* eor	x3, x10, x16 *)
  0xca100224; (* eor	x4, x17, x16 *)
  0xab170118; (* adds	x24, x8, x23 *)
  0x9a1f02ea; (* adc	x10, x23, xzr *)
  0x9bcc7e71; (* umulh	x17, x19, x12 *)
  0xab160318; (* adds	x24, x24, x22 *)
  0xba11014a; (* adcs	x10, x10, x17 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab16014a; (* adds	x10, x10, x22 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xb100061f; (* cmn	x16, #0x1 *)
  0xba030318; (* adcs	x24, x24, x3 *)
  0xba04014a; (* adcs	x10, x10, x4 *)
  0x9a100231; (* adc	x17, x17, x16 *)
  0xab08010f; (* adds	x15, x8, x8 *)
  0xba180307; (* adcs	x7, x24, x24 *)
  0xba0a0148; (* adcs	x8, x10, x10 *)
  0xba110236; (* adcs	x22, x17, x17 *)
  0x9a1f03f7; (* adc	x23, xzr, xzr *)
  0x6f00e5f9; (* movi	v25.2d, #0xffffffff *)
  0x4e905a13; (* uzp2	v19.4s, v16.4s, v16.4s *)
  0x0ea1283a; (* xtn	v26.2s, v1.2d *)
  0x0ea12a16; (* xtn	v22.2s, v16.2d *)
  0x4ea00a04; (* rev64	v4.4s, v16.4s *)
  0x2eb6c347; (* umull	v7.2d, v26.2s, v22.2s *)
  0x2eb3c355; (* umull	v21.2d, v26.2s, v19.2s *)
  0x4e815831; (* uzp2	v17.4s, v1.4s, v1.4s *)
  0x4ea19c84; (* mul	v4.4s, v4.4s, v1.4s *)
  0x6f6014f5; (* usra	v21.2d, v7.2d, #32 *)
  0x2eb3c232; (* umull	v18.2d, v17.2s, v19.2s *)
  0x6ea02884; (* uaddlp	v4.2d, v4.4s *)
  0x4e391ea7; (* and	v7.16b, v21.16b, v25.16b *)
  0x2eb68227; (* umlal	v7.2d, v17.2s, v22.2s *)
  0x4f605484; (* shl	v4.2d, v4.2d, #32 *)
  0x6f6016b2; (* usra	v18.2d, v21.2d, #32 *)
  0x2eb68344; (* umlal	v4.2d, v26.2s, v22.2s *)
  0x6f6014f2; (* usra	v18.2d, v7.2d, #32 *)
  0x4e083c95; (* mov	x21, v4.d[0] *)
  0x4e183c90; (* mov	x16, v4.d[1] *)
  0x9b137e83; (* mul	x3, x20, x19 *)
  0x4e083e4a; (* mov	x10, v18.d[0] *)
  0x4e183e51; (* mov	x17, v18.d[1] *)
  0x9bd37e84; (* umulh	x4, x20, x19 *)
  0xab030158; (* adds	x24, x10, x3 *)
  0xba04020a; (* adcs	x10, x16, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab030305; (* adds	x5, x24, x3 *)
  0xba04014a; (* adcs	x10, x10, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab0a01eb; (* adds	x11, x15, x10 *)
  0xba1100ef; (* adcs	x15, x7, x17 *)
  0xba1f0107; (* adcs	x7, x8, xzr *)
  0xba1f02c8; (* adcs	x8, x22, xzr *)
  0x9a1f02f6; (* adc	x22, x23, xzr *)
  0x0ea12be7; (* xtn	v7.2s, v31.2d *)
  0x0f2087e4; (* shrn	v4.2s, v31.2d, #32 *)
  0x2ea4c0e4; (* umull	v4.2d, v7.2s, v4.2s *)
  0x4f615484; (* shl	v4.2d, v4.2d, #33 *)
  0x2ea780e4; (* umlal	v4.2d, v7.2s, v7.2s *)
  0x4e083c97; (* mov	x23, v4.d[0] *)
  0x4e183c90; (* mov	x16, v4.d[1] *)
  0x9b0c7dc3; (* mul	x3, x14, x12 *)
  0x9bce7dca; (* umulh	x10, x14, x14 *)
  0x9bcc7d91; (* umulh	x17, x12, x12 *)
  0x9bcc7dc4; (* umulh	x4, x14, x12 *)
  0xab030158; (* adds	x24, x10, x3 *)
  0xba04020a; (* adcs	x10, x16, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab030318; (* adds	x24, x24, x3 *)
  0xba04014a; (* adcs	x10, x10, x4 *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab0702f0; (* adds	x16, x23, x7 *)
  0xba080303; (* adcs	x3, x24, x8 *)
  0xba160144; (* adcs	x4, x10, x22 *)
  0x9a1f0238; (* adc	x24, x17, xzr *)
  0xa940440a; (* ldp	x10, x17, [x0] *)
  0xab15014a; (* adds	x10, x10, x21 *)
  0xba050231; (* adcs	x17, x17, x5 *)
  0xa900440a; (* stp	x10, x17, [x0] *)
  0xa941440a; (* ldp	x10, x17, [x0, #16] *)
  0xba0b014a; (* adcs	x10, x10, x11 *)
  0xba0f0231; (* adcs	x17, x17, x15 *)
  0xa901440a; (* stp	x10, x17, [x0, #16] *)
  0xa942440a; (* ldp	x10, x17, [x0, #32] *)
  0xba10014a; (* adcs	x10, x10, x16 *)
  0xba030231; (* adcs	x17, x17, x3 *)
  0xa902440a; (* stp	x10, x17, [x0, #32] *)
  0xa943440a; (* ldp	x10, x17, [x0, #48] *)
  0xba04014a; (* adcs	x10, x10, x4 *)
  0xba180231; (* adcs	x17, x17, x24 *)
  0xa903440a; (* stp	x10, x17, [x0, #48] *)
  0xf9402011; (* ldr	x17, [x0, #64] *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xf9002011; (* str	x17, [x0, #64] *)
  0x6f00e5f9; (* movi	v25.2d, #0xffffffff *)
  0x4e825853; (* uzp2	v19.4s, v2.4s, v2.4s *)
  0x0ea128ba; (* xtn	v26.2s, v5.2d *)
  0x0ea12856; (* xtn	v22.2s, v2.2d *)
  0x4ea00844; (* rev64	v4.4s, v2.4s *)
  0x2eb6c347; (* umull	v7.2d, v26.2s, v22.2s *)
  0x2eb3c355; (* umull	v21.2d, v26.2s, v19.2s *)
  0x4e8558b1; (* uzp2	v17.4s, v5.4s, v5.4s *)
  0x4ea59c84; (* mul	v4.4s, v4.4s, v5.4s *)
  0x6f6014f5; (* usra	v21.2d, v7.2d, #32 *)
  0x2eb3c232; (* umull	v18.2d, v17.2s, v19.2s *)
  0x6ea02884; (* uaddlp	v4.2d, v4.4s *)
  0x4e391ea7; (* and	v7.16b, v21.16b, v25.16b *)
  0x2eb68227; (* umlal	v7.2d, v17.2s, v22.2s *)
  0x4f605484; (* shl	v4.2d, v4.2d, #32 *)
  0x6f6016b2; (* usra	v18.2d, v21.2d, #32 *)
  0x2eb68344; (* umlal	v4.2d, v26.2s, v22.2s *)
  0x6f6014f2; (* usra	v18.2d, v7.2d, #32 *)
  0x4e083c85; (* mov	x5, v4.d[0] *)
  0x4e183c84; (* mov	x4, v4.d[1] *)
  0x6f00e5f9; (* movi	v25.2d, #0xffffffff *)
  0x4e9e5bd1; (* uzp2	v17.4s, v30.4s, v30.4s *)
  0x0ea12813; (* xtn	v19.2s, v0.2d *)
  0x0ea12bda; (* xtn	v26.2s, v30.2d *)
  0x4ea00bc4; (* rev64	v4.4s, v30.4s *)
  0x2ebac267; (* umull	v7.2d, v19.2s, v26.2s *)
  0x2eb1c276; (* umull	v22.2d, v19.2s, v17.2s *)
  0x4e805815; (* uzp2	v21.4s, v0.4s, v0.4s *)
  0x4ea09c84; (* mul	v4.4s, v4.4s, v0.4s *)
  0x6f6014f6; (* usra	v22.2d, v7.2d, #32 *)
  0x2eb1c2b1; (* umull	v17.2d, v21.2s, v17.2s *)
  0x6ea02884; (* uaddlp	v4.2d, v4.4s *)
  0x4e391ec7; (* and	v7.16b, v22.16b, v25.16b *)
  0x2eba82a7; (* umlal	v7.2d, v21.2s, v26.2s *)
  0x4f605484; (* shl	v4.2d, v4.2d, #32 *)
  0x6f6016d1; (* usra	v17.2d, v22.2d, #32 *)
  0x2eba8264; (* umlal	v4.2d, v19.2s, v26.2s *)
  0x6f6014f1; (* usra	v17.2d, v7.2d, #32 *)
  0x4e083c98; (* mov	x24, v4.d[0] *)
  0x4e183c8a; (* mov	x10, v4.d[1] *)
  0x4e083e51; (* mov	x17, v18.d[0] *)
  0xab110084; (* adds	x4, x4, x17 *)
  0x4e183e51; (* mov	x17, v18.d[1] *)
  0xba110318; (* adcs	x24, x24, x17 *)
  0x4e083e31; (* mov	x17, v17.d[0] *)
  0xba11014a; (* adcs	x10, x10, x17 *)
  0x4e183e31; (* mov	x17, v17.d[1] *)
  0x9a1f0231; (* adc	x17, x17, xzr *)
  0xab05008f; (* adds	x15, x4, x5 *)
  0xba040304; (* adcs	x4, x24, x4 *)
  0xba180158; (* adcs	x24, x10, x24 *)
  0xba0a022a; (* adcs	x10, x17, x10 *)
  0x9a1103f1; (* adc	x17, xzr, x17 *)
  0xab050087; (* adds	x7, x4, x5 *)
  0xba0f0308; (* adcs	x8, x24, x15 *)
  0xba040156; (* adcs	x22, x10, x4 *)
  0xba180237; (* adcs	x23, x17, x24 *)
  0xba0a03f0; (* adcs	x16, xzr, x10 *)
  0x9a1103e3; (* adc	x3, xzr, x17 *)
  0xeb0c01d1; (* subs	x17, x14, x12 *)
  0xda912638; (* cneg	x24, x17, cc  // cc = lo, ul, last *)
  0xda9f23e4; (* csetm	x4, cc  // cc = lo, ul, last *)
  0xeb0601b1; (* subs	x17, x13, x6 *)
  0xda91262a; (* cneg	x10, x17, cc  // cc = lo, ul, last *)
  0x9b0a7f11; (* mul	x17, x24, x10 *)
  0x9bca7f18; (* umulh	x24, x24, x10 *)
  0xda84208a; (* cinv	x10, x4, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn	x10, #0x1 *)
  0xca0a0231; (* eor	x17, x17, x10 *)
  0xba1102f7; (* adcs	x23, x23, x17 *)
  0xca0a0311; (* eor	x17, x24, x10 *)
  0xba110210; (* adcs	x16, x16, x17 *)
  0x9a0a0063; (* adc	x3, x3, x10 *)
  0xeb130291; (* subs	x17, x20, x19 *)
  0xda912638; (* cneg	x24, x17, cc  // cc = lo, ul, last *)
  0xda9f23e4; (* csetm	x4, cc  // cc = lo, ul, last *)
  0xeb090051; (* subs	x17, x2, x9 *)
  0xda91262a; (* cneg	x10, x17, cc  // cc = lo, ul, last *)
  0x9b0a7f11; (* mul	x17, x24, x10 *)
  0x9bca7f18; (* umulh	x24, x24, x10 *)
  0xda84208a; (* cinv	x10, x4, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn	x10, #0x1 *)
  0xca0a0231; (* eor	x17, x17, x10 *)
  0xba1101eb; (* adcs	x11, x15, x17 *)
  0xca0a0311; (* eor	x17, x24, x10 *)
  0xba1100ef; (* adcs	x15, x7, x17 *)
  0xba0a0107; (* adcs	x7, x8, x10 *)
  0xba0a02d6; (* adcs	x22, x22, x10 *)
  0xba0a02f7; (* adcs	x23, x23, x10 *)
  0xba0a0210; (* adcs	x16, x16, x10 *)
  0x9a0a0063; (* adc	x3, x3, x10 *)
  0xeb0c0271; (* subs	x17, x19, x12 *)
  0xda912638; (* cneg	x24, x17, cc  // cc = lo, ul, last *)
  0xda9f23e4; (* csetm	x4, cc  // cc = lo, ul, last *)
  0xeb0201b1; (* subs	x17, x13, x2 *)
  0xda91262a; (* cneg	x10, x17, cc  // cc = lo, ul, last *)
  0x9b0a7f11; (* mul	x17, x24, x10 *)
  0x9bca7f18; (* umulh	x24, x24, x10 *)
  0xda84208a; (* cinv	x10, x4, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn	x10, #0x1 *)
  0xca0a0231; (* eor	x17, x17, x10 *)
  0xba1102c8; (* adcs	x8, x22, x17 *)
  0xca0a0311; (* eor	x17, x24, x10 *)
  0xba1102f7; (* adcs	x23, x23, x17 *)
  0xba0a0210; (* adcs	x16, x16, x10 *)
  0x9a0a0063; (* adc	x3, x3, x10 *)
  0xeb0e0291; (* subs	x17, x20, x14 *)
  0xda912638; (* cneg	x24, x17, cc  // cc = lo, ul, last *)
  0xda9f23e4; (* csetm	x4, cc  // cc = lo, ul, last *)
  0xeb0900d1; (* subs	x17, x6, x9 *)
  0xda91262a; (* cneg	x10, x17, cc  // cc = lo, ul, last *)
  0x9b0a7f11; (* mul	x17, x24, x10 *)
  0x9bca7f18; (* umulh	x24, x24, x10 *)
  0xda84208a; (* cinv	x10, x4, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn	x10, #0x1 *)
  0xca0a0231; (* eor	x17, x17, x10 *)
  0xba1101f6; (* adcs	x22, x15, x17 *)
  0xca0a0311; (* eor	x17, x24, x10 *)
  0xba1100e4; (* adcs	x4, x7, x17 *)
  0xba0a0118; (* adcs	x24, x8, x10 *)
  0xba0a02f7; (* adcs	x23, x23, x10 *)
  0xba0a0210; (* adcs	x16, x16, x10 *)
  0x9a0a0063; (* adc	x3, x3, x10 *)
  0xeb0c028c; (* subs	x12, x20, x12 *)
  0xda8c258a; (* cneg	x10, x12, cc  // cc = lo, ul, last *)
  0xda9f23f1; (* csetm	x17, cc  // cc = lo, ul, last *)
  0xeb0901ac; (* subs	x12, x13, x9 *)
  0xda8c2589; (* cneg	x9, x12, cc  // cc = lo, ul, last *)
  0x9b097d4c; (* mul	x12, x10, x9 *)
  0x9bc97d4d; (* umulh	x13, x10, x9 *)
  0xda912229; (* cinv	x9, x17, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn	x9, #0x1 *)
  0xca09018c; (* eor	x12, x12, x9 *)
  0xba0c0084; (* adcs	x4, x4, x12 *)
  0xca0901ac; (* eor	x12, x13, x9 *)
  0xba0c0318; (* adcs	x24, x24, x12 *)
  0xba0902ea; (* adcs	x10, x23, x9 *)
  0xba090211; (* adcs	x17, x16, x9 *)
  0x9a09006d; (* adc	x13, x3, x9 *)
  0xeb0e0273; (* subs	x19, x19, x14 *)
  0xda93266c; (* cneg	x12, x19, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm	x9, cc  // cc = lo, ul, last *)
  0xeb0200c6; (* subs	x6, x6, x2 *)
  0xda8624ce; (* cneg	x14, x6, cc  // cc = lo, ul, last *)
  0x9b0e7d93; (* mul	x19, x12, x14 *)
  0x9bce7d8c; (* umulh	x12, x12, x14 *)
  0xda89212e; (* cinv	x14, x9, cc  // cc = lo, ul, last *)
  0xb10005df; (* cmn	x14, #0x1 *)
  0xca0e0273; (* eor	x19, x19, x14 *)
  0xba130097; (* adcs	x23, x4, x19 *)
  0xca0e0193; (* eor	x19, x12, x14 *)
  0xba130310; (* adcs	x16, x24, x19 *)
  0xba0e0146; (* adcs	x6, x10, x14 *)
  0xba0e0222; (* adcs	x2, x17, x14 *)
  0x9a0e01a9; (* adc	x9, x13, x14 *)
  0xa940380c; (* ldp	x12, x14, [x0] *)
  0x93d020d3; (* extr	x19, x6, x16, #8 *)
  0xab0c026a; (* adds	x10, x19, x12 *)
  0x93c62053; (* extr	x19, x2, x6, #8 *)
  0xba0e0271; (* adcs	x17, x19, x14 *)
  0xa941300e; (* ldp	x14, x12, [x0, #16] *)
  0x93c22133; (* extr	x19, x9, x2, #8 *)
  0xba0e026d; (* adcs	x13, x19, x14 *)
  0x8a0d022e; (* and	x14, x17, x13 *)
  0xd348fd33; (* lsr	x19, x9, #8 *)
  0xba0c0266; (* adcs	x6, x19, x12 *)
  0x8a0601c9; (* and	x9, x14, x6 *)
  0xa942300e; (* ldp	x14, x12, [x0, #32] *)
  0xd37ff8b3; (* lsl	x19, x5, #1 *)
  0xba0e0262; (* adcs	x2, x19, x14 *)
  0x8a02012e; (* and	x14, x9, x2 *)
  0x93c5fd73; (* extr	x19, x11, x5, #63 *)
  0xba0c0263; (* adcs	x3, x19, x12 *)
  0x8a0301c9; (* and	x9, x14, x3 *)
  0xa943300e; (* ldp	x14, x12, [x0, #48] *)
  0x93cbfed3; (* extr	x19, x22, x11, #63 *)
  0xba0e0264; (* adcs	x4, x19, x14 *)
  0x8a04012e; (* and	x14, x9, x4 *)
  0x93d6fef3; (* extr	x19, x23, x22, #63 *)
  0xba0c0278; (* adcs	x24, x19, x12 *)
  0x8a1801cc; (* and	x12, x14, x24 *)
  0xf940200e; (* ldr	x14, [x0, #64] *)
  0x93d7fe13; (* extr	x19, x16, x23, #63 *)
  0x92402273; (* and	x19, x19, #0x1ff *)
  0x9a1301d3; (* adc	x19, x14, x19 *)
  0xd349fe6e; (* lsr	x14, x19, #9 *)
  0xb277da73; (* orr	x19, x19, #0xfffffffffffffe00 *)
  0xeb1f03ff; (* cmp	xzr, xzr *)
  0xba0e015f; (* adcs	xzr, x10, x14 *)
  0xba1f019f; (* adcs	xzr, x12, xzr *)
  0xba1f027f; (* adcs	xzr, x19, xzr *)
  0xba0e014a; (* adcs	x10, x10, x14 *)
  0xba1f0231; (* adcs	x17, x17, xzr *)
  0xba1f01ad; (* adcs	x13, x13, xzr *)
  0xba1f00c6; (* adcs	x6, x6, xzr *)
  0xba1f0042; (* adcs	x2, x2, xzr *)
  0xba1f0069; (* adcs	x9, x3, xzr *)
  0xba1f008c; (* adcs	x12, x4, xzr *)
  0xba1f030e; (* adcs	x14, x24, xzr *)
  0x9a1f0273; (* adc	x19, x19, xzr *)
  0x92402273; (* and	x19, x19, #0x1ff *)
  0xa900440a; (* stp	x10, x17, [x0] *)
  0xa901180d; (* stp	x13, x6, [x0, #16] *)
  0xa9022402; (* stp	x2, x9, [x0, #32] *)
  0xa903380c; (* stp	x12, x14, [x0, #48] *)
  0xf9002013; (* str	x19, [x0, #64] *)
];;

let bignum_sqr_p521_interm1_core_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_sqr_p521_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_sqr_p521_interm1_core_mc" (term_of_bytes byte_list);;

let BIGNUM_SQR_P521_INTERM1_CORE_EXEC =
  ARM_MK_EXEC_RULE bignum_sqr_p521_interm1_core_mc;;

let sqr_p521_eqin = new_definition
  `!s1 s1' x z.
    (sqr_p521_eqin:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
    (C_ARGUMENTS [z; x] s1 /\
     C_ARGUMENTS [z; x] s1' /\
     ?a. bignum_from_memory (x,9) s1 = a /\
         bignum_from_memory (x,9) s1' = a)`;;

let sqr_p521_eqout = new_definition
  `!s1 s1' z.
    (sqr_p521_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,9) s1 = a /\
      bignum_from_memory (z,9) s1' = a)`;;

let actions = [
  ("equal", 0, 1, 0, 1); ("insert", 1, 1, 1, 4);
  ("equal", 1, 2, 4, 5); ("insert", 2, 2, 5, 7);
  ("equal", 2, 3, 7, 8); ("insert", 3, 3, 8, 12);
  ("equal", 3, 4, 12, 13); ("insert", 4, 4, 13, 17); ("equal", 4, 34, 17, 47);
  ("delete", 34, 36, 47, 47); ("insert", 36, 36, 47, 67);
  ("equal", 36, 37, 67, 68); ("delete", 37, 39, 68, 68);
  ("insert", 39, 39, 68, 70); ("equal", 39, 51, 70, 82);
  ("delete", 51, 53, 82, 82); ("insert", 53, 53, 82, 102);
  ("equal", 53, 54, 102, 103); ("delete", 54, 56, 103, 103);
  ("insert", 56, 56, 103, 105); ("equal", 56, 160, 105, 209);
  ("delete", 160, 162, 209, 209); ("insert", 162, 162, 209, 218);
  ("equal", 162, 190, 218, 246); ("delete", 190, 192, 246, 246);
  ("insert", 192, 192, 246, 266); ("equal", 192, 193, 266, 267);
  ("delete", 193, 195, 267, 267); ("insert", 195, 195, 267, 269);
  ("equal", 195, 207, 269, 281); ("delete", 207, 209, 281, 281);
  ("insert", 209, 209, 281, 288); ("equal", 209, 242, 288, 321);
  ("delete", 242, 247, 321, 321); ("insert", 247, 247, 321, 362);
  ("equal", 247, 248, 362, 363); ("delete", 248, 249, 363, 363);
  ("insert", 249, 249, 363, 364); ("equal", 249, 250, 364, 365);
  ("delete", 250, 251, 365, 365); ("insert", 251, 251, 365, 366);
  ("equal", 251, 252, 366, 367); ("delete", 252, 253, 367, 367);
  ("insert", 253, 253, 367, 368); ("equal", 253, 412, 368, 527)
];;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_sqr_p521_core_mc);
        (word pc2,LENGTH bignum_sqr_p521_interm1_core_mc)]`
    sqr_p521_eqin
    sqr_p521_eqout
    bignum_sqr_p521_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_sqr_p521_interm1_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
                       WORD_SQR64_HI; WORD_SQR128_DIGIT0]]
  @ (!extra_word_CONV);;

let BIGNUM_SQR_P521_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_SQR_P521_CORE_EXEC;
    fst BIGNUM_SQR_P521_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC sqr_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_SQR_P521_CORE_EXEC
    BIGNUM_SQR_P521_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[sqr_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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

let bignum_sqr_p521_neon_mc =
  define_from_elf "bignum_sqr_p521_neon_mc"
    "arm/p521/bignum_sqr_p521_neon.o";;

let BIGNUM_SQR_P521_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_sqr_p521_neon_mc;;

let bignum_sqr_p521_neon_core_mc_def,
    bignum_sqr_p521_neon_core_mc,
    BIGNUM_SQR_P521_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_sqr_p521_neon_core_mc"
    bignum_sqr_p521_neon_mc
    (`12`,`LENGTH bignum_sqr_p521_neon_mc - 28`)
    (fst BIGNUM_SQR_P521_NEON_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_sqr_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_sqr_p521_neon_core_mc)]`
    sqr_p521_eqin
    sqr_p521_eqout
    bignum_sqr_p521_interm1_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_sqr_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;


(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws. *)

let inst_map = [10;8;9;14;13;52;68;15;21;49;56;85;23;50;51;20;87;54;22;59;53;18;91;90;62;84;19;64;57;31;93;86;48;32;33;55;89;24;60;88;25;83;58;61;26;28;94;29;34;27;3;63;35;97;36;37;92;38;39;99;71;40;65;117;30;106;101;102;41;98;95;42;43;7;44;96;69;119;2;100;118;45;4;67;46;70;47;72;6;249;73;74;75;282;251;76;1;105;250;77;78;248;211;103;255;283;79;104;120;253;12;80;17;252;81;16;247;82;107;210;254;108;121;284;11;109;110;122;257;111;123;5;256;112;113;124;285;127;125;326;258;126;114;130;66;128;131;261;259;132;262;115;138;260;325;263;322;133;139;323;134;140;135;324;136;116;286;129;143;137;213;206;141;232;329;194;142;330;144;146;212;145;147;327;195;148;196;151;154;214;155;328;156;161;149;162;150;152;163;157;331;158;215;153;169;159;164;160;170;216;165;177;171;343;166;346;178;167;179;174;168;172;185;173;186;180;175;182;181;176;183;219;184;264;189;200;187;349;188;201;197;334;192;190;198;345;217;202;333;199;270;191;193;220;344;222;203;218;221;223;350;224;227;336;348;204;230;225;347;231;233;353;207;234;268;235;226;236;338;352;205;208;237;351;267;228;238;269;332;239;229;335;342;240;337;290;241;242;356;209;243;354;357;244;266;245;355;246;271;289;358;339;292;272;359;273;274;275;276;277;291;278;279;288;280;281;293;294;303;287;295;296;297;298;299;265;300;307;301;302;304;341;311;305;319;362;308;306;309;315;312;313;314;316;361;317;318;320;381;364;382;383;384;360;385;388;366;363;386;368;365;367;369;387;310;340;395;396;321;397;398;399;402;370;401;371;372;390;373;400;406;374;375;392;376;377;378;404;379;380;389;391;393;394;413;415;414;416;420;417;403;405;418;407;408;419;409;410;411;422;412;428;429;430;445;446;447;431;435;432;421;424;423;433;425;434;426;427;448;449;452;461;450;462;463;439;464;451;437;468;465;436;438;456;440;441;454;442;466;443;444;453;455;467;457;472;497;458;493;477;459;470;460;469;482;471;500;473;504;490;474;478;489;475;476;479;480;496;483;481;503;486;484;505;485;487;491;488;494;492;498;495;499;501;506;509;508;507;510;502;511;512;513;514;515;523;516;517;524;518;525;519;520;526;521;522;527];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_SQR_P521_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_SQR_P521_INTERM1_CORE_EXEC;
    fst BIGNUM_SQR_P521_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC sqr_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_SQR_P521_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_SQR_P521_NEON_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[sqr_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_sqr_p521_core_mc);
        (word pc2,LENGTH bignum_sqr_p521_neon_core_mc)]`
    sqr_p521_eqin
    sqr_p521_eqout
    bignum_sqr_p521_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_sqr_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

let sqr_p521_eqout_TRANS = prove(
  `!s s2 s'
    z. sqr_p521_eqout (s,s') z /\ sqr_p521_eqout (s',s2) z
    ==> sqr_p521_eqout (s,s2) z`,
  MESON_TAC[sqr_p521_eqout]);;

let BIGNUM_SQR_P521_CORE_EQUIV = time prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc:int64,LENGTH bignum_sqr_p521_core_mc);
        (word pc3:int64,LENGTH bignum_sqr_p521_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc3:int64,LENGTH bignum_sqr_p521_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_sqr_p521_neon_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_sqr_p521_interm1_core_mc))
        [x,8 * 9] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_SQR_P521_INTERM1_CORE_EXEC;
       fst BIGNUM_SQR_P521_NEON_CORE_EXEC;
       GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_SQR_P521_CORE_EQUIV1,BIGNUM_SQR_P521_CORE_EQUIV2)
    (sqr_p521_eqin,sqr_p521_eqout_TRANS)
    (BIGNUM_SQR_P521_CORE_EXEC,BIGNUM_SQR_P521_INTERM1_CORE_EXEC,BIGNUM_SQR_P521_NEON_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_SQR_P521_NEON_SUBROUTINE_CORRECT
          from BIGNUM_SQR_P521_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_SQR_P384_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64,
        LENGTH (APPEND bignum_sqr_p521_core_mc barrier_inst_bytes))
      (z:int64,8 * 9)`
    [`z:int64`;`x:int64`] bignum_sqr_p521_core_mc
    `\s0. C_ARGUMENTS [z;x] s0`;;

let BIGNUM_SQR_P521_EVENTUALLY_N_AT_PC = time prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_SQR_P521_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_sqr_p521_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              fst BIGNUM_SQR_P521_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_SQR_P521_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_SQR_P521_CORE_EXEC);;


let BIGNUM_SQR_P521_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_SQR_P521_EXEC
    BIGNUM_SQR_P521_CORE_EXEC
    BIGNUM_SQR_P521_CORE_CORRECT
    BIGNUM_SQR_P521_EVENTUALLY_N_AT_PC;;

(* This theorem is a copy of BIGNUM_SQR_P521_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - bignum_sqr_p521_core_mc with bignum_sqr_p521_neon_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)

let BIGNUM_SQR_P521_NEON_CORE_CORRECT = time prove
 (`!z x n pc2.
        nonoverlapping (word pc2,LENGTH bignum_sqr_p521_neon_core_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_sqr_p521_neon_core_mc /\
                  read PC s = word(pc2) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc2 + LENGTH bignum_sqr_p521_neon_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = n EXP 2 MOD p_521))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                      X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program. This is going to be used
     for preparing an initial state by 'overwriting' bignum_montsqr_p384_mc
     at pc. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_sqr_p521_core_mc barrier_inst_bytes)) (z:int64,8 * 9) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_sqr_p521_core_mc barrier_inst_bytes)) (x:int64,8 * 9) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_SQR_P521_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_SQR_P521_CORE_EQUIV BIGNUM_SQR_P521_CORE_CORRECT_N
    (BIGNUM_SQR_P521_CORE_EXEC,BIGNUM_SQR_P521_NEON_CORE_EXEC)
    (sqr_p521_eqin,sqr_p521_eqout));;

let BIGNUM_SQR_P521_NEON_CORRECT = time prove
   (`!z x n pc.
        nonoverlapping (word pc,LENGTH bignum_sqr_p521_neon_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p521_neon_mc /\
                  read PC s = word(pc + 12) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 12 + LENGTH bignum_sqr_p521_neon_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = n EXP 2 MOD p_521))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                      X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,

  ARM_SUB_LIST_OF_MC_TAC
    BIGNUM_SQR_P521_NEON_CORE_CORRECT
    bignum_sqr_p521_neon_core_mc_def
    [fst BIGNUM_SQR_P521_NEON_CORE_EXEC;
     fst BIGNUM_SQR_P521_NEON_EXEC]);;

let BIGNUM_SQR_P521_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),48) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 9); (word_sub stackpointer (word 48),48)]
       [(word pc,LENGTH bignum_sqr_p521_neon_mc); (x,8 * 9)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p521_neon_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = returnaddress /\
                (n < p_521
                 ==> bignum_from_memory (z,9) s = n EXP 2 MOD p_521))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)
    (REWRITE_RULE [fst BIGNUM_SQR_P521_NEON_CORE_EXEC;
                   fst BIGNUM_SQR_P521_NEON_EXEC]
     BIGNUM_SQR_P521_NEON_CORRECT) in
  REWRITE_TAC[fst BIGNUM_SQR_P521_NEON_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_SQR_P521_NEON_EXEC th
   `[X19;X20;X21;X22;X23;X24]` 48);;
