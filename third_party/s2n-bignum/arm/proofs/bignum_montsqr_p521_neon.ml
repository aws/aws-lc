(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-unscheduled program
******************************************************************************)

needs "arm/proofs/bignum_montsqr_p521.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to both
   bignum_montsqr_p521 and bignum_montsqr_p521_neon. This is a vectorized
   version of bignum_montsqr_p521 but instructions are unscheduled. *)

let bignum_montsqr_p521_interm1_ops:int list = [
  0xa9402030; (* ldp	x16, x8, [x1] *)
  0x3dc00032; (* ldr	q18, [x1] *)
  0x3dc00025; (* ldr	q5, [x1] *)
  0x3dc00034; (* ldr	q20, [x1] *)
  0xa9413431; (* ldp	x17, x13, [x1, #16] *)
  0x3dc00431; (* ldr	q17, [x1, #16] *)
  0x3dc00421; (* ldr	q1, [x1, #16] *)
  0x3dc0043c; (* ldr	q28, [x1, #16] *)
  0xa9423c29; (* ldp	x9, x15, [x1, #32] *)
  0x3dc0003b; (* ldr	q27, [x1] *)
  0x3dc0083d; (* ldr	q29, [x1, #32] *)
  0xa9430837; (* ldp	x23, x2, [x1, #48] *)
  0x3dc00c26; (* ldr	q6, [x1, #48] *)
  0x3dc00c24; (* ldr	q4, [x1, #48] *)
  0x9b177d38; (* mul	x24, x9, x23 *)
  0x9b027deb; (* mul	x11, x15, x2 *)
  0x9bd77d34; (* umulh	x20, x9, x23 *)
  0xeb0f0124; (* subs	x4, x9, x15 *)
  0xda842496; (* cneg	x22, x4, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm	x12, cc  // cc = lo, ul, last *)
  0xeb170044; (* subs	x4, x2, x23 *)
  0xda842484; (* cneg	x4, x4, cc  // cc = lo, ul, last *)
  0x9b047ed3; (* mul	x19, x22, x4 *)
  0x9bc47ec4; (* umulh	x4, x22, x4 *)
  0xda8c2187; (* cinv	x7, x12, cc  // cc = lo, ul, last *)
  0xca07026e; (* eor	x14, x19, x7 *)
  0xca070096; (* eor	x22, x4, x7 *)
  0xab14030c; (* adds	x12, x24, x20 *)
  0x9a1f0293; (* adc	x19, x20, xzr *)
  0x9bc27de4; (* umulh	x4, x15, x2 *)
  0xab0b018c; (* adds	x12, x12, x11 *)
  0xba040273; (* adcs	x19, x19, x4 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab0b0273; (* adds	x19, x19, x11 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xb10004ff; (* cmn	x7, #0x1 *)
  0xba0e018c; (* adcs	x12, x12, x14 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0x9a070084; (* adc	x4, x4, x7 *)
  0xab18030b; (* adds	x11, x24, x24 *)
  0xba0c0194; (* adcs	x20, x12, x12 *)
  0xba13026a; (* adcs	x10, x19, x19 *)
  0xba040083; (* adcs	x3, x4, x4 *)
  0x9a1f03e5; (* adc	x5, xzr, xzr *)
  0x3dc0083e; (* ldr	q30, [x1, #32] *)
  0x2ebec3c0; (* umull	v0.2d, v30.2s, v30.2s *)
  0x6ebec3c2; (* umull2	v2.2d, v30.4s, v30.4s *)
  0x0ea12bd8; (* xtn	v24.2s, v30.2d *)
  0x4e9e5bde; (* uzp2	v30.4s, v30.4s, v30.4s *)
  0x2eb8c3de; (* umull	v30.2d, v30.2s, v24.2s *)
  0x4e083c07; (* mov	x7, v0.d[0] *)
  0x4e183c0e; (* mov	x14, v0.d[1] *)
  0x4e083c53; (* mov	x19, v2.d[0] *)
  0x4e183c56; (* mov	x22, v2.d[1] *)
  0x4e083fc4; (* mov	x4, v30.d[0] *)
  0x4e183fcc; (* mov	x12, v30.d[1] *)
  0xab0484f5; (* adds	x21, x7, x4, lsl #33 *)
  0xd35ffc84; (* lsr	x4, x4, #31 *)
  0x9a0401ce; (* adc	x14, x14, x4 *)
  0xab0c8673; (* adds	x19, x19, x12, lsl #33 *)
  0xd35ffd84; (* lsr	x4, x12, #31 *)
  0x9a0402d6; (* adc	x22, x22, x4 *)
  0x9b0f7d24; (* mul	x4, x9, x15 *)
  0x9bcf7d2c; (* umulh	x12, x9, x15 *)
  0xab0405d8; (* adds	x24, x14, x4, lsl #1 *)
  0x93c4fd84; (* extr	x4, x12, x4, #63 *)
  0xba040273; (* adcs	x19, x19, x4 *)
  0xd37ffd84; (* lsr	x4, x12, #63 *)
  0x9a0402c4; (* adc	x4, x22, x4 *)
  0xab13016b; (* adds	x11, x11, x19 *)
  0xba040294; (* adcs	x20, x20, x4 *)
  0xba1f014a; (* adcs	x10, x10, xzr *)
  0xba1f0063; (* adcs	x3, x3, xzr *)
  0x9a1f00a6; (* adc	x6, x5, xzr *)
  0x6f00e5e3; (* movi	v3.2d, #0xffffffff *)
  0x4e845890; (* uzp2	v16.4s, v4.4s, v4.4s *)
  0x0ea128d9; (* xtn	v25.2s, v6.2d *)
  0x0ea12897; (* xtn	v23.2s, v4.2d *)
  0x4ea0089e; (* rev64	v30.4s, v4.4s *)
  0x2eb7c338; (* umull	v24.2d, v25.2s, v23.2s *)
  0x2eb0c320; (* umull	v0.2d, v25.2s, v16.2s *)
  0x4e8658c2; (* uzp2	v2.4s, v6.4s, v6.4s *)
  0x4ea69fde; (* mul	v30.4s, v30.4s, v6.4s *)
  0x6f601700; (* usra	v0.2d, v24.2d, #32 *)
  0x2eb0c053; (* umull	v19.2d, v2.2s, v16.2s *)
  0x6ea02bde; (* uaddlp	v30.2d, v30.4s *)
  0x4e231c18; (* and	v24.16b, v0.16b, v3.16b *)
  0x2eb78058; (* umlal	v24.2d, v2.2s, v23.2s *)
  0x4f6057de; (* shl	v30.2d, v30.2d, #32 *)
  0x6f601413; (* usra	v19.2d, v0.2d, #32 *)
  0x2eb7833e; (* umlal	v30.2d, v25.2s, v23.2s *)
  0x6f601713; (* usra	v19.2d, v24.2d, #32 *)
  0x4e083fc5; (* mov	x5, v30.d[0] *)
  0x4e183fc7; (* mov	x7, v30.d[1] *)
  0x9b027eee; (* mul	x14, x23, x2 *)
  0x4e083e73; (* mov	x19, v19.d[0] *)
  0x4e183e64; (* mov	x4, v19.d[1] *)
  0x9bc27ef6; (* umulh	x22, x23, x2 *)
  0xab0e026c; (* adds	x12, x19, x14 *)
  0xba1600f3; (* adcs	x19, x7, x22 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab0e018c; (* adds	x12, x12, x14 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab0a00a7; (* adds	x7, x5, x10 *)
  0xba030183; (* adcs	x3, x12, x3 *)
  0xba06026e; (* adcs	x14, x19, x6 *)
  0x9a1f008a; (* adc	x10, x4, xzr *)
  0xf9402024; (* ldr	x4, [x1, #64] *)
  0x8b040086; (* add	x6, x4, x4 *)
  0x9b047c85; (* mul	x5, x4, x4 *)
  0x9240ce04; (* and	x4, x16, #0xfffffffffffff *)
  0x9b047cd6; (* mul	x22, x6, x4 *)
  0x93d0d104; (* extr	x4, x8, x16, #52 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fec4; (* lsr	x4, x22, #52 *)
  0x8b04026c; (* add	x12, x19, x4 *)
  0xd374cec4; (* lsl	x4, x22, #12 *)
  0x93c43184; (* extr	x4, x12, x4, #12 *)
  0xab0402b5; (* adds	x21, x21, x4 *)
  0x93c8a224; (* extr	x4, x17, x8, #40 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fd84; (* lsr	x4, x12, #52 *)
  0x8b040276; (* add	x22, x19, x4 *)
  0xd374cd84; (* lsl	x4, x12, #12 *)
  0x93c462c4; (* extr	x4, x22, x4, #24 *)
  0xba040318; (* adcs	x24, x24, x4 *)
  0x93d171a4; (* extr	x4, x13, x17, #28 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fec4; (* lsr	x4, x22, #52 *)
  0x8b04026c; (* add	x12, x19, x4 *)
  0xd374cec4; (* lsl	x4, x22, #12 *)
  0x93c49184; (* extr	x4, x12, x4, #36 *)
  0xba04016b; (* adcs	x11, x11, x4 *)
  0x93cd4124; (* extr	x4, x9, x13, #16 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fd84; (* lsr	x4, x12, #52 *)
  0x8b040276; (* add	x22, x19, x4 *)
  0xd374cd84; (* lsl	x4, x12, #12 *)
  0x93c4c2c4; (* extr	x4, x22, x4, #48 *)
  0xba040294; (* adcs	x20, x20, x4 *)
  0xd344fd24; (* lsr	x4, x9, #4 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fec4; (* lsr	x4, x22, #52 *)
  0x8b04026c; (* add	x12, x19, x4 *)
  0xd374cec4; (* lsl	x4, x22, #12 *)
  0x93c4f196; (* extr	x22, x12, x4, #60 *)
  0x93c9e1e4; (* extr	x4, x15, x9, #56 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fd84; (* lsr	x4, x12, #52 *)
  0x8b04026c; (* add	x12, x19, x4 *)
  0xd378dec4; (* lsl	x4, x22, #8 *)
  0x93c42184; (* extr	x4, x12, x4, #8 *)
  0xba0400e7; (* adcs	x7, x7, x4 *)
  0x93cfb2e4; (* extr	x4, x23, x15, #44 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fd84; (* lsr	x4, x12, #52 *)
  0x8b040276; (* add	x22, x19, x4 *)
  0xd374cd84; (* lsl	x4, x12, #12 *)
  0x93c452c4; (* extr	x4, x22, x4, #20 *)
  0xba040061; (* adcs	x1, x3, x4 *)
  0x93d78044; (* extr	x4, x2, x23, #32 *)
  0x9240cc84; (* and	x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fec4; (* lsr	x4, x22, #52 *)
  0x8b04026c; (* add	x12, x19, x4 *)
  0xd374cec4; (* lsl	x4, x22, #12 *)
  0x93c48184; (* extr	x4, x12, x4, #32 *)
  0xba0401ce; (* adcs	x14, x14, x4 *)
  0xd354fc44; (* lsr	x4, x2, #20 *)
  0x9b047cd3; (* mul	x19, x6, x4 *)
  0xd374fd84; (* lsr	x4, x12, #52 *)
  0x8b040273; (* add	x19, x19, x4 *)
  0xd374cd84; (* lsl	x4, x12, #12 *)
  0x93c4b264; (* extr	x4, x19, x4, #44 *)
  0xba040156; (* adcs	x22, x10, x4 *)
  0xd36cfe64; (* lsr	x4, x19, #44 *)
  0x9a0400ac; (* adc	x12, x5, x4 *)
  0x93d52713; (* extr	x19, x24, x21, #9 *)
  0x93d82564; (* extr	x4, x11, x24, #9 *)
  0xa9001013; (* stp	x19, x4, [x0] *)
  0x93cb2693; (* extr	x19, x20, x11, #9 *)
  0x93d424e4; (* extr	x4, x7, x20, #9 *)
  0xa9011013; (* stp	x19, x4, [x0, #16] *)
  0x93c72433; (* extr	x19, x1, x7, #9 *)
  0x93c125c4; (* extr	x4, x14, x1, #9 *)
  0xa9021013; (* stp	x19, x4, [x0, #32] *)
  0x93ce26d3; (* extr	x19, x22, x14, #9 *)
  0x93d62584; (* extr	x4, x12, x22, #9 *)
  0xa9031013; (* stp	x19, x4, [x0, #48] *)
  0x924022b3; (* and	x19, x21, #0x1ff *)
  0xd349fd84; (* lsr	x4, x12, #9 *)
  0x8b040264; (* add	x4, x19, x4 *)
  0xf9002004; (* str	x4, [x0, #64] *)
  0x4e921b82; (* uzp1	v2.4s, v28.4s, v18.4s *)
  0x4ea00b9e; (* rev64	v30.4s, v28.4s *)
  0x4e921a58; (* uzp1	v24.4s, v18.4s, v18.4s *)
  0x4eb29fde; (* mul	v30.4s, v30.4s, v18.4s *)
  0x6ea02bde; (* uaddlp	v30.2d, v30.4s *)
  0x4f6057de; (* shl	v30.2d, v30.2d, #32 *)
  0x2ea2831e; (* umlal	v30.2d, v24.2s, v2.2s *)
  0x4e083fcb; (* mov	x11, v30.d[0] *)
  0x4e183fd4; (* mov	x20, v30.d[1] *)
  0x9bd17e07; (* umulh	x7, x16, x17 *)
  0xeb080204; (* subs	x4, x16, x8 *)
  0xda842496; (* cneg	x22, x4, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm	x12, cc  // cc = lo, ul, last *)
  0xeb1101a4; (* subs	x4, x13, x17 *)
  0xda842484; (* cneg	x4, x4, cc  // cc = lo, ul, last *)
  0x9b047ed3; (* mul	x19, x22, x4 *)
  0x9bc47ec4; (* umulh	x4, x22, x4 *)
  0xda8c2181; (* cinv	x1, x12, cc  // cc = lo, ul, last *)
  0xca01026e; (* eor	x14, x19, x1 *)
  0xca010096; (* eor	x22, x4, x1 *)
  0xab07016c; (* adds	x12, x11, x7 *)
  0x9a1f00f3; (* adc	x19, x7, xzr *)
  0x9bcd7d04; (* umulh	x4, x8, x13 *)
  0xab14018c; (* adds	x12, x12, x20 *)
  0xba040273; (* adcs	x19, x19, x4 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab140273; (* adds	x19, x19, x20 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xb100043f; (* cmn	x1, #0x1 *)
  0xba0e018c; (* adcs	x12, x12, x14 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0x9a010084; (* adc	x4, x4, x1 *)
  0xab0b0175; (* adds	x21, x11, x11 *)
  0xba0c0198; (* adcs	x24, x12, x12 *)
  0xba13026b; (* adcs	x11, x19, x19 *)
  0xba040094; (* adcs	x20, x4, x4 *)
  0x9a1f03e7; (* adc	x7, xzr, xzr *)
  0x6f00e5e3; (* movi	v3.2d, #0xffffffff *)
  0x4e945a90; (* uzp2	v16.4s, v20.4s, v20.4s *)
  0x0ea128b9; (* xtn	v25.2s, v5.2d *)
  0x0ea12a97; (* xtn	v23.2s, v20.2d *)
  0x4ea00a9e; (* rev64	v30.4s, v20.4s *)
  0x2eb7c338; (* umull	v24.2d, v25.2s, v23.2s *)
  0x2eb0c320; (* umull	v0.2d, v25.2s, v16.2s *)
  0x4e8558a2; (* uzp2	v2.4s, v5.4s, v5.4s *)
  0x4ea59fde; (* mul	v30.4s, v30.4s, v5.4s *)
  0x6f601700; (* usra	v0.2d, v24.2d, #32 *)
  0x2eb0c053; (* umull	v19.2d, v2.2s, v16.2s *)
  0x6ea02bde; (* uaddlp	v30.2d, v30.4s *)
  0x4e231c18; (* and	v24.16b, v0.16b, v3.16b *)
  0x2eb78058; (* umlal	v24.2d, v2.2s, v23.2s *)
  0x4f6057de; (* shl	v30.2d, v30.2d, #32 *)
  0x6f601413; (* usra	v19.2d, v0.2d, #32 *)
  0x2eb7833e; (* umlal	v30.2d, v25.2s, v23.2s *)
  0x6f601713; (* usra	v19.2d, v24.2d, #32 *)
  0x4e083fca; (* mov	x10, v30.d[0] *)
  0x4e183fc1; (* mov	x1, v30.d[1] *)
  0x9b087e0e; (* mul	x14, x16, x8 *)
  0x4e083e73; (* mov	x19, v19.d[0] *)
  0x4e183e64; (* mov	x4, v19.d[1] *)
  0x9bc87e16; (* umulh	x22, x16, x8 *)
  0xab0e026c; (* adds	x12, x19, x14 *)
  0xba160033; (* adcs	x19, x1, x22 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab0e0183; (* adds	x3, x12, x14 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab1302a5; (* adds	x5, x21, x19 *)
  0xba040315; (* adcs	x21, x24, x4 *)
  0xba1f0178; (* adcs	x24, x11, xzr *)
  0xba1f028b; (* adcs	x11, x20, xzr *)
  0x9a1f00f4; (* adc	x20, x7, xzr *)
  0x6f00e5e3; (* movi	v3.2d, #0xffffffff *)
  0x4e815830; (* uzp2	v16.4s, v1.4s, v1.4s *)
  0x0ea12a39; (* xtn	v25.2s, v17.2d *)
  0x0ea12837; (* xtn	v23.2s, v1.2d *)
  0x4ea0083e; (* rev64	v30.4s, v1.4s *)
  0x2eb7c338; (* umull	v24.2d, v25.2s, v23.2s *)
  0x2eb0c320; (* umull	v0.2d, v25.2s, v16.2s *)
  0x4e915a22; (* uzp2	v2.4s, v17.4s, v17.4s *)
  0x4eb19fde; (* mul	v30.4s, v30.4s, v17.4s *)
  0x6f601700; (* usra	v0.2d, v24.2d, #32 *)
  0x2eb0c053; (* umull	v19.2d, v2.2s, v16.2s *)
  0x6ea02bde; (* uaddlp	v30.2d, v30.4s *)
  0x4e231c18; (* and	v24.16b, v0.16b, v3.16b *)
  0x2eb78058; (* umlal	v24.2d, v2.2s, v23.2s *)
  0x4f6057de; (* shl	v30.2d, v30.2d, #32 *)
  0x6f601413; (* usra	v19.2d, v0.2d, #32 *)
  0x2eb7833e; (* umlal	v30.2d, v25.2s, v23.2s *)
  0x6f601713; (* usra	v19.2d, v24.2d, #32 *)
  0x4e083fc7; (* mov	x7, v30.d[0] *)
  0x4e183fc1; (* mov	x1, v30.d[1] *)
  0x9b0d7e2e; (* mul	x14, x17, x13 *)
  0x4e083e73; (* mov	x19, v19.d[0] *)
  0x4e183e64; (* mov	x4, v19.d[1] *)
  0x9bcd7e36; (* umulh	x22, x17, x13 *)
  0xab0e026c; (* adds	x12, x19, x14 *)
  0xba160033; (* adcs	x19, x1, x22 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab0e018c; (* adds	x12, x12, x14 *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab1800e1; (* adds	x1, x7, x24 *)
  0xba0b018e; (* adcs	x14, x12, x11 *)
  0xba140276; (* adcs	x22, x19, x20 *)
  0x9a1f008c; (* adc	x12, x4, xzr *)
  0xa9401013; (* ldp	x19, x4, [x0] *)
  0xab0a0273; (* adds	x19, x19, x10 *)
  0xba030084; (* adcs	x4, x4, x3 *)
  0xa9001013; (* stp	x19, x4, [x0] *)
  0xa9411013; (* ldp	x19, x4, [x0, #16] *)
  0xba050273; (* adcs	x19, x19, x5 *)
  0xba150084; (* adcs	x4, x4, x21 *)
  0xa9011013; (* stp	x19, x4, [x0, #16] *)
  0xa9421013; (* ldp	x19, x4, [x0, #32] *)
  0xba010273; (* adcs	x19, x19, x1 *)
  0xba0e0084; (* adcs	x4, x4, x14 *)
  0xa9021013; (* stp	x19, x4, [x0, #32] *)
  0xa9431013; (* ldp	x19, x4, [x0, #48] *)
  0xba160273; (* adcs	x19, x19, x22 *)
  0xba0c0084; (* adcs	x4, x4, x12 *)
  0xa9031013; (* stp	x19, x4, [x0, #48] *)
  0xf9402004; (* ldr	x4, [x0, #64] *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xf9002004; (* str	x4, [x0, #64] *)
  0x6f00e5e3; (* movi	v3.2d, #0xffffffff *)
  0x4e9d5ba2; (* uzp2	v2.4s, v29.4s, v29.4s *)
  0x0ea12b70; (* xtn	v16.2s, v27.2d *)
  0x0ea12bb9; (* xtn	v25.2s, v29.2d *)
  0x4ea00bbe; (* rev64	v30.4s, v29.4s *)
  0x2eb9c218; (* umull	v24.2d, v16.2s, v25.2s *)
  0x2ea2c217; (* umull	v23.2d, v16.2s, v2.2s *)
  0x4e9b5b60; (* uzp2	v0.4s, v27.4s, v27.4s *)
  0x4ebb9fde; (* mul	v30.4s, v30.4s, v27.4s *)
  0x6f601717; (* usra	v23.2d, v24.2d, #32 *)
  0x2ea2c002; (* umull	v2.2d, v0.2s, v2.2s *)
  0x6ea02bde; (* uaddlp	v30.2d, v30.4s *)
  0x4e231ef8; (* and	v24.16b, v23.16b, v3.16b *)
  0x2eb98018; (* umlal	v24.2d, v0.2s, v25.2s *)
  0x4f6057de; (* shl	v30.2d, v30.2d, #32 *)
  0x6f6016e2; (* usra	v2.2d, v23.2d, #32 *)
  0x2eb9821e; (* umlal	v30.2d, v16.2s, v25.2s *)
  0x6f601702; (* usra	v2.2d, v24.2d, #32 *)
  0x4e083fc6; (* mov	x6, v30.d[0] *)
  0x4e183fd6; (* mov	x22, v30.d[1] *)
  0x9b177e2c; (* mul	x12, x17, x23 *)
  0x9b027db3; (* mul	x19, x13, x2 *)
  0x4e083c44; (* mov	x4, v2.d[0] *)
  0xab0402d6; (* adds	x22, x22, x4 *)
  0x4e183c44; (* mov	x4, v2.d[1] *)
  0xba04018c; (* adcs	x12, x12, x4 *)
  0x9bd77e24; (* umulh	x4, x17, x23 *)
  0xba040273; (* adcs	x19, x19, x4 *)
  0x9bc27da4; (* umulh	x4, x13, x2 *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0xab0602d5; (* adds	x21, x22, x6 *)
  0xba160196; (* adcs	x22, x12, x22 *)
  0xba0c026c; (* adcs	x12, x19, x12 *)
  0xba130093; (* adcs	x19, x4, x19 *)
  0x9a0403e4; (* adc	x4, xzr, x4 *)
  0xab0602d8; (* adds	x24, x22, x6 *)
  0xba15018b; (* adcs	x11, x12, x21 *)
  0xba160274; (* adcs	x20, x19, x22 *)
  0xba0c0081; (* adcs	x1, x4, x12 *)
  0xba1303ee; (* adcs	x14, xzr, x19 *)
  0x9a0403e7; (* adc	x7, xzr, x4 *)
  0xeb0d0224; (* subs	x4, x17, x13 *)
  0xda84248c; (* cneg	x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb170044; (* subs	x4, x2, x23 *)
  0xda842493; (* cneg	x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul	x4, x12, x19 *)
  0x9bd37d8c; (* umulh	x12, x12, x19 *)
  0xda9622d3; (* cinv	x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn	x19, #0x1 *)
  0xca130084; (* eor	x4, x4, x19 *)
  0xba040021; (* adcs	x1, x1, x4 *)
  0xca130184; (* eor	x4, x12, x19 *)
  0xba0401ce; (* adcs	x14, x14, x4 *)
  0x9a1300e7; (* adc	x7, x7, x19 *)
  0xeb080204; (* subs	x4, x16, x8 *)
  0xda84248c; (* cneg	x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb0901e4; (* subs	x4, x15, x9 *)
  0xda842493; (* cneg	x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul	x4, x12, x19 *)
  0x9bd37d8c; (* umulh	x12, x12, x19 *)
  0xda9622d3; (* cinv	x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn	x19, #0x1 *)
  0xca130084; (* eor	x4, x4, x19 *)
  0xba0402aa; (* adcs	x10, x21, x4 *)
  0xca130184; (* eor	x4, x12, x19 *)
  0xba040318; (* adcs	x24, x24, x4 *)
  0xba13016b; (* adcs	x11, x11, x19 *)
  0xba130294; (* adcs	x20, x20, x19 *)
  0xba130021; (* adcs	x1, x1, x19 *)
  0xba1301ce; (* adcs	x14, x14, x19 *)
  0x9a1300e7; (* adc	x7, x7, x19 *)
  0xeb0d0104; (* subs	x4, x8, x13 *)
  0xda84248c; (* cneg	x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb0f0044; (* subs	x4, x2, x15 *)
  0xda842493; (* cneg	x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul	x4, x12, x19 *)
  0x9bd37d8c; (* umulh	x12, x12, x19 *)
  0xda9622d3; (* cinv	x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn	x19, #0x1 *)
  0xca130084; (* eor	x4, x4, x19 *)
  0xba040294; (* adcs	x20, x20, x4 *)
  0xca130184; (* eor	x4, x12, x19 *)
  0xba040021; (* adcs	x1, x1, x4 *)
  0xba1301ce; (* adcs	x14, x14, x19 *)
  0x9a1300e7; (* adc	x7, x7, x19 *)
  0xeb110204; (* subs	x4, x16, x17 *)
  0xda84248c; (* cneg	x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb0902e4; (* subs	x4, x23, x9 *)
  0xda842493; (* cneg	x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul	x4, x12, x19 *)
  0x9bd37d8c; (* umulh	x12, x12, x19 *)
  0xda9622d3; (* cinv	x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn	x19, #0x1 *)
  0xca130084; (* eor	x4, x4, x19 *)
  0xba040318; (* adcs	x24, x24, x4 *)
  0xca130184; (* eor	x4, x12, x19 *)
  0xba04016b; (* adcs	x11, x11, x4 *)
  0xba130294; (* adcs	x20, x20, x19 *)
  0xba130021; (* adcs	x1, x1, x19 *)
  0xba1301ce; (* adcs	x14, x14, x19 *)
  0x9a1300e7; (* adc	x7, x7, x19 *)
  0xeb0d0204; (* subs	x4, x16, x13 *)
  0xda84248c; (* cneg	x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb090044; (* subs	x4, x2, x9 *)
  0xda842493; (* cneg	x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul	x4, x12, x19 *)
  0x9bd37d8c; (* umulh	x12, x12, x19 *)
  0xda9622d3; (* cinv	x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn	x19, #0x1 *)
  0xca130084; (* eor	x4, x4, x19 *)
  0xba04016b; (* adcs	x11, x11, x4 *)
  0xca130184; (* eor	x4, x12, x19 *)
  0xba040294; (* adcs	x20, x20, x4 *)
  0xba130021; (* adcs	x1, x1, x19 *)
  0xba1301ce; (* adcs	x14, x14, x19 *)
  0x9a1300e7; (* adc	x7, x7, x19 *)
  0xeb110104; (* subs	x4, x8, x17 *)
  0xda84248c; (* cneg	x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm	x22, cc  // cc = lo, ul, last *)
  0xeb0f02e4; (* subs	x4, x23, x15 *)
  0xda842493; (* cneg	x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul	x4, x12, x19 *)
  0x9bd37d8c; (* umulh	x12, x12, x19 *)
  0xda9622d3; (* cinv	x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn	x19, #0x1 *)
  0xca130084; (* eor	x4, x4, x19 *)
  0xba040163; (* adcs	x3, x11, x4 *)
  0xca130184; (* eor	x4, x12, x19 *)
  0xba040285; (* adcs	x5, x20, x4 *)
  0xba130021; (* adcs	x1, x1, x19 *)
  0xba1301ce; (* adcs	x14, x14, x19 *)
  0x9a1300f6; (* adc	x22, x7, x19 *)
  0xa9404c0c; (* ldp	x12, x19, [x0] *)
  0x93c52024; (* extr	x4, x1, x5, #8 *)
  0xab0c008b; (* adds	x11, x4, x12 *)
  0x93c121c4; (* extr	x4, x14, x1, #8 *)
  0xba130094; (* adcs	x20, x4, x19 *)
  0xa9413013; (* ldp	x19, x12, [x0, #16] *)
  0x93ce22c4; (* extr	x4, x22, x14, #8 *)
  0xba130087; (* adcs	x7, x4, x19 *)
  0x8a070293; (* and	x19, x20, x7 *)
  0xd348fec4; (* lsr	x4, x22, #8 *)
  0xba0c0081; (* adcs	x1, x4, x12 *)
  0x8a010276; (* and	x22, x19, x1 *)
  0xa9423013; (* ldp	x19, x12, [x0, #32] *)
  0xd37ff8c4; (* lsl	x4, x6, #1 *)
  0xba13008e; (* adcs	x14, x4, x19 *)
  0x8a0e02d3; (* and	x19, x22, x14 *)
  0x93c6fd44; (* extr	x4, x10, x6, #63 *)
  0xba0c0095; (* adcs	x21, x4, x12 *)
  0x8a150276; (* and	x22, x19, x21 *)
  0xa9433013; (* ldp	x19, x12, [x0, #48] *)
  0x93caff04; (* extr	x4, x24, x10, #63 *)
  0xba130082; (* adcs	x2, x4, x19 *)
  0x8a0202d3; (* and	x19, x22, x2 *)
  0x93d8fc64; (* extr	x4, x3, x24, #63 *)
  0xba0c0098; (* adcs	x24, x4, x12 *)
  0x8a18026c; (* and	x12, x19, x24 *)
  0xf9402013; (* ldr	x19, [x0, #64] *)
  0x93c3fca4; (* extr	x4, x5, x3, #63 *)
  0x92402084; (* and	x4, x4, #0x1ff *)
  0x9a040264; (* adc	x4, x19, x4 *)
  0xd349fc93; (* lsr	x19, x4, #9 *)
  0xb277d884; (* orr	x4, x4, #0xfffffffffffffe00 *)
  0xeb1f03ff; (* cmp	xzr, xzr *)
  0xba13017f; (* adcs	xzr, x11, x19 *)
  0xba1f019f; (* adcs	xzr, x12, xzr *)
  0xba1f009f; (* adcs	xzr, x4, xzr *)
  0xba13016b; (* adcs	x11, x11, x19 *)
  0xba1f0294; (* adcs	x20, x20, xzr *)
  0xba1f00e7; (* adcs	x7, x7, xzr *)
  0xba1f0021; (* adcs	x1, x1, xzr *)
  0xba1f01ce; (* adcs	x14, x14, xzr *)
  0xba1f02b6; (* adcs	x22, x21, xzr *)
  0xba1f004c; (* adcs	x12, x2, xzr *)
  0xba1f0318; (* adcs	x24, x24, xzr *)
  0x9a1f0084; (* adc	x4, x4, xzr *)
  0x92402093; (* and	x19, x4, #0x1ff *)
  0xd377d964; (* lsl	x4, x11, #9 *)
  0x93cbde8b; (* extr	x11, x20, x11, #55 *)
  0x93d4dcf4; (* extr	x20, x7, x20, #55 *)
  0x93c7dc27; (* extr	x7, x1, x7, #55 *)
  0x93c1ddc1; (* extr	x1, x14, x1, #55 *)
  0xaa040264; (* orr	x4, x19, x4 *)
  0x93cedece; (* extr	x14, x22, x14, #55 *)
  0x93d6dd96; (* extr	x22, x12, x22, #55 *)
  0x93ccdf0c; (* extr	x12, x24, x12, #55 *)
  0x93d8dc93; (* extr	x19, x4, x24, #55 *)
  0xd377fc84; (* lsr	x4, x4, #55 *)
  0xa900500b; (* stp	x11, x20, [x0] *)
  0xa9010407; (* stp	x7, x1, [x0, #16] *)
  0xa902580e; (* stp	x14, x22, [x0, #32] *)
  0xa9034c0c; (* stp	x12, x19, [x0, #48] *)
  0xf9002004; (* str	x4, [x0, #64] *)
];;

let bignum_montsqr_p521_interm1_core_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_montsqr_p521_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_montsqr_p521_interm1_core_mc" (term_of_bytes byte_list);;

let BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC =
  ARM_MK_EXEC_RULE bignum_montsqr_p521_interm1_core_mc;;

let montsqr_p521_eqin = new_definition
  `!s1 s1' x z.
    (montsqr_p521_eqin:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
    (C_ARGUMENTS [z; x] s1 /\
     C_ARGUMENTS [z; x] s1' /\
     ?a. bignum_from_memory (x,9) s1 = a /\
         bignum_from_memory (x,9) s1' = a)`;;

let montsqr_p521_eqout = new_definition
  `!s1 s1' z.
    (montsqr_p521_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,9) s1 = a /\
      bignum_from_memory (z,9) s1' = a)`;;

let actions1 = [
  ("equal", 0, 1, 0, 1); ("insert", 1, 1, 1, 4); ("equal", 1, 2, 4, 5);
  ("insert", 2, 2, 5, 8); ("equal", 2, 3, 8, 9); ("insert", 3, 3, 9, 11);
  ("equal", 3, 4, 11, 12); ("insert", 4, 4, 12, 14); ("equal", 4, 34, 14, 44);
  ("delete", 34, 46, 44, 44); ("insert", 46, 46, 44, 69)
];;
(* rewrite WORD_SQR128_DIGIT3;WORD_SQR128_DIGIT2;WORD_SQR128_DIGIT1;
           WORD_SQR128_DIGIT0 before actions2 *)
let actions2 = [
  ("equal", 46, 51, 69, 74); ("delete", 51, 53, 74, 74);
  ("insert", 53, 53, 74, 94); ("equal", 53, 54, 94, 95);
  ("delete", 54, 56, 95, 95); ("insert", 56, 56, 95, 97);
  ("equal", 56, 160, 97, 201); ("delete", 160, 162, 201, 201);
  ("insert", 162, 162, 201, 210); ("equal", 162, 190, 210, 238);
  ("delete", 190, 192, 238, 238); ("insert", 192, 192, 238, 258);
  ("equal", 192, 193, 258, 259); ("delete", 193, 195, 259, 259);
  ("insert", 195, 195, 259, 261); ("equal", 195, 207, 261, 273);
  ("delete", 207, 209, 273, 273); ("insert", 209, 209, 273, 293);
  ("equal", 209, 210, 293, 294); ("delete", 210, 212, 294, 294);
  ("insert", 212, 212, 294, 296); ("equal", 212, 242, 296, 326);
  ("delete", 242, 244, 326, 326); ("insert", 244, 244, 326, 346);
  ("equal", 244, 246, 346, 348); ("delete", 246, 247, 348, 348);
  ("insert", 247, 247, 348, 349); ("equal", 247, 248, 349, 350);
  ("delete", 248, 249, 350, 350); ("insert", 249, 249, 350, 351);
  ("equal", 249, 423, 351, 525)
];;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montsqr_p521_core_mc);
        (word pc2,LENGTH bignum_montsqr_p521_interm1_core_mc)]`
    montsqr_p521_eqin
    montsqr_p521_eqout
    bignum_montsqr_p521_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_montsqr_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
                       WORD_SQR64_HI]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTSQR_P521_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P521_CORE_EXEC;
    fst BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC;bignum] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions1
    BIGNUM_MONTSQR_P521_CORE_EXEC
    BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC THEN

  RULE_ASSUM_TAC (REWRITE_RULE[WORD_SQR128_DIGIT3;
    WORD_SQR128_DIGIT2;WORD_SQR128_DIGIT1;WORD_SQR128_DIGIT0]) THEN

  EQUIV_STEPS_TAC actions2
    BIGNUM_MONTSQR_P521_CORE_EXEC
    BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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

let bignum_montsqr_p521_neon_mc =
  define_from_elf "bignum_montsqr_p521_neon_mc"
    "arm/p521/bignum_montsqr_p521_neon.o";;

let BIGNUM_MONTSQR_P521_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p521_neon_mc;;

let bignum_montsqr_p521_neon_core_mc_def,
    bignum_montsqr_p521_neon_core_mc,
    BIGNUM_MONTSQR_P521_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p521_neon_core_mc"
    bignum_montsqr_p521_neon_mc
    (`12`,`LENGTH bignum_montsqr_p521_neon_mc - 28`)
    (fst BIGNUM_MONTSQR_P521_NEON_EXEC);;

let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montsqr_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_montsqr_p521_neon_core_mc)]`
    montsqr_p521_eqin
    montsqr_p521_eqout
    bignum_montsqr_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_montsqr_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws. *)

let inst_map = [
  14;9;12;13;45;79;17;83;77;76;48;78;49;81;15;86;80;28;63;75;82;29;18;50;89;20;19;85;8;21;16;84;2;22;30;46;203;25;31;56;91;47;55;205;87;23;52;51;32;3;4;33;34;90;88;35;57;54;53;58;202;204;92;59;61;60;6;240;26;24;242;62;36;241;10;37;206;64;27;38;39;40;41;95;244;42;1;245;246;43;11;44;65;94;207;68;66;7;97;67;98;239;248;69;70;96;249;71;243;109;5;72;208;73;112;247;74;99;277;100;93;101;102;110;251;103;114;113;254;104;105;252;115;106;275;122;116;107;278;111;146;108;119;117;118;123;120;124;130;121;282;131;125;127;132;126;128;147;129;138;148;139;133;134;135;140;136;137;187;186;250;143;188;211;285;141;153;256;142;161;288;144;154;281;145;276;151;149;155;150;162;169;152;158;156;163;157;170;159;166;164;160;171;165;167;189;190;177;178;172;173;174;168;175;179;176;280;180;181;192;331;279;193;182;290;183;224;184;185;212;191;214;253;274;213;215;283;216;199;198;209;200;194;218;210;201;195;284;217;335;286;219;222;334;223;225;287;330;221;226;289;220;291;329;227;228;255;328;229;230;332;231;196;333;232;197;259;296;336;233;234;262;338;295;235;260;327;236;258;261;237;339;238;340;263;294;257;337;264;341;265;266;267;297;268;269;270;271;293;342;292;272;273;298;299;300;301;355;302;303;304;308;305;312;344;306;343;307;353;309;316;310;313;311;320;314;348;324;317;318;351;319;347;321;349;346;315;322;345;325;382;383;384;385;386;389;350;388;352;323;326;354;356;368;369;370;371;372;375;357;387;358;393;373;359;360;361;374;362;391;363;377;364;365;366;367;379;376;378;380;381;400;401;402;403;407;404;390;392;405;394;409;395;406;396;397;398;399;415;417;416;418;419;422;408;420;410;411;424;421;412;413;414;448;449;450;432;433;434;451;455;452;453;435;439;436;426;437;423;425;457;427;428;438;429;483;480;430;441;431;440;454;443;442;469;464;444;445;484;477;446;447;456;458;459;476;460;490;487;461;491;462;492;465;467;463;466;468;470;473;471;474;472;478;475;481;479;485;482;488;486;489;493;494;496;495;497;498;499;500;501;510;502;511;512;503;513;521;504;505;514;506;522;516;507;517;508;523;518;509;515;519;520;524;525];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTSQR_P521_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTSQR_P521_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p521_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_MONTSQR_P521_NEON_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,9) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange left **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0':armstate` (concl th)) THEN
    (MONOTONE_MAYCHANGE_TAC ORELSE (PRINT_GOAL_TAC THEN FAIL_TAC "maychange1"));

    (** SUBGOAL 3. Maychange right **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0:armstate` (concl th)) THEN
    (MONOTONE_MAYCHANGE_TAC ORELSE (PRINT_GOAL_TAC THEN FAIL_TAC "maychange2"));
  ]);;



(******************************************************************************
  Use transitivity of two program equivalences to prove end-to-end
  correctness
******************************************************************************)

let equiv_goal = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montsqr_p521_core_mc);
        (word pc2,LENGTH bignum_montsqr_p521_neon_core_mc)]`
    montsqr_p521_eqin
    montsqr_p521_eqout
    bignum_montsqr_p521_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_montsqr_p521_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

let montsqr_p521_eqout_TRANS = prove(
  `!s s2 s'
    z. montsqr_p521_eqout (s,s') z /\ montsqr_p521_eqout (s',s2) z
    ==> montsqr_p521_eqout (s,s2) z`,
  MESON_TAC[montsqr_p521_eqout]);;

let BIGNUM_MONTSQR_P521_CORE_EQUIV = time prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc:int64,LENGTH bignum_montsqr_p521_core_mc);
        (word pc3:int64,LENGTH bignum_montsqr_p521_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc3:int64,LENGTH bignum_montsqr_p521_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montsqr_p521_neon_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montsqr_p521_interm1_core_mc))
        [x,8 * 9] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTSQR_P521_NEON_CORE_EXEC;
       GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTSQR_P521_CORE_EQUIV1,BIGNUM_MONTSQR_P521_CORE_EQUIV2)
    (montsqr_p521_eqin,montsqr_p521_eqout_TRANS)
    (BIGNUM_MONTSQR_P521_CORE_EXEC,BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC,
     BIGNUM_MONTSQR_P521_NEON_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MONTSQR_P521_NEON_SUBROUTINE_CORRECT
          from BIGNUM_MONTSQR_P521_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTSQR_P384_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64,
        LENGTH (APPEND bignum_montsqr_p521_core_mc barrier_inst_bytes))
      (z:int64,8 * 9)`
    [`z:int64`;`x:int64`] bignum_montsqr_p521_core_mc
    `\s0. C_ARGUMENTS [z;x] s0`;;

let BIGNUM_MONTSQR_P521_EVENTUALLY_N_AT_PC = time prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTSQR_P521_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montsqr_p521_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              fst BIGNUM_MONTSQR_P521_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P521_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTSQR_P521_CORE_EXEC);;


let BIGNUM_MONTSQR_P521_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTSQR_P521_EXEC
    BIGNUM_MONTSQR_P521_CORE_EXEC
    BIGNUM_MONTSQR_P521_CORE_CORRECT
    BIGNUM_MONTSQR_P521_EVENTUALLY_N_AT_PC;;

(* This theorem is a copy of BIGNUM_MONTSQR_P521_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - bignum_montsqr_p521_core_mc with bignum_montsqr_p521_neon_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)

let BIGNUM_MONTSQR_P521_NEON_CORE_CORRECT = time prove
 (`!z x n pc2.
        nonoverlapping (word pc2,LENGTH bignum_montsqr_p521_neon_core_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p521_neon_core_mc /\
                  read PC s = word(pc2) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p521_neon_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
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
        LENGTH (APPEND bignum_montsqr_p521_core_mc barrier_inst_bytes)) (z:int64,8 * 9) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p521_core_mc barrier_inst_bytes)) (x:int64,8 * 9) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P521_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P521_CORE_EQUIV BIGNUM_MONTSQR_P521_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P521_CORE_EXEC,BIGNUM_MONTSQR_P521_NEON_CORE_EXEC)
    (montsqr_p521_eqin,montsqr_p521_eqout));;


let BIGNUM_MONTSQR_P521_NEON_CORRECT = time prove
   (`!z x n pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p521_neon_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_neon_mc /\
                  read PC s = word(pc + 12) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 12 + LENGTH bignum_montsqr_p521_neon_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                      X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,

  ARM_SUB_LIST_OF_MC_TAC
    BIGNUM_MONTSQR_P521_NEON_CORE_CORRECT
    bignum_montsqr_p521_neon_core_mc_def
    [fst BIGNUM_MONTSQR_P521_NEON_CORE_EXEC;
     fst BIGNUM_MONTSQR_P521_NEON_EXEC]);;

let BIGNUM_MONTSQR_P521_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),48) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 9); (word_sub stackpointer (word 48),48)]
       [(word pc,LENGTH bignum_montsqr_p521_neon_mc); (x,8 * 9)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_neon_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = returnaddress /\
                (n < p_521
                 ==> bignum_from_memory (z,9) s =
                     (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)
    (REWRITE_RULE [fst BIGNUM_MONTSQR_P521_NEON_CORE_EXEC;
                   fst BIGNUM_MONTSQR_P521_NEON_EXEC]
     BIGNUM_MONTSQR_P521_NEON_CORRECT) in
  REWRITE_TAC[fst BIGNUM_MONTSQR_P521_NEON_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTSQR_P521_NEON_EXEC th
   `[X19;X20;X21;X22;X23;X24]` 48);;
