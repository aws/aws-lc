(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-unscheduled program
******************************************************************************)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bignum_montmul_p384.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to both
   bignum_montmul_p384 and bignum_montmul_p384_neon. This is a vectorized
   version of bignum_montmul_p384 but instructions are unscheduled. *)

let bignum_montmul_p384_interm1_ops:int list = [
  0xa9bf53f3; (* stp	x19, x20, [sp, #-16]! *)
  0xa9bf5bf5; (* stp	x21, x22, [sp, #-16]! *)
  0xa9bf63f7; (* stp	x23, x24, [sp, #-16]! *)
  0xa9405423; (* ldp	x3, x21, [x1] *)
  0x3dc0003e; (* ldr	q30, [x1] *)
  0xa9416028; (* ldp	x8, x24, [x1, #16] *)
  0xa9422825; (* ldp	x5, x10, [x1, #32] *)
  0xa9405c4d; (* ldp	x13, x23, [x2] *)
  0x3dc00053; (* ldr	q19, [x2] *)
  0xa9413846; (* ldp	x6, x14, [x2, #16] *)
  0xa942444f; (* ldp	x15, x17, [x2, #32] *)
  0x3dc00821; (* ldr	q1, [x1, #32] *)
  0x3dc0085c; (* ldr	q28, [x2, #32] *)
  0x4e9e1a65; (* uzp1	v5.4s, v19.4s, v30.4s *)
  0x4ea00a73; (* rev64	v19.4s, v19.4s *)
  0x4e9e1bc0; (* uzp1	v0.4s, v30.4s, v30.4s *)
  0x4ebe9e75; (* mul	v21.4s, v19.4s, v30.4s *)
  0x6ea02ab3; (* uaddlp	v19.2d, v21.4s *)
  0x4f605673; (* shl	v19.2d, v19.2d, #32 *)
  0x2ea58013; (* umlal	v19.2d, v0.2s, v5.2s *)
  0x4e083e6c; (* mov	x12, v19.d[0] *)
  0x4e183e70; (* mov	x16, v19.d[1] *)
  0x9b067d14; (* mul	x20, x8, x6 *)
  0x9bcd7c64; (* umulh	x4, x3, x13 *)
  0x9bd77ea1; (* umulh	x1, x21, x23 *)
  0x9bc67d02; (* umulh	x2, x8, x6 *)
  0xab100084; (* adds	x4, x4, x16 *)
  0xba140033; (* adcs	x19, x1, x20 *)
  0x9a1f0054; (* adc	x20, x2, xzr *)
  0xab0c008b; (* adds	x11, x4, x12 *)
  0xba040270; (* adcs	x16, x19, x4 *)
  0xba130281; (* adcs	x1, x20, x19 *)
  0x9a1f0282; (* adc	x2, x20, xzr *)
  0xab0c0207; (* adds	x7, x16, x12 *)
  0xba040024; (* adcs	x4, x1, x4 *)
  0xba130049; (* adcs	x9, x2, x19 *)
  0x9a1f0293; (* adc	x19, x20, xzr *)
  0xeb150062; (* subs	x2, x3, x21 *)
  0xda822454; (* cneg	x20, x2, cc  // cc = lo, ul, last *)
  0xda9f23f0; (* csetm	x16, cc  // cc = lo, ul, last *)
  0xeb0d02e2; (* subs	x2, x23, x13 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e81; (* mul	x1, x20, x2 *)
  0x9bc27e82; (* umulh	x2, x20, x2 *)
  0xda902210; (* cinv	x16, x16, cc  // cc = lo, ul, last *)
  0xca100021; (* eor	x1, x1, x16 *)
  0xca100042; (* eor	x2, x2, x16 *)
  0xb100061f; (* cmn	x16, #0x1 *)
  0xba01016b; (* adcs	x11, x11, x1 *)
  0xba0200e7; (* adcs	x7, x7, x2 *)
  0xba100084; (* adcs	x4, x4, x16 *)
  0xba100129; (* adcs	x9, x9, x16 *)
  0x9a100273; (* adc	x19, x19, x16 *)
  0xeb080062; (* subs	x2, x3, x8 *)
  0xda822454; (* cneg	x20, x2, cc  // cc = lo, ul, last *)
  0xda9f23f0; (* csetm	x16, cc  // cc = lo, ul, last *)
  0xeb0d00c2; (* subs	x2, x6, x13 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e81; (* mul	x1, x20, x2 *)
  0x9bc27e82; (* umulh	x2, x20, x2 *)
  0xda902210; (* cinv	x16, x16, cc  // cc = lo, ul, last *)
  0xca100021; (* eor	x1, x1, x16 *)
  0xca100042; (* eor	x2, x2, x16 *)
  0xb100061f; (* cmn	x16, #0x1 *)
  0xba0100e7; (* adcs	x7, x7, x1 *)
  0xba020084; (* adcs	x4, x4, x2 *)
  0xba100129; (* adcs	x9, x9, x16 *)
  0x9a100273; (* adc	x19, x19, x16 *)
  0xeb0802a2; (* subs	x2, x21, x8 *)
  0xda822454; (* cneg	x20, x2, cc  // cc = lo, ul, last *)
  0xda9f23f0; (* csetm	x16, cc  // cc = lo, ul, last *)
  0xeb1700c2; (* subs	x2, x6, x23 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e81; (* mul	x1, x20, x2 *)
  0x9bc27e82; (* umulh	x2, x20, x2 *)
  0xda902210; (* cinv	x16, x16, cc  // cc = lo, ul, last *)
  0xca100021; (* eor	x1, x1, x16 *)
  0xca100042; (* eor	x2, x2, x16 *)
  0xb100061f; (* cmn	x16, #0x1 *)
  0xba010084; (* adcs	x4, x4, x1 *)
  0xba020134; (* adcs	x20, x9, x2 *)
  0x9a100270; (* adc	x16, x19, x16 *)
  0xd3607d82; (* lsl	x2, x12, #32 *)
  0x8b0c0053; (* add	x19, x2, x12 *)
  0xd360fe62; (* lsr	x2, x19, #32 *)
  0xeb130041; (* subs	x1, x2, x19 *)
  0xda1f0262; (* sbc	x2, x19, xzr *)
  0x93c18041; (* extr	x1, x2, x1, #32 *)
  0xd360fc42; (* lsr	x2, x2, #32 *)
  0xab13004c; (* adds	x12, x2, x19 *)
  0x9a1f03e2; (* adc	x2, xzr, xzr *)
  0xeb010161; (* subs	x1, x11, x1 *)
  0xfa0c00e7; (* sbcs	x7, x7, x12 *)
  0xfa020084; (* sbcs	x4, x4, x2 *)
  0xfa1f0294; (* sbcs	x20, x20, xzr *)
  0xfa1f0210; (* sbcs	x16, x16, xzr *)
  0xda1f0269; (* sbc	x9, x19, xzr *)
  0xd3607c22; (* lsl	x2, x1, #32 *)
  0x8b010053; (* add	x19, x2, x1 *)
  0xd360fe62; (* lsr	x2, x19, #32 *)
  0xeb130041; (* subs	x1, x2, x19 *)
  0xda1f0262; (* sbc	x2, x19, xzr *)
  0x93c18041; (* extr	x1, x2, x1, #32 *)
  0xd360fc42; (* lsr	x2, x2, #32 *)
  0xab13004c; (* adds	x12, x2, x19 *)
  0x9a1f03e2; (* adc	x2, xzr, xzr *)
  0xeb0100e1; (* subs	x1, x7, x1 *)
  0xfa0c0084; (* sbcs	x4, x4, x12 *)
  0xfa020294; (* sbcs	x20, x20, x2 *)
  0xfa1f0210; (* sbcs	x16, x16, xzr *)
  0xfa1f0127; (* sbcs	x7, x9, xzr *)
  0xda1f0269; (* sbc	x9, x19, xzr *)
  0xd3607c22; (* lsl	x2, x1, #32 *)
  0x8b010053; (* add	x19, x2, x1 *)
  0xd360fe62; (* lsr	x2, x19, #32 *)
  0xeb130041; (* subs	x1, x2, x19 *)
  0xda1f0262; (* sbc	x2, x19, xzr *)
  0x93c1804c; (* extr	x12, x2, x1, #32 *)
  0xd360fc42; (* lsr	x2, x2, #32 *)
  0xab130041; (* adds	x1, x2, x19 *)
  0x9a1f03e2; (* adc	x2, xzr, xzr *)
  0xeb0c0084; (* subs	x4, x4, x12 *)
  0xfa010294; (* sbcs	x20, x20, x1 *)
  0xfa020210; (* sbcs	x16, x16, x2 *)
  0xfa1f00ec; (* sbcs	x12, x7, xzr *)
  0xfa1f0121; (* sbcs	x1, x9, xzr *)
  0xda1f0262; (* sbc	x2, x19, xzr *)
  0xa9005004; (* stp	x4, x20, [x0] *)
  0xa9013010; (* stp	x16, x12, [x0, #16] *)
  0xa9020801; (* stp	x1, x2, [x0, #32] *)
  0x9b0e7f16; (* mul	x22, x24, x14 *)
  0x6f00e5ff; (* movi	v31.2d, #0xffffffff *)
  0x4e9c5b90; (* uzp2	v16.4s, v28.4s, v28.4s *)
  0x0ea12826; (* xtn	v6.2s, v1.2d *)
  0x0ea12b9e; (* xtn	v30.2s, v28.2d *)
  0x4ea00b9c; (* rev64	v28.4s, v28.4s *)
  0x2ebec0c5; (* umull	v5.2d, v6.2s, v30.2s *)
  0x2eb0c0c0; (* umull	v0.2d, v6.2s, v16.2s *)
  0x4e815833; (* uzp2	v19.4s, v1.4s, v1.4s *)
  0x4ea19f94; (* mul	v20.4s, v28.4s, v1.4s *)
  0x6f6014a0; (* usra	v0.2d, v5.2d, #32 *)
  0x2eb0c261; (* umull	v1.2d, v19.2s, v16.2s *)
  0x6ea02a98; (* uaddlp	v24.2d, v20.4s *)
  0x4e3f1c05; (* and	v5.16b, v0.16b, v31.16b *)
  0x2ebe8265; (* umlal	v5.2d, v19.2s, v30.2s *)
  0x4f605713; (* shl	v19.2d, v24.2d, #32 *)
  0x6f601401; (* usra	v1.2d, v0.2d, #32 *)
  0x2ebe80d3; (* umlal	v19.2d, v6.2s, v30.2s *)
  0x6f6014a1; (* usra	v1.2d, v5.2d, #32 *)
  0x4e083e74; (* mov	x20, v19.d[0] *)
  0x4e183e70; (* mov	x16, v19.d[1] *)
  0x9bce7f0c; (* umulh	x12, x24, x14 *)
  0x4e083c21; (* mov	x1, v1.d[0] *)
  0x4e183c22; (* mov	x2, v1.d[1] *)
  0xab140184; (* adds	x4, x12, x20 *)
  0xba100034; (* adcs	x20, x1, x16 *)
  0x9a1f0050; (* adc	x16, x2, xzr *)
  0xab160087; (* adds	x7, x4, x22 *)
  0xba04028c; (* adcs	x12, x20, x4 *)
  0xba140201; (* adcs	x1, x16, x20 *)
  0x9a1f0202; (* adc	x2, x16, xzr *)
  0xab160189; (* adds	x9, x12, x22 *)
  0xba040033; (* adcs	x19, x1, x4 *)
  0xba140044; (* adcs	x4, x2, x20 *)
  0x9a1f0214; (* adc	x20, x16, xzr *)
  0xeb050302; (* subs	x2, x24, x5 *)
  0xda822450; (* cneg	x16, x2, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm	x12, cc  // cc = lo, ul, last *)
  0xeb0e01e2; (* subs	x2, x15, x14 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e01; (* mul	x1, x16, x2 *)
  0x9bc27e02; (* umulh	x2, x16, x2 *)
  0xda8c218c; (* cinv	x12, x12, cc  // cc = lo, ul, last *)
  0xca0c0021; (* eor	x1, x1, x12 *)
  0xca0c0042; (* eor	x2, x2, x12 *)
  0xb100059f; (* cmn	x12, #0x1 *)
  0xba0100eb; (* adcs	x11, x7, x1 *)
  0xba020129; (* adcs	x9, x9, x2 *)
  0xba0c0273; (* adcs	x19, x19, x12 *)
  0xba0c0084; (* adcs	x4, x4, x12 *)
  0x9a0c0294; (* adc	x20, x20, x12 *)
  0xeb0a0302; (* subs	x2, x24, x10 *)
  0xda822450; (* cneg	x16, x2, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm	x12, cc  // cc = lo, ul, last *)
  0xeb0e0222; (* subs	x2, x17, x14 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e01; (* mul	x1, x16, x2 *)
  0x9bc27e02; (* umulh	x2, x16, x2 *)
  0xda8c218c; (* cinv	x12, x12, cc  // cc = lo, ul, last *)
  0xca0c0021; (* eor	x1, x1, x12 *)
  0xca0c0042; (* eor	x2, x2, x12 *)
  0xb100059f; (* cmn	x12, #0x1 *)
  0xba010127; (* adcs	x7, x9, x1 *)
  0xba020273; (* adcs	x19, x19, x2 *)
  0xba0c0084; (* adcs	x4, x4, x12 *)
  0x9a0c0294; (* adc	x20, x20, x12 *)
  0xeb0a00a2; (* subs	x2, x5, x10 *)
  0xda822450; (* cneg	x16, x2, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm	x12, cc  // cc = lo, ul, last *)
  0xeb0f0222; (* subs	x2, x17, x15 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e01; (* mul	x1, x16, x2 *)
  0x9bc27e02; (* umulh	x2, x16, x2 *)
  0xda8c2190; (* cinv	x16, x12, cc  // cc = lo, ul, last *)
  0xca100021; (* eor	x1, x1, x16 *)
  0xca100042; (* eor	x2, x2, x16 *)
  0xb100061f; (* cmn	x16, #0x1 *)
  0xba010273; (* adcs	x19, x19, x1 *)
  0xba02008c; (* adcs	x12, x4, x2 *)
  0x9a100281; (* adc	x1, x20, x16 *)
  0xeb030302; (* subs	x2, x24, x3 *)
  0xfa1500b8; (* sbcs	x24, x5, x21 *)
  0xfa080155; (* sbcs	x21, x10, x8 *)
  0xda1f03e5; (* ngc	x5, xzr *)
  0xb10004bf; (* cmn	x5, #0x1 *)
  0xca050042; (* eor	x2, x2, x5 *)
  0xba1f0044; (* adcs	x4, x2, xzr *)
  0xca050302; (* eor	x2, x24, x5 *)
  0xba1f0054; (* adcs	x20, x2, xzr *)
  0xca0502a2; (* eor	x2, x21, x5 *)
  0x9a1f0050; (* adc	x16, x2, xzr *)
  0xeb0e01a2; (* subs	x2, x13, x14 *)
  0xfa0f02f8; (* sbcs	x24, x23, x15 *)
  0xfa1100c8; (* sbcs	x8, x6, x17 *)
  0xda1f03f5; (* ngc	x21, xzr *)
  0xb10006bf; (* cmn	x21, #0x1 *)
  0xca150042; (* eor	x2, x2, x21 *)
  0xba1f004f; (* adcs	x15, x2, xzr *)
  0xca150302; (* eor	x2, x24, x21 *)
  0xba1f004e; (* adcs	x14, x2, xzr *)
  0xca150102; (* eor	x2, x8, x21 *)
  0x9a1f0046; (* adc	x6, x2, xzr *)
  0xca1500a9; (* eor	x9, x5, x21 *)
  0xa9400815; (* ldp	x21, x2, [x0] *)
  0xab1502ca; (* adds	x10, x22, x21 *)
  0xba020165; (* adcs	x5, x11, x2 *)
  0xa9410815; (* ldp	x21, x2, [x0, #16] *)
  0xba1500f8; (* adcs	x24, x7, x21 *)
  0xba020268; (* adcs	x8, x19, x2 *)
  0xa9420815; (* ldp	x21, x2, [x0, #32] *)
  0xba150195; (* adcs	x21, x12, x21 *)
  0xba020022; (* adcs	x2, x1, x2 *)
  0x9a1f03f3; (* adc	x19, xzr, xzr *)
  0xa900140a; (* stp	x10, x5, [x0] *)
  0xa9012018; (* stp	x24, x8, [x0, #16] *)
  0xa9020815; (* stp	x21, x2, [x0, #32] *)
  0x9b0f7c8c; (* mul	x12, x4, x15 *)
  0x9b0e7e85; (* mul	x5, x20, x14 *)
  0x9b067e18; (* mul	x24, x16, x6 *)
  0x9bcf7c88; (* umulh	x8, x4, x15 *)
  0x9bce7e95; (* umulh	x21, x20, x14 *)
  0x9bc67e02; (* umulh	x2, x16, x6 *)
  0xab05010a; (* adds	x10, x8, x5 *)
  0xba1802a5; (* adcs	x5, x21, x24 *)
  0x9a1f0058; (* adc	x24, x2, xzr *)
  0xab0c0157; (* adds	x23, x10, x12 *)
  0xba0a00a8; (* adcs	x8, x5, x10 *)
  0xba050315; (* adcs	x21, x24, x5 *)
  0x9a1f0302; (* adc	x2, x24, xzr *)
  0xab0c010d; (* adds	x13, x8, x12 *)
  0xba0a02a1; (* adcs	x1, x21, x10 *)
  0xba05004a; (* adcs	x10, x2, x5 *)
  0x9a1f0305; (* adc	x5, x24, xzr *)
  0xeb140082; (* subs	x2, x4, x20 *)
  0xda822458; (* cneg	x24, x2, cc  // cc = lo, ul, last *)
  0xda9f23e8; (* csetm	x8, cc  // cc = lo, ul, last *)
  0xeb0f01c2; (* subs	x2, x14, x15 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027f15; (* mul	x21, x24, x2 *)
  0x9bc27f02; (* umulh	x2, x24, x2 *)
  0xda882108; (* cinv	x8, x8, cc  // cc = lo, ul, last *)
  0xca0802b5; (* eor	x21, x21, x8 *)
  0xca080042; (* eor	x2, x2, x8 *)
  0xb100051f; (* cmn	x8, #0x1 *)
  0xba1502f7; (* adcs	x23, x23, x21 *)
  0xba0201ad; (* adcs	x13, x13, x2 *)
  0xba080021; (* adcs	x1, x1, x8 *)
  0xba08014a; (* adcs	x10, x10, x8 *)
  0x9a0800a5; (* adc	x5, x5, x8 *)
  0xeb100082; (* subs	x2, x4, x16 *)
  0xda822458; (* cneg	x24, x2, cc  // cc = lo, ul, last *)
  0xda9f23e8; (* csetm	x8, cc  // cc = lo, ul, last *)
  0xeb0f00c2; (* subs	x2, x6, x15 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027f15; (* mul	x21, x24, x2 *)
  0x9bc27f02; (* umulh	x2, x24, x2 *)
  0xda882108; (* cinv	x8, x8, cc  // cc = lo, ul, last *)
  0xca0802b5; (* eor	x21, x21, x8 *)
  0xca080042; (* eor	x2, x2, x8 *)
  0xb100051f; (* cmn	x8, #0x1 *)
  0xba1501a4; (* adcs	x4, x13, x21 *)
  0xba02002d; (* adcs	x13, x1, x2 *)
  0xba080141; (* adcs	x1, x10, x8 *)
  0x9a0800aa; (* adc	x10, x5, x8 *)
  0xeb100282; (* subs	x2, x20, x16 *)
  0xda822458; (* cneg	x24, x2, cc  // cc = lo, ul, last *)
  0xda9f23e8; (* csetm	x8, cc  // cc = lo, ul, last *)
  0xeb0e00c2; (* subs	x2, x6, x14 *)
  0xda822442; (* cneg	x2, x2, cc  // cc = lo, ul, last *)
  0x9b027f15; (* mul	x21, x24, x2 *)
  0x9bc27f02; (* umulh	x2, x24, x2 *)
  0xda882105; (* cinv	x5, x8, cc  // cc = lo, ul, last *)
  0xca0502b5; (* eor	x21, x21, x5 *)
  0xca050042; (* eor	x2, x2, x5 *)
  0xb10004bf; (* cmn	x5, #0x1 *)
  0xba1501b8; (* adcs	x24, x13, x21 *)
  0xba020028; (* adcs	x8, x1, x2 *)
  0x9a050155; (* adc	x21, x10, x5 *)
  0xa9404014; (* ldp	x20, x16, [x0] *)
  0xa9413c11; (* ldp	x17, x15, [x0, #16] *)
  0xa942180e; (* ldp	x14, x6, [x0, #32] *)
  0xb100053f; (* cmn	x9, #0x1 *)
  0xca090182; (* eor	x2, x12, x9 *)
  0xba14004c; (* adcs	x12, x2, x20 *)
  0xca0902e2; (* eor	x2, x23, x9 *)
  0xba100057; (* adcs	x23, x2, x16 *)
  0xca090082; (* eor	x2, x4, x9 *)
  0xba11004d; (* adcs	x13, x2, x17 *)
  0xca090302; (* eor	x2, x24, x9 *)
  0xba0f004a; (* adcs	x10, x2, x15 *)
  0xca090102; (* eor	x2, x8, x9 *)
  0xba0e0045; (* adcs	x5, x2, x14 *)
  0xca0902a2; (* eor	x2, x21, x9 *)
  0xba060058; (* adcs	x24, x2, x6 *)
  0xba130121; (* adcs	x1, x9, x19 *)
  0xba1f0128; (* adcs	x8, x9, xzr *)
  0xba1f0135; (* adcs	x21, x9, xzr *)
  0x9a1f0122; (* adc	x2, x9, xzr *)
  0xab14014a; (* adds	x10, x10, x20 *)
  0xba1000a5; (* adcs	x5, x5, x16 *)
  0xba110318; (* adcs	x24, x24, x17 *)
  0xba0f0031; (* adcs	x17, x1, x15 *)
  0xba0e010f; (* adcs	x15, x8, x14 *)
  0xba0602ae; (* adcs	x14, x21, x6 *)
  0x9a130046; (* adc	x6, x2, x19 *)
  0xd3607d82; (* lsl	x2, x12, #32 *)
  0x8b0c0041; (* add	x1, x2, x12 *)
  0xd360fc22; (* lsr	x2, x1, #32 *)
  0xeb010055; (* subs	x21, x2, x1 *)
  0xda1f0022; (* sbc	x2, x1, xzr *)
  0x93d58055; (* extr	x21, x2, x21, #32 *)
  0xd360fc42; (* lsr	x2, x2, #32 *)
  0xab010048; (* adds	x8, x2, x1 *)
  0x9a1f03e2; (* adc	x2, xzr, xzr *)
  0xeb1502f5; (* subs	x21, x23, x21 *)
  0xfa0801b7; (* sbcs	x23, x13, x8 *)
  0xfa02014a; (* sbcs	x10, x10, x2 *)
  0xfa1f00a5; (* sbcs	x5, x5, xzr *)
  0xfa1f0318; (* sbcs	x24, x24, xzr *)
  0xda1f002d; (* sbc	x13, x1, xzr *)
  0xd3607ea2; (* lsl	x2, x21, #32 *)
  0x8b150041; (* add	x1, x2, x21 *)
  0xd360fc22; (* lsr	x2, x1, #32 *)
  0xeb010055; (* subs	x21, x2, x1 *)
  0xda1f0022; (* sbc	x2, x1, xzr *)
  0x93d58055; (* extr	x21, x2, x21, #32 *)
  0xd360fc42; (* lsr	x2, x2, #32 *)
  0xab010048; (* adds	x8, x2, x1 *)
  0x9a1f03e2; (* adc	x2, xzr, xzr *)
  0xeb1502f5; (* subs	x21, x23, x21 *)
  0xfa08014a; (* sbcs	x10, x10, x8 *)
  0xfa0200a5; (* sbcs	x5, x5, x2 *)
  0xfa1f0318; (* sbcs	x24, x24, xzr *)
  0xfa1f01b7; (* sbcs	x23, x13, xzr *)
  0xda1f002d; (* sbc	x13, x1, xzr *)
  0xd3607ea2; (* lsl	x2, x21, #32 *)
  0x8b150041; (* add	x1, x2, x21 *)
  0xd360fc22; (* lsr	x2, x1, #32 *)
  0xeb010055; (* subs	x21, x2, x1 *)
  0xda1f0022; (* sbc	x2, x1, xzr *)
  0x93d58048; (* extr	x8, x2, x21, #32 *)
  0xd360fc42; (* lsr	x2, x2, #32 *)
  0xab010055; (* adds	x21, x2, x1 *)
  0x9a1f03e2; (* adc	x2, xzr, xzr *)
  0xeb08014a; (* subs	x10, x10, x8 *)
  0xfa1500a5; (* sbcs	x5, x5, x21 *)
  0xfa020318; (* sbcs	x24, x24, x2 *)
  0xfa1f02e8; (* sbcs	x8, x23, xzr *)
  0xfa1f01b5; (* sbcs	x21, x13, xzr *)
  0xda1f0022; (* sbc	x2, x1, xzr *)
  0xab080237; (* adds	x23, x17, x8 *)
  0xba1501ed; (* adcs	x13, x15, x21 *)
  0xba0201c1; (* adcs	x1, x14, x2 *)
  0x9a1f00c2; (* adc	x2, x6, xzr *)
  0x91000448; (* add	x8, x2, #0x1 *)
  0xd3607d02; (* lsl	x2, x8, #32 *)
  0xeb020115; (* subs	x21, x8, x2 *)
  0xda1f0042; (* sbc	x2, x2, xzr *)
  0xab15014a; (* adds	x10, x10, x21 *)
  0xba0200a5; (* adcs	x5, x5, x2 *)
  0xba080318; (* adcs	x24, x24, x8 *)
  0xba1f02e8; (* adcs	x8, x23, xzr *)
  0xba1f01b5; (* adcs	x21, x13, xzr *)
  0xba1f002d; (* adcs	x13, x1, xzr *)
  0xda9f23e1; (* csetm	x1, cc  // cc = lo, ul, last *)
  0xb2407fe2; (* mov	x2, #0xffffffff            	// #4294967295 *)
  0x8a010042; (* and	x2, x2, x1 *)
  0xab02014a; (* adds	x10, x10, x2 *)
  0xca010042; (* eor	x2, x2, x1 *)
  0xba0200a5; (* adcs	x5, x5, x2 *)
  0x92800022; (* mov	x2, #0xfffffffffffffffe    	// #-2 *)
  0x8a010042; (* and	x2, x2, x1 *)
  0xba020318; (* adcs	x24, x24, x2 *)
  0xba010108; (* adcs	x8, x8, x1 *)
  0xba0102b5; (* adcs	x21, x21, x1 *)
  0x9a0101a2; (* adc	x2, x13, x1 *)
  0xa900140a; (* stp	x10, x5, [x0] *)
  0xa9012018; (* stp	x24, x8, [x0, #16] *)
  0xa9020815; (* stp	x21, x2, [x0, #32] *)
  0xa8c163f7; (* ldp	x23, x24, [sp], #16 *)
  0xa8c15bf5; (* ldp	x21, x22, [sp], #16 *)
  0xa8c153f3; (* ldp	x19, x20, [sp], #16 *)
  0xd65f03c0; (* ret *)
];;

let bignum_montmul_p384_interm1_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_montmul_p384_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_montmul_p384_interm1_mc" (term_of_bytes byte_list);;

let BIGNUM_MONTMUL_P384_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p384_interm1_mc;;

let bignum_montmul_p384_interm1_core_mc_def,
    bignum_montmul_p384_interm1_core_mc,
    BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p384_interm1_core_mc"
    bignum_montmul_p384_interm1_mc
    (`12`,`LENGTH bignum_montmul_p384_interm1_mc - 28`)
    (fst BIGNUM_MONTMUL_P384_INTERM1_EXEC);;

let montmul_p384_eqin = new_definition
  `!s1 s1' x y z.
    (montmul_p384_eqin:(armstate#armstate)->int64->int64->int64->bool) (s1,s1') x y z <=>
    (C_ARGUMENTS [z; x; y] s1 /\
     C_ARGUMENTS [z; x; y] s1' /\
     ?a. bignum_from_memory (x,6) s1 = a /\
         bignum_from_memory (x,6) s1' = a /\
      (?b. bignum_from_memory (y,6) s1 = b /\
           bignum_from_memory (y,6) s1' = b))`;;

let montmul_p384_eqout = new_definition
  `!s1 s1' z.
    (montmul_p384_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,6) s1 = a /\
      bignum_from_memory (z,6) s1' = a)`;;

(* This diff is generated by tools/gen-actions.py. *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 4, 2, 5);
  ("insert", 4, 4, 5, 6);
  ("equal", 4, 6, 6, 8);
  ("replace", 6, 8, 8, 19);
  ("equal", 8, 117, 19, 128);
  ("replace", 117, 119, 128, 148);
  ("equal", 119, 120, 148, 149);
  ("replace", 120, 122, 149, 151);
  ("equal", 122, 377, 151, 406);
];;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montmul_p384_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p384_interm1_core_mc)]`
    montmul_p384_eqin
    montmul_p384_eqout
    bignum_montmul_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montmul_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`;;


let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTMUL_P384_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P384_CORE_EXEC;
    fst BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p384_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTMUL_P384_CORE_EXEC
    BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,6) state`;
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

let bignum_montmul_p384_neon_mc =
  define_from_elf "bignum_montmul_p384_neon_mc"
    "arm/p384/bignum_montmul_p384_neon.o";;

let BIGNUM_MONTMUL_P384_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p384_neon_mc;;

let bignum_montmul_p384_neon_core_mc_def,
    bignum_montmul_p384_neon_core_mc,
    BIGNUM_MONTMUL_P384_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p384_neon_core_mc"
    bignum_montmul_p384_neon_mc
    (`12`,`LENGTH bignum_montmul_p384_neon_mc - 28`)
    (fst BIGNUM_MONTMUL_P384_NEON_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montmul_p384_interm1_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p384_neon_core_mc)]`
    montmul_p384_eqin
    montmul_p384_eqout
    bignum_montmul_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montmul_p384_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`;;


(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)

let inst_map = [
  2;6;5;1;12;11;21;14;13;10;3;35;9;129;37;22;133;130;36;38;131;132;39;7;137;15;42;40;136;135;16;17;20;139;51;134;52;23;19;43;18;53;138;24;25;41;26;144;27;141;28;140;29;142;30;31;143;32;33;44;34;54;55;58;45;56;46;47;48;57;49;50;66;67;59;68;69;70;145;71;73;61;146;62;60;63;64;80;72;74;8;81;65;4;82;75;83;84;76;77;85;86;78;79;87;149;88;89;90;91;95;96;92;128;93;97;94;98;99;100;101;102;103;104;105;106;110;111;107;112;108;109;113;114;115;116;117;118;119;147;120;121;125;122;123;126;150;124;163;148;164;165;166;151;170;167;127;168;152;153;154;155;169;156;171;157;158;159;160;161;162;173;172;174;175;176;177;178;179;180;181;182;186;183;208;209;184;210;211;194;187;196;195;197;201;198;219;220;215;199;221;213;222;185;212;202;214;216;217;218;228;200;223;224;226;225;227;229;189;188;190;247;191;192;203;231;193;204;205;234;246;206;207;237;232;245;233;230;235;241;236;244;238;242;239;240;277;249;243;278;279;248;292;310;293;294;280;281;284;261;283;262;263;264;268;282;265;295;296;299;250;266;251;252;253;254;267;255;256;257;258;259;298;269;260;271;272;270;312;273;285;274;297;301;275;276;287;288;398;286;289;300;290;291;302;306;307;303;316;304;305;309;311;308;314;333;313;315;320;317;318;319;321;322;323;334;335;324;325;336;337;326;327;338;339;328;329;330;331;393;332;340;341;342;343;348;349;344;345;350;346;347;351;352;353;354;355;356;357;358;363;359;364;360;365;361;362;366;367;369;368;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;399;394;395;396;397;400;404;401;402;405;403;406
];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTMUL_P384_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTMUL_P384_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p384_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_MONTMUL_P384_NEON_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,6) state`;
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
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montmul_p384_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p384_neon_core_mc)]`
    montmul_p384_eqin
    montmul_p384_eqout
    bignum_montmul_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montmul_p384_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`;;

let montmul_p384_eqout_TRANS = prove(
  `!s s2 s'
    z. montmul_p384_eqout (s,s') z /\ montmul_p384_eqout (s',s2) z
    ==> montmul_p384_eqout (s,s2) z`,
  MESON_TAC[montmul_p384_eqout]);;

let BIGNUM_MONTMUL_P384_CORE_EQUIV = time prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc:int64,LENGTH bignum_montmul_p384_core_mc);
        (word pc3:int64,LENGTH bignum_montmul_p384_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc3:int64,LENGTH bignum_montmul_p384_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montmul_p384_neon_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montmul_p384_interm1_core_mc))
        [x,8 * 6; y,8 * 6] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTMUL_P384_NEON_CORE_EXEC;
       fst BIGNUM_MONTMUL_P384_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTMUL_P384_CORE_EQUIV1,BIGNUM_MONTMUL_P384_CORE_EQUIV2)
    (montmul_p384_eqin,montmul_p384_eqout_TRANS)
    (BIGNUM_MONTMUL_P384_CORE_EXEC,BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC,
     BIGNUM_MONTMUL_P384_NEON_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MONTMUL_P384_NEON_SUBROUTINE_CORRECT
          from BIGNUM_MONTMUL_P384_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTMUL_P384_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64, LENGTH
        (APPEND bignum_montmul_p384_core_mc barrier_inst_bytes))
      (z:int64,8 * 6)`
    [`z:int64`;`x:int64`;`y:int64`] bignum_montmul_p384_core_mc
    `\s0. C_ARGUMENTS [z;x;y] s0`;;

let BIGNUM_MONTMUL_P384_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTMUL_P384_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montmul_p384_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_MONTMUL_P384_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P384_CORE_EXEC]
    THEN CONV_TAC NUM_DIVIDES_CONV
    THEN NO_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTMUL_P384_CORE_EXEC);;


let BIGNUM_MONTMUL_P384_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTMUL_P384_EXEC
    BIGNUM_MONTMUL_P384_CORE_EXEC
    BIGNUM_MONTMUL_P384_CORE_CORRECT
    BIGNUM_MONTMUL_P384_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_MONTMUL_P384_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montmul_p384_core_mc replaced with
    bignum_montmul_p384_neon_core_m
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_MONTMUL_P384_NEON_CORE_CORRECT = time prove(
  `!z x y a b pc2.
      nonoverlapping (word pc2,LENGTH bignum_montmul_p384_neon_core_mc) (z,8 * 6)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p384_neon_core_mc /\
                read PC s = word (pc2) /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
            (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p384_neon_core_mc) /\
                (a * b <= 2 EXP 384 * p_384
                  ==> bignum_from_memory (z,6) s =
                      (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17; X19;
                        X20; X21; X22; X23; X24] ,,
             MAYCHANGE MODIFIABLE_SIMD_REGS ,,
             MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
             MAYCHANGE SOME_FLAGS)`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_core_mc barrier_inst_bytes)) (y:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P384_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P384_CORE_EQUIV BIGNUM_MONTMUL_P384_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P384_CORE_EXEC,BIGNUM_MONTMUL_P384_NEON_CORE_EXEC)
    (montmul_p384_eqin,montmul_p384_eqout));;

let BIGNUM_MONTMUL_P384_NEON_CORRECT = time prove(
  `!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_neon_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_neon_mc /\
                  read PC s = word (pc+12) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word ((pc + 12) + LENGTH bignum_montmul_p384_neon_core_mc) /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P384_NEON_CORE_CORRECT
      bignum_montmul_p384_neon_core_mc_def
      [fst BIGNUM_MONTMUL_P384_NEON_EXEC;
       fst BIGNUM_MONTMUL_P384_NEON_CORE_EXEC]);;

let BIGNUM_MONTMUL_P384_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p384_neon_mc) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,LENGTH bignum_montmul_p384_neon_mc); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_neon_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
           (\s. read PC s = returnaddress /\
                (a * b <= 2 EXP 384 * p_384
                 ==> bignum_from_memory (z,6) s =
                     (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[fst BIGNUM_MONTMUL_P384_NEON_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_NEON_EXEC
   (let th = REWRITE_RULE [fst BIGNUM_MONTMUL_P384_NEON_CORE_EXEC;
        fst BIGNUM_MONTMUL_P384_NEON_EXEC;GSYM ADD_ASSOC]
      BIGNUM_MONTMUL_P384_NEON_CORRECT in
    CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
   `[X19;X20;X21;X22;X23;X24]` 48);;


(******************************************************************************
          Inducing BIGNUM_AMONTMUL_P384_NEON_SUBROUTINE_CORRECT
          from BIGNUM_AMONTMUL_P384_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTMUL_P384_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTMUL_P384_EXEC
    BIGNUM_MONTMUL_P384_CORE_EXEC
    BIGNUM_AMONTMUL_P384_CORE_CORRECT
    BIGNUM_MONTMUL_P384_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_AMONTMUL_P384_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montmul_p384_core_mc with
    bignum_montmul_p384_neon_core_m
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_AMONTMUL_P384_NEON_CORE_CORRECT = time prove(
  `!z x y a b pc2.
      nonoverlapping (word pc2,LENGTH bignum_montmul_p384_neon_core_mc) (z,8 * 6)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p384_neon_core_mc /\
                read PC s = word (pc2) /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
            (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p384_neon_core_mc) /\
                (bignum_from_memory (z,6) s ==
                  inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17; X19;
                        X20; X21; X22; X23; X24] ,,
             MAYCHANGE MODIFIABLE_SIMD_REGS ,,
             MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
             MAYCHANGE SOME_FLAGS)`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_core_mc barrier_inst_bytes)) (y:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P384_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P384_CORE_EQUIV BIGNUM_AMONTMUL_P384_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P384_CORE_EXEC,BIGNUM_MONTMUL_P384_NEON_CORE_EXEC)
    (montmul_p384_eqin,montmul_p384_eqout));;

let BIGNUM_AMONTMUL_P384_NEON_CORRECT = time prove(
  `!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_neon_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_neon_mc /\
                  read PC s = word (pc+12) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + (12 + LENGTH bignum_montmul_p384_neon_core_mc)) /\
                  (bignum_from_memory (z,6) s ==
                       inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17; X19;
                        X20; X21; X22; X23; X24] ,,
             MAYCHANGE MODIFIABLE_SIMD_REGS ,,
             MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
             MAYCHANGE SOME_FLAGS)`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTMUL_P384_NEON_CORE_CORRECT
      bignum_montmul_p384_neon_core_mc_def
      [fst BIGNUM_MONTMUL_P384_NEON_EXEC;
       fst BIGNUM_MONTMUL_P384_NEON_CORE_EXEC]);;


let BIGNUM_AMONTMUL_P384_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p384_neon_mc) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,LENGTH bignum_montmul_p384_neon_mc); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_neon_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
           (\s. read PC s = returnaddress /\
                (bignum_from_memory (z,6) s ==
                     inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[fst BIGNUM_MONTMUL_P384_NEON_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_NEON_EXEC
   (let th = REWRITE_RULE [fst BIGNUM_MONTMUL_P384_NEON_CORE_EXEC;
        fst BIGNUM_MONTMUL_P384_NEON_EXEC;GSYM ADD_ASSOC]
      BIGNUM_AMONTMUL_P384_NEON_CORRECT in
    CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
   `[X19;X20;X21;X22;X23;X24]` 48);;
