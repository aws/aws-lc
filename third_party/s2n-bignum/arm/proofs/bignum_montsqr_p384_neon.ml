(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-unscheduled program
******************************************************************************)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bignum_montsqr_p384.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to both
   bignum_montsqr_p384 and bignum_montsqr_p384_neon. This is a vectorized
   version of bignum_montsqr_p384 but instructions are unscheduled. *)

let bignum_montsqr_p384_interm1_ops:int list = [
  0xa9400829; (* ldp      x9, x2, [x1] *)
  0x3dc00032; (* ldr      q18, [x1] *)
  0x3dc00033; (* ldr      q19, [x1] *)
  0xa9411824; (* ldp      x4, x6, [x1, #16] *)
  0xa9422825; (* ldp      x5, x10, [x1, #32] *)
  0x3dc00835; (* ldr      q21, [x1, #32] *)
  0x3dc0083c; (* ldr      q28, [x1, #32] *)
  0x9b027d2c; (* mul      x12, x9, x2 *)
  0x9b047d21; (* mul      x1, x9, x4 *)
  0x9b047c4d; (* mul      x13, x2, x4 *)
  0x6f00e5e0; (* movi     v0.2d, #0xffffffff *)
  0x4e935a65; (* uzp2     v5.4s, v19.4s, v19.4s *)
  0x0ea12a59; (* xtn      v25.2s, v18.2d *)
  0x0ea12a64; (* xtn      v4.2s, v19.2d *)
  0x4ea00a77; (* rev64    v23.4s, v19.4s *)
  0x2ea4c334; (* umull    v20.2d, v25.2s, v4.2s *)
  0x2ea5c33e; (* umull    v30.2d, v25.2s, v5.2s *)
  0x4e925a53; (* uzp2     v19.4s, v18.4s, v18.4s *)
  0x4eb29ef6; (* mul      v22.4s, v23.4s, v18.4s *)
  0x6f60169e; (* usra     v30.2d, v20.2d, #32 *)
  0x2ea5c272; (* umull    v18.2d, v19.2s, v5.2s *)
  0x6ea02ad6; (* uaddlp   v22.2d, v22.4s *)
  0x4e201fd4; (* and      v20.16b, v30.16b, v0.16b *)
  0x2ea48274; (* umlal    v20.2d, v19.2s, v4.2s *)
  0x4f6056d3; (* shl      v19.2d, v22.2d, #32 *)
  0x6f6017d2; (* usra     v18.2d, v30.2d, #32 *)
  0x2ea48333; (* umlal    v19.2d, v25.2s, v4.2s *)
  0x6f601692; (* usra     v18.2d, v20.2d, #32 *)
  0x4e083e67; (* mov      x7, v19.d[0] *)
  0x4e183e71; (* mov      x17, v19.d[1] *)
  0x9b047c90; (* mul      x16, x4, x4 *)
  0x9bc27d23; (* umulh    x3, x9, x2 *)
  0xab03002f; (* adds     x15, x1, x3 *)
  0x9bc47d21; (* umulh    x1, x9, x4 *)
  0xba0101ad; (* adcs     x13, x13, x1 *)
  0x9bc47c41; (* umulh    x1, x2, x4 *)
  0xba1f0028; (* adcs     x8, x1, xzr *)
  0x4e083e4b; (* mov      x11, v18.d[0] *)
  0x4e183e4e; (* mov      x14, v18.d[1] *)
  0x9bc47c81; (* umulh    x1, x4, x4 *)
  0xab0c0183; (* adds     x3, x12, x12 *)
  0xba0f01ef; (* adcs     x15, x15, x15 *)
  0xba0d01ad; (* adcs     x13, x13, x13 *)
  0xba08010c; (* adcs     x12, x8, x8 *)
  0x9a1f0021; (* adc      x1, x1, xzr *)
  0xab03016b; (* adds     x11, x11, x3 *)
  0xba0f0223; (* adcs     x3, x17, x15 *)
  0xba0d01d1; (* adcs     x17, x14, x13 *)
  0xba0c020f; (* adcs     x15, x16, x12 *)
  0x9a1f002d; (* adc      x13, x1, xzr *)
  0xd3607ce1; (* lsl      x1, x7, #32 *)
  0x8b070030; (* add      x16, x1, x7 *)
  0xd360fe01; (* lsr      x1, x16, #32 *)
  0xeb10002c; (* subs     x12, x1, x16 *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0x93cc802c; (* extr     x12, x1, x12, #32 *)
  0xd360fc21; (* lsr      x1, x1, #32 *)
  0xab100027; (* adds     x7, x1, x16 *)
  0x9a1f03e1; (* adc      x1, xzr, xzr *)
  0xeb0c016c; (* subs     x12, x11, x12 *)
  0xfa07006b; (* sbcs     x11, x3, x7 *)
  0xfa010231; (* sbcs     x17, x17, x1 *)
  0xfa1f01ef; (* sbcs     x15, x15, xzr *)
  0xfa1f01ad; (* sbcs     x13, x13, xzr *)
  0xda1f0203; (* sbc      x3, x16, xzr *)
  0xd3607d81; (* lsl      x1, x12, #32 *)
  0x8b0c0030; (* add      x16, x1, x12 *)
  0xd360fe01; (* lsr      x1, x16, #32 *)
  0xeb10002c; (* subs     x12, x1, x16 *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0x93cc802c; (* extr     x12, x1, x12, #32 *)
  0xd360fc21; (* lsr      x1, x1, #32 *)
  0xab100027; (* adds     x7, x1, x16 *)
  0x9a1f03e1; (* adc      x1, xzr, xzr *)
  0xeb0c016c; (* subs     x12, x11, x12 *)
  0xfa070231; (* sbcs     x17, x17, x7 *)
  0xfa0101ef; (* sbcs     x15, x15, x1 *)
  0xfa1f01ad; (* sbcs     x13, x13, xzr *)
  0xfa1f006b; (* sbcs     x11, x3, xzr *)
  0xda1f0203; (* sbc      x3, x16, xzr *)
  0xd3607d81; (* lsl      x1, x12, #32 *)
  0x8b0c0030; (* add      x16, x1, x12 *)
  0xd360fe01; (* lsr      x1, x16, #32 *)
  0xeb10002c; (* subs     x12, x1, x16 *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0x93cc8027; (* extr     x7, x1, x12, #32 *)
  0xd360fc21; (* lsr      x1, x1, #32 *)
  0xab10002c; (* adds     x12, x1, x16 *)
  0x9a1f03e1; (* adc      x1, xzr, xzr *)
  0xeb070231; (* subs     x17, x17, x7 *)
  0xfa0c01ef; (* sbcs     x15, x15, x12 *)
  0xfa0101ad; (* sbcs     x13, x13, x1 *)
  0xfa1f0167; (* sbcs     x7, x11, xzr *)
  0xfa1f006c; (* sbcs     x12, x3, xzr *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0xa9003c11; (* stp      x17, x15, [x0] *)
  0xa9011c0d; (* stp      x13, x7, [x0, #16] *)
  0xa902040c; (* stp      x12, x1, [x0, #32] *)
  0x9b067d2e; (* mul      x14, x9, x6 *)
  0x9b057c4f; (* mul      x15, x2, x5 *)
  0x9b0a7c8d; (* mul      x13, x4, x10 *)
  0x9bc67d27; (* umulh    x7, x9, x6 *)
  0x9bc57c4c; (* umulh    x12, x2, x5 *)
  0x9bca7c81; (* umulh    x1, x4, x10 *)
  0xab0f00ef; (* adds     x15, x7, x15 *)
  0xba0d0190; (* adcs     x16, x12, x13 *)
  0x9a1f002d; (* adc      x13, x1, xzr *)
  0xab0e01eb; (* adds     x11, x15, x14 *)
  0xba0f0207; (* adcs     x7, x16, x15 *)
  0xba1001ac; (* adcs     x12, x13, x16 *)
  0x9a1f01a1; (* adc      x1, x13, xzr *)
  0xab0e00f1; (* adds     x17, x7, x14 *)
  0xba0f018f; (* adcs     x15, x12, x15 *)
  0xba100023; (* adcs     x3, x1, x16 *)
  0x9a1f01b0; (* adc      x16, x13, xzr *)
  0xeb020121; (* subs     x1, x9, x2 *)
  0xda81242d; (* cneg     x13, x1, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm    x7, cc  // cc = lo, ul, last *)
  0xeb0600a1; (* subs     x1, x5, x6 *)
  0xda812421; (* cneg     x1, x1, cc  // cc = lo, ul, last *)
  0x9b017dac; (* mul      x12, x13, x1 *)
  0x9bc17da1; (* umulh    x1, x13, x1 *)
  0xda8720e7; (* cinv     x7, x7, cc  // cc = lo, ul, last *)
  0xca07018c; (* eor      x12, x12, x7 *)
  0xca070021; (* eor      x1, x1, x7 *)
  0xb10004ff; (* cmn      x7, #0x1 *)
  0xba0c016b; (* adcs     x11, x11, x12 *)
  0xba010231; (* adcs     x17, x17, x1 *)
  0xba0701ef; (* adcs     x15, x15, x7 *)
  0xba070063; (* adcs     x3, x3, x7 *)
  0x9a070210; (* adc      x16, x16, x7 *)
  0xeb040129; (* subs     x9, x9, x4 *)
  0xda89252d; (* cneg     x13, x9, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm    x7, cc  // cc = lo, ul, last *)
  0xeb060141; (* subs     x1, x10, x6 *)
  0xda812421; (* cneg     x1, x1, cc  // cc = lo, ul, last *)
  0x9b017dac; (* mul      x12, x13, x1 *)
  0x9bc17da1; (* umulh    x1, x13, x1 *)
  0xda8720e7; (* cinv     x7, x7, cc  // cc = lo, ul, last *)
  0xca07018c; (* eor      x12, x12, x7 *)
  0xca070021; (* eor      x1, x1, x7 *)
  0xb10004ff; (* cmn      x7, #0x1 *)
  0xba0c0231; (* adcs     x17, x17, x12 *)
  0xba0101ef; (* adcs     x15, x15, x1 *)
  0xba07006d; (* adcs     x13, x3, x7 *)
  0x9a070207; (* adc      x7, x16, x7 *)
  0xeb040042; (* subs     x2, x2, x4 *)
  0xda82244c; (* cneg     x12, x2, cc  // cc = lo, ul, last *)
  0xda9f23e1; (* csetm    x1, cc  // cc = lo, ul, last *)
  0xeb050142; (* subs     x2, x10, x5 *)
  0xda822442; (* cneg     x2, x2, cc  // cc = lo, ul, last *)
  0x9b027d84; (* mul      x4, x12, x2 *)
  0x9bc27d82; (* umulh    x2, x12, x2 *)
  0xda812021; (* cinv     x1, x1, cc  // cc = lo, ul, last *)
  0xca010084; (* eor      x4, x4, x1 *)
  0xca010042; (* eor      x2, x2, x1 *)
  0xb100043f; (* cmn      x1, #0x1 *)
  0xba0401ec; (* adcs     x12, x15, x4 *)
  0xba0201a4; (* adcs     x4, x13, x2 *)
  0x9a0100e2; (* adc      x2, x7, x1 *)
  0xab0e01c1; (* adds     x1, x14, x14 *)
  0xba0b0170; (* adcs     x16, x11, x11 *)
  0xba110231; (* adcs     x17, x17, x17 *)
  0xba0c018f; (* adcs     x15, x12, x12 *)
  0xba04008d; (* adcs     x13, x4, x4 *)
  0xba020047; (* adcs     x7, x2, x2 *)
  0x9a1f03ec; (* adc      x12, xzr, xzr *)
  0xa9400804; (* ldp      x4, x2, [x0] *)
  0xab040021; (* adds     x1, x1, x4 *)
  0xba020210; (* adcs     x16, x16, x2 *)
  0xa9410804; (* ldp      x4, x2, [x0, #16] *)
  0xba040231; (* adcs     x17, x17, x4 *)
  0xba0201ef; (* adcs     x15, x15, x2 *)
  0xa9420804; (* ldp      x4, x2, [x0, #32] *)
  0xba0401ad; (* adcs     x13, x13, x4 *)
  0xba0200e7; (* adcs     x7, x7, x2 *)
  0x9a1f018b; (* adc      x11, x12, xzr *)
  0xd3607c22; (* lsl      x2, x1, #32 *)
  0x8b01004c; (* add      x12, x2, x1 *)
  0xd360fd82; (* lsr      x2, x12, #32 *)
  0xeb0c0044; (* subs     x4, x2, x12 *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0x93c48044; (* extr     x4, x2, x4, #32 *)
  0xd360fc42; (* lsr      x2, x2, #32 *)
  0xab0c0041; (* adds     x1, x2, x12 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xeb040204; (* subs     x4, x16, x4 *)
  0xfa010230; (* sbcs     x16, x17, x1 *)
  0xfa0201f1; (* sbcs     x17, x15, x2 *)
  0xfa1f01af; (* sbcs     x15, x13, xzr *)
  0xfa1f00ed; (* sbcs     x13, x7, xzr *)
  0xda1f0187; (* sbc      x7, x12, xzr *)
  0xd3607c82; (* lsl      x2, x4, #32 *)
  0x8b04004c; (* add      x12, x2, x4 *)
  0xd360fd82; (* lsr      x2, x12, #32 *)
  0xeb0c0044; (* subs     x4, x2, x12 *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0x93c48044; (* extr     x4, x2, x4, #32 *)
  0xd360fc42; (* lsr      x2, x2, #32 *)
  0xab0c0041; (* adds     x1, x2, x12 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xeb040204; (* subs     x4, x16, x4 *)
  0xfa010230; (* sbcs     x16, x17, x1 *)
  0xfa0201f1; (* sbcs     x17, x15, x2 *)
  0xfa1f01af; (* sbcs     x15, x13, xzr *)
  0xfa1f00ed; (* sbcs     x13, x7, xzr *)
  0xda1f0187; (* sbc      x7, x12, xzr *)
  0xd3607c82; (* lsl      x2, x4, #32 *)
  0x8b04004c; (* add      x12, x2, x4 *)
  0xd360fd82; (* lsr      x2, x12, #32 *)
  0xeb0c0044; (* subs     x4, x2, x12 *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0x93c48041; (* extr     x1, x2, x4, #32 *)
  0xd360fc42; (* lsr      x2, x2, #32 *)
  0xab0c0044; (* adds     x4, x2, x12 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xeb010203; (* subs     x3, x16, x1 *)
  0xfa040231; (* sbcs     x17, x17, x4 *)
  0xfa0201ef; (* sbcs     x15, x15, x2 *)
  0xfa1f01a1; (* sbcs     x1, x13, xzr *)
  0xfa1f00e4; (* sbcs     x4, x7, xzr *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0xab01016d; (* adds     x13, x11, x1 *)
  0xba1f0087; (* adcs     x7, x4, xzr *)
  0xba1f004c; (* adcs     x12, x2, xzr *)
  0xba1f03f0; (* adcs     x16, xzr, xzr *)
  0x9b067cc2; (* mul      x2, x6, x6 *)
  0xab020063; (* adds     x3, x3, x2 *)
  0x0ea12b9e; (* xtn      v30.2s, v28.2d *)
  0x0f20879a; (* shrn     v26.2s, v28.2d, #32 *)
  0x2ebac3da; (* umull    v26.2d, v30.2s, v26.2s *)
  0x4f615753; (* shl      v19.2d, v26.2d, #33 *)
  0x2ebe83d3; (* umlal    v19.2d, v30.2s, v30.2s *)
  0x4e083e61; (* mov      x1, v19.d[0] *)
  0x4e183e64; (* mov      x4, v19.d[1] *)
  0x9bc67cc2; (* umulh    x2, x6, x6 *)
  0xba020231; (* adcs     x17, x17, x2 *)
  0x9bc57ca2; (* umulh    x2, x5, x5 *)
  0xba0101ef; (* adcs     x15, x15, x1 *)
  0xba0201ad; (* adcs     x13, x13, x2 *)
  0x9bca7d42; (* umulh    x2, x10, x10 *)
  0xba0400e7; (* adcs     x7, x7, x4 *)
  0xba02018c; (* adcs     x12, x12, x2 *)
  0x9a1f0210; (* adc      x16, x16, xzr *)
  0x4e080cdc; (* dup      v28.2d, x6 *)
  0x6f00e5e0; (* movi     v0.2d, #0xffffffff *)
  0x4e955aa5; (* uzp2     v5.4s, v21.4s, v21.4s *)
  0x0ea12b99; (* xtn      v25.2s, v28.2d *)
  0x0ea12aa4; (* xtn      v4.2s, v21.2d *)
  0x4ea00ab3; (* rev64    v19.4s, v21.4s *)
  0x2ea4c33e; (* umull    v30.2d, v25.2s, v4.2s *)
  0x2ea5c337; (* umull    v23.2d, v25.2s, v5.2s *)
  0x4e9c5b94; (* uzp2     v20.4s, v28.4s, v28.4s *)
  0x4ebc9e73; (* mul      v19.4s, v19.4s, v28.4s *)
  0x6f6017d7; (* usra     v23.2d, v30.2d, #32 *)
  0x2ea5c292; (* umull    v18.2d, v20.2s, v5.2s *)
  0x6ea02a73; (* uaddlp   v19.2d, v19.4s *)
  0x4e201efe; (* and      v30.16b, v23.16b, v0.16b *)
  0x2ea4829e; (* umlal    v30.2d, v20.2s, v4.2s *)
  0x4f605673; (* shl      v19.2d, v19.2d, #32 *)
  0x6f6016f2; (* usra     v18.2d, v23.2d, #32 *)
  0x2ea48333; (* umlal    v19.2d, v25.2s, v4.2s *)
  0x6f6017d2; (* usra     v18.2d, v30.2d, #32 *)
  0x4e083e66; (* mov      x6, v19.d[0] *)
  0x4e183e61; (* mov      x1, v19.d[1] *)
  0x9b0a7ca4; (* mul      x4, x5, x10 *)
  0x4e083e42; (* mov      x2, v18.d[0] *)
  0xab020021; (* adds     x1, x1, x2 *)
  0x4e183e42; (* mov      x2, v18.d[1] *)
  0xba020084; (* adcs     x4, x4, x2 *)
  0x9bca7ca5; (* umulh    x5, x5, x10 *)
  0x9a1f00a2; (* adc      x2, x5, xzr *)
  0xab0600c5; (* adds     x5, x6, x6 *)
  0xba010026; (* adcs     x6, x1, x1 *)
  0xba040081; (* adcs     x1, x4, x4 *)
  0xba020044; (* adcs     x4, x2, x2 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xab050231; (* adds     x17, x17, x5 *)
  0xba0601ef; (* adcs     x15, x15, x6 *)
  0xba0101ad; (* adcs     x13, x13, x1 *)
  0xba0400e7; (* adcs     x7, x7, x4 *)
  0xba02018c; (* adcs     x12, x12, x2 *)
  0x9a1f0202; (* adc      x2, x16, xzr *)
  0xb26083e5; (* mov      x5, #0xffffffff00000001         // #-4294967295 *)
  0xb2407fe6; (* mov      x6, #0xffffffff                 // #4294967295 *)
  0xd2800021; (* mov      x1, #0x1                        // #1 *)
  0xab05007f; (* cmn      x3, x5 *)
  0xba06023f; (* adcs     xzr, x17, x6 *)
  0xba0101ff; (* adcs     xzr, x15, x1 *)
  0xba1f01bf; (* adcs     xzr, x13, xzr *)
  0xba1f00ff; (* adcs     xzr, x7, xzr *)
  0xba1f019f; (* adcs     xzr, x12, xzr *)
  0x9a1f0042; (* adc      x2, x2, xzr *)
  0xcb0203e4; (* neg      x4, x2 *)
  0x8a0400a2; (* and      x2, x5, x4 *)
  0xab02006a; (* adds     x10, x3, x2 *)
  0x8a0400c2; (* and      x2, x6, x4 *)
  0xba020225; (* adcs     x5, x17, x2 *)
  0x8a040022; (* and      x2, x1, x4 *)
  0xba0201e6; (* adcs     x6, x15, x2 *)
  0xba1f01a1; (* adcs     x1, x13, xzr *)
  0xba1f00e4; (* adcs     x4, x7, xzr *)
  0x9a1f0182; (* adc      x2, x12, xzr *)
  0xa900140a; (* stp      x10, x5, [x0] *)
  0xa9010406; (* stp      x6, x1, [x0, #16] *)
  0xa9020804; (* stp      x4, x2, [x0, #32] *)
  0xd65f03c0; (* ret *)
];;

let bignum_montsqr_p384_interm1_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_montsqr_p384_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_montsqr_p384_interm1_mc" (term_of_bytes byte_list);;

let BIGNUM_MONTSQR_P384_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p384_interm1_mc;;

let bignum_montsqr_p384_interm1_core_mc_def,
    bignum_montsqr_p384_interm1_core_mc,
    BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p384_interm1_core_mc"
    bignum_montsqr_p384_interm1_mc
    (`0`,`LENGTH bignum_montsqr_p384_interm1_mc - 4`)
    (fst BIGNUM_MONTSQR_P384_INTERM1_EXEC);;

let montsqr_p384_eqin = new_definition
  `!s1 s1' x z.
    (montsqr_p384_eqin:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
     (C_ARGUMENTS [z; x] s1 /\
      C_ARGUMENTS [z; x] s1' /\
      ?a. bignum_from_memory (x,6) s1 = a /\
          bignum_from_memory (x,6) s1' = a)`;;

let montsqr_p384_eqout = new_definition
  `!s1 s1' z.
    (montsqr_p384_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,6) s1 = a /\
      bignum_from_memory (z,6) s1' = a)`;;

(* This diff is generated by tools/gen-actions.py. *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 3);
  ("equal", 1, 3, 3, 5);
  ("insert", 3, 3, 5, 7);
  ("equal", 3, 6, 7, 10);
  ("replace", 6, 8, 10, 30);
  ("equal", 8, 15, 30, 37);
  ("replace", 15, 17, 37, 39);
  ("equal", 17, 206, 39, 228);
  ("replace", 206, 208, 228, 235);
  ("equal", 208, 217, 235, 244);
  ("replace", 217, 219, 244, 265);
  ("equal", 219, 220, 265, 266);
  ("replace", 220, 221, 266, 267);
  ("equal", 221, 222, 267, 268);
  ("replace", 222, 223, 268, 269);
  ("equal", 223, 260, 269, 306);
];;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montsqr_p384_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p384_interm1_core_mc)]`
    montsqr_p384_eqin
    montsqr_p384_eqout
    bignum_montsqr_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montsqr_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
                       WORD_SQR128_DIGIT0]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTSQR_P384_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P384_CORE_EXEC;
    fst BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p384_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTSQR_P384_CORE_EXEC
    BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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

let bignum_montsqr_p384_neon_mc =
  define_from_elf "bignum_montsqr_p384_neon_mc"
    "arm/p384/bignum_montsqr_p384_neon.o";;

let BIGNUM_MONTSQR_P384_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p384_neon_mc;;

let bignum_montsqr_p384_neon_core_mc_def,
    bignum_montsqr_p384_neon_core_mc,
    BIGNUM_MONTSQR_P384_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p384_neon_core_mc"
    bignum_montsqr_p384_neon_mc
    (`0`,`LENGTH bignum_montsqr_p384_neon_mc - 4`)
    (fst BIGNUM_MONTSQR_P384_NEON_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montsqr_p384_interm1_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p384_neon_core_mc)]`
    montsqr_p384_eqin
    montsqr_p384_eqout
    bignum_montsqr_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montsqr_p384_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`;;

(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)

let inst_map = [
3;1;2;4;15;12;32;14;19;7;13;6;18;5;34;22;16;9;17;230;229;25;21;10;27;231;20;36;11;247;33;23;35;26;245;37;29;24;8;30;232;248;250;51;253;233;28;41;40;52;254;249;42;53;43;252;44;251;38;256;45;257;246;54;255;55;46;31;260;39;47;56;48;258;49;57;259;261;50;58;262;59;60;61;66;62;67;263;63;68;64;65;69;104;70;71;72;73;74;75;76;81;103;77;82;78;83;79;80;84;85;86;87;88;89;90;102;91;92;93;100;94;96;95;101;116;97;118;117;98;99;105;106;107;119;120;123;121;122;124;108;109;110;111;112;113;114;125;115;132;134;133;147;148;149;135;139;136;126;127;137;128;129;138;130;131;150;154;151;141;142;140;152;143;144;145;171;153;146;157;155;158;168;156;159;174;160;161;271;162;163;164;165;166;167;169;170;266;172;173;238;178;179;175;265;176;180;177;181;241;182;183;184;185;186;187;188;193;189;194;190;195;191;192;196;197;199;198;200;201;202;208;203;204;209;269;210;205;267;206;207;211;212;268;270;214;213;272;215;227;216;217;218;264;219;220;221;222;273;274;234;275;236;276;277;223;224;225;226;228;235;237;285;239;240;242;243;244;278;279;280;281;284;282;286;283;287;288;289;290;291;292;293;294;295;296;297;298;299;300;304;301;302;305;303;306];;


(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTSQR_P384_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTSQR_P384_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p384_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_MONTSQR_P384_NEON_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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
      [(word pc:int64,LENGTH bignum_montsqr_p384_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p384_neon_core_mc)]`
    montsqr_p384_eqin
    montsqr_p384_eqout
    bignum_montsqr_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montsqr_p384_neon_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS`;;

let montsqr_p384_eqout_TRANS = prove(
  `!s s2 s'
    z. montsqr_p384_eqout (s,s') z /\ montsqr_p384_eqout (s',s2) z
    ==> montsqr_p384_eqout (s,s2) z`,
  MESON_TAC[montsqr_p384_eqout]);;

let BIGNUM_MONTSQR_P384_CORE_EQUIV = time prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc:int64,LENGTH bignum_montsqr_p384_core_mc);
        (word pc3:int64,LENGTH bignum_montsqr_p384_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc3:int64,LENGTH bignum_montsqr_p384_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montsqr_p384_neon_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montsqr_p384_interm1_core_mc))
        [x,8 * 6] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTSQR_P384_NEON_CORE_EXEC;
       GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTSQR_P384_CORE_EQUIV1,BIGNUM_MONTSQR_P384_CORE_EQUIV2)
    (montsqr_p384_eqin,montsqr_p384_eqout_TRANS)
    (BIGNUM_MONTSQR_P384_CORE_EXEC,BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC,
     BIGNUM_MONTSQR_P384_NEON_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MONTSQR_P384_NEON_SUBROUTINE_CORRECT
          from BIGNUM_MONTSQR_P384_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTSQR_P384_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64,
        LENGTH (APPEND bignum_montsqr_p384_core_mc barrier_inst_bytes))
      (z:int64,8 * 6)`
    [`z:int64`;`x:int64`] bignum_montsqr_p384_core_mc
    `\s0. C_ARGUMENTS [z;x] s0`;;

let BIGNUM_MONTSQR_P384_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTSQR_P384_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montsqr_p384_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_MONTSQR_P384_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P384_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTSQR_P384_CORE_EXEC);;


let BIGNUM_MONTSQR_P384_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTSQR_P384_EXEC
    BIGNUM_MONTSQR_P384_CORE_EXEC
    BIGNUM_MONTSQR_P384_CORE_CORRECT
    BIGNUM_MONTSQR_P384_EVENTUALLY_N_AT_PC;;

(* This theorem is a copy of BIGNUM_MONTSQR_P384_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - bignum_montsqr_p384_core_mc with bignum_montsqr_p384_neon_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)

let BIGNUM_MONTSQR_P384_NEON_CORE_CORRECT = prove(
  `!z x a pc2.
        nonoverlapping (word pc2,LENGTH bignum_montsqr_p384_neon_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p384_neon_core_mc /\
                  read PC s = word pc2 /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p384_neon_core_mc) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program. This is going to be used
     for preparing an initial state by 'overwriting' bignum_montsqr_p384_mc
     at pc. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P384_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P384_CORE_EQUIV BIGNUM_MONTSQR_P384_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P384_CORE_EXEC,BIGNUM_MONTSQR_P384_NEON_CORE_EXEC)
    (montsqr_p384_eqin,montsqr_p384_eqout));;

let BIGNUM_MONTSQR_P384_NEON_CORRECT = time prove(
  `!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_neon_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_neon_mc /\
                  read PC s = word (pc) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_neon_core_mc) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P384_NEON_CORE_CORRECT
    bignum_montsqr_p384_neon_core_mc_def
    [fst BIGNUM_MONTSQR_P384_NEON_CORE_EXEC;
     fst BIGNUM_MONTSQR_P384_NEON_EXEC]);;

let BIGNUM_MONTSQR_P384_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_neon_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_neon_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[fst BIGNUM_MONTSQR_P384_NEON_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P384_NEON_EXEC
    (REWRITE_RULE [fst BIGNUM_MONTSQR_P384_NEON_EXEC;
        fst BIGNUM_MONTSQR_P384_NEON_CORE_EXEC]
      BIGNUM_MONTSQR_P384_NEON_CORRECT));;

(******************************************************************************
          Inducing BIGNUM_AMONTSQR_P384_NEON_SUBROUTINE_CORRECT
          from BIGNUM_AMONTSQR_P384_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTSQR_P384_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTSQR_P384_EXEC
    BIGNUM_MONTSQR_P384_CORE_EXEC
    BIGNUM_AMONTSQR_P384_CORE_CORRECT
    BIGNUM_MONTSQR_P384_EVENTUALLY_N_AT_PC;;

(* This theorem is a copy of BIGNUM_MONTSQR_P384_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montsqr_p384_core_mc with
    bignum_montsqr_p384_neon_core_m
  - The MAYCHANGE set replaced with the Neon version's one *)

let BIGNUM_AMONTSQR_P384_NEON_CORE_CORRECT = prove(
  `!z x a pc2.
        nonoverlapping (word pc2,LENGTH bignum_montsqr_p384_neon_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p384_neon_core_mc /\
                  read PC s = word pc2 /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p384_neon_core_mc) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2)
                   (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program. This is going to be used
     for preparing an initial state by 'overwriting' bignum_montsqr_p384_mc
     at pc. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P384_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P384_CORE_EQUIV BIGNUM_AMONTSQR_P384_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P384_CORE_EXEC,BIGNUM_MONTSQR_P384_NEON_CORE_EXEC)
    (montsqr_p384_eqin,montsqr_p384_eqout));;

let BIGNUM_AMONTSQR_P384_NEON_CORRECT = time prove(
  `!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_neon_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_neon_mc /\
                  read PC s = word (pc) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_neon_core_mc) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2)
                   (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTSQR_P384_NEON_CORE_CORRECT
    bignum_montsqr_p384_neon_core_mc_def
    [fst BIGNUM_MONTSQR_P384_NEON_CORE_EXEC;
     fst BIGNUM_MONTSQR_P384_NEON_EXEC]);;

let BIGNUM_AMONTSQR_P384_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_neon_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_neon_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2)
                  (mod p_384))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)])`,
  REWRITE_TAC[fst BIGNUM_MONTSQR_P384_NEON_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P384_NEON_EXEC
    (REWRITE_RULE [fst BIGNUM_MONTSQR_P384_NEON_EXEC;
        fst BIGNUM_MONTSQR_P384_NEON_CORE_EXEC]
      BIGNUM_AMONTSQR_P384_NEON_CORRECT));;

