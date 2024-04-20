(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  The first program equivalence between the source program and
  its SIMD-vectorized but not instruction-unscheduled program
******************************************************************************)

needs "arm/proofs/bignum_montmul_p256.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to both
   bignum_montmul_p256 and bignum_montmul_p256_neon. This is a vectorized
   version of bignum_montmul_p256 but instructions are unscheduled. *)

let bignum_montmul_p256_interm1_ops:int list = [
    0xa9403427; (* ldp      x7, x13, [x1] *)
    0x3dc00030; (* ldr      q16, [x1] *)
    0xa9413c29; (* ldp      x9, x15, [x1, #16] *)
    0xa940104e; (* ldp      x14, x4, [x2] *)
    0x3dc00053; (* ldr      q19, [x2] *)
    0xa941404c; (* ldp      x12, x16, [x2, #16] *)
    0x3dc0043d; (* ldr      q29, [x1, #16] *)
    0x3dc0045e; (* ldr      q30, [x2, #16] *)
    0x4e901a71; (* uzp1     v17.4s, v19.4s, v16.4s *)
    0x4ea00a72; (* rev64    v18.4s, v19.4s *)
    0x4e901a1c; (* uzp1     v28.4s, v16.4s, v16.4s *)
    0x4eb09e58; (* mul      v24.4s, v18.4s, v16.4s *)
    0x6ea02b12; (* uaddlp   v18.2d, v24.4s *)
    0x4f605650; (* shl      v16.2d, v18.2d, #32 *)
    0x2eb18390; (* umlal    v16.2d, v28.2s, v17.2s *)
    0x4e083e02; (* mov      x2, v16.d[0] *)
    0x4e183e01; (* mov      x1, v16.d[1] *)
    0x9bce7ce5; (* umulh    x5, x7, x14 *)
    0xab010051; (* adds     x17, x2, x1 *)
    0x9bc47da3; (* umulh    x3, x13, x4 *)
    0xba0300a8; (* adcs     x8, x5, x3 *)
    0xba1f006a; (* adcs     x10, x3, xzr *)
    0xab1100a5; (* adds     x5, x5, x17 *)
    0xba080021; (* adcs     x1, x1, x8 *)
    0xba1f0148; (* adcs     x8, x10, xzr *)
    0xeb0d00f1; (* subs     x17, x7, x13 *)
    0xda912623; (* cneg     x3, x17, cc  // cc = lo, ul, last *)
    0xda9f23eb; (* csetm    x11, cc  // cc = lo, ul, last *)
    0xeb0e008a; (* subs     x10, x4, x14 *)
    0xda8a2546; (* cneg     x6, x10, cc  // cc = lo, ul, last *)
    0x9b067c71; (* mul      x17, x3, x6 *)
    0x9bc67c66; (* umulh    x6, x3, x6 *)
    0xda8b216b; (* cinv     x11, x11, cc  // cc = lo, ul, last *)
    0xca0b0231; (* eor      x17, x17, x11 *)
    0xca0b00c3; (* eor      x3, x6, x11 *)
    0xb100057f; (* cmn      x11, #0x1 *)
    0xba1100a5; (* adcs     x5, x5, x17 *)
    0xba03002a; (* adcs     x10, x1, x3 *)
    0x9a0b0101; (* adc      x1, x8, x11 *)
    0xd3607c43; (* lsl      x3, x2, #32 *)
    0xeb030051; (* subs     x17, x2, x3 *)
    0xd360fc4b; (* lsr      x11, x2, #32 *)
    0xda0b0048; (* sbc      x8, x2, x11 *)
    0xab0300a2; (* adds     x2, x5, x3 *)
    0xba0b0146; (* adcs     x6, x10, x11 *)
    0xba110023; (* adcs     x3, x1, x17 *)
    0x9a1f010a; (* adc      x10, x8, xzr *)
    0xd3607c45; (* lsl      x5, x2, #32 *)
    0xeb050051; (* subs     x17, x2, x5 *)
    0xd360fc4b; (* lsr      x11, x2, #32 *)
    0xda0b0048; (* sbc      x8, x2, x11 *)
    0xab0500c2; (* adds     x2, x6, x5 *)
    0xba0b0066; (* adcs     x6, x3, x11 *)
    0xba110141; (* adcs     x1, x10, x17 *)
    0x9a1f0111; (* adc      x17, x8, xzr *)
    0xa9001802; (* stp      x2, x6, [x0] *)
    0xa9014401; (* stp      x1, x17, [x0, #16] *)
    0x6f00e5fc; (* movi     v28.2d, #0xffffffff *)
    0x4e9e5bd6; (* uzp2     v22.4s, v30.4s, v30.4s *)
    0x0ea12ba4; (* xtn      v4.2s, v29.2d *)
    0x0ea12bdb; (* xtn      v27.2s, v30.2d *)
    0x4ea00bd7; (* rev64    v23.4s, v30.4s *)
    0x2ebbc091; (* umull    v17.2d, v4.2s, v27.2s *)
    0x2eb6c087; (* umull    v7.2d, v4.2s, v22.2s *)
    0x4e9d5bb0; (* uzp2     v16.4s, v29.4s, v29.4s *)
    0x4ebd9efd; (* mul      v29.4s, v23.4s, v29.4s *)
    0x6f601627; (* usra     v7.2d, v17.2d, #32 *)
    0x2eb6c21e; (* umull    v30.2d, v16.2s, v22.2s *)
    0x6ea02bb4; (* uaddlp   v20.2d, v29.4s *)
    0x4e3c1cf2; (* and      v18.16b, v7.16b, v28.16b *)
    0x2ebb8212; (* umlal    v18.2d, v16.2s, v27.2s *)
    0x4f605690; (* shl      v16.2d, v20.2d, #32 *)
    0x6f6014fe; (* usra     v30.2d, v7.2d, #32 *)
    0x2ebb8090; (* umlal    v16.2d, v4.2s, v27.2s *)
    0x6f60165e; (* usra     v30.2d, v18.2d, #32 *)
    0x4e083e0b; (* mov      x11, v16.d[0] *)
    0x4e183e05; (* mov      x5, v16.d[1] *)
    0x4e083fc2; (* mov      x2, v30.d[0] *)
    0xab050163; (* adds     x3, x11, x5 *)
    0x4e183fd1; (* mov      x17, v30.d[1] *)
    0xba110048; (* adcs     x8, x2, x17 *)
    0xba1f0221; (* adcs     x1, x17, xzr *)
    0xab030051; (* adds     x17, x2, x3 *)
    0xba0800a8; (* adcs     x8, x5, x8 *)
    0xba1f0021; (* adcs     x1, x1, xzr *)
    0xeb0f0122; (* subs     x2, x9, x15 *)
    0xda822446; (* cneg     x6, x2, cc  // cc = lo, ul, last *)
    0xda9f23e3; (* csetm    x3, cc  // cc = lo, ul, last *)
    0xeb0c0202; (* subs     x2, x16, x12 *)
    0xda822445; (* cneg     x5, x2, cc  // cc = lo, ul, last *)
    0x9b057cca; (* mul      x10, x6, x5 *)
    0x9bc57cc5; (* umulh    x5, x6, x5 *)
    0xda832063; (* cinv     x3, x3, cc  // cc = lo, ul, last *)
    0xca03014a; (* eor      x10, x10, x3 *)
    0xca0300a6; (* eor      x6, x5, x3 *)
    0xb100047f; (* cmn      x3, #0x1 *)
    0xba0a0222; (* adcs     x2, x17, x10 *)
    0xba060106; (* adcs     x6, x8, x6 *)
    0x9a030025; (* adc      x5, x1, x3 *)
    0xeb070127; (* subs     x7, x9, x7 *)
    0xfa0d01e3; (* sbcs     x3, x15, x13 *)
    0xda1f03f1; (* ngc      x17, xzr *)
    0xb100063f; (* cmn      x17, #0x1 *)
    0xca1100e8; (* eor      x8, x7, x17 *)
    0xba1f010d; (* adcs     x13, x8, xzr *)
    0xca11006f; (* eor      x15, x3, x17 *)
    0xba1f01e1; (* adcs     x1, x15, xzr *)
    0xeb0c01c9; (* subs     x9, x14, x12 *)
    0xfa10008e; (* sbcs     x14, x4, x16 *)
    0xda1f03e3; (* ngc      x3, xzr *)
    0xb100047f; (* cmn      x3, #0x1 *)
    0xca03012c; (* eor      x12, x9, x3 *)
    0xba1f0187; (* adcs     x7, x12, xzr *)
    0xca0301cc; (* eor      x12, x14, x3 *)
    0xba1f018c; (* adcs     x12, x12, xzr *)
    0xca03022a; (* eor      x10, x17, x3 *)
    0xa9403c04; (* ldp      x4, x15, [x0] *)
    0xab040171; (* adds     x17, x11, x4 *)
    0xba0f0050; (* adcs     x16, x2, x15 *)
    0xa9413c03; (* ldp      x3, x15, [x0, #16] *)
    0xba0300cb; (* adcs     x11, x6, x3 *)
    0xba0f00a9; (* adcs     x9, x5, x15 *)
    0x9a1f03ee; (* adc      x14, xzr, xzr *)
    0x9b077da6; (* mul      x6, x13, x7 *)
    0x9b0c7c28; (* mul      x8, x1, x12 *)
    0x9bc77da5; (* umulh    x5, x13, x7 *)
    0xab0800c3; (* adds     x3, x6, x8 *)
    0x9bcc7c22; (* umulh    x2, x1, x12 *)
    0xba0200a4; (* adcs     x4, x5, x2 *)
    0xba1f004f; (* adcs     x15, x2, xzr *)
    0xab0300a3; (* adds     x3, x5, x3 *)
    0xba040104; (* adcs     x4, x8, x4 *)
    0xba1f01ef; (* adcs     x15, x15, xzr *)
    0xeb0101a1; (* subs     x1, x13, x1 *)
    0xda812428; (* cneg     x8, x1, cc  // cc = lo, ul, last *)
    0xda9f23e5; (* csetm    x5, cc  // cc = lo, ul, last *)
    0xeb070181; (* subs     x1, x12, x7 *)
    0xda812422; (* cneg     x2, x1, cc  // cc = lo, ul, last *)
    0x9b027d07; (* mul      x7, x8, x2 *)
    0x9bc27d02; (* umulh    x2, x8, x2 *)
    0xda8520ad; (* cinv     x13, x5, cc  // cc = lo, ul, last *)
    0xca0d00e7; (* eor      x7, x7, x13 *)
    0xca0d0042; (* eor      x2, x2, x13 *)
    0xb10005bf; (* cmn      x13, #0x1 *)
    0xba070063; (* adcs     x3, x3, x7 *)
    0xba020084; (* adcs     x4, x4, x2 *)
    0x9a0d01e5; (* adc      x5, x15, x13 *)
    0xb100055f; (* cmn      x10, #0x1 *)
    0xca0a00c8; (* eor      x8, x6, x10 *)
    0xba11010f; (* adcs     x15, x8, x17 *)
    0xca0a0062; (* eor      x2, x3, x10 *)
    0xba100042; (* adcs     x2, x2, x16 *)
    0xca0a0086; (* eor      x6, x4, x10 *)
    0xba0b00c3; (* adcs     x3, x6, x11 *)
    0xca0a00a7; (* eor      x7, x5, x10 *)
    0xba0900e1; (* adcs     x1, x7, x9 *)
    0xba0a01cd; (* adcs     x13, x14, x10 *)
    0xba1f014c; (* adcs     x12, x10, xzr *)
    0x9a1f014a; (* adc      x10, x10, xzr *)
    0xab110065; (* adds     x5, x3, x17 *)
    0xba100028; (* adcs     x8, x1, x16 *)
    0xba0b01ad; (* adcs     x13, x13, x11 *)
    0xba090186; (* adcs     x6, x12, x9 *)
    0x9a0e0144; (* adc      x4, x10, x14 *)
    0xd3607de9; (* lsl      x9, x15, #32 *)
    0xeb0901e7; (* subs     x7, x15, x9 *)
    0xd360fde1; (* lsr      x1, x15, #32 *)
    0xda0101ee; (* sbc      x14, x15, x1 *)
    0xab09004a; (* adds     x10, x2, x9 *)
    0xba0100af; (* adcs     x15, x5, x1 *)
    0xba070105; (* adcs     x5, x8, x7 *)
    0x9a1f01c7; (* adc      x7, x14, xzr *)
    0xd3607d4c; (* lsl      x12, x10, #32 *)
    0xeb0c0151; (* subs     x17, x10, x12 *)
    0xd360fd49; (* lsr      x9, x10, #32 *)
    0xda090143; (* sbc      x3, x10, x9 *)
    0xab0c01ec; (* adds     x12, x15, x12 *)
    0xba0900a5; (* adcs     x5, x5, x9 *)
    0xba1100ee; (* adcs     x14, x7, x17 *)
    0x9a1f0062; (* adc      x2, x3, xzr *)
    0xab0e01ae; (* adds     x14, x13, x14 *)
    0xba0200c6; (* adcs     x6, x6, x2 *)
    0x9a1f0091; (* adc      x17, x4, xzr *)
    0x91000627; (* add      x7, x17, #0x1 *)
    0xd3607cf0; (* lsl      x16, x7, #32 *)
    0xab1000c3; (* adds     x3, x6, x16 *)
    0x9a1f0221; (* adc      x1, x17, xzr *)
    0xcb0703ef; (* neg      x15, x7 *)
    0xd100060d; (* sub      x13, x16, #0x1 *)
    0xeb0f0189; (* subs     x9, x12, x15 *)
    0xfa0d00a8; (* sbcs     x8, x5, x13 *)
    0xfa1f01cf; (* sbcs     x15, x14, xzr *)
    0xfa070063; (* sbcs     x3, x3, x7 *)
    0xfa070027; (* sbcs     x7, x1, x7 *)
    0xab070124; (* adds     x4, x9, x7 *)
    0xb2407fe6; (* mov      x6, #0xffffffff                 // #4294967295 *)
    0x8a0700d1; (* and      x17, x6, x7 *)
    0xba110108; (* adcs     x8, x8, x17 *)
    0xba1f01e5; (* adcs     x5, x15, xzr *)
    0xb26083ea; (* mov      x10, #0xffffffff00000001        // #-4294967295 *)
    0x8a070141; (* and      x1, x10, x7 *)
    0x9a01006c; (* adc      x12, x3, x1 *)
    0xa9002004; (* stp      x4, x8, [x0] *)
    0xa9013005; (* stp      x5, x12, [x0, #16] *)
    0xd65f03c0; (* ret *)
];;

let bignum_montmul_p256_interm1_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_montmul_p256_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_montmul_p256_interm1_mc" (term_of_bytes byte_list);;

let BIGNUM_MONTMUL_P256_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p256_interm1_mc;;

let bignum_montmul_p256_interm1_core_mc_def,
    bignum_montmul_p256_interm1_core_mc,
    BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p256_interm1_core_mc"
    bignum_montmul_p256_interm1_mc
    (`0`,`LENGTH bignum_montmul_p256_interm1_mc - 4`)
    BIGNUM_MONTMUL_P256_INTERM1_EXEC;;

let equiv_input_states = new_definition
  `!s1 s1' x y z.
    (equiv_input_states:(armstate#armstate)->int64->int64->int64->bool) (s1,s1') x y z <=>
    (?a b.
      C_ARGUMENTS [z; x; y] s1 /\
      C_ARGUMENTS [z; x; y] s1' /\
      bignum_from_memory (x,4) s1 = a /\
      bignum_from_memory (x,4) s1' = a /\
      bignum_from_memory (y,4) s1 = b /\
      bignum_from_memory (y,4) s1' = b)`;;

let equiv_output_states = new_definition
  `!s1 s1' z.
    (equiv_output_states:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,4) s1 = a /\
      bignum_from_memory (z,4) s1' = a)`;;

(* This diff is generated by tools/diff.py. *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 3, 2, 4);
  ("insert", 3, 3, 4, 5);
  ("equal", 3, 4, 5, 6);
  ("replace", 4, 6, 6, 17);
  ("equal", 6, 46, 17, 57);
  ("replace", 46, 49, 57, 78);
  ("equal", 49, 50, 78, 79);
  ("replace", 50, 51, 79, 80);
  ("equal", 51, 175, 80, 204)
];;

let equiv_goal1 = mk_equiv_statement
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montmul_p256_mc);
       (word pc2:int64,LENGTH bignum_montmul_p256_interm1_mc)]`
    equiv_input_states
    equiv_output_states
    bignum_montmul_p256_core_mc 0
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montmul_p256_interm1_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`;;



let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTMUL_P256_EQUIV1 = prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    BIGNUM_MONTMUL_P256_EXEC;
    BIGNUM_MONTMUL_P256_CORE_EXEC;
    BIGNUM_MONTMUL_P256_INTERM1_EXEC;
    BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC equiv_input_states THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTMUL_P256_CORE_EXEC
    BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[equiv_output_states;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,4) state`;
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
  The second program equivalence between the intermediate program and
  fully optimized program
******************************************************************************)

let bignum_montmul_p256_neon_mc =
  define_from_elf "bignum_montmul_p256_neon_mc"
    "arm/p256/bignum_montmul_p256_neon.o";;

let BIGNUM_MONTMUL_P256_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p256_neon_mc;;

let bignum_montmul_p256_neon_core_mc_def,
    bignum_montmul_p256_neon_core_mc,
    BIGNUM_MONTMUL_P256_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p256_neon_core_mc"
    bignum_montmul_p256_neon_mc
    (`0`,`LENGTH bignum_montmul_p256_neon_mc - 4`)
    BIGNUM_MONTMUL_P256_NEON_EXEC;;


let equiv_goal2 = mk_equiv_statement
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montmul_p256_interm1_mc);
       (word pc2:int64,LENGTH bignum_montmul_p256_neon_mc)]`
    equiv_input_states
    equiv_output_states
    bignum_montmul_p256_interm1_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`
    bignum_montmul_p256_neon_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`;;

(* Line numbers from bignum_montmul_p256_neon_core_mc (the fully optimized
   prog.) to bignum_montmul_p256_interm1_core_mc (the intermediate prog.)
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)
let inst_map = [
  5;1;2;4;3;10;26;28;27;12;20;9;100;8;101;102;86;13;18;11;87;14;88;29;104;15;30;33;103;7;105;31;106;107;61;16;17;59;32;34;19;21;60;22;23;24;6;25;36;37;35;38;40;39;108;109;42;110;89;93;90;41;114;43;44;45;91;46;112;47;111;92;113;115;48;49;50;51;52;53;126;63;54;64;55;62;57;58;124;66;134;65;136;67;125;68;135;69;137;70;128;72;138;71;141;74;127;139;95;129;56;73;130;140;131;132;142;75;133;144;77;145;143;146;76;80;78;147;79;81;117;82;83;94;84;85;96;120;97;98;99;118;119;116;121;149;122;123;148;151;150;153;152;154;155;196;156;167;157;158;159;160;161;162;163;165;164;166;168;169;170;173;171;175;172;174;176;177;178;179;180;181;182;183;184;188;185;186;189;187;190;191;192;193;194;200;195;197;198;201;203;199;202;204
];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTMUL_P256_EQUIV2 = prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    BIGNUM_MONTMUL_P256_INTERM1_EXEC;
    BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC;
    BIGNUM_MONTMUL_P256_NEON_EXEC;
    BIGNUM_MONTMUL_P256_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC equiv_input_states THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC
    (1--204) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_MONTMUL_P256_NEON_CORE_EXEC
    (1--204) inst_map state_to_abbrevs THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[equiv_output_states;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,4) state`;
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

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montmul_p256_mc);
       (word pc2:int64,LENGTH bignum_montmul_p256_neon_mc)]`
    equiv_input_states
    equiv_output_states
    bignum_montmul_p256_core_mc 0
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montmul_p256_neon_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`;;

let equiv_output_states_TRANS = prove(
  `!s s2 s'
    z. equiv_output_states (s,s') z /\ equiv_output_states (s',s2) z
    ==> equiv_output_states (s,s2) z`,
  MESON_TAC[equiv_output_states]);;

let BIGNUM_MONTMUL_P256_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * 4))
        [word pc:int64, LENGTH bignum_montmul_p256_mc;
         word pc3:int64, LENGTH bignum_montmul_p256_interm1_mc] /\
      ALL (nonoverlapping (z,8 * 4))
        [word pc3:int64, LENGTH bignum_montmul_p256_interm1_mc;
         word pc2:int64, LENGTH bignum_montmul_p256_neon_mc] /\
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montmul_p256_interm1_mc))
        [x,8 * 4; y,8 * 4] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       BIGNUM_MONTMUL_P256_INTERM1_EXEC;BIGNUM_MONTMUL_P256_NEON_EXEC;
       BIGNUM_MONTMUL_P256_EXEC;GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC_ALL (MATCH_MP BIGNUM_MONTMUL_P256_EQUIV1 th))) THEN
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC_ALL (MATCH_MP BIGNUM_MONTMUL_P256_EQUIV2 th))) THEN
  FIRST_X_ASSUM (fun c1 ->
    FIRST_X_ASSUM (fun c2 ->
      MP_TAC (REWRITE_RULE [] (MATCH_MP ENSURES2_CONJ2 (CONJ c1 c2)))
    )) THEN

  (* break 'ALL nonoverlapping' in assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE[
      ALLPAIRS;ALL;
      BIGNUM_MONTMUL_P256_EXEC;
      BIGNUM_MONTMUL_P256_NEON_EXEC;
      BIGNUM_MONTMUL_P256_INTERM1_EXEC;
      NONOVERLAPPING_CLAUSES]) THEN
  SPLIT_FIRST_CONJ_ASSUM_TAC THEN

  MATCH_MP_TAC ENSURES2_WEAKEN THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ q /\ r) /\ p /\ q /\ r' <=> p /\ q /\ r /\ r'`] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc3,LENGTH bignum_montmul_p256_interm1_core_mc))
          bignum_montmul_p256_interm1_core_mc
          (write PC (word pc3) s')` THEN
    PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC THENL [
      UNDISCH_TAC `equiv_input_states (s,s') x y z` THEN
      REWRITE_TAC[equiv_input_states;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`a:num`;`b:num`] THEN
      REWRITE_TAC[] THEN
      PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC;

      UNDISCH_TAC `equiv_input_states (s,s') x y z` THEN
      REWRITE_TAC[equiv_input_states;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`a:num`;`b:num`] THEN
      REWRITE_TAC[] THEN
      PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTMUL_P256_INTERM1_CORE_EXEC
    ];

    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[equiv_output_states_TRANS];

    SUBSUMED_MAYCHANGE_TAC
  ]);;




let event_n_at_pc_goal = mk_eventually_n_at_pc_statement
    `nonoverlapping (word pc:int64,LENGTH bignum_montmul_p256_mc)
                    (z:int64,8 * 4)`
    [`z:int64`;`x:int64`;`y:int64`] (*pc_mc_ofs*)0 bignum_montmul_p256_core_mc (*pc_ofs*)0
    `\s0. C_ARGUMENTS [z;x;y] s0`;;

let BIGNUM_MONTMUL_P256_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;BIGNUM_MONTMUL_P256_CORE_EXEC;
              BIGNUM_MONTMUL_P256_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montmul_p256_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              BIGNUM_MONTMUL_P256_CORE_EXEC]) THENL [
    REWRITE_TAC[BIGNUM_MONTMUL_P256_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT_N 4 GEN_TAC THEN
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTMUL_P256_CORE_EXEC);;


(******************************************************************************
          Inducing BIGNUM_MONTMUL_P256_NEON_SUBROUTINE_CORRECT
          from BIGNUM_MONTMUL_P256_CORE_CORRECT
******************************************************************************)

let BIGNUM_MONTMUL_P256_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTMUL_P256_EXEC
    BIGNUM_MONTMUL_P256_CORE_EXEC
    BIGNUM_MONTMUL_P256_CORE_CORRECT
    BIGNUM_MONTMUL_P256_EVENTUALLY_N_AT_PC;;


let BIGNUM_MONTMUL_P256_NEON_CORE_CORRECT = prove(
  `!z x a pc2.
    nonoverlapping (word pc2,LENGTH bignum_montmul_p256_neon_mc) (z,8 * 4)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p256_neon_core_mc /\
              read PC s = word pc2 /\
              C_ARGUMENTS [z; x; y] s /\
              bignum_from_memory (x,4) s = a /\
              bignum_from_memory (y,4) s = b)
          (\s. read PC s = word (pc2 + 816) /\
               (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (z:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (x:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (y:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[BIGNUM_MONTMUL_P256_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    CONV_TAC (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  VCGEN_EQUIV_TAC BIGNUM_MONTMUL_P256_EQUIV BIGNUM_MONTMUL_P256_CORE_CORRECT_N
    [BIGNUM_MONTMUL_P256_EXEC;NONOVERLAPPING_CLAUSES] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[NONOVERLAPPING_CLAUSES;BIGNUM_MONTMUL_P256_EXEC;
             BIGNUM_MONTMUL_P256_NEON_EXEC]) THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[equiv_input_states] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND bignum_montmul_p256_core_mc barrier_inst_bytes)))
          (APPEND bignum_montmul_p256_core_mc barrier_inst_bytes)
          (write PC (word pc) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTMUL_P256_CORE_EXEC) THEN
    (* Now has only one subgoal: the equivalence! *)
    REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY EXISTS_TAC [`a:num`;`b:num`] THEN
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTMUL_P256_CORE_EXEC);

    (** SUBGOAL 2. Postcond **)
    MESON_TAC[equiv_output_states;BIGNUM_FROM_MEMORY_BYTES];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
  ]);;

let BIGNUM_MONTMUL_P256_NEON_CORRECT = time prove
 (`!z x y a b pc.
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_neon_mc) (z,8 * 4)
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_neon_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [z; x; y] s /\
               bignum_from_memory (x,4) s = a /\
               bignum_from_memory (y,4) s = b)
          (\s. read PC s = word (pc + 816) /\
                (a * b <= 2 EXP 256 * p_256
                    ==> bignum_from_memory (z,4) s =
                        (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP BIGNUM_MONTMUL_P256_NEON_CORE_CORRECT th)) THEN
      REWRITE_TAC[ensures] THEN
      DISCH_THEN (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
  EXISTS_TAC `x:int64` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bignum_montmul_p256_neon_core_mc_def;BIGNUM_MONTMUL_P256_NEON_EXEC;
      WORD_RULE`word (x+y)=word_add (word x) (word y)`] THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ONCE_REWRITE_TAC[WORD_RULE `word pc:int64 = word_add (word pc) (word 0)`] THEN
  ASM_SIMP_TAC[ALIGNED_BYTES_LOADED_SUB_LIST;WORD_ADD_0;NUM_DIVIDES_CONV`4 divides 0`]);;

let BIGNUM_MONTMUL_P256_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_neon_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_neon_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[BIGNUM_MONTMUL_P256_NEON_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_P256_NEON_EXEC
    (REWRITE_RULE[BIGNUM_MONTMUL_P256_NEON_EXEC] BIGNUM_MONTMUL_P256_NEON_CORRECT));;


(******************************************************************************
          Inducing BIGNUM_AMONTMUL_P256_NEON_SUBROUTINE_CORRECT
          from BIGNUM_AMONTMUL_P256_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTMUL_P256_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTMUL_P256_EXEC
    BIGNUM_MONTMUL_P256_CORE_EXEC
    BIGNUM_AMONTMUL_P256_CORE_CORRECT
    BIGNUM_MONTMUL_P256_EVENTUALLY_N_AT_PC;;

let BIGNUM_AMONTMUL_P256_NEON_CORE_CORRECT = prove(
  `!z x y a b pc2.
        nonoverlapping (word pc2,LENGTH bignum_montmul_p256_neon_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p256_neon_core_mc /\
                  read PC s = word pc2 /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc2 + 816) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (z:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (x:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p256_mc) (y:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[BIGNUM_MONTMUL_P256_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    CONV_TAC (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN
  
  VCGEN_EQUIV_TAC BIGNUM_MONTMUL_P256_EQUIV BIGNUM_AMONTMUL_P256_CORE_CORRECT_N
    [BIGNUM_MONTMUL_P256_EXEC;NONOVERLAPPING_CLAUSES] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[NONOVERLAPPING_CLAUSES;BIGNUM_MONTMUL_P256_EXEC;
             BIGNUM_MONTMUL_P256_NEON_EXEC]) THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[equiv_input_states] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND bignum_montmul_p256_core_mc barrier_inst_bytes)))
          (APPEND bignum_montmul_p256_core_mc barrier_inst_bytes)
          (write PC (word pc) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTMUL_P256_CORE_EXEC) THEN
    (* Now has only one subgoal: the equivalence! *)
    REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY EXISTS_TAC [`a:num`;`b:num`] THEN
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTMUL_P256_CORE_EXEC);

    (** SUBGOAL 2. Postcond **)
    MESON_TAC[equiv_output_states;BIGNUM_FROM_MEMORY_BYTES];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
  ]);;
  
let BIGNUM_AMONTMUL_P256_NEON_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_neon_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_neon_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + 816) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP BIGNUM_AMONTMUL_P256_NEON_CORE_CORRECT th)) THEN
        REWRITE_TAC[ensures] THEN
        DISCH_THEN (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
    MAP_EVERY EXISTS_TAC [`x:int64`;`y:int64`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_montmul_p256_neon_core_mc_def;BIGNUM_MONTMUL_P256_NEON_EXEC;
        WORD_RULE`word (x+y)=word_add (word x) (word y)`] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    ONCE_REWRITE_TAC[WORD_RULE `word pc:int64 = word_add (word pc) (word 0)`] THEN
    ASM_SIMP_TAC[ALIGNED_BYTES_LOADED_SUB_LIST;WORD_ADD_0;NUM_DIVIDES_CONV`4 divides 0`]);;

let BIGNUM_AMONTMUL_P256_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montmul_p256_neon_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p256_neon_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a * b) (mod p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[BIGNUM_MONTMUL_P256_NEON_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_P256_NEON_EXEC
    (REWRITE_RULE[BIGNUM_MONTMUL_P256_NEON_EXEC] BIGNUM_AMONTMUL_P256_NEON_CORRECT));;

