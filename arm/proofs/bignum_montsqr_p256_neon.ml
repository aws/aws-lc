(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  The first program equivalence between the source program and
  its SIMD-vectorized but not instruction-unscheduled program
******************************************************************************)

needs "arm/proofs/bignum_montsqr_p256.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* This is the intermediate program that is equivalent to both
   bignum_montsqr_p256 and bignum_montsqr_p256_neon. This is a vectorized
   version of bignum_montsqr_p256 but instructions are unscheduled. *)

let bignum_montsqr_p256_interm1_ops:int list = [
    0xa9400c27; (* ldp      x7, x3, [x1] *)
    0x3dc00026; (* ldr      q6, [x1] *)
    0xa9412029; (* ldp      x9, x8, [x1, #16] *)
    0x3dc00432; (* ldr      q18, [x1, #16] *)
    0x3dc0003b; (* ldr      q27, [x1] *)
    0x2ebbc370; (* umull    v16.2d, v27.2s, v27.2s *)
    0x6ebbc371; (* umull2   v17.2d, v27.4s, v27.4s *)
    0x0ea12b7e; (* xtn      v30.2s, v27.2d *)
    0x4e9b5b7b; (* uzp2     v27.4s, v27.4s, v27.4s *)
    0x2ebec37b; (* umull    v27.2d, v27.2s, v30.2s *)
    0x4e083e06; (* mov      x6, v16.d[0] *)
    0x4e183e0c; (* mov      x12, v16.d[1] *)
    0x4e083e2d; (* mov      x13, v17.d[0] *)
    0x4e183e21; (* mov      x1, v17.d[1] *)
    0x4e083f6f; (* mov      x15, v27.d[0] *)
    0x4e183f6a; (* mov      x10, v27.d[1] *)
    0xab0f84c4; (* adds     x4, x6, x15, lsl #33 *)
    0xd35ffde6; (* lsr      x6, x15, #31 *)
    0x9a06018f; (* adc      x15, x12, x6 *)
    0xab0a85ad; (* adds     x13, x13, x10, lsl #33 *)
    0xd35ffd46; (* lsr      x6, x10, #31 *)
    0x9a06002c; (* adc      x12, x1, x6 *)
    0x9b037ce6; (* mul      x6, x7, x3 *)
    0x9bc37ce1; (* umulh    x1, x7, x3 *)
    0xab0605e5; (* adds     x5, x15, x6, lsl #1 *)
    0x93c6fc26; (* extr     x6, x1, x6, #63 *)
    0xba0601aa; (* adcs     x10, x13, x6 *)
    0xd37ffc26; (* lsr      x6, x1, #63 *)
    0x9a06018f; (* adc      x15, x12, x6 *)
    0xd3607c86; (* lsl      x6, x4, #32 *)
    0xeb06008d; (* subs     x13, x4, x6 *)
    0xd360fc8c; (* lsr      x12, x4, #32 *)
    0xda0c0081; (* sbc      x1, x4, x12 *)
    0xab0600a6; (* adds     x6, x5, x6 *)
    0xba0c0145; (* adcs     x5, x10, x12 *)
    0xba0d01ea; (* adcs     x10, x15, x13 *)
    0x9a1f002f; (* adc      x15, x1, xzr *)
    0xd3607ccd; (* lsl      x13, x6, #32 *)
    0xeb0d00cc; (* subs     x12, x6, x13 *)
    0xd360fcc1; (* lsr      x1, x6, #32 *)
    0xda0100c6; (* sbc      x6, x6, x1 *)
    0xab0d00b0; (* adds     x16, x5, x13 *)
    0xba01014b; (* adcs     x11, x10, x1 *)
    0xba0c01e2; (* adcs     x2, x15, x12 *)
    0x9a1f00d1; (* adc      x17, x6, xzr *)
    0x4e861a5e; (* uzp1     v30.4s, v18.4s, v6.4s *)
    0x4ea00a5b; (* rev64    v27.4s, v18.4s *)
    0x4e8618d2; (* uzp1     v18.4s, v6.4s, v6.4s *)
    0x4ea69f7b; (* mul      v27.4s, v27.4s, v6.4s *)
    0x6ea02b65; (* uaddlp   v5.2d, v27.4s *)
    0x4f6054a6; (* shl      v6.2d, v5.2d, #32 *)
    0x2ebe8246; (* umlal    v6.2d, v18.2s, v30.2s *)
    0x4e083cc4; (* mov      x4, v6.d[0] *)
    0x4e183cc5; (* mov      x5, v6.d[1] *)
    0x9bc97cea; (* umulh    x10, x7, x9 *)
    0xeb0300e6; (* subs     x6, x7, x3 *)
    0xda8624cd; (* cneg     x13, x6, cc  // cc = lo, ul, last *)
    0xda9f23ec; (* csetm    x12, cc  // cc = lo, ul, last *)
    0xeb090106; (* subs     x6, x8, x9 *)
    0xda8624c6; (* cneg     x6, x6, cc  // cc = lo, ul, last *)
    0x9b067da1; (* mul      x1, x13, x6 *)
    0x9bc67da6; (* umulh    x6, x13, x6 *)
    0xda8c218f; (* cinv     x15, x12, cc  // cc = lo, ul, last *)
    0xca0f002c; (* eor      x12, x1, x15 *)
    0xca0f00cd; (* eor      x13, x6, x15 *)
    0xab0a0081; (* adds     x1, x4, x10 *)
    0x9a1f0146; (* adc      x6, x10, xzr *)
    0x9bc87c63; (* umulh    x3, x3, x8 *)
    0xab050021; (* adds     x1, x1, x5 *)
    0xba0300c6; (* adcs     x6, x6, x3 *)
    0x9a1f0063; (* adc      x3, x3, xzr *)
    0xab0500c6; (* adds     x6, x6, x5 *)
    0x9a1f0063; (* adc      x3, x3, xzr *)
    0xb10005ff; (* cmn      x15, #0x1 *)
    0xba0c002c; (* adcs     x12, x1, x12 *)
    0xba0d00c1; (* adcs     x1, x6, x13 *)
    0x9a0f0063; (* adc      x3, x3, x15 *)
    0xab040086; (* adds     x6, x4, x4 *)
    0xba0c018d; (* adcs     x13, x12, x12 *)
    0xba01002c; (* adcs     x12, x1, x1 *)
    0xba030061; (* adcs     x1, x3, x3 *)
    0x9a1f03e3; (* adc      x3, xzr, xzr *)
    0xab1000c6; (* adds     x6, x6, x16 *)
    0xba0b01a5; (* adcs     x5, x13, x11 *)
    0xba02018a; (* adcs     x10, x12, x2 *)
    0xba11002f; (* adcs     x15, x1, x17 *)
    0x9a1f006d; (* adc      x13, x3, xzr *)
    0xd3607cc3; (* lsl      x3, x6, #32 *)
    0xeb0300cc; (* subs     x12, x6, x3 *)
    0xd360fcc1; (* lsr      x1, x6, #32 *)
    0xda0100c6; (* sbc      x6, x6, x1 *)
    0xab0300a3; (* adds     x3, x5, x3 *)
    0xba010145; (* adcs     x5, x10, x1 *)
    0xba0c01ef; (* adcs     x15, x15, x12 *)
    0xba0601ad; (* adcs     x13, x13, x6 *)
    0x9a1f03ea; (* adc      x10, xzr, xzr *)
    0xd3607c66; (* lsl      x6, x3, #32 *)
    0xeb06006c; (* subs     x12, x3, x6 *)
    0xd360fc61; (* lsr      x1, x3, #32 *)
    0xda010063; (* sbc      x3, x3, x1 *)
    0xab0600a6; (* adds     x6, x5, x6 *)
    0xba0101ef; (* adcs     x15, x15, x1 *)
    0xba0c01ad; (* adcs     x13, x13, x12 *)
    0xba03014c; (* adcs     x12, x10, x3 *)
    0x9a1f03e1; (* adc      x1, xzr, xzr *)
    0x9b097d23; (* mul      x3, x9, x9 *)
    0xab0300c5; (* adds     x5, x6, x3 *)
    0x9b087d06; (* mul      x6, x8, x8 *)
    0x9bc97d23; (* umulh    x3, x9, x9 *)
    0xba0301ef; (* adcs     x15, x15, x3 *)
    0xba0601ad; (* adcs     x13, x13, x6 *)
    0x9bc87d03; (* umulh    x3, x8, x8 *)
    0xba03018c; (* adcs     x12, x12, x3 *)
    0x9a1f0021; (* adc      x1, x1, xzr *)
    0x9b087d26; (* mul      x6, x9, x8 *)
    0x9bc87d23; (* umulh    x3, x9, x8 *)
    0xab0600c8; (* adds     x8, x6, x6 *)
    0xba030069; (* adcs     x9, x3, x3 *)
    0x9a1f03e3; (* adc      x3, xzr, xzr *)
    0xab0801ea; (* adds     x10, x15, x8 *)
    0xba0901af; (* adcs     x15, x13, x9 *)
    0xba03018d; (* adcs     x13, x12, x3 *)
    0xba1f002c; (* adcs     x12, x1, xzr *)
    0xb2407fe3; (* mov      x3, #0xffffffff                 // #4294967295 *)
    0xb10004a6; (* adds     x6, x5, #0x1 *)
    0xfa030148; (* sbcs     x8, x10, x3 *)
    0xb26083e3; (* mov      x3, #0xffffffff00000001         // #-4294967295 *)
    0xfa1f01e9; (* sbcs     x9, x15, xzr *)
    0xfa0301a1; (* sbcs     x1, x13, x3 *)
    0xfa1f019f; (* sbcs     xzr, x12, xzr *)
    0x9a8520c6; (* csel     x6, x6, x5, cs  // cs = hs, nlast *)
    0x9a8a2108; (* csel     x8, x8, x10, cs  // cs = hs, nlast *)
    0x9a8f2129; (* csel     x9, x9, x15, cs  // cs = hs, nlast *)
    0x9a8d2023; (* csel     x3, x1, x13, cs  // cs = hs, nlast *)
    0xa9002006; (* stp      x6, x8, [x0] *)
    0xa9010c09; (* stp      x9, x3, [x0, #16] *)
    0xd65f03c0; (* ret *)
];;

let bignum_montsqr_p256_interm1_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    bignum_montsqr_p256_interm1_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "bignum_montsqr_p256_interm1_mc" (term_of_bytes byte_list);;

let BIGNUM_MONTSQR_P256_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p256_interm1_mc;;

let bignum_montsqr_p256_interm1_core_mc_def,
    bignum_montsqr_p256_interm1_core_mc,
    BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p256_interm1_core_mc"
    bignum_montsqr_p256_interm1_mc
    (`0`,`LENGTH bignum_montsqr_p256_interm1_mc - 4`)
    BIGNUM_MONTSQR_P256_INTERM1_EXEC;;


let equiv_input_states = new_definition
  `!s1 s1' x z.
    (equiv_input_states:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
    (?a.
      C_ARGUMENTS [z; x] s1 /\
      C_ARGUMENTS [z; x] s1' /\
      bignum_from_memory (x,4) s1 = a /\
      bignum_from_memory (x,4) s1' = a)`;;

let equiv_output_states = new_definition
  `!s1 s1' z.
    (equiv_output_states:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,4) s1 = a /\
      bignum_from_memory (z,4) s1' = a)`;;

(* This diff is generated by tools/diff.py, then splitted into two
   lists to manually apply necessary equality rules on words. *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 2, 2, 3);
  ("replace", 2, 24, 3, 29);
];;

let actions2 = [
  ("equal", 24, 40, 29, 45);
  ("replace", 40, 42, 45, 54);
  ("equal", 42, 124, 54, 136);
];;

let equiv_goal1 = mk_equiv_statement
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montsqr_p256_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p256_interm1_mc)]`
    equiv_input_states
    equiv_output_states
    bignum_montsqr_p256_core_mc 0
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montsqr_p256_interm1_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`;;


let lemma1 = prove(`!(x:int64).
  (word_mul
        (word_zx (word_subword x (0,32):int32):int64)
        (word_zx (word_subword x (0,32):int32):int64)) =
  word (0 +
       val ((word_zx:(64)word->(32)word) x) *
       val ((word_zx:(64)word->(32)word) x))`,
  CONV_TAC WORD_BLAST);;

let lemma2 = prove(`!(x:int64).
  (word_mul
        (word_zx (word_subword x (32,32):int32):int64)
        (word_zx (word_subword x (0,32):int32)):int64) =
  word (0 +
        val ((word_zx:(64)word->(32)word) x) *
        val ((word_zx:(64)word->(32)word) (word_ushr x 32)))`,
  CONV_TAC WORD_BLAST);;

let lemma3 = prove (`!(x:int64). word_add x x = word_shl x 1`,
  CONV_TAC WORD_BLAST);;

let lemma4 = prove (`!(x:int64).
 (word_mul
   ((word_zx:(32)word->(64)word) (word_subword x (32,32)))
  ((word_zx:(32)word->(64)word) (word_subword x (32,32)))) =
 (word (0 +
   val ((word_zx:(64)word->(32)word) (word_ushr x 32)) *
   val ((word_zx:(64)word->(32)word) (word_ushr x 32))))`,
  CONV_TAC WORD_BLAST);;

let pth = prove(
  `(val (x:int64) * val (y:int64)) MOD 2 EXP 128 = val (x:int64) * val (y:int64)`,
  IMP_REWRITE_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE`2 EXP 128 = 2 EXP 64 * 2 EXP 64`] THEN
  MAP_EVERY (fun t -> ASSUME_TAC (SPEC t VAL_BOUND_64)) [`x:int64`;`y:int64`] THEN
  IMP_REWRITE_TAC[LT_MULT2]);;

let lemma5 = prove (
 `!(a'_0:int64) (a'_1:int64).
    (word_add
      (word_shl
        ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64))
        1)
      ((word:num->(64)word)
        (bitval
          (2 EXP 64 <=
          val
            ((word:num->(64)word) (0 + val a'_0 * val a'_1)) +
          val
            ((word:num->(64)word) (0 + val a'_0 * val a'_1)))))) =
 
    ((word_subword:(128)word->num#num->(64)word)
      ((word_join:(64)word->(64)word->(128)word)
        (word ((val a'_0 * val a'_1) DIV 2 EXP 64))
        (word (0 + val a'_0 * val a'_1)))
      (63,64))`,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?(a:int128). val a = val (a'_0:int64) * val (a'_1:int64)` MP_TAC THENL [
    EXISTS_TAC `word(val (a'_0:int64) * val (a'_1:int64)):int128` THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_128;pth];
    ALL_TAC
  ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[bitval; WORD_BLAST
    `val(a:int128) DIV 2 EXP 64 = val(word_ushr a 64)`] THEN
  SPEC_TAC (`a:int128`,`a:int128`) THEN
  BITBLAST_TAC);;

let lemma6 = prove(
  `!(a'_0:int64) (a'_1:int64).
    ((word:num->(64)word)
      (bitval
        (2 EXP 64 <=
          val ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64)) +
          val ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64)) +
          bitval
            (2 EXP 64 <=
              val ((word:num->(64)word) (0 + val a'_0 * val a'_1)) +
              val ((word:num->(64)word) (0 + val a'_0 * val a'_1)))))) =

    (word_ushr
      ((word:num->(64)word) ((val a'_0 * val a'_1) DIV 2 EXP 64))
      63)`,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?(a:int128). val a = val (a'_0:int64) * val (a'_1:int64)` MP_TAC THENL [
    EXISTS_TAC `word(val (a'_0:int64) * val (a'_1:int64)):int128` THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_128;pth];
    ALL_TAC
  ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM (fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[bitval; WORD_BLAST
    `val(a:int128) DIV 2 EXP 64 = val(word_ushr a 64)`] THEN
  SPEC_TAC (`a:int128`,`a:int128`) THEN
  BITBLAST_TAC);;



let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_SQR64_LO; WORD_SQR64_HI;
                       WORD_MUL64_LO]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTSQR_P256_EQUIV1 = prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    BIGNUM_MONTSQR_P256_EXEC;BIGNUM_MONTSQR_P256_CORE_EXEC;
    BIGNUM_MONTSQR_P256_INTERM1_EXEC;
    BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC equiv_input_states THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTSQR_P256_CORE_EXEC
    BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC THEN
  
  (* checker:
  (fun (asl,g) ->
    let a = List.filter (fun (_,th) ->
      let t = concl th in
      if not (is_eq t) then false else
      let lhs = fst (dest_eq t) in
      lhs = `read X15 s24` || lhs = `read X4 s29'`) asl in
    if not (snd (dest_eq (concl (snd (List.nth a 0)))) =
            snd (dest_eq (concl (snd (List.nth a 1))))) then
      failwith ".."
    else ALL_TAC (asl,g))
    *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    lemma1;lemma2; (* X15 of prog1 = X4 of prog2 *)
    lemma3;lemma4; (* X16 of prog1 = X5 of prog2 *)
    lemma5; (* X17 of prog1 = X10 of prog2 *)
    lemma6; (* X1 of prog1 = X15 of prog2 *)
    ]) THEN

  EQUIV_STEPS_TAC actions2
    BIGNUM_MONTSQR_P256_CORE_EXEC
    BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC THEN

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

let bignum_montsqr_p256_neon_mc =
  define_from_elf "bignum_montsqr_p256_neon_mc"
    "arm/p256/bignum_montsqr_p256_neon.o";;

let BIGNUM_MONTSQR_P256_NEON_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p256_neon_mc;;

let bignum_montsqr_p256_neon_core_mc_def,
    bignum_montsqr_p256_neon_core_mc,
    BIGNUM_MONTSQR_P256_NEON_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p256_neon_core_mc"
    bignum_montsqr_p256_neon_mc
    (`0`,`LENGTH bignum_montsqr_p256_neon_mc - 4`)
    BIGNUM_MONTSQR_P256_NEON_EXEC;;


let equiv_goal2 = mk_equiv_statement
    `ALL (nonoverlapping (z:int64,8 * 4))
      [(word pc:int64,LENGTH bignum_montsqr_p256_interm1_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p256_neon_mc)]`
    equiv_input_states
    equiv_output_states
    bignum_montsqr_p256_interm1_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`
    bignum_montsqr_p256_neon_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`;;

(* Line numbers from bignum_montmul_p256_neon_core_mc (the fully optimized
   prog.) to bignum_montmul_p256_interm1_core_mc (the intermediate prog.)
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)
let inst_map = [
  5;1;4;2;3;9;8;24;47;6;10;49;56;55;12;7;11;46;50;28;23;15;58;57;14;13;59;16;60;63;17;26;18;48;51;19;20;21;30;52;22;25;32;62;27;29;31;33;34;53;61;35;38;68;36;40;37;39;41;42;54;43;116;44;65;45;66;67;69;64;115;70;71;72;73;74;108;75;76;112;77;78;79;80;81;82;83;106;84;90;85;88;109;86;124;87;117;118;127;119;89;91;92;93;97;99;94;95;96;98;100;101;102;103;104;105;107;110;111;113;114;120;121;122;123;125;126;128;129;130;131;133;134;132;136;135;137
];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTSQR_P256_EQUIV2 = prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    BIGNUM_MONTSQR_P256_INTERM1_EXEC;BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC;
    BIGNUM_MONTSQR_P256_NEON_EXEC;
    BIGNUM_MONTSQR_P256_NEON_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC equiv_input_states THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  (* necessary to run ldr qs *)
  COMBINE_READ_BYTES64_PAIRS_TAC THEN

  (* Left *)
  ARM_STEPS'_AND_ABBREV_TAC BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC (1--136) state_to_abbrevs THEN

  (* Right *)
  ARM_STEPS'_AND_REWRITE_TAC BIGNUM_MONTSQR_P256_NEON_CORE_EXEC (1--136) inst_map state_to_abbrevs THEN

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
      [(word pc:int64,LENGTH bignum_montsqr_p256_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p256_neon_mc)]`
    equiv_input_states
    equiv_output_states
    bignum_montsqr_p256_core_mc 0
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
     MAYCHANGE SOME_FLAGS`
    bignum_montsqr_p256_neon_core_mc 0
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(z,8 * 4)]`;;

let equiv_output_states_TRANS = prove(
  `!s s2 s'
    z. equiv_output_states (s,s') z /\ equiv_output_states (s',s2) z
    ==> equiv_output_states (s,s2) z`,
  MESON_TAC[equiv_output_states]);;

let BIGNUM_MONTSQR_P256_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * 4))
        [word pc:int64, LENGTH bignum_montsqr_p256_mc;
         word pc3:int64, LENGTH bignum_montsqr_p256_interm1_mc] /\
      ALL (nonoverlapping (z,8 * 4))
        [word pc3:int64, LENGTH bignum_montsqr_p256_interm1_mc;
         word pc2:int64, LENGTH bignum_montsqr_p256_neon_mc] /\
      nonoverlapping (x,8 * 4)
        (word pc3:int64, LENGTH bignum_montsqr_p256_interm1_mc) /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       BIGNUM_MONTSQR_P256_INTERM1_EXEC;BIGNUM_MONTSQR_P256_NEON_EXEC;
       BIGNUM_MONTSQR_P256_EXEC;GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC_ALL (MATCH_MP BIGNUM_MONTSQR_P256_EQUIV1 th))) THEN
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC_ALL (MATCH_MP BIGNUM_MONTSQR_P256_EQUIV2 th))) THEN
  FIRST_X_ASSUM (fun c1 ->
    FIRST_X_ASSUM (fun c2 ->
      MP_TAC (REWRITE_RULE [] (MATCH_MP ENSURES2_CONJ2 (CONJ c1 c2)))
    )) THEN

  (* break 'ALL nonoverlapping' in assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE[
      ALLPAIRS;ALL;
      BIGNUM_MONTSQR_P256_EXEC;BIGNUM_MONTSQR_P256_NEON_EXEC;
      BIGNUM_MONTSQR_P256_INTERM1_EXEC;
      NONOVERLAPPING_CLAUSES]) THEN
  SPLIT_FIRST_CONJ_ASSUM_TAC THEN

  MATCH_MP_TAC ENSURES2_WEAKEN THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ q /\ r) /\ p /\ q /\ r' <=> p /\ q /\ r /\ r'`] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc3,LENGTH bignum_montsqr_p256_interm1_core_mc))
          bignum_montsqr_p256_interm1_core_mc
          (write PC (word pc3) s')` THEN
    REPEAT CONJ_TAC THEN (TRY (
      REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN
      ASM_REWRITE_TAC[] THEN NO_TAC
    )) THENL [
      REWRITE_TAC[aligned_bytes_loaded;bytes_loaded] THEN
      RULE_ASSUM_TAC (REWRITE_RULE[aligned_bytes_loaded]) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC READ_OVER_WRITE_MEMORY_BYTELIST THEN
      REWRITE_TAC[BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC] THEN
      ARITH_TAC;

      UNDISCH_TAC `equiv_input_states (s,s') x z` THEN
      REWRITE_TAC[equiv_input_states;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `a:num` THEN
      REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
        REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN ASM_REWRITE_TAC[];
        REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN ASM_REWRITE_TAC[];
        EXPAND_RHS_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC;
      ];

      UNDISCH_TAC `equiv_input_states (s,s') x z` THEN
      REWRITE_TAC[equiv_input_states;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;BIGNUM_MONTSQR_P256_INTERM1_CORE_EXEC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `a:num` THEN
      REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
        REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN ASM_REWRITE_TAC[];
        REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN ASM_REWRITE_TAC[];
        EXPAND_RHS_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC;
      ]
    ];

    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[equiv_output_states_TRANS];

    SUBSUMED_MAYCHANGE_TAC
  ]);;




let event_n_at_pc_goal = mk_eventually_n_at_pc_statement
    `nonoverlapping (word pc:int64,LENGTH bignum_montsqr_p256_mc) (z:int64,8 * 4)`
    [`z:int64`;`x:int64`] (*pc_mc_ofs*)0 bignum_montsqr_p256_core_mc (*pc_ofs*)0
    `\s0. C_ARGUMENTS [z;x] s0`;;

let BIGNUM_MONTSQR_P256_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;BIGNUM_MONTSQR_P256_CORE_EXEC;BIGNUM_MONTSQR_P256_EXEC;
                BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montsqr_p256_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              BIGNUM_MONTSQR_P256_CORE_EXEC]) THENL [
    REWRITE_TAC[BIGNUM_MONTSQR_P256_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT_N 3 GEN_TAC THEN
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTSQR_P256_CORE_EXEC);;


(******************************************************************************
          Inducing BIGNUM_MONTSQR_P256_NEON_SUBROUTINE_CORRECT
          from BIGNUM_MONTSQR_P256_CORE_CORRECT
******************************************************************************)

let BIGNUM_MONTSQR_P256_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTSQR_P256_EXEC
    BIGNUM_MONTSQR_P256_CORE_EXEC
    BIGNUM_MONTSQR_P256_CORE_CORRECT
    BIGNUM_MONTSQR_P256_EVENTUALLY_N_AT_PC;;


let BIGNUM_MONTSQR_P256_NEON_CORE_CORRECT = prove(
  `!z x a pc2.
    nonoverlapping (word pc2,LENGTH bignum_montsqr_p256_neon_mc) (z,8 * 4)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p256_neon_core_mc /\
              read PC s = word pc2 /\
              C_ARGUMENTS [z; x] s /\
              bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc2 + 544) /\
              (a EXP 2 <= 2 EXP 256 * p_256
                ==> bignum_from_memory (z,4) s =
                    (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (z:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (x:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[BIGNUM_MONTSQR_P256_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    CONV_TAC (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN
  
  VCGEN_EQUIV_TAC BIGNUM_MONTSQR_P256_EQUIV BIGNUM_MONTSQR_P256_CORE_CORRECT_N
    [BIGNUM_MONTSQR_P256_EXEC;NONOVERLAPPING_CLAUSES] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[NONOVERLAPPING_CLAUSES;BIGNUM_MONTSQR_P256_EXEC;
             BIGNUM_MONTSQR_P256_NEON_EXEC]) THEN
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
          (word pc,LENGTH (APPEND bignum_montsqr_p256_core_mc barrier_inst_bytes)))
          (APPEND bignum_montsqr_p256_core_mc barrier_inst_bytes)
          (write PC (word pc) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTSQR_P256_CORE_EXEC) THEN
    (* Now has only one subgoal: the equivalence! *)
    REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY EXISTS_TAC [`a:num`] THEN
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTSQR_P256_CORE_EXEC);

    (** SUBGOAL 2. Postcond **)
    MESON_TAC[equiv_output_states;BIGNUM_FROM_MEMORY_BYTES];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
  ]);;

let BIGNUM_MONTSQR_P256_NEON_CORRECT = time prove
 (`!z x a pc.
      nonoverlapping (word pc,LENGTH bignum_montsqr_p256_neon_mc) (z,8 * 4)
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_neon_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [z; x] s /\
              bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc + 544) /\
              (a EXP 2 <= 2 EXP 256 * p_256
                ==> bignum_from_memory (z,4) s =
                    (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP BIGNUM_MONTSQR_P256_NEON_CORE_CORRECT th)) THEN
      REWRITE_TAC[ensures] THEN
      DISCH_THEN (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
  EXISTS_TAC `x:int64` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bignum_montsqr_p256_neon_core_mc_def;BIGNUM_MONTSQR_P256_NEON_EXEC;
      WORD_RULE`word (x+y)=word_add (word x) (word y)`] THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ONCE_REWRITE_TAC[WORD_RULE `word pc:int64 = word_add (word pc) (word 0)`] THEN
  ASM_SIMP_TAC[ALIGNED_BYTES_LOADED_SUB_LIST;WORD_ADD_0;NUM_DIVIDES_CONV`4 divides 0`]);;

let BIGNUM_MONTSQR_P256_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_neon_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_neon_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[BIGNUM_MONTSQR_P256_NEON_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P256_NEON_EXEC
    (REWRITE_RULE[BIGNUM_MONTSQR_P256_NEON_EXEC] BIGNUM_MONTSQR_P256_NEON_CORRECT));;


(******************************************************************************
          Inducing BIGNUM_AMONTSQR_P256_NEON_SUBROUTINE_CORRECT
          from BIGNUM_AMONTSQR_P256_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTSQR_P256_CORE_CORRECT_N =
  prove_correct_n
    BIGNUM_MONTSQR_P256_EXEC
    BIGNUM_MONTSQR_P256_CORE_EXEC
    BIGNUM_AMONTSQR_P256_CORE_CORRECT
    BIGNUM_MONTSQR_P256_EVENTUALLY_N_AT_PC;;

let BIGNUM_AMONTSQR_P256_NEON_CORE_CORRECT = prove(
  `!z x a pc2.
    nonoverlapping (word pc2,LENGTH bignum_montsqr_p256_neon_mc) (z,8 * 4)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p256_neon_core_mc /\
              read PC s = word pc2 /\
              C_ARGUMENTS [z; x] s /\
              bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc2 + 544) /\
              (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (z:int64,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_montsqr_p256_mc) (x:int64,8 * 4) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[BIGNUM_MONTSQR_P256_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    CONV_TAC (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN
  
  VCGEN_EQUIV_TAC BIGNUM_MONTSQR_P256_EQUIV BIGNUM_AMONTSQR_P256_CORE_CORRECT_N
    [BIGNUM_MONTSQR_P256_EXEC;NONOVERLAPPING_CLAUSES] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[NONOVERLAPPING_CLAUSES;BIGNUM_MONTSQR_P256_EXEC;
             BIGNUM_MONTSQR_P256_NEON_EXEC]) THEN
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
          (word pc,LENGTH (APPEND bignum_montsqr_p256_core_mc barrier_inst_bytes)))
          (APPEND bignum_montsqr_p256_core_mc barrier_inst_bytes)
          (write PC (word pc) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTSQR_P256_CORE_EXEC) THEN
    (* Now has only one subgoal: the equivalence! *)
    REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY EXISTS_TAC [`a:num`] THEN
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MONTSQR_P256_CORE_EXEC);

    (** SUBGOAL 2. Postcond **)
    MESON_TAC[equiv_output_states;BIGNUM_FROM_MEMORY_BYTES];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
  ]);;

let BIGNUM_AMONTSQR_P256_NEON_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_neon_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_neon_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 544) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP BIGNUM_AMONTSQR_P256_NEON_CORE_CORRECT th)) THEN
        REWRITE_TAC[ensures] THEN
        DISCH_THEN (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
    EXISTS_TAC `x:int64` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_montsqr_p256_neon_core_mc_def;BIGNUM_MONTSQR_P256_NEON_EXEC;
        WORD_RULE`word (x+y)=word_add (word x) (word y)`] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    ONCE_REWRITE_TAC[WORD_RULE `word pc:int64 = word_add (word pc) (word 0)`] THEN
    ASM_SIMP_TAC[ALIGNED_BYTES_LOADED_SUB_LIST;WORD_ADD_0;NUM_DIVIDES_CONV`4 divides 0`]);;

let BIGNUM_AMONTSQR_P256_NEON_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256_neon_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256_neon_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  REWRITE_TAC[BIGNUM_MONTSQR_P256_NEON_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P256_NEON_EXEC
    (REWRITE_RULE[BIGNUM_MONTSQR_P256_NEON_EXEC] BIGNUM_AMONTSQR_P256_NEON_CORRECT));;

