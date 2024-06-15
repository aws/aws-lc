(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time table lookup.                                               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

let bignum_copy_row_from_table_mc =
  define_assert_from_elf "bignum_copy_row_from_table_mc"
                         "arm/generic/bignum_copy_row_from_table.o"
[
  0xb4000342;       (* arm_CBZ X2 (word 104) *)
  0xb4000323;       (* arm_CBZ X3 (word 100) *)
  0xaa0303e5;       (* arm_MOV X5 X3 *)
  0xaa0003e6;       (* arm_MOV X6 X0 *)
  0xf90000df;       (* arm_STR XZR X6 (Immediate_Offset (word 0)) *)
  0x910020c6;       (* arm_ADD X6 X6 (rvalue (word 8)) *)
  0xf10004a5;       (* arm_SUBS X5 X5 (rvalue (word 1)) *)
  0x54ffffa1;       (* arm_BNE (word 2097140) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa0103e8;       (* arm_MOV X8 X1 *)
  0xeb0400bf;       (* arm_CMP X5 X4 *)
  0xda9f13e6;       (* arm_CSETM X6 Condition_EQ *)
  0xaa0303e7;       (* arm_MOV X7 X3 *)
  0xaa0003e9;       (* arm_MOV X9 X0 *)
  0xf940010a;       (* arm_LDR X10 X8 (Immediate_Offset (word 0)) *)
  0xf940012b;       (* arm_LDR X11 X9 (Immediate_Offset (word 0)) *)
  0x8a06014a;       (* arm_AND X10 X10 X6 *)
  0xaa0a016b;       (* arm_ORR X11 X11 X10 *)
  0xf900012b;       (* arm_STR X11 X9 (Immediate_Offset (word 0)) *)
  0x91002108;       (* arm_ADD X8 X8 (rvalue (word 8)) *)
  0x91002129;       (* arm_ADD X9 X9 (rvalue (word 8)) *)
  0xf10004e7;       (* arm_SUBS X7 X7 (rvalue (word 1)) *)
  0x54ffff01;       (* arm_BNE (word 2097120) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xeb0200bf;       (* arm_CMP X5 X2 *)
  0x54fffe21;       (* arm_BNE (word 2097092) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_COPY_ROW_FROM_TABLE_EXEC = ARM_MK_EXEC_RULE bignum_copy_row_from_table_mc;;

(* ARITH_RULE for proving `lp=rp` where lp and rp are pairs *)
let PAIR_EQ_ARITH_RULE (lp:term) (rp:term) =
  let lpl,lpr = dest_pair lp in
  let rpl,rpr = dest_pair rp in
  let lth = ARITH_RULE (mk_eq (lpl,rpl)) in
  let rth = ARITH_RULE (mk_eq (lpr,rpr)) in
  let th = REFL lp in
  let th = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [lth] th in
  GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [rth] th;;

let REWRITE_ASSUMES_TAC (t:term) =
    UNDISCH_THEN t (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm]) THEN ASSUME_TAC thm);;

let READ_MEMORY_BYTES_0 = prove(`read (memory :> bytes (z,0)) s = 0`,
    REWRITE_TAC[PAIR_EQ_ARITH_RULE `(x:int64,0)` `(x:int64, 8*0)`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL]);;

let LT_WORD_64 = prove(`!x (y:int64). x < val y ==> x < 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LT_TRANS `val (y:int64)` THEN
  ONCE_REWRITE_TAC [GSYM DIMINDEX_64] THEN ASM_REWRITE_TAC[VAL_BOUND]);;

let READ_MEMORY_BYTES_ELEM = prove(`!z w s m k.
  w > k /\ read (memory :> bytes (z,8 * w)) s = m ==>
  val (read (memory :> bytes64 (word_add z (word (8 * k)))) s) = lowdigits (highdigits m k) 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SING] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_FIRSTELEM = prove(`!z w s m.
  w > 0 /\ read (memory :> bytes (z,8 * w)) s = m ==>
  val (read (memory :> bytes64 z) s) = lowdigits m 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z:int64 = word_add z (word (8 * 0))` (fun thm -> ONCE_REWRITE_TAC[thm]) THENL
  [CONV_TAC WORD_RULE; ALL_TAC] THEN
  IMP_REWRITE_TAC[READ_MEMORY_BYTES_ELEM] THEN REWRITE_TAC[HIGHDIGITS_0]);;

let READ_MEMORY_BYTES_SLICE = prove(`!z w s m k w'.
  w >= k + w' /\ read (memory :> bytes (z,8 * w)) s = m ==>
  read (memory :> bytes (word_add z (word (8 * k)), 8 * w')) s = lowdigits (highdigits m k) w'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_SLICE_HIGH = prove(`!z w s m k w'.
  w = k + w' /\ read (memory :> bytes (z,8 * w)) s = m ==>
  read (memory :> bytes (word_add z (word (8 * k)), 8 * w')) s = highdigits m k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_MERGE = prove(`!z w w' w'' s m.
    read (memory :> bytes (z,8 * w)) s = lowdigits m w /\
    read (memory :> bytes (word_add z (word (8 * w)),8 * w')) s = highdigits m w /\
    w + w' = w'' ==>
    read (memory :> bytes (z, 8 * w'')) s = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN EXPAND_TAC "w''" THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[HIGH_LOW_DIGITS]);;

let READ_MEMORY_BYTES_BYTES64 = prove(`!z s.
  read (memory :> bytes (z,8)) s = val (read (memory :> bytes64 z) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIR_EQ_ARITH_RULE `(z:int64,8)` `(z:int64,8*1)`;
              GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING]);;


let BIGNUM_COPY_ROW_FROM_TABLE_SUBROUTINE_CORRECT = prove(
  `!z table height width idx pc n m returnaddress.
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_mc)
                   (z, 8 * val width) /\
    nonoverlapping (word pc, LENGTH bignum_copy_row_from_table_mc)
                   (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    8 * val width < 2 EXP 64 /\
    val idx < val height
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_row_from_table_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read PC s = returnaddress /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * val width)])`,

  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_COPY_ROW_FROM_TABLE_EXEC;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  ASM_CASES_TAC `val (height:(64)word) = 0` THENL [
    UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT] THEN ENSURES_INIT_TAC "s0" THEN ITAUT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `width = (word 0):(64)word` THENL [
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_0; WORD_ADD_0] THEN
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [1;2;3] THEN
    ASM_MESON_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val (width:64 word) = 0)` ASSUME_TAC THENL [
    UNDISCH_TAC `~(width = word 0:64 word)` THEN
    REWRITE_TAC[VAL_EQ_0];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x10`
      `\s. read X30 s = returnaddress /\ read X0 s = z /\ read X1 s = table /\
          read X2 s = height /\ read X3 s = width /\ read X4 s = idx /\
          read X5 s = width /\ read X6 s = z /\
          bignum_from_memory (table, val height * val width) s = n /\
          bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
              = m` THEN CONJ_TAC THENL [
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--4);

    ALL_TAC] THEN

  (* This is necessary to avoid stores from overwriting the table *)
  SUBGOAL_THEN `val (idx:int64) * val (width:int64) + val width <= val (height:int64) * val width` ASSUME_TAC
      THENL [IMP_REWRITE_TAC[LE_MULT_ADD]; ALL_TAC] THEN

  (* bignum_copy_row_from_table_initzero *)
  ENSURES_WHILE_PDOWN_TAC `val (width:64 word):num` `pc + 0x10` `pc + 0x1c`
    `\i s.  (read X30 s = returnaddress /\ read X0 s = z /\ read X1 s = table /\
            read X2 s = height /\ read X3 s = width /\ read X4 s = idx /\
            read X5 s = word i /\ read X6 s = word (val z + 8 * (val width - i)) /\
            bignum_from_memory (table, val height * val width) s = n /\
            bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
                = m /\
            bignum_from_memory (z, val width - i) s = 0) /\
            (read ZF s <=> i = 0)` THEN REPEAT CONJ_TAC THENL [
    (* 1. width > 0 *)
    ASM_MESON_TAC[];

    (* 2. loop starts *)
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [] THEN
      REWRITE_TAC[SUB_REFL; WORD_VAL; MULT_0; ADD_0; GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];

    (* 3. loop body *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes64 (word (val (z:int64) + 8 * (val (width:int64) - (i + 1))))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
        val width. *)
      REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
      ABBREV_TAC `w' = val (width:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC;

      ALL_TAC] THEN

    ENSURES_INIT_TAC "s0" THEN

    SUBGOAL_THEN `val (width:64 word) - (i + 1) < val (width:64 word)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8 * (val (width:int64) - (i + 1)) + 8 <= 18446744073709551616` ASSUME_TAC
      THENL [ASM_ARITH_TAC; ALL_TAC] THEN

    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [
      CONV_TAC WORD_RULE;

      REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN UNDISCH_TAC `i < val (width:64 word)`
      THEN ARITH_TAC;

      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC [ARITH_RULE `i < val (width:64 word) ==> val width - i = (val width - (i + 1)) + 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; WORD_RULE `word_add z (word c) = word (val z + c)`] THEN
      CONV_TAC WORD_RULE;

      REWRITE_TAC[WORD_SUB_ADD; VAL_WORD] THEN
      SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [
        TRANS_TAC LT_TRANS `val (width:64 word)` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `8 * val (width:64 word) < 2 EXP 64` THEN
        ARITH_TAC;

        ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_LT; DIMINDEX_64]];

    (* 4. loop backedge *)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--1);

    (* next *)
    ALL_TAC] THEN

  (* bignum_copy_row_from_table_outerloop *)
  ENSURES_WHILE_PUP_TAC `val (height:64 word):num` `pc + 0x28` `pc + 0x64`
    `\i s.  (read X30 s = returnaddress /\ read X0 s = z /\ read X1 s = table /\
            read X2 s = height /\ read X3 s = width /\ read X4 s = idx /\
            read X5 s = word i /\ read X8 s = word_add table (word (8 * i * val width)) /\
            bignum_from_memory (table, val height * val width) s = n /\
            bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
                = m /\
            ((i <= val idx  /\ bignum_from_memory (z, val width) s = 0) \/
              (i > val idx /\ bignum_from_memory (z, val width) s = m))) /\
            (read ZF s <=> i = val height)` THEN REPEAT CONJ_TAC THENL [
    (* 1. height > 0 *)
    ASM_MESON_TAC[];

    (* 2. to loop start *)
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--3) THEN
    REWRITE_TAC[ARITH_RULE `x * 0 = 0`; ARITH_RULE `0 * x = 0`; WORD_ADD_0] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `x - 0 = x`]) THEN
    ASM_REWRITE_TAC[LE_0];

    (* 3. loop body - pass *)
    ALL_TAC;

    (* 4. loop backedge *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--1);

    (* next *)
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [1;2] THEN
    CASES_FIRST_DISJ_ASSUM_TAC THEN SPLIT_FIRST_CONJ_ASSUM_TAC THENL [
      UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
      UNDISCH_TAC `val (height:int64) <= val (idx:int64)` THEN
      ARITH_TAC;

      ASM_MESON_TAC[]]] THEN

  REPEAT STRIP_TAC THEN

  ENSURES_WHILE_PDOWN_TAC `val (width:64 word):num` `pc + 0x38` `pc + 0x58`
    `\j s.  (read X30 s = returnaddress /\ read X0 s = z /\ read X1 s = table /\
            read X2 s = height /\ read X3 s = width /\ read X4 s = idx /\ read X5 s = word i /\
            read X6 s = (if i = val idx then word 18446744073709551615 else word 0) /\
            read X7 s = word j /\
            // pointers
            read X8 s = word_add table (word (8 * (i * val width + (val width - j)))) /\
            read X9 s = word_add z (word (8 * (val width - j)):64 word) /\
            bignum_from_memory (table, val height * val width) s = n /\
            bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
                = m /\
            ((i < val idx /\
              bignum_from_memory (z, val width - j) s = 0 /\
              bignum_from_memory (word_add z (word (8 * (val width - j))), j) s = 0)
              \/
              (i = val idx /\
              bignum_from_memory (z, val width - j) s = lowdigits m (val width - j) /\
              bignum_from_memory (word_add z (word (8 * (val width - j))), j) s = 0)
              \/
              (i > val idx /\
              bignum_from_memory (z, val width - j) s = lowdigits m (val width - j) /\
              bignum_from_memory (word_add z (word (8 * (val width - j))), j) s = highdigits m (val width - j)))) /\
            (read ZF s <=> j = 0)` THEN REPEAT CONJ_TAC THENL [
    ASM_MESON_TAC[];

    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC (1--4) THEN
    ASM_REWRITE_TAC[WORD_VAL; ADD_0; MULT_0; WORD_ADD_0] THEN
    CONJ_TAC THENL [
      ASM_CASES_TAC `i = val (idx:int64)` THENL [
        ASM_REWRITE_TAC[VAL_WORD] THEN IMP_REWRITE_TAC[MOD_LT; VAL_BOUND];

        ASM_REWRITE_TAC[VAL_WORD] THEN IMP_REWRITE_TAC[MOD_LT] THEN
        TRANS_TAC LT_TRANS `val (height:int64)` THEN
        ASM_REWRITE_TAC[VAL_BOUND]];

      ASM_CASES_TAC `i > val (idx:int64)` THENL [
        SUBGOAL_THEN `~(i <= val (idx:int64))` ASSUME_TAC THENL
          [ASM_REWRITE_TAC[NOT_LE; GSYM GT]; ALL_TAC] THEN
        REWRITE_TAC[ASSUME `i > val (idx:int64)`] THEN
        REWRITE_ASSUMES_TAC `i > val (idx:int64)` THEN
        REWRITE_ASSUMES_TAC `~(i <= val (idx:int64))` THEN
        ASM_REWRITE_TAC[READ_MEMORY_BYTES_0; LOWDIGITS_0; HIGHDIGITS_0];

        SUBGOAL_THEN `i <= val (idx:int64)` ASSUME_TAC THENL
          [UNDISCH_TAC `~(i > val (idx:int64))` THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_ASSUMES_TAC `i <= val (idx:int64)` THEN
        REWRITE_ASSUMES_TAC `~(i > val (idx:int64))` THEN
        ASM_REWRITE_TAC[ASSUME `~(i > val (idx:int64))`; LOWDIGITS_0; READ_MEMORY_BYTES_0] THEN
        UNDISCH_TAC `i <= val (idx:int64)` THEN
        ARITH_TAC]];

    (* loop body *)
    ALL_TAC;

    (* backedge *)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [1];

    (* finishes outer loop; pc 88 -> 100 *)
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [1;2;3] THEN
    SUBGOAL_THEN `m < 2 EXP (64 * val (width:int64))` ASSUME_TAC THENL
      [EXPAND_TAC "m" THEN SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD; ARITH_RULE `a*b+b-0=(a+1)*b`] THEN
    REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;ARITH_RULE `1 MOD 2 EXP 64 = 1`; ADD_0] THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [
      TRANS_TAC LT_TRANS `val (height:int64)` THEN
      ASM_MESON_TAC[VAL_BOUND_64];
      ALL_TAC] THEN
    SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [
      TRANS_TAC LET_TRANS `val (height:int64)` THEN
      CONJ_TAC THENL [
        UNDISCH_TAC `i < val (height:int64)` THEN ARITH_TAC;
        REWRITE_TAC[VAL_BOUND_64]];

      ALL_TAC] THEN
    IMP_REWRITE_TAC[MOD_LT; VAL_BOUND_64] THEN

    ASM_CASES_TAC `i < val (idx:int64)` THENL [
      REWRITE_ASSUMES_TAC `i < val (idx:int64)` THEN
      SUBGOAL_THEN `~(i = val (idx:int64))` (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm])) THENL [
        UNDISCH_TAC `i < val (idx:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(i > val (idx:int64))` (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm])) THENL [
        UNDISCH_TAC `i < val (idx:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `x - 0 = x`]) THEN
      ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
      UNDISCH_TAC `i < val (idx:int64)` THEN ARITH_TAC;

      ASM_CASES_TAC `i = val (idx:int64)` THENL [
        REWRITE_ASSUMES_TAC `i = val (idx:int64)` THEN
        RULE_ASSUM_TAC (REWRITE_RULE [LT_REFL; GT_REFL; SUB_0]) THEN
        SPLIT_FIRST_CONJ_ASSUM_TAC THEN DISJ2_TAC THEN
        ASM_REWRITE_TAC[ARITH_RULE `p + 1 > p`] THEN
        IMP_REWRITE_TAC[LOWDIGITS_SELF] THEN
        EXPAND_TAC "m" THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[SUB_0; BIGNUM_FROM_MEMORY_BOUND];

        REWRITE_ASSUMES_TAC `~(i = val (idx:int64))` THEN
        REWRITE_ASSUMES_TAC `~(i < val (idx:int64))` THEN
        REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN (* get `i > val idx` *)
        RULE_ASSUM_TAC (REWRITE_RULE [SUB_0]) THEN
        DISJ2_TAC THEN
        ASM_SIMP_TAC[ARITH_RULE `x > y ==> x + 1 > y`; ASSUME `i > val (idx:int64)`] THEN
        ASM_REWRITE_TAC[LOWDIGITS_EQ_SELF]
      ]]

    ] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes64 (word (val (z:int64) + 8 * (val (width:int64) - (i' + 1))))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
        val width. *)
      REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
      ABBREV_TAC `w' = val (width:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC;

      ALL_TAC] THEN

    ENSURES_INIT_TAC "s0" THEN

    ABBREV_TAC `p = read
      (memory :> bytes64 (word_add table
          (word (8 * (i * val (width:int64) + val (width:int64) - (i' + 1)))):int64))
          s0` THEN
    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [1] THEN
    ABBREV_TAC `q = read
      (memory :> bytes64 (word_add z
          (word (8 * (val (width:int64) - (i' + 1))):int64))) s1` THEN
    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [2;3;4] THEN
    SUBGOAL_THEN `val (width:int64) - (i'+1) < val width` ASSUME_TAC THENL [
      UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i * val (width:int64) + val (width:int64) - (i' + 1) <
                  val (height:int64) * val (width:int64)` ASSUME_TAC THENL [
      TRANS_TAC LTE_TRANS `i * val (width:int64) + val (width:int64)` THEN
      IMP_REWRITE_TAC[LE_MULT_ADD] THEN
    REWRITE_TAC[LT_ADD_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8 * (val (width:int64) - (i' + 1)) + 8 * (i' + 1) <=
                    18446744073709551616` ASSUME_TAC THENL [
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      IMP_REWRITE_TAC[SUB_ADD] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN

  ASM_CASES_TAC `i = val (idx:int64)` THENL [
    (* case 1 *)
    REWRITE_TAC[ASSUME `i = val (idx:int64)`; LT_REFL; GT_REFL] THEN
    REWRITE_ASSUMES_TAC `i = val (idx:int64)` THEN
    RULE_ASSUM_TAC (REWRITE_RULE [LT_REFL; GT_REFL]) THEN
    SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    SUBGOAL_THEN `
      q:int64 = word 0 /\
      read (memory :>
        bytes (word_add z (word (8 * (val (width:int64) - i'))),8 * i')) s4 = 0`
      (fun thm -> MAP_EVERY ASSUME_TAC (let x,y=CONJ_PAIR thm in [x;y])) THENL [
      CONJ_TAC THENL [
        EXPAND_TAC "q" THEN REWRITE_TAC[GSYM VAL_EQ] THEN
          REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SING; VAL_WORD_0] THEN
        SUBGOAL_THEN `!z. (z:int64,1) = (z:int64, MIN (i'+1) 1)` (fun thm -> REWRITE_TAC[thm]) THENL [
          STRIP_TAC THEN REWRITE_TAC[MIN] THEN AP_TERM_TAC THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY; BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_TRIVIAL];

        UNDISCH_TAC `read
          (memory :>
            bytes (word_add z (word (8 * (val (width:int64) - (i' + 1)))):int64,
                    8 * (i' + 1))) s4 = 0` THEN
          REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
          REWRITE_TAC[PAIR_EQ_ARITH_RULE `(temp:int64,i'+1)` `(temp:int64,1+i')`] THEN
          REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
          REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; ARITH_RULE `~(2 EXP (64 * 1) = 0)`] THEN
          SUBGOAL_THEN
          `word_add (word_add (z:int64) (word (8 * (val (width:int64) - (i' + 1))):int64):int64)
                    (word (8 * 1)):int64 =
            word_add z (word (8 * (val (width:int64) - i')):int64)`
            (fun thm -> REWRITE_TAC[thm]) THENL [
            REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

            ALL_TAC] THEN
        MESON_TAC[]
      ];

      ALL_TAC
    ] THEN

    SUBST_ALL_TAC (ASSUME `q=word 0:int64`) THEN
    SUBGOAL_THEN `val (width:int64) - (i' + 1) < val (width:int64) - i'` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8 * (val (width:int64) - i') + 8 * i' <= 18446744073709551616` ASSUME_TAC THENL [
      ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8 * (val (width:int64) - (i' + 1)) + 8 <= 18446744073709551616` ASSUME_TAC THENL [
      ASM_ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [5] THEN
    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [6;7;8] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_SUB_ADD; WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT CONJ_TAC THENL [
      REPEAT AP_TERM_TAC THEN
      UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

      REPEAT AP_TERM_TAC THEN
      UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      SUBGOAL_THEN `val (width:int64) - i' = val width - (i'+1) + 1` (fun thm -> REWRITE_TAC[thm]) THENL [
        UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS; BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_BLAST `word_and p (word 18446744073709551615) = p:int64`] THEN
      MAP_EVERY EXPAND_TAC ["p";"m"] THEN
      ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      SUBGOAL_THEN `val (width:int64) - (i' + 1) < val width` (fun thm->REWRITE_TAC[thm]) THENL [
        UNDISCH_TAC `i'<val (width:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[WORD_VAL; WORD_ADD_ASSOC_CONSTS; LEFT_ADD_DISTRIB];

      IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64; LT_WORD_64]
    ];

    (* case 2 *)
    ASM_CASES_TAC `i < val (idx:int64)` THENL [
      REWRITE_TAC [ASSUME `i < val (idx:int64)`] THEN
      REWRITE_ASSUMES_TAC `i < val (idx:int64)` THEN
      REWRITE_TAC [ASSUME `~(i = val (idx:int64))`] THEN
      REWRITE_ASSUMES_TAC `~(i = val (idx:int64))` THEN
      SUBGOAL_THEN `~(i > val (idx:int64))` ASSUME_TAC THENL
        [UNDISCH_TAC `i < val (idx:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC [ASSUME `~(i > val (idx:int64))`] THEN
      REWRITE_ASSUMES_TAC `~(i > val (idx:int64))` THEN
      SUBGOAL_THEN `q = word 0:int64` SUBST_ALL_TAC THENL [
        EXPAND_TAC "q" THEN REWRITE_TAC[GSYM VAL_EQ] THEN
        IMP_REWRITE_TAC[READ_MEMORY_BYTES_FIRSTELEM] THEN
        MAP_EVERY EXISTS_TAC [`0:num`; `i'+1:num`] THEN
        ASM_REWRITE_TAC[HIGHDIGITS_TRIVIAL; LOWDIGITS_TRIVIAL; VAL_WORD_0] THEN
        ARITH_TAC;

        ALL_TAC] THEN
      SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      ASSERT_USING_ASM_ARITH_TAC `8 * (val (width:int64) - (i' + 1)) + 8 <= 18446744073709551616` THEN
      SUBGOAL_THEN `read (memory :> bytes
          ((word_add (word_add (z:int64) (word (8 * (val (width:int64) - (i' + 1))))) (word (8 * 1))),8 * i'))
          s4 = 0` (fun thm -> ASSUME_TAC (REWRITE_RULE [WORD_ADD_ASSOC_CONSTS] thm)) THENL
        [IMP_REWRITE_TAC[READ_MEMORY_BYTES_SLICE; HIGHDIGITS_TRIVIAL; LOWDIGITS_TRIVIAL] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `8 * (val (width:int64) - (i' + 1)) + 8 * 1 = 8 * (val (width:int64) - i')`
        (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm])) THENL [
          UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      ASSERT_USING_UNDISCH_AND_ARITH_TAC `val (width:int64) - (i' + 1) < val (width:int64) - i'` `i' < val (width:int64)` THEN
      ASSERT_USING_ASM_ARITH_TAC `8 * (val (width:int64) - i') + 8 * i' <= 18446744073709551616` THEN
      ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [5] THEN
      ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [6;7;8] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[WORD_SUB_ADD; WORD_ADD_ASSOC_CONSTS] THEN
      REPEAT CONJ_TAC THENL [
        REPEAT AP_TERM_TAC THEN
        UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

        REPEAT AP_TERM_TAC THEN
        UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

        MATCH_MP_TAC (SPECL [`z:int64`; `(val (width:int64) - (i' + 1)):num`; `1:num`] READ_MEMORY_BYTES_MERGE) THEN
        ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL; HIGHDIGITS_TRIVIAL; ARITH_RULE `8*1=8`; READ_MEMORY_BYTES_BYTES64;
            WORD_AND_0; VAL_WORD_0] THEN UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

        IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64; LT_WORD_64]
      ];

      (* last case *)
      ASSERT_USING_ASM_ARITH_TAC `i > val (idx:int64)` THEN
      MAP_EVERY (fun t -> REWRITE_TAC [ASSUME t] THEN REWRITE_ASSUMES_TAC t)
        [`i > val (idx:int64)`; `~(i = val (idx:int64))`; `~(i < val (idx:int64))`] THEN
      SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      ASSERT_USING_ASM_ARITH_TAC `8 * (val (width:int64) - (i' + 1)) + 8 <= 18446744073709551616` THEN
      SUBGOAL_THEN `
        q:int64 = word (lowdigits (highdigits m (val (width:int64) - (i' + 1))) 1) /\
        read (memory :>
          bytes (word_add z (word (8 * (val width - i'))),8 * i')) s4 = highdigits m (val width - i')`
        (fun thm -> MAP_EVERY ASSUME_TAC (let x,y=CONJ_PAIR thm in [x;y])) THENL [
        CONJ_TAC THENL [
          EXPAND_TAC "q" THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
          SUBGOAL_THEN `!x. (lowdigits x 1) MOD 2 EXP 64 = lowdigits x 1` (fun thm -> REWRITE_TAC [thm]) THENL [
            STRIP_TAC THEN IMP_REWRITE_TAC[MOD_LT] THEN ONCE_REWRITE_TAC[ARITH_RULE `64=64*1`] THEN MESON_TAC[LOWDIGITS_BOUND];
            ALL_TAC
          ] THEN
          MATCH_MP_TAC READ_MEMORY_BYTES_FIRSTELEM THEN
          EXISTS_TAC `i'+1` THEN CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]];

          SUBGOAL_THEN
            `word_add z (word (8 * (val (width:int64) - i'))):int64 =
            word_add (word_add z (word (8 * (val width - (i'+1))))) (word (8 * 1))` (fun thm->ONCE_REWRITE_TAC[thm]) THENL
            [REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN REPEAT AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;
            ALL_TAC] THEN
          IMP_REWRITE_TAC[READ_MEMORY_BYTES_SLICE_HIGH] THEN
          REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN CONJ_TAC THENL [REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC]
        ];

        ALL_TAC
      ] THEN

      ASSERT_USING_ASM_ARITH_TAC `val (width:int64) - (i' + 1) < val width - i'` THEN
      ASSERT_USING_ASM_ARITH_TAC `8 * (val (width:int64) - i') + 8 * i' <= 18446744073709551616` THEN
      ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [5] THEN
      ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_EXEC [6;7;8] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[WORD_SUB_ADD; WORD_ADD_ASSOC_CONSTS] THEN
      REPEAT CONJ_TAC THENL [
        REPEAT AP_TERM_TAC THEN
        UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

        REPEAT AP_TERM_TAC THEN
        UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

        MATCH_MP_TAC (SPECL [`z:int64`; `(val (width:int64) - (i' + 1)):num`; `1:num`] READ_MEMORY_BYTES_MERGE) THEN
        ASM_REWRITE_TAC[ARITH_RULE `8*1=8`; READ_MEMORY_BYTES_BYTES64; LOWDIGITS_LOWDIGITS;
            WORD_OR_0; WORD_AND_0; VAL_WORD] THEN
        REPEAT CONJ_TAC THENL [
          AP_TERM_TAC THEN ARITH_TAC;

          SUBGOAL_THEN `!x. (lowdigits x 1) MOD 2 EXP 64 = lowdigits x 1` (fun thm -> REWRITE_TAC [DIMINDEX_64; thm]) THENL [
            STRIP_TAC THEN IMP_REWRITE_TAC[MOD_LT] THEN ONCE_REWRITE_TAC[ARITH_RULE `64=64*1`] THEN MESON_TAC[LOWDIGITS_BOUND];
            ALL_TAC
          ] THEN
          REWRITE_TAC[lowdigits; highdigits] THEN
          REWRITE_TAC[DIV_MOD] THEN
          AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
          REWRITE_TAC[GSYM EXP_ADD] THEN
          AP_TERM_TAC THEN
          UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;

          UNDISCH_TAC `i' < val (width:int64)` THEN ARITH_TAC;
        ];

        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_MESON_TAC[MOD_LT; LT_WORD_64]
      ]
    ]
  ]);;

