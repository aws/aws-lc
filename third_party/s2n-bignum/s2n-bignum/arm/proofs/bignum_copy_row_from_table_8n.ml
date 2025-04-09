(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time table lookup.                                               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

let bignum_copy_row_from_table_8n_mc =
  define_assert_from_elf "bignum_copy_row_from_table_8n_mc"
                         "arm/generic/bignum_copy_row_from_table_8n.o"
[
  0xb4000542;       (* arm_CBZ X2 (word 168) *)
  0xb4000523;       (* arm_CBZ X3 (word 164) *)
  0xaa0303e5;       (* arm_MOV X5 X3 *)
  0xaa0003e6;       (* arm_MOV X6 X0 *)
  0x4e080ff0;       (* arm_DUP_GEN Q16 XZR *)
  0x3d8000d0;       (* arm_STR Q16 X6 (Immediate_Offset (word 0)) *)
  0x3d8004d0;       (* arm_STR Q16 X6 (Immediate_Offset (word 16)) *)
  0x3d8008d0;       (* arm_STR Q16 X6 (Immediate_Offset (word 32)) *)
  0x3d800cd0;       (* arm_STR Q16 X6 (Immediate_Offset (word 48)) *)
  0x910100c6;       (* arm_ADD X6 X6 (rvalue (word 64)) *)
  0xf10020a5;       (* arm_SUBS X5 X5 (rvalue (word 8)) *)
  0x54ffff41;       (* arm_BNE (word 2097128) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa0103e8;       (* arm_MOV X8 X1 *)
  0xeb0400bf;       (* arm_CMP X5 X4 *)
  0xda9f13e6;       (* arm_CSETM X6 Condition_EQ *)
  0x4e080cd0;       (* arm_DUP_GEN Q16 X6 *)
  0xaa0303e7;       (* arm_MOV X7 X3 *)
  0xaa0003e9;       (* arm_MOV X9 X0 *)
  0x3dc00111;       (* arm_LDR Q17 X8 (Immediate_Offset (word 0)) *)
  0x3dc00132;       (* arm_LDR Q18 X9 (Immediate_Offset (word 0)) *)
  0x6eb01e32;       (* arm_BIT Q18 Q17 Q16 128 *)
  0x3d800132;       (* arm_STR Q18 X9 (Immediate_Offset (word 0)) *)
  0x3dc00511;       (* arm_LDR Q17 X8 (Immediate_Offset (word 16)) *)
  0x3dc00532;       (* arm_LDR Q18 X9 (Immediate_Offset (word 16)) *)
  0x6eb01e32;       (* arm_BIT Q18 Q17 Q16 128 *)
  0x3d800532;       (* arm_STR Q18 X9 (Immediate_Offset (word 16)) *)
  0x3dc00911;       (* arm_LDR Q17 X8 (Immediate_Offset (word 32)) *)
  0x3dc00932;       (* arm_LDR Q18 X9 (Immediate_Offset (word 32)) *)
  0x6eb01e32;       (* arm_BIT Q18 Q17 Q16 128 *)
  0x3d800932;       (* arm_STR Q18 X9 (Immediate_Offset (word 32)) *)
  0x3dc00d11;       (* arm_LDR Q17 X8 (Immediate_Offset (word 48)) *)
  0x3dc00d32;       (* arm_LDR Q18 X9 (Immediate_Offset (word 48)) *)
  0x6eb01e32;       (* arm_BIT Q18 Q17 Q16 128 *)
  0x3d800d32;       (* arm_STR Q18 X9 (Immediate_Offset (word 48)) *)
  0x91010108;       (* arm_ADD X8 X8 (rvalue (word 64)) *)
  0x91010129;       (* arm_ADD X9 X9 (rvalue (word 64)) *)
  0xf10020e7;       (* arm_SUBS X7 X7 (rvalue (word 8)) *)
  0x54fffda1;       (* arm_BNE (word 2097076) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xeb0200bf;       (* arm_CMP X5 X2 *)
  0x54fffca1;       (* arm_BNE (word 2097044) *)
  0xd65f03c0        (* arm_RET X30 *)
];;


let BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC = ARM_MK_EXEC_RULE bignum_copy_row_from_table_8n_mc;;

(* ARITH_RULE for proving `lp=rp` where lp and rp are pairs *)
let PAIR_EQ_ARITH_RULE (lp,rp:term*term) =
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
    REWRITE_TAC[PAIR_EQ_ARITH_RULE (`(x:int64,0)`,`(x:int64, 8*0)`)] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL]);;

let LT_WORD_64 = prove(`!x (y:int64). x < val y ==> x < 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LT_TRANS `val (y:int64)` THEN
  ONCE_REWRITE_TAC [GSYM DIMINDEX_64] THEN ASM_REWRITE_TAC[VAL_BOUND]);;

let LT_WORD_64_DIV_N = prove(`!x (y:int64) n. x < val y DIV n ==> x < 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LT_WORD_64 THEN EXISTS_TAC `y:int64` THEN
  TRANS_TAC LTE_TRANS `val (y:int64) DIV n` THEN ASM_REWRITE_TAC[DIV_LE]);;

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
  REWRITE_TAC[PAIR_EQ_ARITH_RULE (`(z:int64,8)`, `(z:int64,8*1)`);
              GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING]);;

let READ_MEMORY_BYTES_BYTES128 = prove(`!z s.
    read (memory :> bytes (z,16)) s = val (read (memory :> bytes128 z) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  REWRITE_TAC[VAL_WORD_JOIN;DIMINDEX_64;DIMINDEX_128] THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE`2 EXP 128 = 2 EXP 64 * 2 EXP 64`] THEN
  IMP_REWRITE_TAC[LT_MULT_ADD_MULT] THEN
  REWRITE_TAC[VAL_BOUND_64;ARITH_RULE`0<2 EXP 64`;LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE`16 = 8*(1+1)`;GSYM BIGNUM_FROM_MEMORY_BYTES;BIGNUM_FROM_MEMORY_STEP;BIGNUM_FROM_MEMORY_SING] THEN
  REWRITE_TAC[ARITH_RULE`8*1=8`;ARITH_RULE`64*1=64`] THEN ARITH_TAC);;

let READ_MEMORY_BYTES_MERGE_FOUR128 = prove(
    `!z0 z1 z2 z3 m0 m1 m2 m3 m s.
      val (read (memory :> bytes128 z0) s) = m0 /\
      val (read (memory :> bytes128 z1) s) = m1 /\
      val (read (memory :> bytes128 z2) s) = m2 /\
      val (read (memory :> bytes128 z3) s) = m3 /\
      z1 = word_add z0 (word 16) /\
      z2 = word_add z0 (word 32) /\
      z3 = word_add z0 (word 48) /\
      (2 EXP 384) * m3 + (2 EXP 256) * m2 + (2 EXP 128) * m1 + m0 = m ==>
      read (memory :> bytes (z0, 64)) s = m`,
  REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128] THEN
  REWRITE_TAC(map ARITH_RULE [`16=8*2`;`32=8*4`;`48=8*6`]) THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> UNDISCH_THEN t SUBST_ALL_TAC) [
    `z1 = word_add z0 (word (8*2)):int64`;
    `z2 = word_add z0 (word (8*4)):int64`;
    `z3 = word_add z0 (word (8*6)):int64`
  ] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ADD_ASSOC]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ARITH_RULE`2 EXP 384=2 EXP (128 + 128 + 128)`;ARITH_RULE`2 EXP 256=2 EXP (128 + 128)`]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [EXP_ADD;GSYM MULT_ASSOC;GSYM LEFT_ADD_DISTRIB]) THEN
  let mytac s = EXPAND_TAC s THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      SIMP_TAC[BIGNUM_FROM_MEMORY_BOUND;ARITH_RULE`128=64*2`] in
  SUBGOAL_THEN `m0 < 2 EXP 128` ASSUME_TAC THENL [ mytac "m0"; ALL_TAC ] THEN
  SUBGOAL_THEN `m1 < 2 EXP 128` ASSUME_TAC THENL [ mytac "m1"; ALL_TAC ] THEN
  SUBGOAL_THEN `m2 < 2 EXP 128` ASSUME_TAC THENL [ mytac "m2"; ALL_TAC ] THEN
  SUBGOAL_THEN `m3 < 2 EXP 128` ASSUME_TAC THENL [ mytac "m3"; ALL_TAC ] THEN

  SUBGOAL_THEN `m0 = lowdigits m 2` SUBST_ALL_TAC THENL
  [ EXPAND_TAC "m" THEN REWRITE_TAC[lowdigits;ARITH_RULE`64*2=128`] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    IMP_REWRITE_TAC[MOD_LT]; ALL_TAC ] THEN
  SUBGOAL_THEN `m1 = lowdigits (highdigits m 2) 2` SUBST_ALL_TAC THENL
  [ EXPAND_TAC "m" THEN REWRITE_TAC[lowdigits;highdigits;ARITH_RULE`64*2=128`] THEN
    IMP_REWRITE_TAC[DIV_MULT_ADD; MOD_DIV_EQ_0;ADD_0;MOD_MULT_ADD] THEN
    IMP_REWRITE_TAC[MOD_LT] THEN ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `m2 = lowdigits (highdigits m 4) 2` SUBST_ALL_TAC THENL
  [ EXPAND_TAC "m" THEN REWRITE_TAC[lowdigits;highdigits;
      ARITH_RULE`64*4=128+128`;ARITH_RULE`64*2=128`;EXP_ADD;GSYM DIV_DIV] THEN
    IMP_REWRITE_TAC[DIV_MULT_ADD; MOD_DIV_EQ_0;ADD_0;MOD_MULT_ADD] THEN
    IMP_REWRITE_TAC[MOD_LT] THEN ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `m3 = highdigits m 6` SUBST_ALL_TAC THENL
  [ EXPAND_TAC "m" THEN REWRITE_TAC[lowdigits;highdigits;
      ARITH_RULE`64*6=128+128+128`;ARITH_RULE`64*2=128`;EXP_ADD;GSYM DIV_DIV] THEN
    IMP_REWRITE_TAC[DIV_MULT_ADD; MOD_DIV_EQ_0;ADD_0;MOD_MULT_ADD] THEN
    ARITH_TAC; ALL_TAC ] THEN

  REWRITE_TAC[ARITH_RULE`64=8*8`] THEN

  MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
  MAP_EVERY EXISTS_TAC [`2`;`6`] THEN
  ASM_REWRITE_TAC[ARITH_RULE`2+6=8`] THEN

  MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
  MAP_EVERY EXISTS_TAC [`2`;`4`] THEN
  ASM_REWRITE_TAC[ARITH_RULE`2+4=6`] THEN

  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*2+8*2=8*4`] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
  MAP_EVERY EXISTS_TAC [`2`;`2`] THEN
  ASM_REWRITE_TAC[ARITH_RULE`2+2=4`;ARITH_RULE`2+4=6`;
      HIGHDIGITS_HIGHDIGITS;WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*4+8*2=8*6`]);;

let ABBREV_Z_READ_128BITS_TAC name stname ofs =
  let v = mk_var (name, `:int128`) in
  let templ =
    if ofs = 0 then
      `read (memory :> bytes128 (word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)))):int64)) s0`
    else
      let templ0 = `read (memory :> bytes128 (word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + ofs)):int64)) s0` in
      let newofs = mk_numeral (num ofs) in
      subst [(newofs,`ofs:num`)] templ0 in
  let rhs = subst [(mk_var(stname, `:armstate`),`st0:armstate`)] templ in
  ABBREV_TAC (mk_eq (v,rhs));;

let ABBREV_TABLE_READ_128BITS_TAC name stname ofs =
  let v = mk_var (name, `:int128`) in
  let templ =
    if ofs = 0 then
      `read (memory :> bytes128 (word_add table
            (word (8 * (i * val (width:int64) + val (width:int64) - 8 * (i' + 1)))):int64)) s0`
    else
      let templ0 = `read (memory :> bytes128 (word_add table
            (word (8 * (i * val (width:int64) + val (width:int64) - 8 * (i' + 1)) + ofs)):int64)) s0` in
      let newofs = mk_numeral (num ofs) in
      subst [(newofs,`ofs:num`)] templ0 in
  let rhs = subst [(mk_var(stname, `:armstate`),`st0:armstate`)] templ in
  ABBREV_TAC (mk_eq (v,rhs));;

let READ_MEMORY_BYTES_FIRSTELEM128 = prove(`!z w s m.
    w >= 2 /\ read (memory :> bytes (z,8 * w)) s = m ==>
    val (read (memory :> bytes128 z) s) = lowdigits m 2`,
  REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128; ARITH_RULE`16=8*2`] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN
  EXPAND_TAC"m" THEN REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC);;

let WORD_AND_128_FULLBITS = prove(
  `!(x:int128). word_and (word 340282366920938463463374607431768211455) x = x /\
                word_and x (word 340282366920938463463374607431768211455) = x`,
  STRIP_TAC THEN CONV_TAC WORD_BLAST);;

let VAL_WORD_8_EQ_0 = prove(
  `!i' x. i' < val (x:int64) DIV 8 ==> (val (word (8 * i'):int64) = 0 <=> i' = 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
  SUBGOAL_THEN `val (x:int64) < 2 EXP 64` ASSUME_TAC THENL [REWRITE_TAC[VAL_BOUND_64]; ALL_TAC] THEN
  SUBGOAL_THEN `8*i'<2 EXP 64` (fun thm -> REWRITE_TAC[MATCH_MP MOD_LT thm]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ARITH_TAC);;


let BIGNUM_COPY_ROW_FROM_TABLE_8N_SUBROUTINE_CORRECT = prove(
  `!z table height width idx pc n m returnaddress.
    nonoverlapping (word pc, 0xac) (z, 8 * val width) /\
    nonoverlapping (word pc, 0xac) (table, 8 * val height * val width) /\
    nonoverlapping (z, 8 * val width) (table, 8 * val height * val width) /\
    8 * val width < 2 EXP 64 /\ val width MOD 8 = 0 /\ val idx < val height
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_row_from_table_8n_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [z; table; height; width; idx] s /\
           bignum_from_memory (table, val height * val width) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m)
      (\s. read PC s = returnaddress /\
           bignum_from_memory (z, val width) s = m)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * val width)])`,

  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  ASM_CASES_TAC `val (height:(64)word) = 0` THENL [
    UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT] THEN ENSURES_INIT_TAC "s0" THEN ITAUT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `width = (word 0):(64)word` THENL [
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_0; WORD_ADD_0] THEN
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC [1;2;3] THEN
    ASM_MESON_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val (width:64 word) = 0)` ASSUME_TAC THENL [
    UNDISCH_TAC `~(width = word 0:64 word)` THEN
    REWRITE_TAC[VAL_EQ_0];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x14`
    `\s. read X30 s = returnaddress /\ read X0 s = z /\ read X1 s = table /\
         read X2 s = height /\ read X3 s = width /\ read X4 s = idx /\
         read X5 s = width /\ read X6 s = z /\
         bignum_from_memory (table, val height * val width) s = n /\
         bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s = m /\
         read Q16 s = word 0` THEN CONJ_TAC THENL [
  ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--5);

  ALL_TAC] THEN

(* This is necessary to avoid stores from overwriting the table *)
  SUBGOAL_THEN `val (idx:int64) * val (width:int64) + val width <= val (height:int64) * val width` ASSUME_TAC
    THENL [IMP_REWRITE_TAC[LE_MULT_ADD]; ALL_TAC] THEN

  SUBGOAL_THEN `word (8 * val width DIV 8) = width:int64` ASSUME_TAC THENL [
  REWRITE_TAC [GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN CONJ_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

(* bignum_copy_row_from_table_initzero *)
  ENSURES_WHILE_PDOWN_TAC `val (width:64 word) DIV 8:num` `pc + 0x14` `pc + 0x2c`
  `\i s.  (read X30 s = returnaddress /\ read X0 s = z /\ read X1 s = table /\
          read X2 s = height /\ read X3 s = width /\ read X4 s = idx /\
          read X5 s = word (8 * i) /\
          read X6 s = word (val z + 64 * (val width DIV 8 - i)) /\
          read Q16 s = word 0 /\
          bignum_from_memory (table, val height * val width) s = n /\
          bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
              = m /\
          bignum_from_memory (z, 8 * (val width DIV 8 - i)) s = 0) /\
          (read ZF s <=> i = 0)` THEN REPEAT CONJ_TAC THENL [
  (* 1. width > 0 *)
  ASM_ARITH_TAC;

  (* 2. loop starts *)
  ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC [] THEN
    REWRITE_TAC[SUB_REFL; WORD_VAL; MULT_0; ADD_0; GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];

  (* 3. loop body *)
  REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [
      memory :> bytes128 (word (val (z:int64) + 64 * (val (width:int64) DIV 8 - (i + 1))));
      memory :> bytes128 (word_add (word (val (z:int64) + 64 * (val (width:int64) DIV 8 - (i + 1))))
                           (word 16));
      memory :> bytes128 (word_add (word (val (z:int64) + 64 * (val (width:int64) DIV 8 - (i + 1))))
                           (word 32));
      memory :> bytes128 (word_add (word (val (z:int64) + 64 * (val (width:int64) DIV 8 - (i + 1))))
                           (word 48))]` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  CONJ_TAC THENL [
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
       val width. *)
    REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    ABBREV_TAC `w' = val (width:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC;

    ALL_TAC] THEN

  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY ASSERT_USING_ASM_ARITH_TAC [
    `8 * (val (width:int64) DIV 8 - (i + 1)) + 2 <= val (width:int64)`;
    `(8 * (val (width:int64) DIV 8 - (i + 1)) + 2) + 2 <= val (width:int64)`;
    `(8 * (val (width:int64) DIV 8 - (i + 1)) + 4) + 2 <= val (width:int64)`;
    `(8 * (val (width:int64) DIV 8 - (i + 1)) + 6) + 2 <= val (width:int64)`;
    `64 * (val (width:int64) DIV 8 - (i + 1)) + 16 <= 18446744073709551616`;
    `(64 * (val (width:int64) DIV 8 - (i + 1)) + 16) + 16 <= 18446744073709551616`;
    `(64 * (val (width:int64) DIV 8 - (i + 1)) + 32) + 16 <= 18446744073709551616`;
    `(64 * (val (width:int64) DIV 8 - (i + 1)) + 48) + 16 <= 18446744073709551616`] THEN
  ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    CONV_TAC WORD_RULE;

    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `i < val (width:int64) DIV 8` THEN ARITH_TAC;

    MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
    MAP_EVERY EXISTS_TAC [`8 * (val (width:int64) DIV 8 - (i + 1))`; `8`] THEN
    ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL; HIGHDIGITS_TRIVIAL] THEN
    CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `i < val (width:int64) DIV 8` THEN ARITH_TAC] THEN
    REWRITE_TAC[ARITH_RULE`8*8=64`] THEN MATCH_MP_TAC READ_MEMORY_BYTES_MERGE_FOUR128 THEN
    MAP_EVERY EXISTS_TAC [
      `word_add (word (val (z:int64) + 64 * (val (width:int64) DIV 8 - (i + 1)))) (word 16):int64`;
      `word_add (word (val (z:int64) + 64 * (val (width:int64) DIV 8 - (i + 1)))) (word 32):int64`;
      `word_add (word (val (z:int64) + 64 * (val (width:int64) DIV 8 - (i + 1)))) (word 48):int64`
    ] THEN
    ASM_REWRITE_TAC [WORD_RULE `word_add x (word y) = word (val x + y)`; ARITH_RULE`8*8*x=64*x`] THEN
    MAP_EVERY EXISTS_TAC [`0`;`0`;`0`;`0`] THEN
    REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC;

    REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_64; VAL_WORD] THEN
    SUBGOAL_THEN `(8 * (i + 1)) < 2 EXP 64`
        (fun thm -> REWRITE_TAC[MATCH_MP MOD_LT thm] THEN ASSUME_TAC thm) THENL [
      TRANS_TAC LET_TRANS `val (width:int64)` THEN
      CONJ_TAC THENL [
        IMP_REWRITE_TAC [GSYM LDIV_LT_EQ] THEN ARITH_TAC;
        UNDISCH_TAC `8 * val (width:int64) < 2 EXP 64` THEN ARITH_TAC
      ];

      ALL_TAC
    ] THEN
    REWRITE_TAC[ARITH_RULE `8 MOD 2 EXP 64 = 8`] THEN
    ONCE_REWRITE_TAC[MATCH_MP ADD_SUB_SWAP (ARITH_RULE`2 EXP 64>=8 /\ 8*(i+1)>=8`)] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    REWRITE_TAC[MOD_REFL;MOD_MOD_REFL;ADD;ARITH_RULE`8*(i+1)-8=8*i`] THEN
    SUBGOAL_THEN `8*i < 2 EXP 64` (fun thm -> REWRITE_TAC[MATCH_MP MOD_LT thm]) THENL [
      UNDISCH_TAC `8*(i+1)<2 EXP 64` THEN ARITH_TAC; ALL_TAC
    ] THEN ARITH_TAC
  ];

  (* 4. loop backedge *)
  REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--1);

  ALL_TAC
  ] THEN

(* bignum_copy_row_from_table_outerloop *)
  ENSURES_WHILE_PUP_TAC `val (height:64 word):num` `pc + 0x38` `pc + 0xa4`
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
  ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--3) THEN
  REWRITE_TAC[ARITH_RULE `x * 0 = 0`; ARITH_RULE `0 * x = 0`; WORD_ADD_0] THEN
  SUBGOAL_THEN `8 * (val (width:int64) DIV 8 - 0) = val width` (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm])) THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LE_0];

  (* 3. loop body - pass *)
  ALL_TAC;

  (* 4. loop backedge *)
  REPEAT STRIP_TAC THEN
  ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--1);

  (* next *)
  ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC [1;2] THEN
  CASES_FIRST_DISJ_ASSUM_TAC THEN SPLIT_FIRST_CONJ_ASSUM_TAC THENL [
    UNDISCH_TAC `val (idx:int64) < val (height:int64)` THEN
    UNDISCH_TAC `val (height:int64) <= val (idx:int64)` THEN
    ARITH_TAC;

    ASM_MESON_TAC[]]
] THEN

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [ASM_MESON_TAC[LT_WORD_64]; ALL_TAC] THEN
  SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [
    TRANS_TAC LET_TRANS `val (height:int64)` THEN
    CONJ_TAC THENL [
      UNDISCH_TAC `i < val (height:int64)` THEN ARITH_TAC;
      REWRITE_TAC[VAL_BOUND_64]];

    ALL_TAC] THEN

  ENSURES_WHILE_PDOWN_TAC `(val (width:64 word) DIV 8):num` `pc + 0x4c` `pc + 0x98`
  `\j s.  (read X30 s = returnaddress /\ read X0 s = z /\ read X1 s = table /\
          read X2 s = height /\ read X3 s = width /\ read X4 s = idx /\ read X5 s = word i /\
          read Q16 s = (if i = val idx then word 340282366920938463463374607431768211455 else word 0) /\
          read X7 s = word (8 * j) /\
          // pointers
          read X8 s = word_add table (word (8 * (i * val width + (val width - 8 * j)))) /\
          read X9 s = word_add z (word (8 * (val width - 8 * j)):64 word) /\
          bignum_from_memory (table, val height * val width) s = n /\
          bignum_from_memory (word_add table (word (8 * val idx * val width)), val width) s
              = m /\
           ((i < val idx /\
             bignum_from_memory (z, val width - 8 * j) s = 0 /\
             bignum_from_memory (word_add z (word (8 * (val width - 8 * j))), 8 * j) s = 0)
            \/
            (i = val idx /\
             bignum_from_memory (z, val width - 8 * j) s = lowdigits m (val width - 8 * j) /\
             bignum_from_memory (word_add z (word (8 * (val width - 8 * j))), 8 * j) s = 0)
            \/
            (i > val idx /\
             bignum_from_memory (z, val width - 8 * j) s = lowdigits m (val width - 8 * j) /\
             bignum_from_memory (word_add z (word (8 * (val width - 8 * j))), 8 * j) s = highdigits m (val width - 8 * j)))) /\
          (read ZF s <=> j = 0)` THEN REPEAT CONJ_TAC THENL [
  ASM_ARITH_TAC;

  ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--5) THEN
  SUBGOAL_THEN `8 * val (width:int64) DIV 8 = val width` (fun thm -> REWRITE_TAC[thm]) THENL [
    UNDISCH_TAC `val (width:int64) MOD 8 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUB_REFL; WORD_VAL; ADD_0; MULT_0; WORD_ADD_0] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_0; LOWDIGITS_0; HIGHDIGITS_0] THEN
    CONJ_TAC THENL [
    ASM_CASES_TAC `i = val (idx:int64)` THENL [
      ASM_REWRITE_TAC[VAL_WORD] THEN IMP_REWRITE_TAC[MOD_LT; VAL_BOUND] THEN
      CONV_TAC WORD_REDUCE_CONV;

      ASM_REWRITE_TAC[VAL_WORD] THEN IMP_REWRITE_TAC[DIMINDEX_64; MOD_LT] THEN
      CONV_TAC WORD_REDUCE_CONV];

    ASM_CASES_TAC `i > val (idx:int64)` THENL [
      SUBGOAL_THEN `~(i <= val (idx:int64))` ASSUME_TAC THENL
        [ASM_REWRITE_TAC[NOT_LE; GSYM GT]; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `i > val (idx:int64)`] THEN
      REWRITE_ASSUMES_TAC `i > val (idx:int64)` THEN
      REWRITE_ASSUMES_TAC `~(i <= val (idx:int64))` THEN
      ASM_REWRITE_TAC[];

      SUBGOAL_THEN `i <= val (idx:int64)` ASSUME_TAC THENL
        [UNDISCH_TAC `~(i > val (idx:int64))` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_ASSUMES_TAC `i <= val (idx:int64)` THEN
      REWRITE_ASSUMES_TAC `~(i > val (idx:int64))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i <= val (idx:int64)` THEN
      ARITH_TAC]];

  (* loop body *)
  ALL_TAC;

  (* backedge *)
  REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC [1];

  (* finishes outer loop; pc ac -> b4 *)
  ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC [1;2;3] THEN
  REWRITE_TAC[WORD_ADD; ARITH_RULE `a*b+b-8*0=(a+1)*b`] THEN
  REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;ARITH_RULE `1 MOD 2 EXP 64 = 1`; ADD_0] THEN
  REWRITE_TAC[MATCH_MP MOD_LT (ASSUME `i < 2 EXP 64`); MATCH_MP MOD_LT (ASSUME `i + 1 < 2 EXP 64`)] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `8*0=0`; SUB_0; READ_MEMORY_BYTES_0]) THEN
  SUBGOAL_THEN `m < 2 EXP (64 * val (width:int64))` ASSUME_TAC THENL
    [EXPAND_TAC "m" THEN SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [MATCH_MP LOWDIGITS_SELF (ASSUME `m < 2 EXP (64 * val (width:int64))`)]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [MATCH_MP HIGHDIGITS_ZERO (ASSUME `m < 2 EXP (64 * val (width:int64))`)]) THEN

  ASM_CASES_TAC `i < val (idx:int64)` THENL [
    REWRITE_ASSUMES_TAC `i < val (idx:int64)` THEN
    ASSERT_USING_UNDISCH_AND_ARITH_TAC `~(i = val (idx:int64))` `i < val (idx:int64)` THEN
    ASSERT_USING_UNDISCH_AND_ARITH_TAC `~(i > val (idx:int64))` `i < val (idx:int64)` THEN
    MAP_EVERY REWRITE_ASSUMES_TAC [`~(i = val (idx:int64))`; `~(i > val (idx:int64))`] THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    UNDISCH_TAC `i < val (idx:int64)` THEN ARITH_TAC;

    ASM_CASES_TAC `i = val (idx:int64)` THENL [
      REWRITE_ASSUMES_TAC `i = val (idx:int64)` THEN
      RULE_ASSUM_TAC (REWRITE_RULE [LT_REFL; GT_REFL; SUB_0]) THEN
      DISJ2_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `p + 1 > p`];

      REWRITE_ASSUMES_TAC `~(i = val (idx:int64))` THEN
      REWRITE_ASSUMES_TAC `~(i < val (idx:int64))` THEN
      SPLIT_FIRST_CONJ_ASSUM_TAC THEN (* get `i > val idx` *)
      DISJ2_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `x > y ==> x + 1 > y`; ASSUME `i > val (idx:int64)`]
    ]]

  ] THEN


  REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [
      memory :> bytes128 (word_add (z:int64) (word (8 * (val (width:int64) - 8 * (i' + 1)))));
      memory :> bytes128 (word_add (z:int64) (word (8 * (val (width:int64) - 8 * (i' + 1)) + 16)));
      memory :> bytes128 (word_add (z:int64) (word (8 * (val (width:int64) - 8 * (i' + 1)) + 32)));
      memory :> bytes128 (word_add (z:int64) (word (8 * (val (width:int64) - 8 * (i' + 1)) + 48)))]` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  CONJ_TAC THENL [
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    (* SIMPLE_ARITH_TAC isn't good at dealing with assumptions containing 'val'. Let's abbreviate
       val width. *)
    REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    ABBREV_TAC `w' = val (width:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC;

    ALL_TAC] THEN

  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY ASSERT_USING_ASM_ARITH_TAC [
  `val (width:int64) - 8 * (i' + 1) + 2 <= val width`;
  `(val (width:int64) - 8 * (i' + 1) + 2) + 2 <= val width`;
  `(val (width:int64) - 8 * (i' + 1) + 4) + 2 <= val width`;
  `(val (width:int64) - 8 * (i' + 1) + 6) + 2 <= val width`] THEN
  MAP_EVERY (fun t -> ASSERT_USING_UNDISCH_AND_ARITH_TAC t `8 * val (width:int64) < 2 EXP 64`) [
  `(8 * (val (width:int64) - 8 * (i' + 1)) + 48) + 16 <= 18446744073709551616`;
  `(8 * (val (width:int64) - 8 * (i' + 1)) + 32) + 16 <= 18446744073709551616`;
  `(8 * (val (width:int64) - 8 * (i' + 1)) + 16) + 16 <= 18446744073709551616`;
  `8 * (val (width:int64) - 8 * (i' + 1)) + 16 <= 18446744073709551616`] THEN
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL [
    TRANS_TAC LE_TRANS `i * val (width:int64) + val width` THEN CONJ_TAC THENL
    [UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;
     IMP_REWRITE_TAC [LE_MULT_ADD]];
    ALL_TAC
  ]) [
  `((i * val (width:int64) + val width - 8 * (i' + 1)) + 6) + 2 <= val (height:int64) * val width`;
  `((i * val (width:int64) + val width - 8 * (i' + 1)) + 4) + 2 <= val (height:int64) * val width`;
  `((i * val (width:int64) + val width - 8 * (i' + 1)) + 2) + 2 <= val (height:int64) * val width`;
  `(i * val (width:int64) + val width - 8 * (i' + 1)) + 2 <= val (height:int64) * val width`] THEN
  MAP_EVERY (fun i ->
    let si = string_of_int i in
    ABBREV_TABLE_READ_128BITS_TAC ("p" ^ si) "s0" (i*16) THEN
    ABBREV_Z_READ_128BITS_TAC ("q" ^ si) "s0" (i*16)) (0--3) THEN

  ASM_CASES_TAC `i = val (idx:int64)` THENL [
  (* case 1 *)
  REWRITE_TAC[ASSUME `i = val (idx:int64)`; LT_REFL; GT_REFL] THEN
  REWRITE_ASSUMES_TAC `i = val (idx:int64)` THEN
  RULE_ASSUM_TAC (REWRITE_RULE [LT_REFL; GT_REFL]) THEN
  SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  SUBGOAL_THEN
    `val (q0:int128) = lowdigits 0 2 /\ val (q1:int128) = lowdigits (highdigits 0 2) 2 /\
      val (q2:int128) = lowdigits (highdigits 0 4) 2 /\ val (q3:int128) = lowdigits (highdigits 0 6) 2`
    (fun thm ->
      let thm2 = REWRITE_RULE
        [LOWDIGITS_TRIVIAL; HIGHDIGITS_TRIVIAL; WORD_ARITH `val (x:int128) = 0 <=> x = word 0`]
        thm in
      RULE_ASSUM_TAC (REWRITE_RULE [thm2])) THENL [
    MAP_EVERY EXPAND_TAC ["q0";"q1";"q2";"q3"] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC_CONSTS] THEN REWRITE_TAC(map ARITH_RULE [`16=8*2`;`32=8*4`;`48=8*6`]) THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC READ_MEMORY_BYTES_FIRSTELEM128 THEN EXISTS_TAC `8 * (i' + 1)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

      REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128] THEN
      REWRITE_TAC[ARITH_RULE `16=8*2`] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES_SLICE THEN EXISTS_TAC `8 * (i' + 1)` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];

    ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :>
      bytes (word_add (word_add (z:int64) (word (8 * (val (width:int64) - 8 * (i' + 1))))) (word (8 * 8)),
            8 * 8 * i')) s0 =
      highdigits 0 8` (fun thm ->
      ASSUME_TAC (REWRITE_RULE [HIGHDIGITS_TRIVIAL; WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*8=64`] thm)) THENL [
    MATCH_MP_TAC READ_MEMORY_BYTES_SLICE_HIGH THEN
    EXISTS_TAC `8 * (i' + 1)` THEN ASM_REWRITE_TAC[ARITH_RULE `8*(x+1)=8+8*x`];

    ALL_TAC] THEN
  ABBREV_TAC `i'' = val (width:int64) - 8 * (i'+1)` THEN
  ASSERT_USING_ASM_ARITH_TAC `(8 * i'' + 64) + 8 * 8 * i' <= 18446744073709551616` THEN

  ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--19) THEN
  ENSURES_FINAL_STATE_TAC THEN
  SUBST_ALL_TAC (GSYM (ASSUME `val (width:int64) - 8 * (i' + 1) = i''`)) THEN
  SUBGOAL_THEN `8 * (val (width:int64) - 8 * (i' + 1)) + 64 = 8 * (val width - 8 * i')` SUBST_ALL_TAC THENL [
  UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[WORD_SUB_ADD; WORD_ADD_ASSOC_CONSTS;
    WORD_RULE `word_sub (word (8 * (i' + 1))) (word 8):int64 = word (8 * i')`] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;

    REPEAT AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;

    MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
    MAP_EVERY EXISTS_TAC [`val (width:int64) - 8 * (i'+1)`; `8`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [
      REWRITE_TAC[LOWDIGITS_LOWDIGITS] THEN AP_TERM_TAC THEN ARITH_TAC;

      REWRITE_TAC[ARITH_RULE`8*8=64`] THEN MATCH_MP_TAC READ_MEMORY_BYTES_MERGE_FOUR128 THEN
      MAP_EVERY EXISTS_TAC [
        `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 16)):int64`;
        `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 32)):int64`;
        `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 48)):int64`;
      ] THEN
      MAP_EVERY EXISTS_TAC [`val (p0:int128)`;`val (p1:int128)`;`val (p2:int128)`;`val (p3:int128)`] THEN
      ASM_REWRITE_TAC[WORD_AND_128_FULLBITS] THEN
      REPEAT CONJ_TAC THEN TRY (REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC WORD_ARITH) THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read Q17 s19 = p3`] THEN
      MAP_EVERY EXPAND_TAC ["p0";"p1";"p2";"p3";"m"] THEN
      REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128;ARITH_RULE`16=8*2`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY;ARITH_RULE`MIN x (x-y) = x-y`] THEN
      REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
      SUBGOAL_THEN `val (width:int64) - 8 * i' - (val width - 8 * (i' + 1)) = 8` (fun thm -> REWRITE_TAC[thm]) THENL [
        UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC; ALL_TAC
      ] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      REWRITE_TAC((map PAIR_EQ_ARITH_RULE [
          (`(x:int64,8)`, `(x:int64,2+6)`);
          (`(x:int64,6)`, `(x:int64,2+4)`);
          (`(x:int64,4)`, `(x:int64,2+2)`)]) @ [BIGNUM_FROM_MEMORY_SPLIT]) THEN
      REWRITE_TAC [WORD_ADD_ASSOC_CONSTS; LEFT_ADD_DISTRIB;MULT_ASSOC;GSYM EXP_ADD;GSYM ADD_ASSOC] THEN
      ARITH_TAC;

      UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC
    ];

    IMP_REWRITE_TAC[VAL_WORD_8_EQ_0]
  ]; ALL_TAC] THEN

  (* case 2 *)
  REWRITE_ASSUMES_TAC `~(i = val (idx:int64))` THEN
  REWRITE_TAC[ASSUME `~(i = val (idx:int64))`] THEN
  ASM_CASES_TAC `i < val (idx:int64)` THENL [
    ASSERT_USING_UNDISCH_AND_ARITH_TAC `~(i > val (idx:int64))` `i < val (idx:int64)` THEN
    MAP_EVERY REWRITE_ASSUMES_TAC [`~(i > val (idx:int64))`; `i < val (idx:int64)`] THEN
    MAP_EVERY (fun t -> REWRITE_TAC[ASSUME t]) [`~(i > val (idx:int64))`; `i < val (idx:int64)`] THEN
    SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    SUBGOAL_THEN
      `val (q0:int128) = lowdigits 0 2 /\ val (q1:int128) = lowdigits (highdigits 0 2) 2 /\
        val (q2:int128) = lowdigits (highdigits 0 4) 2 /\ val (q3:int128) = lowdigits (highdigits 0 6) 2`
      (fun thm ->
        let thm2 = REWRITE_RULE
          [LOWDIGITS_TRIVIAL; HIGHDIGITS_TRIVIAL; WORD_ARITH `val (x:int128) = 0 <=> x = word 0`]
          thm in
        RULE_ASSUM_TAC (REWRITE_RULE [thm2])) THENL [
      MAP_EVERY EXPAND_TAC ["q0";"q1";"q2";"q3"] THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC_CONSTS] THEN REWRITE_TAC(map ARITH_RULE [`16=8*2`;`32=8*4`;`48=8*6`]) THEN
      CONJ_TAC THENL [
        MATCH_MP_TAC READ_MEMORY_BYTES_FIRSTELEM128 THEN EXISTS_TAC `8 * (i' + 1)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

        REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128] THEN
        REWRITE_TAC[ARITH_RULE `16=8*2`] THEN
        REPEAT CONJ_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES_SLICE THEN EXISTS_TAC `8 * (i' + 1)` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];

      ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :>
        bytes (word_add (word_add (z:int64) (word (8 * (val (width:int64) - 8 * (i' + 1))))) (word (8 * 8)),
              8 * 8 * i')) s0 =
        highdigits 0 8` (fun thm ->
        ASSUME_TAC (REWRITE_RULE [HIGHDIGITS_TRIVIAL; WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*8=64`] thm)) THENL [
      MATCH_MP_TAC READ_MEMORY_BYTES_SLICE_HIGH THEN
      EXISTS_TAC `8 * (i' + 1)` THEN ASM_REWRITE_TAC[ARITH_RULE `8*(x+1)=8+8*x`];

      ALL_TAC] THEN
    ABBREV_TAC `i'' = val (width:int64) - 8 * (i'+1)` THEN
    ASSERT_USING_ASM_ARITH_TAC `(8 * i'' + 64) + 8 * 8 * i' <= 18446744073709551616` THEN

    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN
    SUBST_ALL_TAC (GSYM (ASSUME `val (width:int64) - 8 * (i' + 1) = i''`)) THEN
    SUBGOAL_THEN `8 * (val (width:int64) - 8 * (i' + 1)) + 64 = 8 * (val width - 8 * i')` SUBST_ALL_TAC THENL [
    UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB_ADD; WORD_ADD_ASSOC_CONSTS;
      WORD_RULE `word_sub (word (8 * (i' + 1))) (word 8):int64 = word (8 * i')`] THEN
    REPEAT CONJ_TAC THENL [
      REPEAT AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;

      REPEAT AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;

      MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
      MAP_EVERY EXISTS_TAC [`val (width:int64) - 8 * (i'+1)`; `8`] THEN
      ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL] THEN
      CONJ_TAC THENL [
        REWRITE_TAC[ARITH_RULE`8*8=64`] THEN MATCH_MP_TAC READ_MEMORY_BYTES_MERGE_FOUR128 THEN
        MAP_EVERY EXISTS_TAC [
          `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 16)):int64`;
          `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 32)):int64`;
          `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 48)):int64`;
        ] THEN
        MAP_EVERY EXISTS_TAC [`val (word 0:int128)`;`val (word 0:int128)`;`val (word 0:int128)`;`val (word 0:int128)`] THEN
        ASM_REWRITE_TAC[VAL_WORD_0; WORD_AND_0; HIGHDIGITS_TRIVIAL; MULT_0; ADD_0] THEN
        REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC WORD_ARITH;

        UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC
      ];

      IMP_REWRITE_TAC[VAL_WORD_8_EQ_0]
    ]; ALL_TAC] THEN

  ASSERT_USING_ASM_ARITH_TAC `i > val (idx:int64)` THEN
  MAP_EVERY REWRITE_ASSUMES_TAC [`~(i < val (idx:int64))`; `i > val (idx:int64)`] THEN
  MAP_EVERY (fun t -> REWRITE_TAC[ASSUME t]) [`~(i < val (idx:int64))`; `i > val (idx:int64)`] THEN
  SPLIT_FIRST_CONJ_ASSUM_TAC THEN

  ABBREV_TAC `i'' = val (width:int64) - 8 * (i'+1)` THEN
  SUBGOAL_THEN `read (memory :> bytes (z, 8 * val (width:int64))) s0 = m` ASSUME_TAC THENL [
    MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
    MAP_EVERY EXISTS_TAC [`i'':num`; `8*((i':num)+1)`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "i''" THEN ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN
      `(q0:int128) = word (lowdigits (highdigits m i'') 2) /\
      (q1:int128) = word (lowdigits (highdigits m (i''+2)) 2) /\
      (q2:int128) = word (lowdigits (highdigits m (i''+4)) 2) /\
      (q3:int128) = word (lowdigits (highdigits m (i''+6)) 2)`
      (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm])) THENL [
    MAP_EVERY EXPAND_TAC ["q0";"q1";"q2";"q3"] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC_CONSTS] THEN REWRITE_TAC(map ARITH_RULE [`16=8*2`;`32=8*4`;`48=8*6`]) THEN
    REPEAT CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    SIMP_TAC[VAL_WORD_EQ;DIMINDEX_128;ARITH_RULE`128=64*2`;LOWDIGITS_BOUND] THENL [
      MATCH_MP_TAC READ_MEMORY_BYTES_FIRSTELEM128 THEN EXISTS_TAC `8 * (i' + 1)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

      REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128] THEN
      REWRITE_TAC[ARITH_RULE `16=8*2`; WORD_ADD_ASSOC_CONSTS; GSYM LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC READ_MEMORY_BYTES_SLICE THEN EXISTS_TAC `val (width:int64)` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

      REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128] THEN
      REWRITE_TAC[ARITH_RULE `16=8*2`; WORD_ADD_ASSOC_CONSTS; GSYM LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC READ_MEMORY_BYTES_SLICE THEN EXISTS_TAC `val (width:int64)` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

      REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128] THEN
      REWRITE_TAC[ARITH_RULE `16=8*2`; WORD_ADD_ASSOC_CONSTS; GSYM LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC READ_MEMORY_BYTES_SLICE THEN EXISTS_TAC `val (width:int64)` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ];

    ALL_TAC
  ] THEN
  SUBGOAL_THEN `read (memory :>
      bytes (word_add (word_add (z:int64) (word (8 * i''))) (word (8 * 8)), 8 * 8 * i')) s0 =
      highdigits (highdigits m i'') 8` (fun thm ->
      ASSUME_TAC (REWRITE_RULE [HIGHDIGITS_HIGHDIGITS; WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8*8=64`] thm)) THENL [
    MATCH_MP_TAC READ_MEMORY_BYTES_SLICE_HIGH THEN
    EXISTS_TAC `8 * (i' + 1)` THEN ASM_REWRITE_TAC[ARITH_RULE `8*(x+1)=8+8*x`];

    ALL_TAC] THEN
  ASSERT_USING_ASM_ARITH_TAC `(8 * i'' + 64) + 8 * 8 * i' <= 18446744073709551616` THEN

  ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_8N_EXEC (1--19) THEN
  ENSURES_FINAL_STATE_TAC THEN
  SUBST_ALL_TAC (GSYM (ASSUME `val (width:int64) - 8 * (i' + 1) = i''`)) THEN
  SUBGOAL_THEN `8 * (val (width:int64) - 8 * (i' + 1)) + 64 = 8 * (val width - 8 * i')` SUBST_ALL_TAC THENL [
  UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[WORD_SUB_ADD; WORD_ADD_ASSOC_CONSTS;
    WORD_RULE `word_sub (word (8 * (i' + 1))) (word 8):int64 = word (8 * i')`] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;

    REPEAT AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;

    MATCH_MP_TAC READ_MEMORY_BYTES_MERGE THEN
    MAP_EVERY EXISTS_TAC [`val (width:int64) - 8 * (i'+1)`; `8`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [
      REWRITE_TAC[LOWDIGITS_LOWDIGITS] THEN AP_TERM_TAC THEN ARITH_TAC;

      REWRITE_TAC[ARITH_RULE`8*8=64`] THEN MATCH_MP_TAC READ_MEMORY_BYTES_MERGE_FOUR128 THEN
      MAP_EVERY EXISTS_TAC [
        `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 16)):int64`;
        `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 32)):int64`;
        `word_add z (word (8 * (val (width:int64) - 8 * (i' + 1)) + 48)):int64`;
      ] THEN
      MAP_EVERY EXISTS_TAC [
        `lowdigits (highdigits m (val (width:int64) - 8 * (i' + 1))) 2`;
        `lowdigits (highdigits m (val (width:int64) - 8 * (i' + 1) + 2)) 2`;
        `lowdigits (highdigits m (val (width:int64) - 8 * (i' + 1) + 4)) 2`;
        `lowdigits (highdigits m (val (width:int64) - 8 * (i' + 1) + 6)) 2`] THEN
      ASM_SIMP_TAC [WORD_AND_0;WORD_OR_0;VAL_WORD_EQ;DIMINDEX_128;ARITH_RULE`128=64*2`;LOWDIGITS_BOUND;WORD_AND_128_FULLBITS] THEN
      REPEAT CONJ_TAC THEN TRY (REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC WORD_ARITH) THEN
      EXPAND_TAC "m" THEN
      REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES128;ARITH_RULE`16=8*2`;GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY;ARITH_RULE`MIN x (x-y) = x-y`;HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
      IMP_REWRITE_TAC (map ARITH_RULE [
        `!x y. y < x DIV 8 ==> MIN (x-(x-8*(y+1)+6)) 2 = 2`;
        `!x y. y < x DIV 8 ==> MIN (x-(x-8*(y+1)+4)) 2 = 2`;
        `!x y. y < x DIV 8 ==> MIN (x-(x-8*(y+1)+2)) 2 = 2`;
        `!x y. y < x DIV 8 ==> MIN (x-(x-8*(y+1))) 2 = 2`
      ]) THEN
      SUBGOAL_THEN `val (width:int64) - 8 * i' - (val width - 8 * (i' + 1)) = 8` (fun thm -> REWRITE_TAC[thm]) THENL [
        UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC; ALL_TAC
      ] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      REWRITE_TAC((map PAIR_EQ_ARITH_RULE [
          (`(x:int64,8)`, `(x:int64,2+6)`);
          (`(x:int64,6)`, `(x:int64,2+4)`);
          (`(x:int64,4)`, `(x:int64,2+2)`)]) @ [BIGNUM_FROM_MEMORY_SPLIT]) THEN
      REWRITE_TAC [WORD_ADD_ASSOC_CONSTS; LEFT_ADD_DISTRIB;MULT_ASSOC;GSYM EXP_ADD;GSYM ADD_ASSOC] THEN
      ARITH_TAC;

      UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC
    ];

    AP_TERM_TAC THEN UNDISCH_TAC `i' < val (width:int64) DIV 8` THEN ARITH_TAC;

    IMP_REWRITE_TAC[VAL_WORD_8_EQ_0]
  ]);;
