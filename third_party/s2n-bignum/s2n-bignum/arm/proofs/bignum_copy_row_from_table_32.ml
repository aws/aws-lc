(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time table lookup.                                               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

let bignum_copy_row_from_table_32_mc =
  define_assert_from_elf "bignum_copy_row_from_table_32_mc"
                         "arm/generic/bignum_copy_row_from_table_32.o"
[
  0x4e080ff4;       (* arm_DUP_GEN Q20 XZR *)
  0x4eb41e95;       (* arm_MOV_VEC Q21 Q20 128 *)
  0x4eb41e96;       (* arm_MOV_VEC Q22 Q20 128 *)
  0x4eb41e97;       (* arm_MOV_VEC Q23 Q20 128 *)
  0x4eb41e98;       (* arm_MOV_VEC Q24 Q20 128 *)
  0x4eb41e99;       (* arm_MOV_VEC Q25 Q20 128 *)
  0x4eb41e9a;       (* arm_MOV_VEC Q26 Q20 128 *)
  0x4eb41e9b;       (* arm_MOV_VEC Q27 Q20 128 *)
  0x4eb41e9c;       (* arm_MOV_VEC Q28 Q20 128 *)
  0x4eb41e9d;       (* arm_MOV_VEC Q29 Q20 128 *)
  0x4eb41e9e;       (* arm_MOV_VEC Q30 Q20 128 *)
  0x4eb41e9f;       (* arm_MOV_VEC Q31 Q20 128 *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0x4eb41e81;       (* arm_MOV_VEC Q1 Q20 128 *)
  0x4eb41e82;       (* arm_MOV_VEC Q2 Q20 128 *)
  0x4eb41e83;       (* arm_MOV_VEC Q3 Q20 128 *)
  0xd2800006;       (* arm_MOV X6 (rvalue (word 0)) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0xda9f13e5;       (* arm_CSETM X5 Condition_EQ *)
  0x4e080cb1;       (* arm_DUP_GEN Q17 X5 *)
  0x3dc00030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 0)) *)
  0x6eb11e14;       (* arm_BIT Q20 Q16 Q17 128 *)
  0x3dc00430;       (* arm_LDR Q16 X1 (Immediate_Offset (word 16)) *)
  0x6eb11e15;       (* arm_BIT Q21 Q16 Q17 128 *)
  0x3dc00830;       (* arm_LDR Q16 X1 (Immediate_Offset (word 32)) *)
  0x6eb11e16;       (* arm_BIT Q22 Q16 Q17 128 *)
  0x3dc00c30;       (* arm_LDR Q16 X1 (Immediate_Offset (word 48)) *)
  0x6eb11e17;       (* arm_BIT Q23 Q16 Q17 128 *)
  0x3dc01030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 64)) *)
  0x6eb11e18;       (* arm_BIT Q24 Q16 Q17 128 *)
  0x3dc01430;       (* arm_LDR Q16 X1 (Immediate_Offset (word 80)) *)
  0x6eb11e19;       (* arm_BIT Q25 Q16 Q17 128 *)
  0x3dc01830;       (* arm_LDR Q16 X1 (Immediate_Offset (word 96)) *)
  0x6eb11e1a;       (* arm_BIT Q26 Q16 Q17 128 *)
  0x3dc01c30;       (* arm_LDR Q16 X1 (Immediate_Offset (word 112)) *)
  0x6eb11e1b;       (* arm_BIT Q27 Q16 Q17 128 *)
  0x3dc02030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 128)) *)
  0x6eb11e1c;       (* arm_BIT Q28 Q16 Q17 128 *)
  0x3dc02430;       (* arm_LDR Q16 X1 (Immediate_Offset (word 144)) *)
  0x6eb11e1d;       (* arm_BIT Q29 Q16 Q17 128 *)
  0x3dc02830;       (* arm_LDR Q16 X1 (Immediate_Offset (word 160)) *)
  0x6eb11e1e;       (* arm_BIT Q30 Q16 Q17 128 *)
  0x3dc02c30;       (* arm_LDR Q16 X1 (Immediate_Offset (word 176)) *)
  0x6eb11e1f;       (* arm_BIT Q31 Q16 Q17 128 *)
  0x3dc03030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 192)) *)
  0x6eb11e00;       (* arm_BIT Q0 Q16 Q17 128 *)
  0x3dc03430;       (* arm_LDR Q16 X1 (Immediate_Offset (word 208)) *)
  0x6eb11e01;       (* arm_BIT Q1 Q16 Q17 128 *)
  0x3dc03830;       (* arm_LDR Q16 X1 (Immediate_Offset (word 224)) *)
  0x6eb11e02;       (* arm_BIT Q2 Q16 Q17 128 *)
  0x3dc03c30;       (* arm_LDR Q16 X1 (Immediate_Offset (word 240)) *)
  0x6eb11e03;       (* arm_BIT Q3 Q16 Q17 128 *)
  0x91040021;       (* arm_ADD X1 X1 (rvalue (word 256)) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xeb06005f;       (* arm_CMP X2 X6 *)
  0x54fffb41;       (* arm_BNE (word 2097000) *)
  0x3d800014;       (* arm_STR Q20 X0 (Immediate_Offset (word 0)) *)
  0x3d800415;       (* arm_STR Q21 X0 (Immediate_Offset (word 16)) *)
  0x3d800816;       (* arm_STR Q22 X0 (Immediate_Offset (word 32)) *)
  0x3d800c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 48)) *)
  0x3d801018;       (* arm_STR Q24 X0 (Immediate_Offset (word 64)) *)
  0x3d801419;       (* arm_STR Q25 X0 (Immediate_Offset (word 80)) *)
  0x3d80181a;       (* arm_STR Q26 X0 (Immediate_Offset (word 96)) *)
  0x3d801c1b;       (* arm_STR Q27 X0 (Immediate_Offset (word 112)) *)
  0x3d80201c;       (* arm_STR Q28 X0 (Immediate_Offset (word 128)) *)
  0x3d80241d;       (* arm_STR Q29 X0 (Immediate_Offset (word 144)) *)
  0x3d80281e;       (* arm_STR Q30 X0 (Immediate_Offset (word 160)) *)
  0x3d802c1f;       (* arm_STR Q31 X0 (Immediate_Offset (word 176)) *)
  0x3d803000;       (* arm_STR Q0 X0 (Immediate_Offset (word 192)) *)
  0x3d803401;       (* arm_STR Q1 X0 (Immediate_Offset (word 208)) *)
  0x3d803802;       (* arm_STR Q2 X0 (Immediate_Offset (word 224)) *)
  0x3d803c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 240)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_COPY_ROW_FROM_TABLE_32_EXEC =
  ARM_MK_EXEC_RULE bignum_copy_row_from_table_32_mc;;


let REWRITE_ASSUMES_TAC (t:term) =
    UNDISCH_THEN t (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm]) THEN ASSUME_TAC thm);;

let LT_WORD_64 = prove(`!x (y:int64). x < val y ==> x < 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LT_TRANS `val (y:int64)` THEN
  ONCE_REWRITE_TAC [GSYM DIMINDEX_64] THEN ASM_REWRITE_TAC[VAL_BOUND]);;

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

let ABBREV_TABLE_READ_128BITS_TAC name st ofs =
  let v = mk_var (name, `:int128`) in
  let templ =
    if ofs = 0 then
      `read (memory :> bytes128 (word_add table (word (8 * 32 * i)):int64)) s0`
    else
      let templ0 = `read (memory :> bytes128 (word_add table (word (8 * 32 * i + ofs)):int64)) s0`
 in
      let newofs = mk_numeral (num ofs) in
      subst [(newofs,`ofs:num`)] templ0 in
  let rhs = subst [(mk_var(st,`:armstate`),`st0:armstate`)] templ in
  ABBREV_TAC (mk_eq (v,rhs));;

let VAL_WORD_JOIN_BIGDIGIT = prove(
    `!m i j. val (word_join (word (bigdigit m i):int64) (word (bigdigit m j):int64):int128) =
                 2 EXP 64 * (bigdigit m i) + bigdigit m j`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_128; VAL_WORD] THEN
    IMP_REWRITE_TAC[MOD_LT; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 128 = 2 EXP 64 * 2 EXP 64`] THEN
    IMP_REWRITE_TAC[LT_MULT_ADD_MULT; BIGDIGIT_BOUND; LE_REFL] THEN
    ARITH_TAC);;

let HELPER_RULE = prove(`!table i j k k1 m s.
    read (memory :> bytes (word_add table (word i),8 * 32)) s = m /\
    j = i + 8 * k /\ k1 = k + 1 /\ k + 1 < 32 ==>
    read (memory :> bytes128 (word_add table (word j))) s =
    word_join (word (bigdigit m k1):int64) (word (bigdigit m k):int64)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; GSYM READ_MEMORY_BYTES_BYTES128;ARITH_RULE`16=8*2`] THEN
  EXPAND_TAC "m" THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[VAL_WORD_JOIN_BIGDIGIT] THEN
  REWRITE_TAC[ARITH_RULE `f (x, 2) = f (x, (1+1))`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  ASSERT_USING_ASM_ARITH_TAC `k < 32` THEN
  ASM_REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; BIGNUM_FROM_MEMORY_SING] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  REWRITE_TAC[ARITH_RULE`64*1=64`; ARITH_RULE`(i + 8 * k) + 8 * 1 = i + 8 * (k + 1)`]);;

let HELPER_RULE2 = prove(
  `!height idx. val idx < val height ==>
   (val (word_sub height (word_add idx (word 1)):int64) = 0 <=>
    val idx + 1 = val height)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB;VAL_WORD_ADD;DIMINDEX_64;VAL_WORD;ARITH_RULE`1 MOD 2 EXP 64 = 1`] THEN
  SUBGOAL_THEN `val (height:int64) < 2 EXP 64` ASSUME_TAC THENL [REWRITE_TAC[VAL_BOUND_64]; ALL_TAC] THEN
  SUBGOAL_THEN `(val (idx:int64) + 1) MOD 2 EXP 64 = val (idx:int64) + 1`
  (fun thm -> REWRITE_TAC[thm]) THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (height:int64) + 2 EXP 64 - (val (idx:int64) + 1) =
                2 EXP 64 + val height - (val idx + 1)` (fun thm -> REWRITE_TAC[thm]) THENL [
    MATCH_MP_TAC ADD_SUB_SWAP THEN ASM_ARITH_TAC; ALL_TAC] THEN

  ONCE_REWRITE_TAC[GSYM ADD_MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_REFL; ADD] THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  SUBGOAL_THEN `val (height:int64) - (val (idx:int64) + 1) < 2 EXP 64` ASSUME_TAC THENL [
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT;SUB_EQ_0] THEN ASM_ARITH_TAC);;

let HELPER_RULE3 = prove(
  `!i (idx:int64). i < 2 EXP 64 /\ val idx < 2 EXP 64 /\ i < val idx ==>
      ~(val (word_sub (word i) idx) = 0)`,
  REWRITE_TAC[VAL_WORD_SUB;DIMINDEX_64] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN`val (word i:int64) = i` ASSUME_TAC THENL [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(i + 2 EXP 64 - val (idx:int64)) < 2 EXP 64` (fun thm -> SIMP_TAC[MOD_LT; thm]) THEN
  ASM_ARITH_TAC);;

let HELPER_RULE4 = prove(
  `!i (idx:int64). i < 2 EXP 64 /\ val idx < 2 EXP 64 /\ i > val idx ==>
      ~(val (word_sub (word i) idx) = 0)`,
  REWRITE_TAC[VAL_WORD_SUB;DIMINDEX_64] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN`val (word i:int64) = i` ASSUME_TAC THENL [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i + 2 EXP 64 - val (idx:int64) = 2 EXP 64 + i - val (idx:int64)`
    (fun thm -> REWRITE_TAC[thm]) THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM ADD_MOD_MOD_REFL] THEN REWRITE_TAC[MOD_REFL;ADD] THEN IMP_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC);;


let BIGNUM_COPY_ROW_FROM_TABLE_32_SUBROUTINE_CORRECT = prove(
  `!z table height idx pc n m returnaddress.
    nonoverlapping (word pc, 0x124) (z, 8 * 32) /\
    nonoverlapping (word pc, 0x124) (table, 8 * val height * 32) /\
    nonoverlapping (z, 8 * 16) (table, 8 * val height * 32) /\
    val idx < val height
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_row_from_table_32_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [z; table; height; idx] s /\
           bignum_from_memory (table, val height * 32) s = n /\
           bignum_from_memory (word_add table (word (8 * val idx * 32)), 32) s = m)
      (\s. read PC s = returnaddress /\
           bignum_from_memory (z, 32) s = m)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(z,8 * 32)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  (* bignum_copy_row_from_table_32_loop *)
  ENSURES_WHILE_PUP_TAC `val (height:64 word):num` `pc + 0x44` `pc + 0xdc`
    `\i s.  (read X30 s = returnaddress /\ read X0 s = z /\ read X2 s = height /\ read X3 s = idx /\
            read X6 s = word i /\
            read X1 s = word_add table (word (8 * 32 * i)) /\
            bignum_from_memory (table, val height * 32) s = n /\
            bignum_from_memory (word_add table (word (8 * val idx * 32)), 32) s = m /\
            ((i <= val idx /\
              read Q20 s = word 0 /\ read Q21 s = word 0 /\ read Q22 s = word 0 /\ read Q23 s = word 0 /\
              read Q24 s = word 0 /\ read Q25 s = word 0 /\ read Q26 s = word 0 /\ read Q27 s = word 0 /\
              read Q28 s = word 0 /\ read Q29 s = word 0 /\ read Q30 s = word 0 /\ read Q31 s = word 0 /\
              read Q0 s = word 0  /\ read Q1 s = word 0  /\ read Q2 s = word 0  /\ read Q3 s = word 0) \/
              (i > val idx /\
              read Q20 s = word_join (word (bigdigit m 1):64 word) (word (bigdigit m 0):64 word) /\
              read Q21 s = word_join (word (bigdigit m 3):64 word) (word (bigdigit m 2):64 word) /\
              read Q22 s = word_join (word (bigdigit m 5):64 word) (word (bigdigit m 4):64 word) /\
              read Q23 s = word_join (word (bigdigit m 7):64 word) (word (bigdigit m 6):64 word) /\
              read Q24 s = word_join (word (bigdigit m 9):64 word) (word (bigdigit m 8):64 word) /\
              read Q25 s = word_join (word (bigdigit m 11):64 word) (word (bigdigit m 10):64 word) /\
              read Q26 s = word_join (word (bigdigit m 13):64 word) (word (bigdigit m 12):64 word) /\
              read Q27 s = word_join (word (bigdigit m 15):64 word) (word (bigdigit m 14):64 word) /\
              read Q28 s = word_join (word (bigdigit m 17):64 word) (word (bigdigit m 16):64 word) /\
              read Q29 s = word_join (word (bigdigit m 19):64 word) (word (bigdigit m 18):64 word) /\
              read Q30 s = word_join (word (bigdigit m 21):64 word) (word (bigdigit m 20):64 word) /\
              read Q31 s = word_join (word (bigdigit m 23):64 word) (word (bigdigit m 22):64 word) /\
              read Q0 s = word_join (word (bigdigit m 25):64 word) (word (bigdigit m 24):64 word) /\
              read Q1 s = word_join (word (bigdigit m 27):64 word) (word (bigdigit m 26):64 word) /\
              read Q2 s = word_join (word (bigdigit m 29):64 word) (word (bigdigit m 28):64 word) /\
              read Q3 s = word_join (word (bigdigit m 31):64 word) (word (bigdigit m 30):64 word)))) /\
            (read ZF s <=> i = val height)` THEN REPEAT CONJ_TAC THENL [
    (* 1. height > 0 *)
    ASM_ARITH_TAC;

    (* 2. to loop start *)
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_32_EXEC (1--17) THEN
    REWRITE_TAC[ARITH_RULE `x * 0 = 0`; ARITH_RULE `0 * x = 0`; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[LE_0];

    (* 3. loop body - pass *)
    ALL_TAC;

    (* 4. loop backedge *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC BIGNUM_COPY_ROW_FROM_TABLE_32_EXEC (1--1);

    (* to return *)
    SUBGOAL_THEN `val (height:int64) > val (idx:int64)` (fun thm -> REWRITE_TAC[thm]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(val (height:int64) <= val (idx:int64))` (fun thm -> REWRITE_TAC[thm]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `m < 2 EXP (64 * 32)` ASSUME_TAC THENL [EXPAND_TAC "m" THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_32_EXEC (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE`32 = 2+2+2+2+2+2+2+2+2+2+2+2+2+2+2+2`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT;WORD_ADD_ASSOC_CONSTS] THEN
    REWRITE_TAC(map ARITH_RULE [
        `8*2=16`;`16+16=32`;`16+32=48`;`16+48=64`;`16+64=80`;`16+80=96`;`16+96=112`;
        `16+112=128`;`16+128=144`;`16+144=160`;`16+160=176`;`16+176=192`;`16+192=208`;
        `16+208=224`;`16+224=240`;`16+240=256`]) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;ARITH_RULE`8*2=16`;READ_MEMORY_BYTES_BYTES128] THEN
    REWRITE_TAC[VAL_WORD_JOIN;DIMINDEX_64;DIMINDEX_128] THEN
    IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT;VAL_BOUND_64;BIGDIGIT_BOUND] THEN
    IMP_REWRITE_TAC[ARITH_RULE`2 EXP 128 = 2 EXP 64 * 2 EXP 64`;LT_MULT_ADD_MULT;ARITH_RULE`0 < 2 EXP 64`;BIGDIGIT_BOUND;LE_REFL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM HIGHDIGITS_0] THEN
    REPEAT_N 32 (ONCE_REWRITE_TAC[HIGHDIGITS_STEP]) THEN
    CONV_TAC (DEPTH_CONV NUM_ADD_CONV) THEN
    SUBGOAL_THEN `highdigits m 32 = 0` (fun thm -> REWRITE_TAC[thm]) THENL [ASM_REWRITE_TAC[HIGHDIGITS_EQ_0]; ALL_TAC]
    THEN ARITH_TAC
  ] THEN

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  REPEAT_I_N 0 16 (fun i-> ABBREV_TABLE_READ_128BITS_TAC ("tmp" ^ string_of_int i) "s0" (16*i)) THEN
  ASM_CASES_TAC `i <= val (idx:int64)` THENL [
    REWRITE_ASSUMES_TAC `i <= val (idx:int64)` THEN
    ASSERT_USING_ASM_ARITH_TAC `~(i > val (idx:int64))` THEN
    REWRITE_ASSUMES_TAC `~(i > val (idx:int64))` THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_32_EXEC (1--38) THEN
    ASM_CASES_TAC `i = val (idx:int64)` THENL [
      ASSERT_USING_UNDISCH_AND_ARITH_TAC `i + 1 > val (idx:int64)` `i = val (idx:int64)` THEN
      ASSERT_USING_UNDISCH_AND_ARITH_TAC `~(i + 1 <= val (idx:int64))` `i = val (idx:int64)` THEN
      REWRITE_TAC(map ASSUME [`i + 1 > val (idx:int64)`; `~(i + 1 <= val (idx:int64))`]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_AND_0; WORD_VAL; WORD_SUB_REFL; VAL_WORD_0; WORD_OR_0;
          WORD_BLAST `word_and (x:int128) (word_join (word 18446744073709551615:int64)
              (word 18446744073709551615:int64):int128) = x`] THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read Q16 s38 = tmp15`] THEN
      REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THENL
        (* solve equalities involving tmp0 ~ tmp15 *)
        (let t = MATCH_MP_TAC HELPER_RULE THEN EXISTS_TAC `8 * i * 32` THEN
                ASM_REWRITE_TAC[] THEN ARITH_TAC in
        (map (fun i -> EXPAND_TAC ("tmp" ^ string_of_int i) THEN t) (0--15)) @ [ALL_TAC]) THEN
      IMP_REWRITE_TAC[HELPER_RULE2];

      SUBGOAL_THEN `i+1 <= val (idx:int64)` (fun thm -> REWRITE_TAC[thm]) THENL
        [MAP_EVERY UNDISCH_TAC [`~(i = val (idx:int64))`; `i <= val (idx:int64)`] THEN ARITH_TAC;ALL_TAC] THEN
      SUBGOAL_THEN `~((i+1) > val (idx:int64))` (fun thm -> REWRITE_TAC[thm]) THENL
        [MAP_EVERY UNDISCH_TAC [`~(i = val (idx:int64))`; `i <= val (idx:int64)`] THEN ARITH_TAC;ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(val (word_sub (word i) idx:int64) = 0)` (fun thm -> REWRITE_TAC[thm]) THENL [
        MATCH_MP_TAC HELPER_RULE3 THEN REPEAT CONJ_TAC THENL [
          IMP_REWRITE_TAC[LT_WORD_64];
          IMP_REWRITE_TAC[LT_WORD_64];
          MAP_EVERY UNDISCH_TAC [`i <= val (idx:int64)`; `~(i = val (idx:int64))`] THEN ARITH_TAC
        ];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC WORD_RULE) THEN
      IMP_REWRITE_TAC[HELPER_RULE2] THEN
      SUBGOAL_THEN `val (word i:int64)=i` (fun thm->REWRITE_TAC[thm]) THENL [
        SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[LT_WORD_64];

          ALL_TAC] THEN
        IMP_REWRITE_TAC[VAL_WORD;MOD_LT;DIMINDEX_64];

        ALL_TAC] THEN
      ASM_REWRITE_TAC[]
    ];

    REWRITE_ASSUMES_TAC `~(i <= val (idx:int64))` THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    ASSERT_USING_UNDISCH_AND_ARITH_TAC `i + 1 > val (idx:int64)` `i > val (idx:int64)` THEN
    ASSERT_USING_UNDISCH_AND_ARITH_TAC `~(i + 1 <= val (idx:int64))` `i > val (idx:int64)` THEN
    REWRITE_TAC(map ASSUME [`i + 1 > val (idx:int64)`; `~(i + 1 <= val (idx:int64))`]) THEN
    ARM_STEPS_TAC BIGNUM_COPY_ROW_FROM_TABLE_32_EXEC (1--38) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(val (word_sub (word i) idx:int64) = 0)` (fun thm -> REWRITE_TAC[thm]) THENL [
      MATCH_MP_TAC HELPER_RULE4 THEN REPEAT CONJ_TAC THENL [
        MATCH_MP_TAC LT_WORD_64 THEN EXISTS_TAC `(height:int64)` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[VAL_BOUND_64];
        ASM_REWRITE_TAC[]];

      ALL_TAC
    ] THEN
    REWRITE_TAC[
      WORD_BLAST `word_join (word 0:int64) (word 0:int64):int128 = word 0`; WORD_AND_0;WORD_OR_0;
      WORD_BLAST `word_and (x:int128) (word_not (word 0)) = x`] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC WORD_RULE) THEN
    IMP_REWRITE_TAC[HELPER_RULE2] THEN
    SUBGOAL_THEN `val (word i:int64)=i` (fun thm->REWRITE_TAC[thm]) THENL [
      SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [
        IMP_REWRITE_TAC[LT_WORD_64]; ALL_TAC] THEN
      IMP_REWRITE_TAC[VAL_WORD;MOD_LT;DIMINDEX_64];

      ALL_TAC
    ] THEN
    ASM_REWRITE_TAC[]
  ]);;
