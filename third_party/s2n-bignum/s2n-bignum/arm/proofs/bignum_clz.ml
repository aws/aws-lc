(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting leading zero bits in a bignum.                                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_clz.o";;
 ****)

let bignum_clz_mc = define_assert_from_elf "bignum_clz_mc" "arm/generic/bignum_clz.o"
[
  0xb40001e0;       (* arm_CBZ X0 (word 60) *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0x92800003;       (* arm_MOVN X3 (word 0) 0 *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xf8657824;       (* arm_LDR X4 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xf100009f;       (* arm_CMP X4 (rvalue (word 0)) *)
  0x9a8210a2;       (* arm_CSEL X2 X5 X2 Condition_NE *)
  0x9a831083;       (* arm_CSEL X3 X4 X3 Condition_NE *)
  0xeb0000bf;       (* arm_CMP X5 X0 *)
  0x54ffff41;       (* arm_BNE (word 2097128) *)
  0xcb020000;       (* arm_SUB X0 X0 X2 *)
  0xd37ae400;       (* arm_LSL X0 X0 (rvalue (word 6)) *)
  0xdac01064;       (* arm_CLZ X4 X3 *)
  0x8b040000;       (* arm_ADD X0 X0 X4 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CLZ_EXEC = ARM_MK_EXEC_RULE bignum_clz_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CLZ_CORRECT = prove
 (`!k a x pc.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_clz_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read PC s' = word (pc + 0x3c) /\
               C_RETURN s' = word(64 * val k - bitsize x))
         (MAYCHANGE [PC; X0; X2; X3; X4; X5] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_TAC `x < 2 EXP (64 * k)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ARITH_RULE `x < 1 <=> x = 0`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CLZ_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BITSIZE_0; SUB_0];
    ALL_TAC] THEN

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x10` `pc + 0x28`
   `\i s. (bignum_from_memory (a,k) s = x /\
           read X0 s = word k /\
           read X1 s = a /\
           read X5 s = word i /\
           bignum_from_memory(word_add a (word(8 * val(read X2 s))),
                              i - val(read X2 s)) s = 0 /\
           (read X2 s = word 0 /\
            read X3 s = word_not(word 0) \/
            ~(read X2 s = word 0) /\ val(read X2 s) <= i /\
            ~(bigdigit x (val(word_sub (read X2 s) (word 1))) = 0) /\
            read X3 s =
            word(bigdigit x (val(word_sub (read X2 s) (word 1)))))) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CLZ_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0; SUB_REFL] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; TAUT `p \/ q <=> ~p ==> q`] THEN
    GHOST_INTRO_TAC `r:int64` `read X2` THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CLZ_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `r:int64` `read X2` THEN
    ABBREV_TAC `i = val(r:int64)` THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL
     [ASM_MESON_TAC[VAL_BOUND_64]; ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN GHOST_INTRO_TAC `w:int64` `read X3` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; TAUT `p \/ q <=> ~p ==> q`] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CLZ_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAUT `~p ==> q <=> p \/ q`]) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      UNDISCH_TAC `val(word 0:int64) = i` THEN
      REWRITE_TAC[VAL_WORD_0] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; SUB_0; WORD_ADD_0]) THEN
      UNDISCH_TAC `read (memory :> bytes (a,8 * k)) s5 = x` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[BITSIZE_0; SUB_0] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC WORD_RULE;
      ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC] THEN
    SUBGOAL_THEN `val(word_sub r (word 1):int64) = i - 1` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= i <=> ~(i = 0)`];
      ALL_TAC] THEN
    ABBREV_TAC `d = bigdigit x (i - 1)` THEN
    SUBGOAL_THEN `x = 2 EXP (64 * i) * highdigits x i + lowdigits x i`
    SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
    SUBGOAL_THEN `highdigits x i = 0` SUBST1_TAC THENL
     [EXPAND_TAC "x" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[highdigits; BIGNUM_FROM_MEMORY_DIV] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]] THEN
    SUBGOAL_THEN `i = (i - 1) + 1` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
    ASM_SIMP_TAC[BITSIZE_MULT_ADD; LOWDIGITS_BOUND] THEN
    REWRITE_TAC[WORD_CLZ_BITSIZE; DIMINDEX_64] THEN
    EXPAND_TAC "d" THEN SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[ARITH_RULE `m - (n + p):num = (m - n) - p`] THEN
    ONCE_REWRITE_TAC[WORD_SUB] THEN
    SUBGOAL_THEN `bitsize (bigdigit x (i - 1)) <= 64` MP_TAC THENL
     [REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND];
      MAP_EVERY UNDISCH_TAC [`~(i = 0)`; `i:num <= k`]] THEN
    SIMP_TAC[ARITH_RULE
     `~(i = 0) /\ i <= k /\ d <= 64 ==> d <= 64 * k - 64 * (i - 1)`] THEN
    REPEAT DISCH_TAC THEN REWRITE_TAC[WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `~(i = 0) /\ i <= k ==> 64 * (i - 1) <= 64 * k`] THEN
    REWRITE_TAC[ARITH_RULE `64 * (i - 1) = 64 * i - 64`] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `64 <= 64 * i <=> ~(i = 0)`] THEN
    SUBGOAL_THEN `r:int64 = word i` SUBST1_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `val(r:int64) = i`)) THEN REWRITE_TAC[WORD_VAL];
      CONV_TAC WORD_RULE]] THEN

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
  VAL_INT64_TAC `j + 1` THEN
  GHOST_INTRO_TAC `r:int64` `read X2` THEN
  ABBREV_TAC `i = val(r:int64)` THEN
  SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[VAL_BOUND_64]; ALL_TAC] THEN
  VAL_INT64_TAC `i:num` THEN GHOST_INTRO_TAC `w:int64` `read X3` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; TAUT `p \/ q <=> ~p ==> q`] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read(memory :> bytes64(word_add a (word(8 * j)))) s0 = word(bigdigit x j)`
  ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    ASM_REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  ARM_STEPS_TAC BIGNUM_CLZ_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; REWRITE_TAC[CONJ_ASSOC]] THEN
  CONJ_TAC THENL
   [SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND];
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM WORD_ADD] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (TAUT `(~p ==> q) ==> p \/ q`)) THEN
  REWRITE_TAC[WORD_SUB_0] THEN
  ASM_CASES_TAC `bigdigit x j = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r:int64 = word 0` THEN
  ASM_REWRITE_TAC[VAL_WORD_0; SUB_0] THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `val(r:int64) = i` THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; ADD_CLAUSES; MULT_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0; MULT_CLAUSES; SUB_0]) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
    SIMP_TAC[ARITH_RULE `i <= j ==> i <= j + 1`] THEN
    SIMP_TAC[ARITH_RULE `i <= j ==> (j + 1) - i = (j - i) + 1`] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; MULT_EQ_0; ADD_CLAUSES] THEN
    DISJ2_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= j ==> 8 * i + 8 * (j - i) = 8 * j`] THEN
    REWRITE_TAC[VAL_WORD_0];
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `val(r:int64) = i` THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add x y) y = x`] THEN
    VAL_INT64_TAC `j:num` THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    REWRITE_TAC[SUB_REFL; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[LE_REFL] THEN
    VAL_INT64_TAC `j + 1` THEN ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
    ARITH_TAC;
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM VAL_EQ_0]) THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
    VAL_INT64_TAC `j:num` THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; ADD_EQ_0; ARITH_EQ; ADD_SUB; LE_REFL] THEN
    REWRITE_TAC[SUB_REFL; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]]);;

let BIGNUM_CLZ_SUBROUTINE_CORRECT = prove
 (`!k a x pc returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_clz_mc /\
              read PC s = word pc /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read PC s' = returnaddress /\
               C_RETURN s' = word(64 * val k - bitsize x))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CLZ_EXEC BIGNUM_CLZ_CORRECT);;
