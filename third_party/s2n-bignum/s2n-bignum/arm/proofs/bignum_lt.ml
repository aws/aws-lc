(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Comparison < test on bignums.                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_lt.o";;
 ****)

let bignum_lt_mc = define_assert_from_elf "bignum_lt_mc" "arm/generic/bignum_lt.o"
[
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xeb020000;       (* arm_SUBS X0 X0 X2 *)
  0x54000203;       (* arm_BCC (word 64) *)
  0xb40000e2;       (* arm_CBZ X2 (word 28) *)
  0xf8647825;       (* arm_LDR X5 X1 (Shiftreg_Offset X4 3) *)
  0xf8647866;       (* arm_LDR X6 X3 (Shiftreg_Offset X4 3) *)
  0xfa0600bf;       (* arm_SBCS XZR X5 X6 *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5ffff62;       (* arm_CBNZ X2 (word 2097132) *)
  0xb40000c0;       (* arm_CBZ X0 (word 24) *)
  0xf8647825;       (* arm_LDR X5 X1 (Shiftreg_Offset X4 3) *)
  0xfa1f00bf;       (* arm_SBCS XZR X5 XZR *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffff80;       (* arm_CBNZ X0 (word 2097136) *)
  0x9a9f27e0;       (* arm_CSET X0 Condition_CC *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xab020000;       (* arm_ADDS X0 X0 X2 *)
  0xb4000100;       (* arm_CBZ X0 (word 32) *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0xf8647825;       (* arm_LDR X5 X1 (Shiftreg_Offset X4 3) *)
  0xf8647866;       (* arm_LDR X6 X3 (Shiftreg_Offset X4 3) *)
  0xfa0600bf;       (* arm_SBCS XZR X5 X6 *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffff60;       (* arm_CBNZ X0 (word 2097132) *)
  0xf8647865;       (* arm_LDR X5 X3 (Shiftreg_Offset X4 3) *)
  0xfa0503ff;       (* arm_NGCS XZR X5 *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5ffff82;       (* arm_CBNZ X2 (word 2097136) *)
  0x9a9f27e0;       (* arm_CSET X0 Condition_CC *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_LT_EXEC = ARM_MK_EXEC_RULE bignum_lt_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_LT_CORRECT = prove
 (`!m a x n b y pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_lt_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. (read PC s' = word(pc + 0x44) \/
                 read PC s' = word(pc + 0x84)) /\
                C_RETURN s' = if x < y then word 1 else word 0)
          (MAYCHANGE [PC; X0; X2; X4; X5; X6] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`b:int64`; `y:num`] THEN
  X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_LT_EXEC] THEN
  BIGNUM_RANGE_TAC "m" "x" THEN BIGNUM_RANGE_TAC "n" "y" THEN

  (*** Case split following the initial branch, m >= n case then m < n ***)

  ASM_CASES_TAC `n:num <= m` THENL
   [SUBGOAL_THEN `~(m:num < n)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x28`
     `\s. read X0 s = word (m - n) /\
          read X1 s = a /\
          read X3 s = b /\
          read X4 s = word n /\
          bignum_from_memory (a,m) s = x /\
          bignum_from_memory (b,n) s = y /\
          (read CF s <=> lowdigits y n <= lowdigits x n)` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; LE_REFL] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_UP_TAC `n:num` `pc + 0x10` `pc + 0x24`
       `\i s. read X0 s = word (m - n) /\
              read X1 s = a /\
              read X3 s = b /\
              read X2 s = word(n - i) /\
              read X4 s = word i /\
              bignum_from_memory (a,m) s = x /\
              bignum_from_memory (b,n) s = y /\
              (read CF s <=> lowdigits y i <= lowdigits x i)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; LE_REFL] THEN ASM_REWRITE_TAC[WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        VAL_INT64_TAC `n - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
        ARM_SIM_TAC BIGNUM_LT_EXEC [1]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add a (word(8 * i)))) s0 =
        word(bigdigit x i) /\
        read(memory :> bytes64(word_add b (word(8 * i)))) s0 =
        word(bigdigit y i)`
      ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_LT_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB;
                   ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      REWRITE_TAC[GSYM WORD_IWORD; LOWDIGITS_CLAUSES] THEN
      SIMP_TAC[LEXICOGRAPHIC_LE; LOWDIGITS_BOUND] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[bitval] THEN ARITH_TAC;
      ASM_CASES_TAC `m:num = n` THENL
       [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
        REWRITE_TAC[SUB_REFL; ADD_CLAUSES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
        REWRITE_TAC[GSYM NOT_LT; COND_SWAP];
        ALL_TAC] THEN
      SUBGOAL_THEN `n:num < m /\ 0 < m - n /\ m - n < 2 EXP 64`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ENSURES_WHILE_UP_TAC `m - n:num` `pc + 0x2c` `pc + 0x3c`
       `\i s. read X0 s = word (m - n - i) /\
              read X1 s = a /\
              read X4 s = word(n + i) /\
              bignum_from_memory (a,m) s = x /\
              (read CF s <=> lowdigits y (n + i) <= lowdigits x (n + i))` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SIMPLE_ARITH_TAC;
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
        VAL_INT64_TAC `m - n:num` THEN ASM_REWRITE_TAC[SUB_EQ_0] THEN
        ASM_REWRITE_TAC[GSYM NOT_LT; COND_SWAP];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        VAL_INT64_TAC `m - n - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_SIMP_TAC[ARITH_RULE `n <= m ==> n + m - n:num = m`] THEN
        BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN
        ASM_REWRITE_TAC[] THEN TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
        ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < m /\ n + i < m` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `n + i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add a (word(8 * (n + i))))) s0 =
        word(bigdigit x (n + i))`
      ASSUME_TAC THENL
       [EXPAND_TAC "x" THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_LT_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[WORD_RULE
         `word_sub x (word 1) = word y <=> x = word(y + 1)`] THEN
        AP_TERM_TAC THEN UNDISCH_TAC `n + i:num < m` THEN ARITH_TAC;
        CONV_TAC WORD_RULE;
        SIMP_TAC[ADD_CLAUSES; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
        REWRITE_TAC[ADD_ASSOC; LOWDIGITS_CLAUSES] THEN
        SIMP_TAC[LEXICOGRAPHIC_LE; LOWDIGITS_BOUND] THEN
        SUBGOAL_THEN `bigdigit y (n + i) = 0` SUBST1_TAC THENL
         [MATCH_MP_TAC BIGDIGIT_ZERO THEN
          TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
          ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC;
          REWRITE_TAC[bitval] THEN ARITH_TAC]]];

    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x6c`
     `\s. read X2 s = word (n - m) /\
          read X1 s = a /\
          read X3 s = b /\
          read X4 s = word m /\
          bignum_from_memory (a,m) s = x /\
          bignum_from_memory (b,n) s = y /\
          (read CF s <=> lowdigits y m <= lowdigits x m)` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m = 0` THENL
       [UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC (1--5) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; LE_REFL; WORD_RULE
         `word_add (word_sub (word 0) x) x = word 0`] THEN
        ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_0; DIMINDEX_64] THEN
        ASM_REWRITE_TAC[GSYM NOT_LT] THEN ARITH_TAC;
        ALL_TAC] THEN
      ENSURES_WHILE_UP_TAC `m:num` `pc + 0x54` `pc + 0x68`
       `\i s. read X2 s = word (n - m) /\
              read X1 s = a /\
              read X3 s = b /\
              read X0 s = word(m - i) /\
              read X4 s = word i /\
              bignum_from_memory (a,m) s = x /\
              bignum_from_memory (b,n) s = y /\
              (read CF s <=> lowdigits y i <= lowdigits x i)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ASSUME_TAC(WORD_RULE
         `word_add (word_sub (word m) (word n)) (word n):int64 = word m`) THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC (1--6) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[LOWDIGITS_0; LE_REFL] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN
        ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_0; DIMINDEX_64] THEN
        ASM_REWRITE_TAC[GSYM NOT_LT] THEN ARITH_TAC;
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        VAL_INT64_TAC `m - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
        ARM_SIM_TAC BIGNUM_LT_EXEC [1]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add a (word(8 * i)))) s0 =
        word(bigdigit x i) /\
        read(memory :> bytes64(word_add b (word(8 * i)))) s0 =
        word(bigdigit y i)`
      ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_LT_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB;
                   ARITH_RULE `i < m ==> i <= m /\ i + 1 <= m`] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      REWRITE_TAC[GSYM WORD_IWORD; LOWDIGITS_CLAUSES] THEN
      SIMP_TAC[LEXICOGRAPHIC_LE; LOWDIGITS_BOUND] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[bitval] THEN ARITH_TAC;
      SUBGOAL_THEN `~(n = m) /\ m:num < n /\ 0 < n - m /\ n - m < 2 EXP 64`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ENSURES_WHILE_UP_TAC `n - m:num` `pc + 0x6c` `pc + 0x7c`
       `\i s. read X2 s = word (n - m - i) /\
              read X3 s = b /\
              read X4 s = word(m + i) /\
              bignum_from_memory (b,n) s = y /\
              (read CF s <=> lowdigits y (m + i) <= lowdigits x (m + i))` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SIMPLE_ARITH_TAC;
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        VAL_INT64_TAC `n - m - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_LT_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_SIMP_TAC[ARITH_RULE `n <= m ==> n + m - n:num = m`] THEN
        BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN
        ASM_REWRITE_TAC[] THEN TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
        ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < n /\ m + i < n` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `m + i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add b (word(8 * (m + i))))) s0 =
        word(bigdigit y (m + i))`
      ASSUME_TAC THENL
       [EXPAND_TAC "y" THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_LT_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[WORD_RULE
         `word_sub x (word 1) = word y <=> x = word(y + 1)`] THEN
        AP_TERM_TAC THEN UNDISCH_TAC `m + i:num < n` THEN ARITH_TAC;
        CONV_TAC WORD_RULE;
        SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
        REWRITE_TAC[ADD_ASSOC; LOWDIGITS_CLAUSES] THEN
        SIMP_TAC[LEXICOGRAPHIC_LE; LOWDIGITS_BOUND] THEN
        SUBGOAL_THEN `bigdigit x (m + i) = 0` SUBST1_TAC THENL
         [MATCH_MP_TAC BIGDIGIT_ZERO THEN
          TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
          ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC;
          REWRITE_TAC[bitval] THEN ARITH_TAC]]]]);;

let BIGNUM_LT_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_lt_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. (read PC s' = returnaddress \/
                 read PC s' = returnaddress) /\
                C_RETURN s' = if x < y then word 1 else word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_LT_EXEC BIGNUM_LT_CORRECT);;
