(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Normalization of a bignum in-place in constant time.                      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_normalize.o";;
 ****)

let bignum_normalize_mc =
  define_assert_from_elf "bignum_normalize_mc" "arm/generic/bignum_normalize.o"
[
  0xf1000407;       (* arm_SUBS X7 X0 (rvalue (word 1)) *)
  0x54000463;       (* arm_BCC (word 140) *)
  0xf8677825;       (* arm_LDR X5 X1 (Shiftreg_Offset X7 3) *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0x540001c0;       (* arm_BEQ (word 56) *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xeb1f00bf;       (* arm_CMP X5 XZR *)
  0x9a821442;       (* arm_CSINC X2 X2 X2 Condition_NE *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa0303e5;       (* arm_MOV X5 X3 *)
  0xf8687823;       (* arm_LDR X3 X1 (Shiftreg_Offset X8 3) *)
  0x9a8300a5;       (* arm_CSEL X5 X5 X3 Condition_EQ *)
  0xf8287825;       (* arm_STR X5 X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xcb000106;       (* arm_SUB X6 X8 X0 *)
  0xb5ffff46;       (* arm_CBNZ X6 (word 2097128) *)
  0xf10004e7;       (* arm_SUBS X7 X7 (rvalue (word 1)) *)
  0x54fffe81;       (* arm_BNE (word 2097104) *)
  0xd37ae442;       (* arm_LSL X2 X2 (rvalue (word 6)) *)
  0xdac010a5;       (* arm_CLZ X5 X5 *)
  0x8b050042;       (* arm_ADD X2 X2 X5 *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xf24014bf;       (* arm_TST X5 (rvalue (word 63)) *)
  0xda9f03e9;       (* arm_CSETM X9 Condition_NE *)
  0xcb0503e6;       (* arm_NEG X6 X5 *)
  0xf8677828;       (* arm_LDR X8 X1 (Shiftreg_Offset X7 3) *)
  0x9ac52103;       (* arm_LSL X3 X8 X5 *)
  0xaa040063;       (* arm_ORR X3 X3 X4 *)
  0x9ac62504;       (* arm_LSR X4 X8 X6 *)
  0x8a090084;       (* arm_AND X4 X4 X9 *)
  0xf8277823;       (* arm_STR X3 X1 (Shiftreg_Offset X7 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0000ff;       (* arm_CMP X7 X0 *)
  0x54ffff03;       (* arm_BCC (word 2097120) *)
  0xaa0203e0;       (* arm_MOV X0 X2 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NORMALIZE_EXEC = ARM_MK_EXEC_RULE bignum_normalize_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Copied from bignum_shl_small proof, similar logic to bitloop ***)

let lemma1 = prove
 (`!n c. word_and (word_jushr (word n) (word_neg (word c)))
                  (word_neg (word (bitval (~(c MOD 64 = 0))))):int64 =
         word_ushr (word n) (64 - c MOD 64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_AND_MASK; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
    REWRITE_TAC[SUB_0] THEN MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[VAL_BOUND_64];
    W(MP_TAC o PART_MATCH (lhand o rand) WORD_JUSHR_NEG o lhand o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_64; MOD_64_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC DIVIDES_CONV]);;

let BIGNUM_NORMALIZE_CORRECT = time prove
 (`!k z n pc.
        nonoverlapping (word pc,0x94) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_normalize_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read PC s = word(pc + 0x90) /\
                  bignum_from_memory (z,val k) s =
                  2 EXP (64 * val k - bitsize n) * n /\
                  C_RETURN s = word(64 * val k - bitsize n))
             (MAYCHANGE [PC; X0; X2; X3; X4; X5; X6; X7; X8; X9] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BITSIZE_0] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumption ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** The digitwise normalization "normloop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x48`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        bignum_from_memory(z,k) s = 2 EXP (64 * val(read X2 s)) * n /\
        read X5 s = word(bigdigit (bignum_from_memory(z,k) s) (k - 1)) /\
        val(read X2 s) <= k - 1 /\
        (n = 0 ==> val(read X2 s) = k - 1) /\
        (~(n = 0) ==> 2 EXP (64 * (k - 1)) <= bignum_from_memory(z,k) s)` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; SUB_REFL] THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add z (word(8 * val(word 0:int64))))) s0 =
        word n`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; MULT_CLAUSES]; ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
      ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; EXP] THEN
      ASM_SIMP_TAC[VAL_WORD; GSYM LOWDIGITS_1; DIMINDEX_64; lowdigits; MOD_LT;
                   MULT_CLAUSES] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ARITH_RULE `k - 1 = 0 <=> k = 0 \/ k = 1`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    ENSURES_WHILE_PUP_TAC `k - 1` `pc + 0x14` `pc + 0x44`
     `\i s. (read X0 s = word k /\
             read X1 s = z /\
             read X7 s = word(k - 1 - i) /\
             bignum_from_memory(z,k) s = 2 EXP (64 * val(read X2 s)) * n /\
             read X5 s = word(bigdigit (bignum_from_memory(z,k) s) (k - 1)) /\
             val(read X2 s) <= i /\
             (n = 0 ==> val(read X2 s) = i) /\
             (~(n = 0) ==> 2 EXP (64 * i) <= bignum_from_memory(z,k) s)) /\
            (read ZF s <=> i = k - 1)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ARITH_RULE `k < 1 <=> k = 0`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      MP_TAC(ISPECL [`k:num`; `z:int64`; `s0:armstate`; `k - 1`]
         BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - 1 < k <=> ~(k = 0)`] THEN
      DISCH_THEN(MP_TAC o SYM) THEN
      GEN_REWRITE_TAC LAND_CONV [VAL_WORD_GALOIS] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC THEN
      SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[WORD_SUB; LE_1; VAL_WORD_1]; ALL_TAC] THEN
      VAL_INT64_TAC `k - 1` THEN
      ARM_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUB_0; VAL_WORD_0; MULT_CLAUSES] THEN ARITH_TAC;
      ALL_TAC; (*** Do the main loop invariant below ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC [1];
      ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC [1]] THEN

    (*** Nested loop "shufloop" ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `m:num` `bignum_from_memory (z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN
    GHOST_INTRO_TAC `d:num` `\s. val(read X2 s)` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [VAL_WORD_GALOIS] THEN
    REWRITE_TAC[DIMINDEX_64] THEN GLOBALIZE_PRECONDITION_TAC THEN
    UNDISCH_THEN `m = 2 EXP (64 * d) * n` (ASSUME_TAC o SYM) THEN
    ABBREV_TAC `topz <=> bigdigit m (k - 1) = 0` THEN

    ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x24` `pc + 0x38`
     `\j s. (read X0 s = word k /\
             read X1 s = z /\
             read X2 s = (if topz then word(d + 1) else word d) /\
             read X7 s = word (k - 1 - i) /\
             read X8 s = word j /\
             read X3 s =
               (if j = 0 then word 0 else word(bigdigit m (j - 1))) /\
             (read ZF s <=> topz) /\
             bignum_from_memory(word_add z (word(8 * j)),k - j) s =
             highdigits m j /\
             bignum_from_memory(z,j) s =
             lowdigits (if topz then 2 EXP 64 * m else m) j) /\
            (read X5 s =
             word(bigdigit (bignum_from_memory(z,j) s) (j - 1)))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--4) THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_0; HIGHDIGITS_0; SUB_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[COND_SWAP; GSYM WORD_ADD];
      ALL_TAC; (*** Inner loop invariant below ***)
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--2) THEN
      VAL_INT64_TAC `k - 1` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
      ARM_STEPS_TAC BIGNUM_NORMALIZE_EXEC [3] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> 1 <= k - 1 - i`];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ASSOC]] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM CONJ_ASSOC];
        W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
          lhand o lhand o snd) THEN
        REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
         [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i < k - 1`] THEN
        ARITH_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) LOWDIGITS_SELF o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "topz" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `m = lowdigits m ((k - 1) + 1)` SUBST1_TAC THENL
         [ASM_SIMP_TAC[SUB_ADD; LE_1; LOWDIGITS_SELF];
          ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; MULT_CLAUSES]] THEN
        SUBGOAL_THEN `64 * k = 64 + 64 * (k - 1)` SUBST1_TAC THENL
         [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
        SIMP_TAC[LT_MULT_LCANCEL; LOWDIGITS_BOUND; EXP_EQ_0; ARITH_EQ];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `bigdigit m (k - 1) = 0 <=> topz` (SUBST1_TAC o SYM) THEN
        UNDISCH_THEN `2 EXP (64 * d) * n = m` (SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `n = 0 ==> d:num = i` THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; DIV_0; MOD_0; bigdigit] THEN
        DISCH_THEN SUBST_ALL_TAC THEN VAL_INT64_TAC `i + 1` THEN
        ASM_REWRITE_TAC[LE_REFL];
        UNDISCH_THEN `n = 0 ==> d:num = i` (K ALL_TAC) THEN
        UNDISCH_TAC `~(n = 0) ==> 2 EXP (64 * i) <= m` THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      UNDISCH_THEN `bigdigit m (k - 1) = 0 <=> topz` (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; HIGHDIGITS_EQ_0] THEN
      ASM_CASES_TAC `m < 2 EXP (64 * (k - 1))` THEN ASM_REWRITE_TAC[] THENL
       [VAL_INT64_TAC `d + 1` THEN ASM_REWRITE_TAC[LE_ADD_RCANCEL] THEN
        REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (n + 1) = 64 + 64 * n`] THEN
        ASM_REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL];
        VAL_INT64_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
        ASM_SIMP_TAC[ARITH_RULE `d <= i ==> d <= i + 1`] THEN
        TRANS_TAC LE_TRANS `2 EXP (64 * (k - 1))` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `i < k - 1` THEN ARITH_TAC]] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--5) THEN
    ASM_REWRITE_TAC[ADD_SUB; GSYM WORD_ADD; ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `j < j + 1`] THEN
    UNDISCH_THEN `bigdigit m (k - 1) = 0 <=> topz` (SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `bigdigit m (k - 1) = 0` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LOWDIGITS_CLAUSES; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THENL
     [ALL_TAC; ARITH_TAC] THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP] THEN
    REWRITE_TAC[LOWDIGITS_0; VAL_WORD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[REWRITE_RULE[lowdigits] (GSYM LOWDIGITS_1)] THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_MULT] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    MATCH_MP_TAC(NUM_RING `x:num = y ==> a + e * x = e * y + a`) THEN
    SUBGOAL_THEN `j = SUC(j - 1)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
    THENL [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[bigdigit; EXP_ADD; ARITH_RULE `64 * SUC j = 64 + 64 * j`] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN

  (*** Ghost things up again ***)

  GHOST_INTRO_TAC `m:num` `bignum_from_memory (z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN
  GHOST_INTRO_TAC `d:num` `\s. val(read X2 s)` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [VAL_WORD_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_64] THEN GLOBALIZE_PRECONDITION_TAC THEN
  UNDISCH_THEN `m = 2 EXP (64 * d) * n` (ASSUME_TAC o SYM) THEN

  (*** The "bitloop" loop ***)

  ABBREV_TAC `c = 64 - bitsize(bigdigit m (k - 1))` THEN
  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x68` `pc + 0x84`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = word(64 * d + c) /\
          read X7 s = word i /\
          read X9 s = word_neg(word(bitval(~(c MOD 64 = 0)))) /\
          read X5 s = word c /\
          read X6 s = word_neg(word c) /\
          bignum_from_memory(word_add z (word (8 * i)),k - i) s =
          highdigits m i /\
          2 EXP (64 * i) * val(read X4 s) + bignum_from_memory(z,i) s =
          2 EXP (c MOD 64) * lowdigits m i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--8) THEN
    SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; DIV_0; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES;
                WORD_ADD_0; HIGHDIGITS_0; SUB_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_SUB_LZERO] THEN
    SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)) THEN
    ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN REWRITE_TAC[GSYM WORD_MASK] THEN
    SUBST1_TAC(ARITH_RULE `63 = 2 EXP 6 - 1`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_64_CLAUSES] THEN
    SUBGOAL_THEN `word_clz(word(bigdigit m (k - 1)):int64) = c`
    SUBST1_TAC THENL
     [REWRITE_TAC[WORD_CLZ_BITSIZE; DIMINDEX_64] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND];
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `b:int64` `read X4` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `m - i = 0 <=> ~(i < m)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_64_CLAUSES; LOWDIGITS_CLAUSES] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
     `ee * b + m:num = c * l
      ==> e * d + y = c * z + b
          ==> (ee * e) * d + m + ee * y = c * (ee * z + l)`)) THEN
    REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL; lemma1] THEN
    REWRITE_TAC[word_jshl; MOD_64_CLAUSES; DIMINDEX_64; VAL_WORD_USHR] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o
      rand o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_AND] THEN
      SIMP_TAC[BIT_WORD_SHL; DIMINDEX_64] THEN MATCH_MP_TAC(MESON[]
       `(!i. q i ==> ~s i) ==> !i. p i ==> ~((q i /\ r i) /\ (s i))`) THEN
      REWRITE_TAC[UPPER_BITS_ZERO] THEN
      UNDISCH_THEN
       `2 EXP (64 * i) * val(b:int64) + read (memory :> bytes (z,8 * i)) s7 =
        2 EXP (c MOD 64) * lowdigits m i`
       (MP_TAC o AP_TERM `\x. x DIV 2 EXP (64 * i)`) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      SIMP_TAC[DIV_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
      DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; LOWDIGITS_BOUND; EXP_EQ_0; ARITH_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[VAL_WORD_SHL; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    SUBGOAL_THEN `2 EXP 64 = 2 EXP (c MOD 64) * 2 EXP (64 - c MOD 64)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[MOD_MULT2; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB]] THEN
    REWRITE_TAC[DIVISION_SIMP];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--2);
    GHOST_INTRO_TAC `b:int64` `read X4` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    ARM_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--3)] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `e * b + z = cn
    ==> (e * b < e * 1 ==> e * b = 0)
        ==> cn < e ==> z = cn`)) THEN
  ANTS_TAC THENL
   [SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; MULT_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC `n = 0 ==> d = k - 1` THEN
    UNDISCH_TAC `2 EXP (64 * d) * n = m` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; EXP_LT_0; ARITH_EQ] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "c" THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGDIGIT_0; BITSIZE_0] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    UNDISCH_THEN `n = 0 ==> d = k - 1` (K ALL_TAC) THEN
    UNDISCH_TAC `~(n = 0) ==> 2 EXP (64 * (k - 1)) <= m` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `64 * k = c MOD 64 + (64 * k - c MOD 64)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[EXP_ADD; LT_MULT_LCANCEL; ARITH_EQ; EXP_EQ_0]] THEN
    REWRITE_TAC[GSYM BITSIZE_LE] THEN
    SUBGOAL_THEN
     `m = 2 EXP (64 * (k - 1)) * highdigits m (k - 1) + lowdigits m (k - 1)`
    SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
    ASM_SIMP_TAC[HIGHDIGITS_TOP] THEN
    UNDISCH_THEN `64 - bitsize (bigdigit m (k - 1)) = c`
     (SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `bigdigit m (k - 1) = 0` THENL
     [ASM_REWRITE_TAC[BITSIZE_0; MULT_CLAUSES; ADD_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITSIZE_LE; SUB_0] THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * (k - 1))` THEN
      ASM_REWRITE_TAC[LOWDIGITS_BOUND; LE_EXP; ARITH_EQ] THEN ARITH_TAC;
      ASM_SIMP_TAC[BITSIZE_MULT_ADD; LOWDIGITS_BOUND]] THEN
    MATCH_MP_TAC(ARITH_RULE `a + c <= b ==> a <= b - c MOD 64`) THEN
    MATCH_MP_TAC(ARITH_RULE
     `~(k = 0) /\ b <= 64 ==> (64 * (k - 1) + b) + (64 - b) <= 64 * k`) THEN
    ASM_REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `c MOD 64 = c` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN EXPAND_TAC "c" THEN
    REWRITE_TAC[ARITH_RULE `64 - n < 64 <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[BITSIZE_EQ_0; GSYM HIGHDIGITS_TOP] THEN
    ASM_REWRITE_TAC[HIGHDIGITS_EQ_0; NOT_LT];
    ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `2 EXP (64 * d) * n = m`)) THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM EXP_ADD); MULT_ASSOC] THEN
  SUBGOAL_THEN `64 * k - bitsize n = 64 * d + c`
    (fun th -> REWRITE_TAC[th]) THEN
  EXPAND_TAC "c" THEN MATCH_MP_TAC(ARITH_RULE
   `b <= 64 * k /\ c <= 64 /\ 64 * k + c = 64 * (d + 1) + b
    ==> 64 * k - b = 64 * d + 64 - c`) THEN
  ASM_REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND] THEN
  ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; highdigits; BITSIZE_DIV] THEN
  MATCH_MP_TAC(ARITH_RULE `c:num <= b /\ a + b = c + d ==> a + b - c = d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_BITSIZE] THEN DISCH_THEN(K ALL_TAC) THEN
    TRANS_TAC LE_TRANS `2 EXP (64 * (k - 1))` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
    SUBST1_TAC(SYM(ASSUME `2 EXP (64 * d) * n = m`))] THEN
  REWRITE_TAC[BITSIZE_MULT] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC);;

let BIGNUM_NORMALIZE_SUBROUTINE_CORRECT = time prove
 (`!k z n pc returnaddress.
        nonoverlapping (word pc,0x94) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_normalize_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,val k) s =
                  2 EXP (64 * val k - bitsize n) * n /\
                  C_RETURN s = word(64 * val k - bitsize n))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NORMALIZE_EXEC BIGNUM_NORMALIZE_CORRECT);;
