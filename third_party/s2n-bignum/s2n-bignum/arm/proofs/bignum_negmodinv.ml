(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bignum negated modular inversion.                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_negmodinv.o";;
 ****)

let bignum_negmodinv_mc =
  define_assert_from_elf "bignum_negmodinv_mc" "arm/generic/bignum_negmodinv.o"
[
  0xb40006a0;       (* arm_CBZ X0 (word 212) *)
  0xf9400044;       (* arm_LDR X4 X2 (Immediate_Offset (word 0)) *)
  0xd37ef483;       (* arm_LSL X3 X4 (rvalue (word 2)) *)
  0xcb030083;       (* arm_SUB X3 X4 X3 *)
  0xd27f0063;       (* arm_EOR X3 X3 (rvalue (word 2)) *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0x9b031886;       (* arm_MADD X6 X4 X3 X6 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b030cc3;       (* arm_MADD X3 X6 X3 X3 *)
  0x9b077ce6;       (* arm_MUL X6 X7 X7 *)
  0x9b030ce3;       (* arm_MADD X3 X7 X3 X3 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b030cc3;       (* arm_MADD X3 X6 X3 X3 *)
  0x9b030ce3;       (* arm_MADD X3 X7 X3 X3 *)
  0xf9000023;       (* arm_STR X3 X1 (Immediate_Offset (word 0)) *)
  0xf100041f;       (* arm_CMP X0 (rvalue (word 1)) *)
  0x540004a0;       (* arm_BEQ (word 148) *)
  0x9bc37c86;       (* arm_UMULH X6 X4 X3 *)
  0xd2800029;       (* arm_MOV X9 (rvalue (word 1)) *)
  0xf8697844;       (* arm_LDR X4 X2 (Shiftreg_Offset X9 3) *)
  0x9b037c87;       (* arm_MUL X7 X4 X3 *)
  0xba0600e7;       (* arm_ADCS X7 X7 X6 *)
  0x9bc37c86;       (* arm_UMULH X6 X4 X3 *)
  0xf8297827;       (* arm_STR X7 X1 (Shiftreg_Offset X9 3) *)
  0x91000529;       (* arm_ADD X9 X9 (rvalue (word 1)) *)
  0xcb090004;       (* arm_SUB X4 X0 X9 *)
  0xb5ffff24;       (* arm_CBNZ X4 (word 2097124) *)
  0xf1000800;       (* arm_SUBS X0 X0 (rvalue (word 2)) *)
  0x540002c0;       (* arm_BEQ (word 88) *)
  0x91002021;       (* arm_ADD X1 X1 (rvalue (word 8)) *)
  0xf9400028;       (* arm_LDR X8 X1 (Immediate_Offset (word 0)) *)
  0x9b037d05;       (* arm_MUL X5 X8 X3 *)
  0xf9000025;       (* arm_STR X5 X1 (Immediate_Offset (word 0)) *)
  0xf9400044;       (* arm_LDR X4 X2 (Immediate_Offset (word 0)) *)
  0x9bc57c86;       (* arm_UMULH X6 X4 X5 *)
  0xf100051f;       (* arm_CMP X8 (rvalue (word 1)) *)
  0xd2800029;       (* arm_MOV X9 (rvalue (word 1)) *)
  0xf8697844;       (* arm_LDR X4 X2 (Shiftreg_Offset X9 3) *)
  0xf8697828;       (* arm_LDR X8 X1 (Shiftreg_Offset X9 3) *)
  0x9b057c87;       (* arm_MUL X7 X4 X5 *)
  0xba060108;       (* arm_ADCS X8 X8 X6 *)
  0x9bc57c86;       (* arm_UMULH X6 X4 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xf8297828;       (* arm_STR X8 X1 (Shiftreg_Offset X9 3) *)
  0xcb000124;       (* arm_SUB X4 X9 X0 *)
  0x91000529;       (* arm_ADD X9 X9 (rvalue (word 1)) *)
  0xb5fffec4;       (* arm_CBNZ X4 (word 2097112) *)
  0xf1000400;       (* arm_SUBS X0 X0 (rvalue (word 1)) *)
  0x54fffd81;       (* arm_BNE (word 2097072) *)
  0xf9400428;       (* arm_LDR X8 X1 (Immediate_Offset (word 8)) *)
  0x9b037d05;       (* arm_MUL X5 X8 X3 *)
  0xf9000425;       (* arm_STR X5 X1 (Immediate_Offset (word 8)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NEGMODINV_EXEC = ARM_MK_EXEC_RULE bignum_negmodinv_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_NEGMODINV_CORRECT = prove
 (`!k z x m pc.
        nonoverlapping (word pc,0xd8) (z,8 * val k) /\
        nonoverlapping (x,8 * val k) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_negmodinv_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; x] s /\
                  bignum_from_memory (x,val k) s = m)
             (\s. read PC s = word(pc + 0xd4) /\
                  (ODD m
                   ==> (m * bignum_from_memory(z,val k) s + 1 == 0)
                       (mod (2 EXP (64 * val k)))))
             (MAYCHANGE [PC; X0; X1; X3; X4; X5; X6; X7; X8; X9] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** Initial word-level modular inverse ***)

  ENSURES_SEQUENCE_TAC `pc + 0x38`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = x /\
        bignum_from_memory (x,k) s = m /\
        read X4 s = word(bigdigit m 0) /\
        (ODD m ==> (m * val(read X3 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory(x,k) s0 = highdigits m 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    ARM_STEPS_TAC BIGNUM_NEGMODINV_EXEC (1--5) THEN
    SUBGOAL_THEN `ODD m ==> (m * val (read X3 s5) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read X3 s5` THEN DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_NEGMODINV_EXEC (6--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read X3 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC] THEN

  (*** Handle the next degenerate case k = 1 ***)

  ASM_CASES_TAC `k = 1` THENL
   [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--3) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING] THEN
    ASM_SIMP_TAC[MULT_CLAUSES; VAL_WORD_EQ; DIMINDEX_64];
    ALL_TAC] THEN

  (*** The "initloop" doing the first multiplication setting up output ***)

  SUBGOAL_THEN `1 < k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0) /\ ~(k = 1)`]; ALL_TAC] THEN
  ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0x4c` `pc + 0x64`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = x /\
          read X3 s = word w /\
          bignum_from_memory(x,k) s = m /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits m i /\
          read (memory :> bytes64 z) s = word w /\
          read X9 s = word i /\
          (ODD m
           ==> 2 EXP (64 * i) * (bitval(read CF s) + val(read X6 s)) +
               bignum_from_memory(z,i) s =
               (w * lowdigits m i + 1) + w)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `~(val (word_sub (word k) (word 1):int64) = 0)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_1]; ALL_TAC] THEN
    ARM_ACCSIM_TAC BIGNUM_NEGMODINV_EXEC [5] (1--5) THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[LT_IMP_LE; BITVAL_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64; LOWDIGITS_1] THEN
    REWRITE_TAC[MULT_CLAUSES; REAL_OF_NUM_CLAUSES; EQ_ADD_RCANCEL] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(e * h + l = m * w ==> l + 1 = e)
      ==> e * h + l = m * w ==> e * (1 + h) = w * m + 1`) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MOD_MULT_ADD; MULT_CLAUSES] THEN
    CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN REWRITE_TAC[GSYM CONG] THEN
    ASM_SIMP_TAC[NUMBER_RULE
     `(m * w + 1 == 0) (mod e)
      ==> ((x == m * w) (mod e) <=> e divides x + 1)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    MATCH_MP_TAC(ARITH_RULE
     `x < e ==> e <= x + 1 \/ x + 1 = 0 ==> x + 1 = e`) THEN
    REWRITE_TAC[VAL_BOUND_64];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read X6` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    ARM_ACCSIM_TAC BIGNUM_NEGMODINV_EXEC [2;3] (1--6) THEN
    REWRITE_TAC[GSYM WORD_ADD; LOWDIGITS_CLAUSES] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `(w * (e * d + l) + 1) + w = w * e * d + (w * l + 1) + w`] THEN
    REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    CONV_TAC REAL_RING;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--2);

    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** Handle the "finale" next to share the k = 2 and general cases ***)

  ENSURES_SEQUENCE_TAC `pc + 0xc8`
   `\s. read X1 s = word_sub (word_add z (word (8 * (k - 1)))) (word 8) /\
        read X3 s = word w /\
        (ODD m
        ==> (bignum_from_memory (z,k - 1) s * (m + 1) + 1 ==
             bignum_from_memory (z,k) s)
            (mod (2 EXP (64 * k))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `bignum_from_memory (z,k) = bignum_from_memory (z,(k-1)+1)`
    SUBST1_TAC THENL [ASM_SIMP_TAC[SUB_ADD; LT_IMP_LE]; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    GHOST_INTRO_TAC `l:num` `bignum_from_memory (z,k - 1)` THEN
    GHOST_INTRO_TAC `h:int64`
     `read (memory :> bytes64 (word_add z (word (8 * (k - 1)))))` THEN
    ASSUME_TAC(WORD_RULE
     `!x:int64. word_add (word_sub x (word 8)) (word 8) = x`) THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--3) THEN

    DISCH_THEN(fun th -> REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP th))) THEN
    DISCH_TAC THEN MATCH_MP_TAC(NUMBER_RULE
     `!p. (m * v + h == 0) (mod p) /\ (p * d = e)
          ==> (l * (m + 1) + 1 == l + d * h) (mod e)
              ==> (m * (l + d * v) + 1 == 0) (mod e)`) THEN
    EXISTS_TAC `2 EXP 64` THEN REWRITE_TAC[GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 + 64 * (k - 1) = 64 * k`] THEN
    REWRITE_TAC[VAL_WORD; ADD_CLAUSES; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    UNDISCH_TAC `(m * w + 1 == 0) (mod (2 EXP 64))` THEN
    SPEC_TAC(`2 EXP 64`,`p:num`) THEN CONV_TAC NUMBER_RULE] THEN

  (*** Next degenerate case k = 2 ***)

  ASM_CASES_TAC `k = 2` THENL
   [UNDISCH_THEN `k = 2` SUBST_ALL_TAC THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read X6` THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--4) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_SING; VAL_WORD_EQ; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[ARITH_RULE `w * (m + 1) + 1 = (w * m + 1) + w`] THEN
    REWRITE_TAC[CONG; MOD_MULT_ADD; BIGNUM_FROM_MEMORY_BYTES];
    ALL_TAC] THEN

  (*** Setup of the main loop "outerloop" ***)

  SUBGOAL_THEN `2 < k /\ 1 < k - 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PAUP_TAC `1` `k - 1` `pc + 0x74` `pc + 0xc4`
   `\i s. (read X0 s = word(k - 1 - i) /\
           read X1 s = word_sub (word_add z (word(8 * i))) (word 8) /\
           read X2 s = x /\
           read X3 s = word w /\
           bignum_from_memory (x,k) s = m /\
           (ODD m
            ==> (bignum_from_memory(z,i) s * (m + 1) + 1 ==
                 bignum_from_memory(z,k) s) (mod (2 EXP (64 * k))))) /\
           (read ZF s <=> i = k - 1)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`word k:int64`; `word k:int64`] VAL_WORD_SUB_EQ_0) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN DISCH_TAC THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read X6` THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--4) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_VAL_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `k - 1 - 1 = k - 2`] THEN REWRITE_TAC[WORD_SUB] THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[ARITH_RULE `w * (m + 1) + 1 = (w * m + 1) + w`] THEN
    REWRITE_TAC[CONG; MOD_MULT_ADD];
    ALL_TAC; (*** The main outer loop invariant ***)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC [1];
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC [1]] THEN

  (*** Now completely rebase/reindex to focus on relevant window i...k-1
   ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN

  MP_TAC(ISPECL [`z:int64`; `i:num`; `k - i:num`]
        BIGNUM_FROM_MEMORY_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> i + k - i = k`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `z':int64 = word_add z (word (8 * i))` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  GHOST_INTRO_TAC `l:num` `bignum_from_memory (z,i)` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z',k - i)` THEN
  REWRITE_TAC[NUMBER_RULE
   `(l * (m + 1) + 1 == e * q + l) (mod p) <=>
    (l * m + 1 == e * q) (mod p)`] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[WORD_RULE
   `word_sub (word_add z (word (8 * (i + 1)))) (word 8) =
    word_add z (word (8 * i))`] THEN

  REWRITE_TAC[ARITH_RULE `k - 1 - (i + 1) = k - i - 2`] THEN
  REWRITE_TAC[ARITH_RULE `k - 1 - i = k - i - 1`] THEN
  ABBREV_TAC `p:num = k - i` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x78`
   `\s. read X0 s = word (p - 1) /\
        read X1 s = z' /\
        read X2 s = x /\
        read X3 s = word w /\
        bignum_from_memory (x,k) s = m /\
        bignum_from_memory (x,p) s = lowdigits m p /\
        bignum_from_memory (z,i) s = l /\
        bignum_from_memory (z',p) s = q` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[ARITH_RULE `MIN k (k - i) = k - i`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z',8 * p) (z:int64,8 * i) /\
    nonoverlapping (z',8 * p) (x,8 * p) /\
    nonoverlapping (z',8 * p) (x,8 * k) /\
    nonoverlapping (z',8 * p) (word pc,0xd8)`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [PC; X0; X1; X3; X4; X5; X6; X7; X8; X9] ,,
    MAYCHANGE [memory :> bytes (z',8 * p)] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xc0`
   `\s. read X0 s = word (p - 1) /\
        read X1 s = z' /\
        read X2 s = x /\
        read X3 s = word w /\
        bignum_from_memory (x,k) s = m /\
        bignum_from_memory (z,i) s = l /\
        (ODD m
         ==> ((l + 2 EXP (64 * i) * val(read (memory :> bytes64 z') s)) *
              (m + 1) + 1 ==
              2 EXP (64 * i) * bignum_from_memory (z',p) s + l)
             (mod (2 EXP (64 * k))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN
    REWRITE_TAC[ARITH_RULE `p - 2 = p - 1 - 1`] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WORD_SUB] THEN
    UNDISCH_THEN `k - i:num = p` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> 1 <= k - i - 1`] THEN
    VAL_INT64_TAC `k - i - 1` THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
    UNDISCH_TAC `i < k - 1` THEN ARITH_TAC] THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_FORGET_COMPONENTS_TAC
    [`memory :> bytes (z,8 * i)`; `memory :> bytes (x,8 * k)`] THEN

  ASM_SIMP_TAC[NUMBER_RULE
   `(l * m + 1 == e * q) (mod d)
    ==> (((l + e * z) * (m + 1) + 1 == e * w + l) (mod d) <=>
         (e * (q + m * z + z) == e * w) (mod d))`] THEN
  SUBGOAL_THEN `2 EXP (64 * k) = 2 EXP (64 * i) * 2 EXP (64 * p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN EXPAND_TAC "p" THEN
    UNDISCH_TAC `i < k - 1` THEN ARITH_TAC;
    REWRITE_TAC[CONG_MULT_LCANCEL_ALL; EXP_EQ_0; ARITH_EQ]] THEN

  SUBGOAL_THEN
   `!q w z. (q + m * z + z == w) (mod (2 EXP (64 * p))) <=>
            (q + lowdigits m p * z + z == w) (mod (2 EXP (64 * p)))`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[lowdigits; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD m <=> ODD(lowdigits m p)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[lowdigits; ODD_MOD_POW2] THEN
    ASM_CASES_TAC `ODD m` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "p" THEN UNDISCH_TAC `i < k - 1` THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(m * w + 1 == 0) (mod (2 EXP 64)) <=>
    (lowdigits m p * w + 1 == 0) (mod (2 EXP 64))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `(m == m') (mod e)
      ==> ((m * w + 1 == 0) (mod e) <=> (m' * w + 1 == 0) (mod e))`) THEN
    REWRITE_TAC[lowdigits; CONG; MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "p" THEN
    UNDISCH_TAC `i < k - 1` THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `m' = lowdigits m p` THEN

  SUBGOAL_THEN `2 <= p /\ p < 2 EXP 61` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `z:int64` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `i:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `k:num` o concl))) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN

  SPEC_TAC(`m':num`,`m:num`) THEN SPEC_TAC(`z':int64`,`z:int64`) THEN
  SPEC_TAC(`p:num`,`k:num`) THEN SPEC_TAC(`q:num`,`a:num`) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`m:num`; `a:num`] THEN

  (*** Setup of innermost loop "innerloop" ****)

  ABBREV_TAC `v = (w * a) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `v < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
   (ARITH_RULE `2 <= k ==> 1 < k /\ ~(k = 0)`)) THEN
  ENSURES_WHILE_PAUP_TAC `1` `k:num` `pc + 0x94` `pc + 0xbc`
   `\i s. (read X0 s = word (k - 1) /\
           read X1 s = z /\
           read X2 s = x /\
           read X3 s = word w /\
           bignum_from_memory(x,k) s = m /\
           read X5 s = word v /\
           read (memory :> bytes64 z) s = word v /\
           read X9 s = word i /\
           bignum_from_memory(word_add x (word(8 * i)),k - i) s =
           highdigits m i /\
           bignum_from_memory(word_add z (word(8 * i)),k - i) s =
           highdigits a i /\
           (ODD m
            ==> 2 EXP (64 * i) * (bitval(read CF s) + val(read X6 s)) +
                bignum_from_memory(z,i) s =
                lowdigits a i + lowdigits m i * v + v)) /\
          (read X4 s = word 0 <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(x,k) s0 = highdigits m 0 /\
      bignum_from_memory(z,k) s0 = highdigits a 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_NEGMODINV_EXEC [5] (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      EXPAND_TAC "v" THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[WORD_EQ; CONG; GSYM LOWDIGITS_1; lowdigits] THEN
      REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES] THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[ODD] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; EQ_ADD_RCANCEL; ADD_ASSOC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[LOWDIGITS_1; VAL_WORD_BIGDIGIT; REAL_OF_NUM_CLAUSES] THEN
    ASM_CASES_TAC `bigdigit a 0 = 0` THENL
     [SUBGOAL_THEN `v = 0` SUBST1_TAC THENL
       [EXPAND_TAC "v" THEN ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES]) THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; MOD_0];
        ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
        REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[BITVAL_CLAUSES]];
      ASM_REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`; BITVAL_CLAUSES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_LE] THEN
      MATCH_MP_TAC(ARITH_RULE
       `(e * h + l = mv ==> a + l = e)
        ==> e * h + l = mv ==> e * (1 + h) = a + mv`) THEN
      DISCH_THEN(MP_TAC o SPEC `bigdigit a 0` o MATCH_MP (NUMBER_RULE
       `e * h + l = mv
        ==> !a. (a + mv == 0) (mod e) ==> (a + l == 0) (mod e)`)) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "v" THEN REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits] THEN
        REWRITE_TAC[CONG; MULT_CLAUSES] THEN CONV_TAC MOD_DOWN_CONV THEN
        REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
         `(m * w + 1 == 0) (mod e) ==> (a + m * w * a == 0) (mod e)`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SIMP_TAC[CONG; MOD_CASES; MOD_0; VAL_BOUND_64; BIGDIGIT_BOUND;
               ARITH_RULE `x < e /\ y < e ==> x + y < 2 * e`] THEN
      UNDISCH_TAC `~(bigdigit a 0 = 0)` THEN ARITH_TAC];
    ALL_TAC; (*** The main loop invariant ***)
    REPEAT STRIP_TAC THEN GHOST_INTRO_TAC `diff:int64` `read X4` THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN ASM_REWRITE_TAC[VAL_EQ_0];
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    GHOST_INTRO_TAC `cout:bool` `read CF` THEN
    GHOST_INTRO_TAC `hout:int64` `read X6` THEN
    ARM_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    REWRITE_TAC[CONG; MOD_MULT_ADD]] THEN

  (*** Proof of the inner loop invariant, just a simple multiply-add ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read X6` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  ARM_ACCSIM_TAC BIGNUM_NEGMODINV_EXEC [3;4;6;7] (1--10) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    ALL_TAC;
    REWRITE_TAC[WORD_SUB_EQ_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> (i + 1 = k <=> i = k - 1)`] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC [`i:num < k`; `k < 2 EXP 61`] THEN ARITH_TAC] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  DISCH_THEN(fun th ->
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
  ASM_REWRITE_TAC[ARITH_RULE
   `(e * a' + a) + (e * m' + m) * v + v:num =
    e * (a' + m' * v) + (a + m * v + v)`] THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEN_REWRITE_TAC LAND_CONV
   [TAUT `p /\ q /\ r /\ s <=> p /\ r /\ q /\ s`] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  CONV_TAC REAL_RING);;

let BIGNUM_NEGMODINV_SUBROUTINE_CORRECT = prove
 (`!k z x m pc returnaddress.
        nonoverlapping (word pc,0xd8) (z,8 * val k) /\
        nonoverlapping (x,8 * val k) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_negmodinv_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; x] s /\
                  bignum_from_memory (x,val k) s = m)
             (\s. read PC s = returnaddress /\
                  (ODD m
                   ==> (m * bignum_from_memory(z,val k) s + 1 == 0)
                       (mod (2 EXP (64 * val k)))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_NEGMODINV_EXEC BIGNUM_NEGMODINV_CORRECT);;
