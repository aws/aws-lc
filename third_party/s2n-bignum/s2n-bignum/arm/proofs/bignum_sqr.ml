(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squaring.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_sqr.o";;
 ****)

let bignum_sqr_mc =
  define_assert_from_elf "bignum_sqr_mc" "arm/generic/bignum_sqr.o"
[
  0xb4000600;       (* arm_CBZ X0 (word 192) *)
  0xaa1f03ef;       (* arm_MOV X15 XZR *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0x910004e8;       (* arm_ADD X8 X7 (rvalue (word 1)) *)
  0xd341fd0d;       (* arm_LSR X13 X8 (rvalue (word 1)) *)
  0xeb0201bf;       (* arm_CMP X13 X2 *)
  0x9a8231ad;       (* arm_CSEL X13 X13 X2 Condition_CC *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0x9a9f2108;       (* arm_CSEL X8 X8 XZR Condition_CS *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xeb0801bf;       (* arm_CMP X13 X8 *)
  0x54000229;       (* arm_BLS (word 68) *)
  0xcb0800ec;       (* arm_SUB X12 X7 X8 *)
  0xd37df18c;       (* arm_LSL X12 X12 (rvalue (word 3)) *)
  0x8b0c006c;       (* arm_ADD X12 X3 X12 *)
  0xf8687869;       (* arm_LDR X9 X3 (Shiftreg_Offset X8 3) *)
  0xf85f858a;       (* arm_LDR X10 X12 (Postimmediate_Offset (iword (-- &8))) *)
  0x9b0a7d2b;       (* arm_MUL X11 X9 X10 *)
  0x9bca7d29;       (* arm_UMULH X9 X9 X10 *)
  0xab0b0084;       (* arm_ADDS X4 X4 X11 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb0d011f;       (* arm_CMP X8 X13 *)
  0x54fffee1;       (* arm_BNE (word 2097116) *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0x9a0600c6;       (* arm_ADC X6 X6 X6 *)
  0xf24000ff;       (* arm_TST X7 (rvalue (word 1)) *)
  0x54000121;       (* arm_BNE (word 36) *)
  0xeb02011f;       (* arm_CMP X8 X2 *)
  0x540000e2;       (* arm_BCS (word 28) *)
  0xf8687869;       (* arm_LDR X9 X3 (Shiftreg_Offset X8 3) *)
  0x9b097d2b;       (* arm_MUL X11 X9 X9 *)
  0x9bc97d29;       (* arm_UMULH X9 X9 X9 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab0f0084;       (* arm_ADDS X4 X4 X15 *)
  0xf8277824;       (* arm_STR X4 X1 (Shiftreg_Offset X7 3) *)
  0xba0e00af;       (* arm_ADCS X15 X5 X14 *)
  0x9a1f00ce;       (* arm_ADC X14 X6 XZR *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0000ff;       (* arm_CMP X7 X0 *)
  0x54fffaa3;       (* arm_BCC (word 2096980) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_EXEC = ARM_MK_EXEC_RULE bignum_sqr_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQR_CORRECT = prove
 (`!p n z x a pc.
     ALL (nonoverlapping (z,8 * val p))
         [(word pc,0xc4); (x,8 * val n)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [p; z; n; x] s /\
               bignum_from_memory(x,val n) s = a)
          (\s. read PC s = word (pc + 0xc0) /\
               bignum_from_memory(z,val p) s = lowdigits (a EXP 2) (val p))
          (MAYCHANGE [PC; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val p)])`,
  MAP_EVERY W64_GEN_TAC [`p:num`; `n:num`] THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_RANGE_TAC "n" "a" THEN

  (*** Degenerate case when output size is zero ***)

  ASM_CASES_TAC `p = 0` THENL
   [ARM_SIM_TAC BIGNUM_SQR_EXEC [1] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0];
    ALL_TAC] THEN

  (*** Get basic bbounds from the nonoverlapping assumptions ***)

  SUBGOAL_THEN `8 * p < 2 EXP 64 /\ 8 * n < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th ->
      try MP_TAC
       (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2) th)
      with Failure _ -> ALL_TAC) THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Setup of the outer loop ***)

  ENSURES_WHILE_UP_TAC `p:num` `pc + 0x10` `pc + 0xb8`
   `\k s. read X0 s = word p /\
          read X1 s = z /\
          read X2 s = word n /\
          read X3 s = x /\
          read X7 s = word k /\
          bignum_from_memory (x,n) s = a /\
          2 EXP (64 * k) * (2 EXP 64 * val(read X14 s) + val(read X15 s)) +
          bignum_from_memory(z,k) s =
          nsum {i,j | i < n /\ j < n /\ i + j < k}
            (\(i,j). 2 EXP (64 * (i + j)) * bigdigit a i * bigdigit a j)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_SQR_EXEC (1--4) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[VAL_WORD_0; CONJUNCT1 LT; MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
    REWRITE_TAC[SET_RULE `{(i,j) | F} = {}`; NSUM_CLAUSES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC; (*** This is the main loop invariant ***)
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k:num` THEN
    ARM_SIM_TAC BIGNUM_SQR_EXEC (1--2);
    GHOST_INTRO_TAC `cout:int64` `read X15` THEN
    ARM_SIM_TAC BIGNUM_SQR_EXEC (1--2) THEN
    MP_TAC(SPECL [`a:num`; `n:num`] BIGDIGITSUM_WORKS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[EXP_2; GSYM NSUM_RMUL] THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
    SIMP_TAC[NSUM_NSUM_PRODUCT; FINITE_NUMSEG_LT] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `(e * a) * (f * b):num = (e * f) * a * b`] THEN
    REWRITE_TAC[lowdigits; GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC(MESON[MOD_LT]
     `x < n /\ x MOD n = y MOD n ==> x = y MOD n`) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; IN_ELIM_THM; GSYM CONG] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `n * q + y:num = a ==> (z == a) (mod n) ==> (y == z) (mod n)`)) THEN
    REWRITE_TAC[CONG] THEN
    REPLICATE_TAC 2
     (W(MP_TAC o PART_MATCH (lhand o rand) MOD_NSUM_MOD o lhand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{i:num | i < n} CROSS {i:num | i < n}` THEN
        REWRITE_TAC[FINITE_CROSS_EQ; FINITE_NUMSEG_LT] THEN
        REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS] THEN
        SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN SIMP_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[NOT_LT] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM DIVIDES_MOD] THEN MATCH_MP_TAC DIVIDES_RMUL THEN
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL]] THEN

  (*** The main outer loop invariant ***)

  X_GEN_TAC `k:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k:num` THEN
  SUBGOAL_THEN
   `!f. nsum {i,j | i < n /\ j < n /\ i + j < k + 1} f =
        nsum {i,j | i < n /\ j < n /\ i + j < k} f +
        nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) n} (\i. f(i,k - i))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN X_GEN_TAC `f:num#num->num` THEN
    REWRITE_TAC[ARITH_RULE `i < k + 1 <=> i < k \/ i = k`] THEN
    REWRITE_TAC[LEFT_OR_DISTRIB; SET_RULE
     `{f x y | P x y \/ Q x y} = {f x y | P x y} UNION {f x y | Q x y}`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NSUM_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{i:num | i < n} CROSS {i:num | i < n}` THEN
          REWRITE_TAC[FINITE_CROSS_EQ; FINITE_NUMSEG_LT]) THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
                  DISJOINT; EXTENSION; IN_INTER] THEN
      SIMP_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC] THEN
    MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC `FST:num#num->num` THEN EXISTS_TAC `\i:num. i,k - i` THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `lowsum = nsum {i,j | i < n /\ j < n /\ i + j < k}
             (\(i,j). 2 EXP (64 * (i + j)) * bigdigit a i * bigdigit a j)` THEN
  GHOST_INTRO_TAC `zsum:num` `bignum_from_memory(z,k)` THEN

  GHOST_INTRO_TAC `hh:num` `\s. val(read X14 s)` THEN
  GHOST_INTRO_TAC `ll:num` `\s. val(read X15 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  (*** Computation of inner loop bounds and other initialization ***)

  ENSURES_SEQUENCE_TAC `pc + 0x34`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word n /\
        read X3 s = x /\
        read X7 s = word k /\
        bignum_from_memory (x,n) s = a /\
        bignum_from_memory (z,k) s = zsum /\
        read X14 s = word hh /\
        read X15 s = word ll /\
        read X8 s = word ((k + 1) - n) /\
        read X13 s = word (MIN ((k + 1) DIV 2) n) /\
        read X4 s = word 0 /\
        read X5 s = word 0 /\
        read X6 s = word 0` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_SQR_EXEC (1--9) THEN
    GEN_REWRITE_TAC BINOP_CONV [GSYM VAL_EQ] THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [COND_RAND] THEN
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_USHR; EXP_1] THEN
    VAL_INT64_TAC `k + 1` THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
    REWRITE_TAC[WORD_SUB; GSYM NOT_LT; COND_SWAP] THEN
    REWRITE_TAC[ARITH_RULE `MIN k n = if k < n then k else n`] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
    VAL_INT64_TAC `(k + 1) DIV 2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Separate and handle the part from "innerend" onwards ***)

  ENSURES_SEQUENCE_TAC `pc + 0xa4`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word n /\
        read X3 s = x /\
        read X7 s = word k /\
        bignum_from_memory (x,n) s = a /\
        bignum_from_memory (z,k) s = zsum /\
        ((2 EXP 64 * val(read X14 s) + val(read X15 s)) +
         2 EXP 128 * val(read X6 s) +
         2 EXP 64 * val(read X5 s) + val(read X4 s) ==
         (2 EXP 64 * hh + ll) +
         nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) n}
              (\i. bigdigit a i * bigdigit a (k - i))) (mod (2 EXP 192))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `c:num` `\s. val(read X6 s)` THEN
    GHOST_INTRO_TAC `h:num` `\s. val(read X5 s)` THEN
    GHOST_INTRO_TAC `l:num` `\s. val(read X4 s)` THEN
    GHOST_INTRO_TAC `hh':num` `\s. val(read X14 s)` THEN
    GHOST_INTRO_TAC `ll':num` `\s. val(read X15 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_ACCSIM_TAC BIGNUM_SQR_EXEC [1;3;4] (1--5) THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(ARITH_RULE `!j. j < MIN (k + 1) n ==> j + k - j = k`) THEN
    SIMP_TAC[IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    EXPAND_TAC "lowsum" THEN REWRITE_TAC[NSUM_LMUL; ARITH_RULE
     `a + z + b:num = (c + z) + d <=> a + b = c + d`] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (k + 1) = 64 * k + 64`] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 192` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `hh < 2 EXP 64 /\ ll < 2 EXP 64 /\
        ss <= 2 EXP 64 * (2 EXP 64 - 1) EXP 2
        ==> (2 EXP 64 * hh + ll) + ss < 2 EXP 192`) THEN
      ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS
       `nsum {i | i < 2 EXP 64} (\j. bigdigit a j * bigdigit a (k - j))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
        REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
        UNDISCH_TAC `n < 2 EXP 64` THEN ARITH_TAC;
        MATCH_MP_TAC NSUM_BOUND_GEN THEN
        REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        CONJ_TAC THENL [EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ; EXP_2] THEN
        MATCH_MP_TAC LE_MULT2 THEN
        REWRITE_TAC[ARITH_RULE `d <= 2 EXP 64 - 1 <=> d < 2 EXP 64`] THEN
        REWRITE_TAC[BIGDIGIT_BOUND]];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
       `(s' == z + s) (mod n)
        ==> (z + x == y + s') (mod n) ==> (x == y + s) (mod n)`)) THEN
      REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REAL_INTEGER_TAC]] THEN

  (*** Back off further to the "nosumming" label to handle extra term ***)

  ENSURES_SEQUENCE_TAC `pc + 0x7c`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word n /\
        read X3 s = x /\
        read X7 s = word k /\
        bignum_from_memory (x,n) s = a /\
        bignum_from_memory (z,k) s = zsum /\
        read X14 s = word hh /\
        read X15 s = word ll /\
        read X8 s =
          (if (k + 1) - n < n then word(MIN ((k + 1) DIV 2) n)
           else word((k + 1) - n)) /\
        (2 EXP 128 * val(read X6 s) +
         2 EXP 64 * val(read X5 s) + val(read X4 s) ==
         nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) n /\ ~(2 * i = k)}
              (\i. bigdigit a i * bigdigit a (k - i))) (mod (2 EXP 192))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `c:num` `\s. val(read X6 s)` THEN
    GHOST_INTRO_TAC `h:num` `\s. val(read X5 s)` THEN
    GHOST_INTRO_TAC `l:num` `\s. val(read X4 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_SQR_EXEC (1--2) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
    ASM_REWRITE_TAC[WORD_AND_1_BITVAL; BIT_LSB; VAL_WORD_BITVAL] THEN
    REWRITE_TAC[BITVAL_EQ_0; COND_SWAP] THEN COND_CASES_TAC THENL
     [DISCH_TAC THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; CONG_ADD_LCANCEL_EQ] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONG_TRANS)) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM NOT_EVEN]) THEN
      SIMP_TAC[EVEN_EXISTS; NOT_EXISTS_THM; CONG_REFL];
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_ODD]) THEN DISCH_TAC] THEN
    ARM_STEPS_TAC BIGNUM_SQR_EXEC (3--4) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
    VAL_INT64_TAC `MIN ((k + 1) DIV 2) n` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(k + 1) - n < n` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
      VAL_INT64_TAC `(k + 1) - n` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; CONG_ADD_LCANCEL_EQ] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONG_TRANS)) THEN
      MATCH_MP_TAC EQ_IMP_CONG THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
      SIMPLE_ARITH_TAC] THEN
    REWRITE_TAC[ARITH_RULE `n <= MIN a n <=> n <= a`] THEN COND_CASES_TAC THENL
     [DISCH_TAC THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; CONG_ADD_LCANCEL_EQ] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONG_TRANS)) THEN
      MATCH_MP_TAC EQ_IMP_CONG THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
      UNDISCH_TAC `n <= (k + 1) DIV 2` THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN DISCH_TAC] THEN

    SUBGOAL_THEN
     `read  (memory :> bytes64 (word_add x (word (8 * MIN ((k + 1) DIV 2) n))))
            s4 =
      word(bigdigit a (MIN ((k + 1) DIV 2) n))`
    ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      ASM_REWRITE_TAC[ARITH_RULE `MIN k n < n <=> k < n`; WORD_VAL];
      ALL_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_SQR_EXEC [6;8;9;10] (5--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC
     `(2 EXP 64 * hh + ll) + (2 EXP 128 * c + 2 EXP 64 * h + l) +
      bigdigit a (MIN ((k + 1) DIV 2) n) EXP 2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REAL_INTEGER_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CONG_ADD_LCANCEL_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `(chl:num == x) (mod n) ==> x + d = y ==> (chl + d == y) (mod n)`)) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `kk:num` SUBST_ALL_TAC o
       GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(2 * n + 1) DIV 2 = n`]) THEN
    REWRITE_TAC[ARITH_RULE `2 * a = 2 * b <=> a = b`] THEN
    SUBGOAL_THEN
     `{i | (2 * kk + 1) - n <= i /\ i < MIN (2 * kk + 1) n} =
      kk INSERT
      {i | i IN {j | j < MIN (2 * kk + 1) n} /\
           (2 * kk + 1) - n <= i /\ ~(i = kk)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN SIMPLE_ARITH_TAC;
      SIMP_TAC[NSUM_CLAUSES; FINITE_RESTRICT; FINITE_NUMSEG_LT]] THEN
    REWRITE_TAC[SET_RULE
     `{x | x IN {y | Q y} /\ P x /\ R x} = {x | P x /\ Q x /\ R x}`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXP_2] THEN BINOP_TAC THEN AP_TERM_TAC THEN
    SIMPLE_ARITH_TAC] THEN

  (*** Rewrite the sum using symmetry ***)

  SUBGOAL_THEN
   `!f. nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) n /\ ~(2 * i = k)}
             (\i. f i * f(k - i)) =
        2 * nsum {i | (k + 1) - n <= i /\ i < MIN ((k + 1) DIV 2) n}
                 (\i. f i * f(k - i))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(2 * i = k) <=> 2 * i < k \/ k < 2 * i`] THEN
    REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x /\ (R x \/ S x)} =
      {x | x IN {y | Q y} /\ P x /\ R x} UNION
      {x | x IN {y | Q y} /\ P x /\ S x}`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NSUM_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT; DISJOINT; INTER] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
      ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM]] THEN
    MATCH_MP_TAC(ARITH_RULE `x = z /\ y = z ==> x + y = 2 * z`) THEN
    CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ARITH_TAC;
      MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
      REPEAT(EXISTS_TAC `\i:num. k - i`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ARITH_TAC; GEN_TAC THEN STRIP_TAC] THEN
      REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN

  (*** Case split to trivialize the "no terms in sum" case ***)

  ASM_CASES_TAC `MIN ((k + 1) DIV 2) n <= (k + 1) - n` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE
     `a:num <= b ==> !c. ~(b <= c /\ c < a)`) th]) THEN
    REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    ARM_SIM_TAC BIGNUM_SQR_EXEC (1--2) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; VAL_WORD_0; CONG_REFL] THEN
    MAP_EVERY VAL_INT64_TAC [`MIN ((k + 1) DIV 2) n`; `(k + 1) - n`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(a <= b /\ ~(b = a)) <=> b <= a`] THEN
    COND_CASES_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN
  SUBGOAL_THEN `(k + 1) - n < n` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN

  (*** Setup of the inner loop ***)

  ENSURES_WHILE_AUP_TAC
   `(k + 1) - n` `MIN ((k + 1) DIV 2) n` `pc + 0x48` `pc + 0x68`
   `\i s. (read X0 s = word p /\
           read X1 s = z /\
           read X2 s = word n /\
           read X3 s = x /\
           read X7 s = word k /\
           bignum_from_memory (x,n) s = a /\
           bignum_from_memory (z,k) s = zsum /\
           read X14 s = word hh /\
           read X15 s = word ll /\
           read X13 s = word (MIN ((k + 1) DIV 2) n) /\
           read X8 s = word i /\
           read X12 s = word_add x (word_sub (word(8 * k)) (word(8 * i))) /\
           (2 EXP 128 * val (read X6 s) +
            2 EXP 64 * val (read X5 s) + val (read X4 s) ==
            nsum {j | (k + 1) - n <= j /\ j < i}
                 (\j. bigdigit a j * bigdigit a (k - j)))
           (mod (2 EXP 192)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY VAL_INT64_TAC [`MIN ((k + 1) DIV 2) n`; `(k + 1) - n`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_SQR_EXEC (1--2) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(a <= b /\ ~(b = a)) <=> ~(a < b)`] THEN
    DISCH_TAC THEN ARM_STEPS_TAC BIGNUM_SQR_EXEC (3--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES; LET_ANTISYM] THEN
    REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES; CONG_REFL] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC; (*** The inner loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ARM_SIM_TAC BIGNUM_SQR_EXEC (1--2) THEN
    MAP_EVERY VAL_INT64_TAC [`MIN ((k + 1) DIV 2) n`; `i:num`] THEN
    ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `c:num` `\s. val(read X6 s)` THEN
    GHOST_INTRO_TAC `h:num` `\s. val(read X5 s)` THEN
    GHOST_INTRO_TAC `l:num` `\s. val(read X4 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ARM_ACCSIM_TAC BIGNUM_SQR_EXEC (3--5) (1--5) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `(x == s) (mod n) ==> (chl == 2 * x) (mod n)
      ==> (chl == 2 * s) (mod n)`)) THEN
    REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC] THEN

  (*** The main inner loop invariant ***)

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
  GHOST_INTRO_TAC `c:num` `\s. val(read X6 s)` THEN
  GHOST_INTRO_TAC `h:num` `\s. val(read X5 s)` THEN
  GHOST_INTRO_TAC `l:num` `\s. val(read X4 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read (memory :> bytes64
         (word_add x (word_sub (word (8 * k)) (word (8 * j))))) s0 =
    word(bigdigit a (k - j)) /\
    read (memory :> bytes64 (word_add x (word (8 * j)))) s0 =
    word(bigdigit a j)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `k - j < n /\ j:num < n` (fun th -> REWRITE_TAC[th])
    THENL [SIMPLE_ARITH_TAC; REWRITE_TAC[WORD_VAL]] THEN
    AP_THM_TAC THEN REPLICATE_TAC 4 AP_TERM_TAC THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_SUB] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQR_EXEC [3;5;6;7] (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_neg(word 8):int64`)) THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  SUBGOAL_THEN
   `{i | (k + 1) - n <= i /\ i < j + 1} =
    j INSERT {i | (k + 1) - n <= i /\ i < j}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    UNDISCH_TAC `(k + 1) - n <= j` THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | P x /\ Q x} = {x | x IN {y | Q y} /\ P x}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; FINITE_RESTRICT] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN {y | Q y} /\ P x} = {x | P x /\ Q x}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
   `(s' == s) (mod n)
    ==> (x == y + s') (mod n) ==> (x == y + s) (mod n)`)) THEN
  REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REAL_INTEGER_TAC);;

let BIGNUM_SQR_SUBROUTINE_CORRECT = prove
 (`!p n z x a pc returnaddress.
     ALL (nonoverlapping (z,8 * val p)) [(word pc,0xc4); (x,8 * val n)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_sqr_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [p; z; n; x] s /\
               bignum_from_memory (x,val n) s = a)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,val p) s = lowdigits (a EXP 2) (val p))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val p)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_SQR_EXEC BIGNUM_SQR_CORRECT);;
