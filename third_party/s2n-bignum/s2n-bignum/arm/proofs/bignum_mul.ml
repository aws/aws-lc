(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication.                                                           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_mul.o";;
 ****)

let bignum_mul_mc =
  define_assert_from_elf "bignum_mul_mc" "arm/generic/bignum_mul.o"
[
  0xb4000400;       (* arm_CBZ X0 (word 128) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0x9100052b;       (* arm_ADD X11 X9 (rvalue (word 1)) *)
  0xeb02017f;       (* arm_CMP X11 X2 *)
  0x9a82316c;       (* arm_CSEL X12 X11 X2 Condition_CC *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0x9a9f216b;       (* arm_CSEL X11 X11 XZR Condition_CS *)
  0xeb0b018a;       (* arm_SUBS X10 X12 X11 *)
  0x540001e9;       (* arm_BLS (word 60) *)
  0xd37df16e;       (* arm_LSL X14 X11 (rvalue (word 3)) *)
  0x8b0301ce;       (* arm_ADD X14 X14 X3 *)
  0xcb0c012f;       (* arm_SUB X15 X9 X12 *)
  0xd37df1ef;       (* arm_LSL X15 X15 (rvalue (word 3)) *)
  0x8b0501ef;       (* arm_ADD X15 X15 X5 *)
  0xf84085cb;       (* arm_LDR X11 X14 (Postimmediate_Offset (iword (&8))) *)
  0xf86a79ec;       (* arm_LDR X12 X15 (Shiftreg_Offset X10 3) *)
  0x9b0c7d6d;       (* arm_MUL X13 X11 X12 *)
  0x9bcc7d6b;       (* arm_UMULH X11 X11 X12 *)
  0xab0d00c6;       (* arm_ADDS X6 X6 X13 *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xf100054a;       (* arm_SUBS X10 X10 (rvalue (word 1)) *)
  0x54ffff01;       (* arm_BNE (word 2097120) *)
  0xf8297826;       (* arm_STR X6 X1 (Shiftreg_Offset X9 3) *)
  0xaa0703e6;       (* arm_MOV X6 X7 *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0x91000529;       (* arm_ADD X9 X9 (rvalue (word 1)) *)
  0xeb00013f;       (* arm_CMP X9 X0 *)
  0x54fffca3;       (* arm_BCC (word 2097044) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_EXEC = ARM_MK_EXEC_RULE bignum_mul_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUL_CORRECT = prove
 (`!p m n z x y a b pc.
     ALL (nonoverlapping (z,8 * val p))
         [(word pc,0x84); (x,8 * val m); (y,8 * val n)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_mul_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [p; z; m; x; n; y] s /\
               bignum_from_memory(x,val m) s = a /\
               bignum_from_memory(y,val n) s = b)
          (\s. read PC s = word (pc + 0x80) /\
               bignum_from_memory(z,val p) s = lowdigits (a * b) (val p))
          (MAYCHANGE [PC; X0; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val p)])`,
  MAP_EVERY W64_GEN_TAC [`p:num`; `m:num`; `n:num`] THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_RANGE_TAC "m" "a" THEN
  BIGNUM_RANGE_TAC "n" "b" THEN

  (*** Degenerate case when output size is zero ***)

  ASM_CASES_TAC `p = 0` THENL
   [ARM_SIM_TAC BIGNUM_MUL_EXEC [1] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0];
    ALL_TAC] THEN

  (*** Get basic bbounds from the nonoverlapping assumptions ***)

  SUBGOAL_THEN
   `8 * p < 2 EXP 64 /\ 8 * m < 2 EXP 64 /\ 8 * n < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th ->
      try MP_TAC
       (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2) th)
      with Failure _ -> ALL_TAC) THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Setup of the outer loop ***)

  ENSURES_WHILE_UP_TAC `p:num` `pc + 0x10` `pc + 0x78`
   `\k s. read X0 s = word p /\
          read X1 s = z /\
          read X2 s = word m /\
          read X3 s = x /\
          read X4 s = word n /\
          read X5 s = y /\
          read X9 s = word k /\
          bignum_from_memory (x,m) s = a /\
          bignum_from_memory (y,n) s = b /\
          2 EXP (64 * k) * (2 EXP 64 * val(read X7 s) + val(read X6 s)) +
          bignum_from_memory(z,k) s =
          nsum {i,j | i < m /\ j < n /\ i + j < k}
               (\(i,j). 2 EXP (64 * (i + j)) *
                        bigdigit a i * bigdigit b j)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_MUL_EXEC (1--4) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[VAL_WORD_0; CONJUNCT1 LT; MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
    REWRITE_TAC[SET_RULE `{(i,j) | F} = {}`; NSUM_CLAUSES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; WORD_ADD_0; SUB_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
    REWRITE_TAC[LOWDIGITS_0; ADD_CLAUSES];
    ALL_TAC; (*** This is the main loop invariant ***)
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k:num` THEN
    ARM_SIM_TAC BIGNUM_MUL_EXEC (1--2);
    GHOST_INTRO_TAC `cout:int64` `read X6` THEN
    ARM_SIM_TAC BIGNUM_MUL_EXEC (1--2) THEN
    MP_TAC(SPECL [`b:num`; `n:num`] BIGDIGITSUM_WORKS) THEN
    MP_TAC(SPECL [`a:num`; `m:num`] BIGDIGITSUM_WORKS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[GSYM NSUM_RMUL] THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
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
        EXISTS_TAC `{i:num | i < m} CROSS {i:num | i < n}` THEN
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
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN
   `!f. nsum {i,j | i < m /\ j < n /\ i + j < k + 1} f =
        nsum {i,j | i < m /\ j < n /\ i + j < k} f +
        nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) m} (\i. f(i,k - i))`
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
          EXISTS_TAC `{i:num | i < m} CROSS {i:num | i < n}` THEN
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
   `lowsum = nsum {i,j | i < m /\ j < n /\ i + j < k}
           (\(i,j). 2 EXP (64 * (i + j)) * bigdigit a i * bigdigit b j)` THEN

  GHOST_INTRO_TAC `zsum:num` `bignum_from_memory(z,k)` THEN
  GHOST_INTRO_TAC `h:num` `\s. val(read X7 s)` THEN
  GHOST_INTRO_TAC `l:num` `\s. val(read X6 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0x28`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word m /\
        read X3 s = x /\
        read X4 s = word n /\
        read X5 s = y /\
        read X9 s = word k /\
        read X11 s = word ((k + 1) - n) /\
        read X12 s = word (MIN (k + 1) m) /\
        bignum_from_memory (x,m) s = a /\
        bignum_from_memory (y,n) s = b /\
        bignum_from_memory (z,k) s = zsum /\
        read X8 s = word 0 /\
        read X7 s = word h /\
        read X6 s = word l` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_MUL_EXEC (1--6) THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    VAL_INT64_TAC `k + 1` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_SUB; GSYM NOT_LT; COND_SWAP] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN COND_CASES_TAC THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** Separate and handle the final writeback to z ***)

  ENSURES_SEQUENCE_TAC `pc + 0x68`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word m /\
        read X3 s = x /\
        read X4 s = word n /\
        read X5 s = y /\
        read X9 s = word k /\
        bignum_from_memory (x,m) s = a /\
        bignum_from_memory (y,n) s = b /\
        bignum_from_memory (z,k) s = zsum /\
        2 EXP 128 * val(read X8 s) +
        2 EXP 64 * val(read X7 s) + val(read X6 s) =
        (2 EXP 64 * h + l) +
        nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) m}
             (\i. bigdigit a i * bigdigit b (k - i))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `c':num` `\s. val(read X8 s)` THEN
    GHOST_INTRO_TAC `h':num` `\s. val(read X7 s)` THEN
    GHOST_INTRO_TAC `l':num` `\s. val(read X6 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_SIM_TAC BIGNUM_MUL_EXEC (1--4) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; GSYM WORD_ADD] THEN
    REWRITE_TAC[ARITH_RULE `64 * (k + 1) = 64 * k + 64`; EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE
     `(e * 2 EXP 64) * (2 EXP 64 * c' + h') + zsum + e * l' =
      e * (2 EXP 128 * c' + 2 EXP 64 * h' + l') + zsum`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE
     `e * ((a + a') + b) + c:num = (e * (a + a') + c) + e * b`] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `i < MIN (k + 1) m` THEN ARITH_TAC] THEN

 (*** Case split to trivialize the "no terms in sum" case ***)

  ASM_CASES_TAC `MIN (k + 1) m <= (k + 1) - n` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE
     `b:num <= a ==> !c. ~(a <= c /\ c < b)`) th]) THEN
    REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES; ADD_CLAUSES] THEN
    ARM_SIM_TAC BIGNUM_MUL_EXEC (1--2) THEN
    REWRITE_TAC[ARITH_RULE `~(a:num <= b /\ ~(b = a)) <=> b <= a`] THEN
    MAP_EVERY VAL_INT64_TAC [`MIN (k + 1) m`; `(k + 1) - n`] THEN
    ASM_SIMP_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES;
                 VAL_WORD_EQ; DIMINDEX_64];
    ALL_TAC] THEN

  (*** Setup of the inner loop ***)

  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
  ENSURES_WHILE_PAUP_TAC `(k + 1) - n` `MIN (k + 1) m` `pc + 0x44` `pc + 0x64`
   `\i s. (read X0 s = word p /\
           read X1 s = z /\
           read X2 s = word m /\
           read X3 s = x /\
           read X4 s = word n /\
           read X5 s = y /\
           read X9 s = word k /\
           bignum_from_memory (x,m) s = a /\
           bignum_from_memory (y,n) s = b /\
           bignum_from_memory (z,k) s = zsum /\
           read X10 s = word (MIN (k + 1) m - i) /\
           read X15 s =
           word_add y (word(8 * ((k + 1) - MIN (k + 1) m) + (2 EXP 64 - 8))) /\
           read X14 s = word_add x (word(8 * i)) /\
           2 EXP 128 * val (read X8 s) +
           2 EXP 64 * val (read X7 s) +
           val (read X6 s) =
           (2 EXP 64 * h + l) +
           nsum {j | (k + 1) - n <= j /\ j < i}
                (\j. bigdigit a j * bigdigit b (k - j))) /\
          (read ZF s <=> i = MIN (k + 1) m)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_MUL_EXEC (1--2) THEN
    FIND_ASM_THEN lhand `read PC s2` MP_TAC THEN
    MAP_EVERY VAL_INT64_TAC [`MIN (k + 1) m`; `(k + 1) - n`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(a:num <= b /\ ~(b = a)) <=> b <= a`] THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_MUL_EXEC (3--7) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[LET_ANTISYM; EMPTY_GSPEC; NSUM_CLAUSES] THEN
    ASM_SIMP_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_EQ;
                 DIMINDEX_64] THEN
    MAP_EVERY ABBREV_TAC [`d = MIN (k + 1) m`; `e = (k + 1) - n`] THEN
    REWRITE_TAC[WORD_ADD; LEFT_SUB_DISTRIB] THEN
    ONCE_REWRITE_TAC[WORD_SUB] THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[ARITH_RULE `8 * MIN a b <= 8 * a`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_REDUCE_CONV `word 18446744073709551616:int64`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC; (*** The inner loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ARM_SIM_TAC BIGNUM_MUL_EXEC [1];
    ARM_SIM_TAC BIGNUM_MUL_EXEC [1]] THEN

  (*** The main inner loop invariant ***)

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `c':num` `\s. val(read X8 s)` THEN
  GHOST_INTRO_TAC `h':num` `\s. val(read X7 s)` THEN
  GHOST_INTRO_TAC `l':num` `\s. val(read X6 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[NUM_REDUCE_CONV `2 EXP 64 - 8`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  SUBGOAL_THEN
   `word((8 * ((k + 1) - MIN (k + 1) m) + 18446744073709551608) +
         8 * val(word(MIN (k + 1) m - j):int64)):int64 =
    word(8 * (k - j))`
  ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_ADD; WORD_SUB] THEN
    SUBGOAL_THEN `8 * j <= 8 * k` MP_TAC THENL
     [UNDISCH_TAC `j < MIN (k + 1) m` THEN ARITH_TAC;
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE] THEN DISCH_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * MIN a b <= 8 * a`] THEN
    SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_neg(word 8):int64`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add y (word (8 * (k - j))))) s0 =
    word(bigdigit b (k - j)) /\
    read (memory :> bytes64 (word_add x (word (8 * j)))) s0 =
    word(bigdigit a j)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    MAP_EVERY UNDISCH_TAC
     [`j < MIN (k + 1) m`; `(k + 1) - n <= j`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[WORD_VAL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_MUL_EXEC [3;5;6;7] (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  ONCE_REWRITE_TAC[WORD_SUB] THEN
  ASM_SIMP_TAC[LT_IMP_LE; ARITH_RULE `j + 1 <= n <=> j < n`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    ALL_TAC;
    REWRITE_TAC[VAL_EQ_0; WORD_RULE
     `word_sub (word_sub x (word j)) (word k) = word_sub x (word(j + k))`] THEN
    REWRITE_TAC[WORD_SUB_EQ_0] THEN GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC [`m < 2 EXP 64`; `j < MIN (k + 1) m`] THEN
    ARITH_TAC] THEN

  SUBGOAL_THEN
   `{i | (k + 1) - n <= i /\ i < j + 1} =
    j INSERT {i | (k + 1) - n <= i /\ i < j}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    UNDISCH_TAC `(k + 1) - n <= j` THEN ARITH_TAC;
    ALL_TAC] THEN

  W(MP_TAC o PART_MATCH (lhand o rand) (CONJUNCT2 NSUM_CLAUSES) o
    rand o rand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < j}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN

  GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `a + b + c:num = b + a + c`] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`192`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE
     `ab < 2 EXP 64 * 2 EXP 64 /\ h < 2 EXP 64 /\ l < 2 EXP 64 /\
      s <= (2 EXP 64 - 1) * (2 EXP 64 - 1) EXP 2
      ==> ab + (2 EXP 64 * h + l) + s < 2 EXP 192`) THEN
    ASM_SIMP_TAC[BIGDIGIT_BOUND; LT_MULT2] THEN
    TRANS_TAC LE_TRANS
     `nsum {n | n < 2 EXP 64 - 1} (\i. bigdigit a i * bigdigit b (k - i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      MAP_EVERY UNDISCH_TAC [`j < MIN (k + 1) m`; `m < 2 EXP 64`] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM CARD_NUMSEG_LT] THEN
      MATCH_MP_TAC NSUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG_LT; EXP_2] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
      REWRITE_TAC[ARITH_RULE `x <= 2 EXP 64 - 1 <=> x < 2 EXP 64`] THEN
      REWRITE_TAC[BIGDIGIT_BOUND]];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MUL_SUBROUTINE_CORRECT = prove
 (`!p m n z x y a b pc returnaddress.
     ALL (nonoverlapping (z,8 * val p))
         [(word pc,0x84); (x,8 * val m); (y,8 * val n)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_mul_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [p; z; m; x; n; y] s /\
               bignum_from_memory (x,val m) s = a /\
               bignum_from_memory (y,val n) s = b)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,val p) s =
               lowdigits (a * b) (val p))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val p)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MUL_EXEC BIGNUM_MUL_CORRECT);;
