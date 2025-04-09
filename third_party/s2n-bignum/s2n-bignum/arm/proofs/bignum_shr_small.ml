(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shifting of a bignum right < 64 bits.                                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_shr_small.o";;
 ****)

let bignum_shr_small_mc =
  define_assert_from_elf "bignum_shr_small_mc" "arm/generic/bignum_shr_small.o"
[
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xeb00005f;       (* arm_CMP X2 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf820783f;       (* arm_STR XZR X1 (Shiftreg_Offset X0 3) *)
  0xeb00005f;       (* arm_CMP X2 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0x54000040;       (* arm_BEQ (word 8) *)
  0xf8607867;       (* arm_LDR X7 X3 (Shiftreg_Offset X0 3) *)
  0xcb0403e5;       (* arm_NEG X5 X4 *)
  0x9ac520e7;       (* arm_LSL X7 X7 X5 *)
  0xf240149f;       (* arm_TST X4 (rvalue (word 63)) *)
  0xda9f03e8;       (* arm_CSETM X8 Condition_NE *)
  0x8a0800e7;       (* arm_AND X7 X7 X8 *)
  0xb4000120;       (* arm_CBZ X0 (word 36) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf8607869;       (* arm_LDR X9 X3 (Shiftreg_Offset X0 3) *)
  0x9ac42526;       (* arm_LSR X6 X9 X4 *)
  0xaa0700c6;       (* arm_ORR X6 X6 X7 *)
  0x9ac52127;       (* arm_LSL X7 X9 X5 *)
  0x8a0800e7;       (* arm_AND X7 X7 X8 *)
  0xf8207826;       (* arm_STR X6 X1 (Shiftreg_Offset X0 3) *)
  0xb5ffff20;       (* arm_CBNZ X0 (word 2097124) *)
  0x9ac524e0;       (* arm_LSR X0 X7 X5 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SHR_SMALL_EXEC = ARM_MK_EXEC_RULE bignum_shr_small_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let lemma1 = prove
 (`!n c. word_and (word_jshl (word n) (word_neg (word c)))
                  (word_neg (word (bitval(~(c MOD 64 = 0))))):int64 =
         word (2 EXP (64 - c MOD 64) * n)`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_JSHL_NEG o
      lhand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_64; CONG] THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC DIVIDES_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `64 = 2 EXP 6`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP MIN 64 6 = 64`] THEN
  REWRITE_TAC[WORD_AND_MASK; COND_SWAP; ARITH_RULE `2 EXP 6 = 64`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES; MOD_0];
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `64 - n < 64 <=> ~(n = 0)`] THEN
    REWRITE_TAC[word_shl; WORD_EQ; DIMINDEX_64; CONG; VAL_WORD] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_AC]]);;

let lemma2 = prove
 (`!x e. e <= 64
         ==> ((2 EXP e * x) MOD 2 EXP 64) DIV 2 EXP e = x MOD 2 EXP (64 - e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP 64 = 2 EXP e * 2 EXP (64 - e)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[MOD_MULT2; DIV_MULT; EXP_EQ_0; ARITH_EQ]]);;

let BIGNUM_SHR_SMALL_CORRECT = prove
 (`!p z n x a c pc.
        nonoverlapping (word pc,0x64) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_shr_small_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = word(pc + 0x60) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (a DIV 2 EXP (val c MOD 64)) (val p) /\
                  C_RETURN s = word(a MOD 2 EXP (val c MOD 64)))
             (MAYCHANGE [PC; X0; X5; X6; X7; X8; X9] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `a:num` THEN W64_GEN_TAC `c:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Split the proof at the "nopad" label ***)

  ENSURES_SEQUENCE_TAC `pc + 0x1c`
   `\s. read X1 s = z /\
        read X3 s = x /\
        read X4 s = word c /\
        bignum_from_memory (x,n) s = a /\
        read X0 s = word(MIN n p) /\
        read X7 s = word 0 /\
        bignum_from_memory(word_add z (word(8 * n)),p - n) s = 0 /\
        (read ZF s <=> n <= p)` THEN

  CONJ_TAC THENL
   [ASM_CASES_TAC `p:num <= n` THENL
     [ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--3) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_EQ_0] THEN
      ASM_SIMP_TAC[WORD_SUB_EQ_0; ARITH_RULE `p <= n ==> p - n = 0`] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; GSYM VAL_EQ] THEN
      UNDISCH_TAC `p:num <= n` THEN
      ASM_SIMP_TAC[ARITH_RULE `p <= n ==> MIN n p = p`] THEN ARITH_TAC;
      FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LE])] THEN

    ENSURES_WHILE_ADOWN_TAC `p:num` `n:num` `pc + 0xc` `pc + 0x14`
     `\i s. read X1 s = z /\
            read X2 s = word n /\
            read X3 s = x /\
            read X4 s = word c /\
            bignum_from_memory (x,n) s = a /\
            read X7 s = word 0 /\
            read X0 s = word i /\
            bignum_from_memory(word_add z (word(8 * i)),p - i) s = 0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--3) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASSUME_TAC(WORD_RULE
       `word_sub (word(i + 1)) (word 1):int64 = word i`) THEN
      ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
      ONCE_REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_EXPAND] THEN
      ASM_REWRITE_TAC[ARITH_RULE `p - i = 0 <=> ~(i < p)`] THEN
      REWRITE_TAC[WORD_RULE
       `word_add (word_add z (word (8 * i))) (word 8) =
        word_add z (word(8 * (i + 1)))`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `p - i - 1 = p - (i + 1)`] THEN
      REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2);

      ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
      ASM_SIMP_TAC[ARITH_RULE `n < p ==> MIN n p = n`] THEN
      ASM_REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0; LE_LT]];

    ALL_TAC] THEN

  (*** The possible initialization of the carry-in word ***)

  ENSURES_SEQUENCE_TAC `pc + 0x24`
   `\s. read X1 s = z /\
        read X0 s = word(MIN n p) /\
        read X3 s = x /\
        read X4 s = word c /\
        read X7 s = word(bigdigit a (MIN n p)) /\
        bignum_from_memory (x,MIN n p) s = lowdigits a (MIN n p) /\
        bignum_from_memory(word_add z (word(8 * MIN n p)),
                           p - MIN n p) s = 0` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n:num <= p` THENL
     [ASM_SIMP_TAC[ARITH_RULE `n <= p ==> MIN n p = n`] THEN
      ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC [1] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[BIGDIGIT_ZERO];
      ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      ASM_SIMP_TAC[ARITH_RULE `p < n ==> MIN n p = p`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      MP_TAC(ISPECL [`n:num`; `x:int64`; `s0:armstate`; `p:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN STRIP_TAC THEN
      ARM_STEPS_TAC BIGNUM_SHR_SMALL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "a" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
      ASM_SIMP_TAC[ARITH_RULE `p < n ==> MIN n p = p`]];
    ALL_TAC] THEN

  (*** Adopt q = min(n,p) as a new variable for brevity/convenience ***)

  MP_TAC(ARITH_RULE `MIN n p <= n /\ MIN n p <= p`) THEN
  ABBREV_TAC `q = MIN n p` THEN STRIP_TAC THEN

  (*** The preparation of negated shift and mask ***)

  ENSURES_SEQUENCE_TAC `pc + 0x38`
   `\s. read X1 s = z /\
        read X0 s = word q /\
        read X3 s = x /\
        read X4 s = word c /\
        read X5 s = word_neg(word c) /\
        read X8 s = word_neg(word(bitval(~(c MOD 64 = 0)))) /\
        read X7 s = word(2 EXP (64 - c MOD 64) * bigdigit a q) /\
        bignum_from_memory (x,q) s = lowdigits a q /\
        bignum_from_memory(word_add z (word(8 * q)),p - q) s = 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_SHR_SMALL_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_LZERO] THEN
    SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)) THEN
    ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN REWRITE_TAC[GSYM WORD_MASK] THEN
    SUBST1_TAC(ARITH_RULE `63 = 2 EXP 6 - 1`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP MIN 64 6 = 64`] THEN REWRITE_TAC[lemma1];
    ALL_TAC] THEN

  (*** Deal with the part from "end" immediately to avoid duplication ***)

  ENSURES_SEQUENCE_TAC `pc + 0x5c`
   `\s. bignum_from_memory (z,p) s = lowdigits (a DIV 2 EXP (c MOD 64)) p /\
        read X5 s = word_neg(word c) /\
        read X7 s = word(2 EXP (64 - c MOD 64) * bigdigit a 0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC [1] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) WORD_JUSHR_NEG o lhand o snd) THEN
    REWRITE_TAC[DIMINDEX_64; CONG] THEN ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC DIVIDES_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ARITH_RULE `64 = 2 EXP 6`] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP MIN 64 6 = 64`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 6 = 64`] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[EXP; MOD_1; WORD_EQ; DIMINDEX_64; CONG] THEN
      ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES; MOD_0];
      REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
      SIMP_TAC[lemma2; ARITH_RULE `64 - x <= 64`] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MOD_MOD_EXP_MIN] THEN
      REWRITE_TAC[ARITH_RULE `MIN (64 * 1) (64 - c) = 64 - c`] THEN
      REWRITE_TAC[ARITH_RULE `64 - (64 - c MOD 64) = c MOD 64`]]] THEN

  (*** The degenerate case q = 0 ***)

  ASM_CASES_TAC `q = 0` THENL
   [ASM_REWRITE_TAC[SUB_0; MULT_CLAUSES; WORD_ADD_0] THEN
    ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC [1] THEN
    UNDISCH_TAC `MIN n p = q` THEN
    ASM_REWRITE_TAC[ARITH_RULE `MIN n p = 0 <=> n = 0 \/ p = 0`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[lowdigits; MULT_CLAUSES; MOD_1; EXP] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN

  (*** The main loop ****)

  VAL_INT64_TAC `q:num` THEN

  ENSURES_WHILE_DOWN_TAC `q:num` `pc + 0x3c` `pc + 0x58`
   `\i s. read X1 s = z /\
          read X0 s = word i /\
          read X3 s = x /\
          read X4 s = word c /\
          read X5 s = word_neg(word c) /\
          read X8 s = word_neg(word(bitval(~(c MOD 64 = 0)))) /\
          read X7 s = word(2 EXP (64 - c MOD 64) * bigdigit a i) /\
          bignum_from_memory(x,i) s = lowdigits a i /\
          bignum_from_memory (word_add z (word (8 * i)),p - i) s =
          highdigits (lowdigits (a DIV 2 EXP (c MOD 64)) p) i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC [1] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HIGHDIGITS_ZERO THEN
    SUBST1_TAC(SYM(ASSUME `MIN n p = q`)) THEN REWRITE_TAC[MIN] THEN
    COND_CASES_TAC THEN REWRITE_TAC[LOWDIGITS_BOUND] THEN
    W(MP_TAC o PART_MATCH lhand LOWDIGITS_LE o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
    TRANS_TAC LET_TRANS `a:num` THEN ASM_REWRITE_TAC[DIV_LE];
    ALL_TAC; (*** The main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_SHR_SMALL_EXEC [1];
    REWRITE_TAC[SUB_0; MULT_CLAUSES; WORD_ADD_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_SHR_SMALL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[HIGHDIGITS_0]] THEN

  (*** Now the core inner loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < p` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(WORD_RULE `word_sub (word (i + 1)) (word 1):int64 = word i`) THEN
  DISCH_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BIGNUM_SHR_SMALL_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[lemma1] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `p - i = 0 <=> ~(i < p)`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `p - i - 1 = p - (i + 1)`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word (8 * i))) (word 8) =
    word_add z (word (8 * (i + 1)))`] THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; ARITH_RULE `64 = 2 EXP 6 /\ 256 = 2 EXP 8`] THEN
  REWRITE_TAC[DIMINDEX_8; MOD_MOD_EXP_MIN] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 6 = 64`] THEN
  SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  GEN_REWRITE_TAC RAND_CONV [HIGHDIGITS_STEP] THEN
  REWRITE_TAC[ARITH_RULE `a + n:num = n + b <=> a = b`] THEN
  ASM_REWRITE_TAC[BIGDIGIT_LOWDIGITS] THEN
  MP_TAC(ISPECL
   [`word(bigdigit a (i + 1)):int64`; `word (bigdigit a i):int64`;
    `c MOD 64`; `64 - c MOD 64`]
   WORD_OR_USHR_SHL) THEN
  REWRITE_TAC[word_jushr; word_shl; DIMINDEX_64] THEN
  ANTS_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[WORD_MOD_SIZE] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_64; DIMINDEX_128; ARITH_ADD;
           ARITH_SUC; VAL_WORD_EQ; BIGDIGIT_BOUND] THEN
  GEN_REWRITE_TAC RAND_CONV [bigdigit] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_DIV] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ONCE_REWRITE_TAC[DIV_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM highdigits] THEN
  REPLICATE_TAC 2
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; GSYM CONG] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `n divides a * b ==> (y + z:num == a * b * x + y + z) (mod n)`) THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
  ARITH_TAC);;

let BIGNUM_SHR_SMALL_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc returnaddress.
        nonoverlapping (word pc,0x64) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_shr_small_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (a DIV 2 EXP (val c MOD 64)) (val p) /\
                  C_RETURN s = word(a MOD 2 EXP (val c MOD 64)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_SHR_SMALL_EXEC BIGNUM_SHR_SMALL_CORRECT);;
