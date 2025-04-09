(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Doubling modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_double_p256k1.o";;
 ****)

let bignum_double_p256k1_mc =
  define_assert_from_elf "bignum_double_p256k1_mc" "arm/secp256k1/bignum_double_p256k1.o"
[
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd37ffca6;       (* arm_LSR X6 X5 63 *)
  0x93c4fca5;       (* arm_EXTR X5 X5 X4 63 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x93c3fc84;       (* arm_EXTR X4 X4 X3 63 *)
  0x8a050087;       (* arm_AND X7 X4 X5 *)
  0x93c2fc63;       (* arm_EXTR X3 X3 X2 63 *)
  0x8a0300e7;       (* arm_AND X7 X7 X3 *)
  0xd37ff842;       (* arm_LSL X2 X2 1 *)
  0xd2807a28;       (* arm_MOV X8 (rvalue (word 977)) *)
  0xb2600108;       (* arm_ORR X8 X8 (rvalue (word 4294967296)) *)
  0xab08005f;       (* arm_CMN X2 X8 *)
  0xba1f00ff;       (* arm_ADCS XZR X7 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a9f1108;       (* arm_CSEL X8 X8 XZR Condition_NE *)
  0xab080042;       (* arm_ADDS X2 X2 X8 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DOUBLE_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_double_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_DOUBLE_P256K1_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x58) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x54) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_256k1))
            (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  ARM_STEPS_TAC BIGNUM_DOUBLE_P256K1_EXEC (1--9) THEN
  ABBREV_TAC `topbit <=> bit 63 (m_3:int64)` THEN
  SUBGOAL_THEN `word_ushr (m_3:int64) 63 = word(bitval topbit)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_BITVAL] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "topbit" THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC
   `l = bignum_of_wordlist
     [word_shl m_0 1;
      word_subword ((word_join:int64->int64->int128) m_1 m_0) (63,64);
      word_subword ((word_join:int64->int64->int128) m_2 m_1) (63,64);
      word_subword ((word_join:int64->int64->int128) m_3 m_2) (63,64)]` THEN
  SUBGOAL_THEN `2 EXP 256 * bitval topbit + l = 2 * n` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "n"; "topbit"] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_DOUBLE_P256K1_EXEC (12--14) (10--15) THEN
  RULE_ASSUM_TAC(SIMP_RULE[ADD_CLAUSES; VAL_EQ_0]) THEN
  SUBGOAL_THEN
   `word_add (word (bitval topbit)) (word (bitval carry_s13)) =
    (word 0:int64) <=>
    2 * n < p_256k1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ_0] THEN
    REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    ASM_CASES_TAC `topbit:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS `2 EXP 256 <= l + 4294968273` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[p_256k1] THEN ARITH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 128 <=
      bignum_of_wordlist[word_shl m_0 1;
       word_and
        (word_and
           (word_subword ((word_join:int64->int64->int128) m_2 m_1) (63,64))
           (word_subword ((word_join:int64->int64->int128) m_3 m_2) (63,64)))
         (word_subword ((word_join:int64->int64->int128) m_1 m_0) (63,64))] +
      4294968273` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "l" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP 64 /\ (a < 2 EXP 64 - 1 <=> h < 2 EXP 192 - 1) /\
      (~(h < 2 EXP 192 - 1)
       ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
            2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273))
      ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
           2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273)`) THEN
    SIMP_TAC[VAL_BOUND_64; BIGNUM_OF_WORDLIST_LT_MAX; LENGTH;
             ARITH_MULT; ARITH_ADD; ARITH_SUC; EX; DE_MORGAN_THM;
             WORD_BITWISE_RULE
              `word_and a b = word_not(word 0) <=>
               a = word_not(word 0) /\ b = word_not(word 0)`] THEN
    REWRITE_TAC[DISJ_ACI] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_ACCSTEPS_TAC BIGNUM_DOUBLE_P256K1_EXEC (16--19) (16--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s21" THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 4`;
    `if 2 * n < p_256k1 then &(2 * n) else &(2 * n) - &p_256k1:real`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MULT_2; MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256k1] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `q <=> 2 * n < p_256k1` THEN
  UNDISCH_THEN `2 EXP 256 * bitval topbit + l = 2 * n`
   (SUBST1_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LT] THEN EXPAND_TAC "l" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DOUBLE_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x58) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_256k1))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_DOUBLE_P256K1_EXEC BIGNUM_DOUBLE_P256K1_CORRECT);;
