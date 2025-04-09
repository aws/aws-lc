(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_add_p256k1.o";;
 ****)

let bignum_add_p256k1_mc = define_assert_from_elf "bignum_add_p256k1_mc" "arm/secp256k1/bignum_add_p256k1.o"
[
  0xa9401825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&16))) *)
  0xa9410c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0x8a0700c9;       (* arm_AND X9 X6 X7 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xd2807a24;       (* arm_MOV X4 (rvalue (word 977)) *)
  0xb2600084;       (* arm_ORR X4 X4 (rvalue (word 4294967296)) *)
  0xab0400bf;       (* arm_CMN X5 X4 *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0x9a9f1084;       (* arm_CSEL X4 X4 XZR Condition_NE *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_ADD_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_add_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_ADD_P256K1_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x60) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x5c) /\
                  (m < p_256k1 /\ n < p_256k1
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256k1))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P256K1_EXEC [3;4;7;9] (1--11) THEN
  ABBREV_TAC `l = bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s9]` THEN
  SUBGOAL_THEN `2 EXP 256 * bitval carry_s9 + l = m + n` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P256K1_EXEC (14--16) (12--17) THEN
  SUBGOAL_THEN
   `val(word_add (word(bitval carry_s9))
                 (word(bitval carry_s15)):int64) = 0 <=>
    m + n < p_256k1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    ASM_CASES_TAC `carry_s9:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS `2 EXP 256 <= l + 4294968273` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[p_256k1] THEN ARITH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 128 <=
      bignum_of_wordlist[sum_s3; word_and (word_and sum_s4 sum_s7) sum_s9] +
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
    RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P256K1_EXEC (18--21) (18--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s23" THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 4`;
    `if m + n < p_256k1 then &(m + n) else &(m + n) - &p_256k1:real`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256k1] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `q <=> m + n < p_256k1` THEN
  UNDISCH_THEN `2 EXP 256 * bitval carry_s9 + l = m + n`
   (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "l" THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_ADD_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x60) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_256k1 /\ n < p_256k1
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256k1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_P256K1_EXEC BIGNUM_ADD_P256K1_CORRECT);;
