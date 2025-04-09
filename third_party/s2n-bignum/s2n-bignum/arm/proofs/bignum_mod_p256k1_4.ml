(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_256k1, the field characteristic for secp256k1.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_mod_p256k1_4.o";;
 ****)

let bignum_mod_p256k1_4_mc = define_assert_from_elf "bignum_mod_p256k1_4_mc" "arm/secp256k1/bignum_mod_p256k1_4.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x8a040066;       (* arm_AND X6 X3 X4 *)
  0x8a0500c6;       (* arm_AND X6 X6 X5 *)
  0xd2807a27;       (* arm_MOV X7 (rvalue (word 977)) *)
  0xb26000e7;       (* arm_ORR X7 X7 (rvalue (word 4294967296)) *)
  0xab0200e7;       (* arm_ADDS X7 X7 X2 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a873042;       (* arm_CSEL X2 X2 X7 Condition_CC *)
  0x9a863063;       (* arm_CSEL X3 X3 X6 Condition_CC *)
  0x9a863084;       (* arm_CSEL X4 X4 X6 Condition_CC *)
  0x9a8630a5;       (* arm_CSEL X5 X5 X6 Condition_CC *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_P256K1_4_EXEC = ARM_MK_EXEC_RULE bignum_mod_p256k1_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let P_256K1_AS_WORDLIST = prove
 (`p_256k1 =
   bignum_of_wordlist
    [word 0xfffffffefffffc2f;
     word_not(word 0);word_not(word 0);word_not(word 0)]`,
  REWRITE_TAC[p_256k1; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_OF_WORDLIST_P256K1_LE = prove
 (`p_256k1 <= bignum_of_wordlist[n0;n1;n2;n3] <=>
   0xfffffffefffffc2f <= val n0 /\
   n1 = word_not(word 0) /\ n2 = word_not(word 0) /\ n3 = word_not(word 0)`,
  REWRITE_TAC[P_256K1_AS_WORDLIST] THEN
  ONCE_REWRITE_TAC[BIGNUM_OF_WORDLIST_LE] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[word_not(word 0);word_not(word 0);word_not(word 0)] =
    2 EXP 192 - 1`
  SUBST1_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 192 - 1 < n <=> ~(n < 2 EXP (64 * 3))`] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_MAX; BIGNUM_FROM_WORDLIST_BOUND_GEN; ALL;
           LENGTH; ARITH_MULT; ARITH_ADD; ARITH_SUC; ARITH_LE; ARITH_LT] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

let BIGNUM_OF_WORDLIST_LT_P256K1 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3] < p_256k1 <=>
   n1 = word_not(word 0) /\ n2 = word_not(word 0) /\ n3 = word_not(word 0)
   ==> val n0 < 0xfffffffefffffc2f`,
  REWRITE_TAC[GSYM NOT_LE; BIGNUM_OF_WORDLIST_P256K1_LE] THEN
  CONV_TAC TAUT);;

let BIGNUM_OF_WORDLIST_LT_P256K1_CONDENSED = prove
 (`bignum_of_wordlist[n0;n1;n2;n3] < p_256k1 <=>
   bignum_of_wordlist[n0;word_and n1 (word_and n2 n3)] <
   340282366920938463463374607427473243183`,
  TRANS_TAC EQ_TRANS
   `bignum_of_wordlist[n0;word_and n1 (word_and n2 n3)] <
    bignum_of_wordlist[word 0xfffffffefffffc2f; word 0xffffffffffffffff]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_OF_WORDLIST_LT_P256K1] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_LT; LT_REFL; BIGNUM_OF_WORDLIST_SING] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GSYM DIMINDEX_64; SYM(NUM_REDUCE_CONV `2 EXP 64 - 1`)] THEN
    SIMP_TAC[VAL_BOUND; ARITH_RULE `x < e ==> (x < e - 1 <=> ~(x = e - 1))`;
             VAL_WORD_AND_EQ_MAX] THEN
    REWRITE_TAC[GSYM VAL_EQ; DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC TAUT;
    AP_TERM_TAC THEN REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)]);;

let BIGNUM_MOD_P256K1_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x3c) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p256k1_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = word (pc + 0x38) /\
                bignum_from_memory (z,4) s = n MOD p_256k1)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_MOD_P256K1_4_EXEC [7;8] (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s14" THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 4`;
    `if n < p_256k1 then &n else &n - &p_256k1:real`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT; GSYM COND_RAND] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MOD_CASES THEN
    UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN REWRITE_TAC[p_256k1] THEN
    ARITH_TAC] THEN

  SUBGOAL_THEN `~carry_s8 <=> n < p_256k1` SUBST_ALL_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_LT_P256K1_CONDENSED] THEN
    REWRITE_TAC[WORD_AND_ASSOC] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THENL
   [REAL_INTEGER_TAC; ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_P256K1_LE] THEN
  STRIP_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ASM_CASES_TAC `carry_s7:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
   [DISCH_THEN(CONJUNCTS_THEN2
     (fun th -> MP_TAC(end_itlist CONJ (DECARRY_RULE [th])))
     (fun th -> MP_TAC(end_itlist CONJ (DESUM_RULE [th])))) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p_256k1] THEN REAL_INTEGER_TAC;
    DISCH_THEN(MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES] o CONJUNCT2) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    UNDISCH_TAC `18446744069414583343 <= val(n_0:int64)` THEN
    MP_TAC(SPEC `sum_s7:int64` VAL_BOUND_64) THEN ARITH_TAC]);;

let BIGNUM_MOD_P256K1_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x3c) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p256k1_4_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD p_256k1)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_P256K1_4_EXEC
    BIGNUM_MOD_P256K1_4_CORRECT);;
