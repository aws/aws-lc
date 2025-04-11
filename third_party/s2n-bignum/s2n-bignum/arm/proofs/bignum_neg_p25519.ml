(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negation modulo p_25519, the field characteristic for curve25519.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_neg_p25519.o";;
 ****)

let bignum_neg_p25519_mc = define_assert_from_elf "bignum_neg_p25519_mc" "arm/curve25519/bignum_neg_p25519.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x92800247;       (* arm_MOVN X7 (word 18) 0 *)
  0xaa030046;       (* arm_ORR X6 X2 X3 *)
  0xeb0200e2;       (* arm_SUBS X2 X7 X2 *)
  0x92800007;       (* arm_MOVN X7 (word 0) 0 *)
  0xfa0300e3;       (* arm_SBCS X3 X7 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xaa0400c6;       (* arm_ORR X6 X6 X4 *)
  0xfa0400e4;       (* arm_SBCS X4 X7 X4 *)
  0x92f00007;       (* arm_MOVN X7 (word 32768) 48 *)
  0xaa0500c6;       (* arm_ORR X6 X6 X5 *)
  0xda0500e5;       (* arm_SBC X5 X7 X5 *)
  0xeb1f00df;       (* arm_CMP X6 XZR *)
  0x9a9f1042;       (* arm_CSEL X2 X2 XZR Condition_NE *)
  0x9a9f1063;       (* arm_CSEL X3 X3 XZR Condition_NE *)
  0x9a9f1084;       (* arm_CSEL X4 X4 XZR Condition_NE *)
  0x9a9f10a5;       (* arm_CSEL X5 X5 XZR Condition_NE *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NEG_P25519_EXEC = ARM_MK_EXEC_RULE bignum_neg_p25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let BIGNUM_NEG_P25519_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x50) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p25519_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x4c) /\
                  (n <= p_25519
                   ==> bignum_from_memory (z,4) s = (p_25519 - n) MOD p_25519))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_NEG_P25519_EXEC [4;6;9;12] (1--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s19" THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if n = 0 then &0:real else &p_25519 - &n`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_OR_EQ_0] THEN
  REWRITE_TAC[COND_SWAP; CONJ_ACI; bignum_of_wordlist] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; p_25519] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[INTEGER_CLOSED; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_NEG_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x50) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p25519_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n <= p_25519
                   ==> bignum_from_memory (z,4) s = (p_25519 - n) MOD p_25519))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NEG_P25519_EXEC
      BIGNUM_NEG_P25519_CORRECT);;
