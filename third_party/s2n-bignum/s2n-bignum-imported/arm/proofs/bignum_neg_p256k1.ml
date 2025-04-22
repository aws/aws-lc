(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negation modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_neg_p256k1.o";;
 ****)

let bignum_neg_p256k1_mc = define_assert_from_elf "bignum_neg_p256k1_mc" "arm/secp256k1/bignum_neg_p256k1.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xaa040067;       (* arm_ORR X7 X3 X4 *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xaa0500e7;       (* arm_ORR X7 X7 X5 *)
  0xaa0600e7;       (* arm_ORR X7 X7 X6 *)
  0xeb1f00ff;       (* arm_CMP X7 XZR *)
  0xda9f03e2;       (* arm_CSETM X2 Condition_NE *)
  0xd2807a07;       (* arm_MOV X7 (rvalue (word 976)) *)
  0xb26000e7;       (* arm_ORR X7 X7 (rvalue (word 4294967296)) *)
  0x8a270047;       (* arm_BIC X7 X2 X7 *)
  0xeb0300e3;       (* arm_SUBS X3 X7 X3 *)
  0xfa040044;       (* arm_SBCS X4 X2 X4 *)
  0xfa050045;       (* arm_SBCS X5 X2 X5 *)
  0xda060046;       (* arm_SBC X6 X2 X6 *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NEG_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_neg_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_NEG_P256K1_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x44) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x40) /\
                  (n <= p_256k1
                   ==> bignum_from_memory (z,4) s = (p_256k1 - n) MOD p_256k1))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_NEG_P256K1_EXEC (11--14) (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s16" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `n <= p_256k1` THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; p_256k1] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `(p_256k1 - n) MOD p_256k1 = if n = 0 then 0 else p_256k1 - n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[COND_RAND]] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN

  REWRITE_TAC[WORD_UNMASK_64; WORD_SUB_0; VAL_EQ_0] THEN
  REWRITE_TAC[WORD_AND_MASK; COND_SWAP; WORD_OR_EQ_0; VAL_EQ_0] THEN
  REWRITE_TAC[CONJ_ACI] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[p_256k1; GSYM REAL_OF_NUM_CLAUSES; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_NEG_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x44) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n <= p_256k1
                   ==> bignum_from_memory (z,4) s = (p_256k1 - n) MOD p_256k1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NEG_P256K1_EXEC
      BIGNUM_NEG_P256K1_CORRECT);;
