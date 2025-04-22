(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_256k1, the order of the secp256k1 curve.               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_mod_n256k1_4.o";;
 ****)

let bignum_mod_n256k1_4_mc = define_assert_from_elf "bignum_mod_n256k1_4_mc" "arm/secp256k1/bignum_mod_n256k1_4.o"
[
  0xd2882822;       (* arm_MOV X2 (rvalue (word 16705)) *)
  0xf2ba06c2;       (* arm_MOVK X2 (word 53302) 16 *)
  0xf2cbd182;       (* arm_MOVK X2 (word 24204) 32 *)
  0xf2f7fa42;       (* arm_MOVK X2 (word 49106) 48 *)
  0xd2940763;       (* arm_MOV X3 (rvalue (word 41019)) *)
  0xf2b5e903;       (* arm_MOVK X3 (word 44872) 16 *)
  0xf2db9cc3;       (* arm_MOVK X3 (word 56550) 32 *)
  0xf2f755c3;       (* arm_MOVK X3 (word 47790) 48 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xeb0200c2;       (* arm_SUBS X2 X6 X2 *)
  0xfa0300e3;       (* arm_SBCS X3 X7 X3 *)
  0xfa040104;       (* arm_SBCS X4 X8 X4 *)
  0xba1f0125;       (* arm_ADCS X5 X9 XZR *)
  0x9a8230c2;       (* arm_CSEL X2 X6 X2 Condition_CC *)
  0x9a8330e3;       (* arm_CSEL X3 X7 X3 Condition_CC *)
  0x9a843104;       (* arm_CSEL X4 X8 X4 Condition_CC *)
  0x9a853125;       (* arm_CSEL X5 X9 X5 Condition_CC *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_N256K1_4_EXEC = ARM_MK_EXEC_RULE bignum_mod_n256k1_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_256k1 = define `n_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`;;

let BIGNUM_MOD_N256K1_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x58) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n256k1_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = word (pc + 0x54) /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  BIGNUM_TERMRANGE_TAC `4` `m:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N256K1_4_EXEC (1--21) (1--21) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN `~carry_s15 <=> m < n_256k1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[n_256k1; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s21" THEN

  W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[n_256k1] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_SUB] THEN
  EXPAND_TAC "m" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x:real < y ==> x - &n < y`) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_BITVAL_NOT; n_256k1] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_N256K1_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x58) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n256k1_4_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_N256K1_4_EXEC
    BIGNUM_MOD_N256K1_4_CORRECT);;
