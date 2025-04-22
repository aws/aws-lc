(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional negation modulo p_256k1, the field characteristic for secp256k1. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_optneg_p256k1.o";;
 ****)

let bignum_optneg_p256k1_mc = define_assert_from_elf "bignum_optneg_p256k1_mc" "arm/secp256k1/bignum_optneg_p256k1.o"
[
  0xa9401043;       (* arm_LDP X3 X4 X2 (Immediate_Offset (iword (&0))) *)
  0xaa040067;       (* arm_ORR X7 X3 X4 *)
  0xa9411845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&16))) *)
  0xaa0500e7;       (* arm_ORR X7 X7 X5 *)
  0xaa0600e7;       (* arm_ORR X7 X7 X6 *)
  0xeb1f003f;       (* arm_CMP X1 XZR *)
  0xda9f03e1;       (* arm_CSETM X1 Condition_NE *)
  0xeb1f00ff;       (* arm_CMP X7 XZR *)
  0x9a8103e1;       (* arm_CSEL X1 XZR X1 Condition_EQ *)
  0xd2807a07;       (* arm_MOV X7 (rvalue (word 976)) *)
  0xb26000e7;       (* arm_ORR X7 X7 (rvalue (word 4294967296)) *)
  0x8a0100e7;       (* arm_AND X7 X7 X1 *)
  0xca010063;       (* arm_EOR X3 X3 X1 *)
  0xeb070063;       (* arm_SUBS X3 X3 X7 *)
  0xca010084;       (* arm_EOR X4 X4 X1 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xca0100a5;       (* arm_EOR X5 X5 X1 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xca0100c6;       (* arm_EOR X6 X6 X1 *)
  0xda1f00c6;       (* arm_SBC X6 X6 XZR *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTNEG_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_optneg_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_OPTNEG_P256K1_CORRECT = time prove
 (`!z p x n pc.
        nonoverlapping (word pc,0x5c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x58) /\
                  (n < p_256k1
                  ==> (bignum_from_memory (z,4) s =
                       if ~(p = word 0) then (p_256k1 - n) MOD p_256k1
                       else n)))
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `p:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  ARM_STEPS_TAC BIGNUM_OPTNEG_P256K1_EXEC (1--9) THEN

  FIRST_X_ASSUM(MP_TAC o
    SPEC `word_neg(word(bitval(~(p:int64 = word 0 \/ n = 0)))):int64` o
    MATCH_MP (MESON[] `read X1 s = z ==> !a. z = a ==> read X1 s = a`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[WORD_SUB_0; ADD_EQ_0; VAL_EQ_0] THEN
    REWRITE_TAC[WORD_OR_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[VAL_EQ_0; CONJ_ACI] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[VAL_WORD_0; BITVAL_CLAUSES; WORD_NEG_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0] THEN
    CONV_TAC WORD_REDUCE_CONV;
    DISCH_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_OPTNEG_P256K1_EXEC [14;16;18;20] (10--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  SUBGOAL_THEN
   `(if ~(p:int64 = word 0) then (p_256k1 - n) MOD p_256k1 else n) =
    (if p = word 0 \/ n = 0 then n else p_256k1 - n)`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `p:int64 = word 0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `n < p_256k1` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < p /\ ~(n = 0) ==> p - n < p`] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s22" THEN
  ABBREV_TAC `P <=> p:int64 = word 0 \/ n = 0` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `n < p_256k1` THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; p_256k1] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_OR_MASK; BITVAL_CLAUSES; p_256k1] THEN
  REWRITE_TAC[WORD_NEG_0; WORD_XOR_0; WORD_AND_0] THEN
  REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_OPTNEG_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z p x n pc returnaddress.
        nonoverlapping (word pc,0x5c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_256k1
                   ==> (bignum_from_memory (z,4) s =
                        if ~(p = word 0) then (p_256k1 - n) MOD p_256k1
                        else n)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTNEG_P256K1_EXEC
    BIGNUM_OPTNEG_P256K1_CORRECT);;
