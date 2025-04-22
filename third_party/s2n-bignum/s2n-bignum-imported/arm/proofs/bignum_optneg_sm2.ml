(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional negation mod p_sm2, field characteristic for CC SM2 curve.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_optneg_sm2.o";;
 ****)

let bignum_optneg_sm2_mc = define_assert_from_elf "bignum_optneg_sm2_mc" "arm/sm2/bignum_optneg_sm2.o"
[
  0xa9401043;       (* arm_LDP X3 X4 X2 (Immediate_Offset (iword (&0))) *)
  0xa9411845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&16))) *)
  0xaa040067;       (* arm_ORR X7 X3 X4 *)
  0xaa0600a8;       (* arm_ORR X8 X5 X6 *)
  0xaa0800e9;       (* arm_ORR X9 X7 X8 *)
  0xf100013f;       (* arm_CMP X9 (rvalue (word 0)) *)
  0x9a8103e1;       (* arm_CSEL X1 XZR X1 Condition_EQ *)
  0x92800009;       (* arm_MOVN X9 (word 0) 0 *)
  0xb2607fe8;       (* arm_MOV X8 (rvalue (word 18446744069414584320)) *)
  0x92c0002a;       (* arm_MOVN X10 (word 1) 32 *)
  0xeb030127;       (* arm_SUBS X7 X9 X3 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0xfa050129;       (* arm_SBCS X9 X9 X5 *)
  0xda06014a;       (* arm_SBC X10 X10 X6 *)
  0xf100003f;       (* arm_CMP X1 (rvalue (word 0)) *)
  0x9a8310e7;       (* arm_CSEL X7 X7 X3 Condition_NE *)
  0x9a841108;       (* arm_CSEL X8 X8 X4 Condition_NE *)
  0x9a851129;       (* arm_CSEL X9 X9 X5 Condition_NE *)
  0x9a86114a;       (* arm_CSEL X10 X10 X6 Condition_NE *)
  0xa9002007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTNEG_SM2_EXEC = ARM_MK_EXEC_RULE bignum_optneg_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let BIGNUM_OPTNEG_SM2_CORRECT = time prove
 (`!z p x n pc.
        nonoverlapping (word pc,0x58) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x54) /\
                  (n < p_sm2
                  ==> (bignum_from_memory (z,4) s =
                       if ~(p = word 0) then (p_sm2 - n) MOD p_sm2 else n)))
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7; X8; X9; X10] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `p:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_OPTNEG_SM2_EXEC (11--14) (1--15) THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `p:int64 = word 0 \/ n = 0` o
    MATCH_MP (MESON[] `read ZF s = z ==> !a. z = a ==> read ZF s = a`)) THEN
  ANTS_TAC THENL
   [ASM_CASES_TAC `p:int64 = word 0` THEN
    ASM_REWRITE_TAC[COND_ID; WORD_SUB_0; VAL_WORD_0] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_OR_EQ_0] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[ADD_EQ_0; MULT_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; VAL_EQ_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ARM_STEPS_TAC BIGNUM_OPTNEG_SM2_EXEC (16--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s21" THEN
  ASM_CASES_TAC `p:int64 = word 0` THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(p_sm2 - n) MOD p_sm2 = p_sm2 - n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `~(n = 0)` THEN
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `n < p_sm2` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[p_sm2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_OPTNEG_SM2_SUBROUTINE_CORRECT = time prove
 (`!z p x n pc returnaddress.
        nonoverlapping (word pc,0x58) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_sm2
                   ==> (bignum_from_memory (z,4) s =
                        if ~(p = word 0) then (p_sm2 - n) MOD p_sm2 else n)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTNEG_SM2_EXEC
    BIGNUM_OPTNEG_SM2_CORRECT);;
