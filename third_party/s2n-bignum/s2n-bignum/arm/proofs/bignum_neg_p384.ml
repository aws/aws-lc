(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negation mod p_384, field characteristic for NIST P-384 curve.            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_neg_p384.o";;
 ****)

let bignum_neg_p384_mc = define_assert_from_elf "bignum_neg_p384_mc" "arm/p384/bignum_neg_p384.o"
[
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xa9422428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&32))) *)
  0xaa050082;       (* arm_ORR X2 X4 X5 *)
  0xaa0700c3;       (* arm_ORR X3 X6 X7 *)
  0xaa030042;       (* arm_ORR X2 X2 X3 *)
  0xaa090103;       (* arm_ORR X3 X8 X9 *)
  0xaa030042;       (* arm_ORR X2 X2 X3 *)
  0xf100005f;       (* arm_CMP X2 (rvalue (word 0)) *)
  0xda9f03e2;       (* arm_CSETM X2 Condition_NE *)
  0x92407c43;       (* arm_AND X3 X2 (rvalue (word 4294967295)) *)
  0xeb040064;       (* arm_SUBS X4 X3 X4 *)
  0x92607c43;       (* arm_AND X3 X2 (rvalue (word 18446744069414584320)) *)
  0xfa050065;       (* arm_SBCS X5 X3 X5 *)
  0x927ff843;       (* arm_AND X3 X2 (rvalue (word 18446744073709551614)) *)
  0xfa060066;       (* arm_SBCS X6 X3 X6 *)
  0xfa070047;       (* arm_SBCS X7 X2 X7 *)
  0xfa080048;       (* arm_SBCS X8 X2 X8 *)
  0xda090049;       (* arm_SBC X9 X2 X9 *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NEG_P384_EXEC = ARM_MK_EXEC_RULE bignum_neg_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_NEG_P384_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x5c) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = word (pc + 0x58) /\
                  (n <= p_384
                   ==> bignum_from_memory (z,6) s = (p_384 - n) MOD p_384))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_NEG_P384_EXEC [12;14;16;17;18;19] (1--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s22" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `n <= p_384` THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `(p_384 - n) MOD p_384 = if n = 0 then 0 else p_384 - n`
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
  ASM_REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_NEG_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x5c) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_neg_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = returnaddress /\
                  (n <= p_384
                   ==> bignum_from_memory (z,6) s = (p_384 - n) MOD p_384))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NEG_P384_EXEC
      BIGNUM_NEG_P384_CORRECT);;
