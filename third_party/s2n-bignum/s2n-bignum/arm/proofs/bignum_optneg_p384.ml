(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional negation mod p_384, field characteristic for NIST P-384 curve.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_optneg_p384.o";;
 ****)

let bignum_optneg_p384_mc = define_assert_from_elf "bignum_optneg_p384_mc" "arm/p384/bignum_optneg_p384.o"
[
  0xa9401043;       (* arm_LDP X3 X4 X2 (Immediate_Offset (iword (&0))) *)
  0xa9411845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&16))) *)
  0xa9422047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&32))) *)
  0xaa040069;       (* arm_ORR X9 X3 X4 *)
  0xaa0600aa;       (* arm_ORR X10 X5 X6 *)
  0xaa0800eb;       (* arm_ORR X11 X7 X8 *)
  0xaa0a012c;       (* arm_ORR X12 X9 X10 *)
  0xaa0c016d;       (* arm_ORR X13 X11 X12 *)
  0xf10001bf;       (* arm_CMP X13 (rvalue (word 0)) *)
  0x9a8103e1;       (* arm_CSEL X1 XZR X1 Condition_EQ *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0xb2607fea;       (* arm_MOV X10 (rvalue (word 18446744069414584320)) *)
  0x9280002b;       (* arm_MOVN X11 (word 1) 0 *)
  0x9280000e;       (* arm_MOVN X14 (word 0) 0 *)
  0xeb030129;       (* arm_SUBS X9 X9 X3 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xfa05016b;       (* arm_SBCS X11 X11 X5 *)
  0xfa0601cc;       (* arm_SBCS X12 X14 X6 *)
  0xfa0701cd;       (* arm_SBCS X13 X14 X7 *)
  0xfa0801ce;       (* arm_SBCS X14 X14 X8 *)
  0xf100003f;       (* arm_CMP X1 (rvalue (word 0)) *)
  0x9a831129;       (* arm_CSEL X9 X9 X3 Condition_NE *)
  0x9a84114a;       (* arm_CSEL X10 X10 X4 Condition_NE *)
  0x9a85116b;       (* arm_CSEL X11 X11 X5 Condition_NE *)
  0x9a86118c;       (* arm_CSEL X12 X12 X6 Condition_NE *)
  0x9a8711ad;       (* arm_CSEL X13 X13 X7 Condition_NE *)
  0x9a8811ce;       (* arm_CSEL X14 X14 X8 Condition_NE *)
  0xa9002809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&0))) *)
  0xa901300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&16))) *)
  0xa902380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTNEG_P384_EXEC = ARM_MK_EXEC_RULE bignum_optneg_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_OPTNEG_P384_CORRECT = time prove
 (`!z p x n pc.
        nonoverlapping (word pc,0x7c) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = word (pc + 0x78) /\
                  (n < p_384
                   ==> (bignum_from_memory (z,6) s =
                        if ~(p = word 0) then (p_384 - n) MOD p_384 else n)))
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `p:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_OPTNEG_P384_EXEC (15--20) (1--21) THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `p:int64 = word 0 \/ n = 0` o
    MATCH_MP (MESON[] `read ZF s = z ==> !a. z = a ==> read ZF s = a`)) THEN
  ANTS_TAC THENL
   [ASM_CASES_TAC `p:int64 = word 0` THEN
    ASM_REWRITE_TAC[COND_ID; WORD_SUB_0; VAL_WORD_0] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_OR_EQ_0] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[ADD_EQ_0; MULT_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONJ_ACI; VAL_EQ_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ARM_STEPS_TAC BIGNUM_OPTNEG_P384_EXEC (22--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s30" THEN
  ASM_CASES_TAC `p:int64 = word 0` THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(p_384 - n) MOD p_384 = p_384 - n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `~(n = 0)` THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `n < p_384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[p_384] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[p_384; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_OPTNEG_P384_SUBROUTINE_CORRECT = time prove
 (`!z p x n pc returnaddress.
        nonoverlapping (word pc,0x7c) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optneg_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; p; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_384
                   ==> (bignum_from_memory (z,6) s =
                        if ~(p = word 0) then (p_384 - n) MOD p_384 else n)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTNEG_P384_EXEC
    BIGNUM_OPTNEG_P384_CORRECT);;
