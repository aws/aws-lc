(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Doubling modulo p_384, the field characteristic for the NIST P-384 curve. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_double_p384.o";;
 ****)

let bignum_double_p384_mc = define_assert_from_elf "bignum_double_p384_mc" "arm/p384/bignum_double_p384.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xab020042;       (* arm_ADDS X2 X2 X2 *)
  0xba030063;       (* arm_ADCS X3 X3 X3 *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0600c6;       (* arm_ADCS X6 X6 X6 *)
  0xba0700e7;       (* arm_ADCS X7 X7 X7 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0xeb090049;       (* arm_SUBS X9 X2 X9 *)
  0xb2607fea;       (* arm_MOV X10 (rvalue (word 18446744069414584320)) *)
  0xfa0a006a;       (* arm_SBCS X10 X3 X10 *)
  0x9280002b;       (* arm_MOVN X11 (word 1) 0 *)
  0xfa0b008b;       (* arm_SBCS X11 X4 X11 *)
  0xba1f00ac;       (* arm_ADCS X12 X5 XZR *)
  0xba1f00cd;       (* arm_ADCS X13 X6 XZR *)
  0xba1f00ee;       (* arm_ADCS X14 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0x9a893042;       (* arm_CSEL X2 X2 X9 Condition_CC *)
  0x9a8a3063;       (* arm_CSEL X3 X3 X10 Condition_CC *)
  0x9a8b3084;       (* arm_CSEL X4 X4 X11 Condition_CC *)
  0x9a8c30a5;       (* arm_CSEL X5 X5 X12 Condition_CC *)
  0x9a8d30c6;       (* arm_CSEL X6 X6 X13 Condition_CC *)
  0x9a8e30e7;       (* arm_CSEL X7 X7 X14 Condition_CC *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DOUBLE_P384_EXEC = ARM_MK_EXEC_RULE bignum_double_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_DOUBLE_P384_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x78) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = word (pc + 0x74) /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s = (2 * n) MOD p_384))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_DOUBLE_P384_EXEC (1--29) (1--29) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ADD_CLAUSES; VAL_WORD_BITVAL; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  SUBGOAL_THEN
   `carry_s20 <=> 2 * n < p_384`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `448` THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s29" THEN
  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `n < p ==> 2 * n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `n < p_384` THEN
    REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ]
   `a + b:num = n ==> &n = &a + &b`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_DOUBLE_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x78) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s = (2 * n) MOD p_384))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_DOUBLE_P384_EXEC BIGNUM_DOUBLE_P384_CORRECT);;
