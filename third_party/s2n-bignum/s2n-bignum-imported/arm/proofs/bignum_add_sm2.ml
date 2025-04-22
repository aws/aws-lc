(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition modulo p_sm2, the field characteristic for the CC SM2 curve.     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_add_sm2.o";;
 ****)

let bignum_add_sm2_mc = define_assert_from_elf "bignum_add_sm2_mc" "arm/sm2/bignum_add_sm2.o"
[
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xab080084;       (* arm_ADDS X4 X4 X8 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xa9411c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xb1000488;       (* arm_ADDS X8 X4 (rvalue (word 1)) *)
  0xb2607fe9;       (* arm_MOV X9 (rvalue (word 18446744069414584320)) *)
  0xfa0900a9;       (* arm_SBCS X9 X5 X9 *)
  0xba1f00ca;       (* arm_ADCS X10 X6 XZR *)
  0x92c0002b;       (* arm_MOVN X11 (word 1) 32 *)
  0xfa0b00eb;       (* arm_SBCS X11 X7 X11 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0x9a8a30c6;       (* arm_CSEL X6 X6 X10 Condition_CC *)
  0x9a8b30e7;       (* arm_CSEL X7 X7 X11 Condition_CC *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_ADD_SM2_EXEC = ARM_MK_EXEC_RULE bignum_add_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let BIGNUM_ADD_SM2_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x5c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x58) /\
                  (m < p_sm2 /\ n < p_sm2
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_sm2))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_ADD_SM2_EXEC
   [3;4;7;8;10;12;13;15;16] (1--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s22" THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
   [`64 * 4`;
    `if m + n < p_sm2 then &(m + n) else &(m + n) - &p_sm2:real`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `carry_s16 <=> (m + n) < p_sm2` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_sm2;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(BINOP_CONV(BINOP_CONV REAL_POLY_CONV)) THEN BOUNDER_TAC[];
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

let BIGNUM_ADD_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x5c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_sm2 /\ n < p_sm2
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_sm2))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_SM2_EXEC BIGNUM_ADD_SM2_CORRECT);;
