(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_384, the order of the NIST curve P-384                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_mod_n384_6.o";;
 ****)

let bignum_mod_n384_6_mc =
  define_assert_from_elf "bignum_mod_n384_6_mc" "arm/p384/bignum_mod_n384_6.o"
[
  0xd2852e62;       (* arm_MOV X2 (rvalue (word 10611)) *)
  0xf2b998a2;       (* arm_MOVK X2 (word 52421) 16 *)
  0xf2c32d42;       (* arm_MOVK X2 (word 6506) 32 *)
  0xf2fd9d82;       (* arm_MOVK X2 (word 60652) 48 *)
  0xd294ef43;       (* arm_MOV X3 (rvalue (word 42874)) *)
  0xf2a91603;       (* arm_MOVK X3 (word 18608) 16 *)
  0xf2c1b643;       (* arm_MOVK X3 (word 3506) 32 *)
  0xf2eb0343;       (* arm_MOVK X3 (word 22554) 48 *)
  0xd285bbe4;       (* arm_MOV X4 (rvalue (word 11743)) *)
  0xf2be86e4;       (* arm_MOVK X4 (word 62519) 16 *)
  0xf2c9b024;       (* arm_MOVK X4 (word 19841) 32 *)
  0xf2f8ec64;       (* arm_MOVK X4 (word 51043) 48 *)
  0xa9402428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&16))) *)
  0xa942342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&32))) *)
  0xeb020102;       (* arm_SUBS X2 X8 X2 *)
  0xfa030123;       (* arm_SBCS X3 X9 X3 *)
  0xfa040144;       (* arm_SBCS X4 X10 X4 *)
  0xba1f0165;       (* arm_ADCS X5 X11 XZR *)
  0xba1f0186;       (* arm_ADCS X6 X12 XZR *)
  0xba1f01a7;       (* arm_ADCS X7 X13 XZR *)
  0x9a823102;       (* arm_CSEL X2 X8 X2 Condition_CC *)
  0x9a833123;       (* arm_CSEL X3 X9 X3 Condition_CC *)
  0x9a843144;       (* arm_CSEL X4 X10 X4 Condition_CC *)
  0x9a853165;       (* arm_CSEL X5 X11 X5 Condition_CC *)
  0x9a863186;       (* arm_CSEL X6 X12 X6 Condition_CC *)
  0x9a8731a7;       (* arm_CSEL X7 X13 X7 Condition_CC *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_N384_6_EXEC = ARM_MK_EXEC_RULE bignum_mod_n384_6_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_384 = new_definition `n_384 = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643`;;

let BIGNUM_MOD_N384_6_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x7c) (z,8 * 6)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n384_6_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = n)
           (\s. read PC s = word (pc + 0x78) /\
                bignum_from_memory (z,6) s = n MOD n_384)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  BIGNUM_TERMRANGE_TAC `6` `m:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N384_6_EXEC (1--30) (1--30) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN `carry_s21 <=> n_384 <= m` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[n_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[NOT_LE] THEN DISCARD_STATE_TAC "s30" THEN

  W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[n_384] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_SUB] THEN
  EXPAND_TAC "m" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x:real < y ==> x - &n < y`) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_BITVAL_NOT; n_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_N384_6_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x7c) (z,8 * 6)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n384_6_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,6) s = n MOD n_384)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_MOD_N384_6_EXEC BIGNUM_MOD_N384_6_CORRECT);;
