(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition modulo p_384, the field characteristic for the NIST P-384 curve. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_add_p384.o";;
 ****)

let bignum_add_p384_mc = define_assert_from_elf "bignum_add_p384_mc" "arm/p384/bignum_add_p384.o"
[
  0xa9401825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&16))) *)
  0xa9410c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422829;       (* arm_LDP X9 X10 X1 (Immediate_Offset (iword (&32))) *)
  0xa9420c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0xeb0400bf;       (* arm_CMP X5 X4 *)
  0xb2607fe4;       (* arm_MOV X4 (rvalue (word 18446744069414584320)) *)
  0xfa0400df;       (* arm_SBCS XZR X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0xfa0400ff;       (* arm_SBCS XZR X7 X4 *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0xba1f015f;       (* arm_ADCS XZR X10 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xfa0400c6;       (* arm_SBCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xda03014a;       (* arm_SBC X10 X10 X3 *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_ADD_P384_EXEC = ARM_MK_EXEC_RULE bignum_add_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_ADD_P384_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x9c) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = m /\
                  bignum_from_memory (y,6) s = n)
             (\s. read PC s = word (pc + 0x98) /\
                  (m < p_384 /\ n < p_384
                   ==> bignum_from_memory (z,6) s = (m + n) MOD p_384))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 6)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 6)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P384_EXEC (1--13) (1--13) THEN

  SUBGOAL_THEN
   `2 EXP 384 * bitval carry_s12 +
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8; sum_s11; sum_s12] =
    m + n`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P384_EXEC (14--22) (14--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN

  SUBGOAL_THEN
   `carry_s22 <=>
    p_384 <=
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8; sum_s11; sum_s12]`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_384;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_STEPS_TAC BIGNUM_ADD_P384_EXEC [23;24] THEN

  FIRST_X_ASSUM(MP_TAC o
    SPEC `word_neg(word(bitval(p_384 <= m + n))):int64` o
    MATCH_MP (MESON[] `read X3 s = z ==> !a. z = a ==> read X3 s = a`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; ADD_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[BITVAL_BOUND; MOD_LT; ADD_EQ_0; BITVAL_EQ_0;
             ARITH_RULE `a <= 1 /\ b <= 1 ==> a + b <  2 EXP 64`] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 5 RAND_CONV) [SYM th]) THEN
    BOOL_CASES_TAC `carry_s12:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; COND_SWAP; MULT_CLAUSES;
                ADD_CLAUSES; WORD_MASK] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P384_EXEC (25--38) (25--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s38" THEN

  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_384`; `n < p_384`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[p_384] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ]
   `a:num = m + n ==> &m + &n = &a`)) THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_ADD_P384_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x9c) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = m /\
                  bignum_from_memory (y,6) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_384 /\ n < p_384
                   ==> bignum_from_memory (z,6) s = (m + n) MOD p_384))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_P384_EXEC BIGNUM_ADD_P384_CORRECT);;
