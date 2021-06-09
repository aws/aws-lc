(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Addition modulo p_256, the field characteristic for the NIST P-256 curve. *)
(* ========================================================================= *)

(**** print_literal_from_elf "Arm/p256/bignum_add_p256.o";;
 ****)

let bignum_add_p256_mc = define_assert_from_elf "bignum_add_p256_mc" "Arm/p256/bignum_add_p256.o"
[
  0xa9401825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&16))) *)
  0xa9410c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0x92800004;       (* arm_MOVN X4 (word 0) 0 *)
  0xeb0400bf;       (* arm_CMP X5 X4 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0xfa0400df;       (* arm_SBCS XZR X6 X4 *)
  0xfa1f00ff;       (* arm_SBCS XZR X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0xfa04011f;       (* arm_SBCS XZR X8 X4 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xfa0400c6;       (* arm_SBCS X6 X6 X4 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xda040108;       (* arm_SBC X8 X8 X4 *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_ADD_P256_EXEC = ARM_MK_EXEC_RULE bignum_add_p256_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let BIGNUM_ADD_P256_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x74) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x70) /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P256_EXEC (1--9) (1--9) THEN

  SUBGOAL_THEN
   `2 EXP 256 * bitval carry_s8 +
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8] =
    m + n`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P256_EXEC (10--16) (10--16) THEN

  SUBGOAL_THEN
   `carry_s16 <=>
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8] < p_256`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_256;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(BINOP_CONV(BINOP_CONV REAL_POLY_CONV)) THEN BOUNDER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_STEPS_TAC BIGNUM_ADD_P256_EXEC [17;18] THEN

  FIRST_X_ASSUM(MP_TAC o
    SPEC `word_neg(word(bitval(p_256 <= m + n))):int64` o
    MATCH_MP (MESON[] `read X3 s = z ==> !a. z = a ==> read X3 s = a`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; ADD_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[BITVAL_BOUND; MOD_LT; ADD_EQ_0; BITVAL_EQ_0;
             ARITH_RULE `a <= 1 /\ b <= 1 ==> a + b <  2 EXP 64`] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 5 RAND_CONV) [SYM th]) THEN
    BOOL_CASES_TAC `carry_s8:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; COND_SWAP; MULT_CLAUSES;
                ADD_CLAUSES; WORD_MASK] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P256_EXEC (19--28) (19--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s28" THEN

  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[p_256] THEN REAL_ARITH_TAC;
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
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_ADD_P256_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x74) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_P256_EXEC BIGNUM_ADD_P256_CORRECT);;
