(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Doubling modulo p_25519, the field characteristic for curve25519.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_double_p25519.o";;
 ****)

let bignum_double_p25519_mc = define_assert_from_elf "bignum_double_p25519_mc" "arm/curve25519/bignum_double_p25519.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xab020042;       (* arm_ADDS X2 X2 X2 *)
  0xba030063;       (* arm_ADCS X3 X3 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0x9a0500a5;       (* arm_ADC X5 X5 X5 *)
  0xd2f00009;       (* arm_MOVZ X9 (word 32768) 48 *)
  0xb1004c46;       (* arm_ADDS X6 X2 (rvalue (word 19)) *)
  0xba1f0067;       (* arm_ADCS X7 X3 XZR *)
  0xba1f0088;       (* arm_ADCS X8 X4 XZR *)
  0xba0900a9;       (* arm_ADCS X9 X5 X9 *)
  0x9a863042;       (* arm_CSEL X2 X2 X6 Condition_CC *)
  0x9a873063;       (* arm_CSEL X3 X3 X7 Condition_CC *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DOUBLE_P25519_EXEC = ARM_MK_EXEC_RULE bignum_double_p25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let BIGNUM_DOUBLE_P25519_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x48) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p25519_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x44) /\
                  (n < p_25519
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_25519))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** Do the whole simulation as a single block ***)

  ARM_ACCSTEPS_TAC BIGNUM_DOUBLE_P25519_EXEC [2;3;5;6;8;9;10;11] (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Derive basic bound on the top words ***)

  SUBGOAL_THEN `n DIV 2 EXP 192 < 2 EXP 63` MP_TAC THENL
   [UNDISCH_TAC `n < p_25519` THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV)] THEN

  (*** Characterize the top carry ***)

  SUBGOAL_THEN `carry_s11 <=> p_25519 <= 2 * n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "n" THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
      MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Hence the overall result ***)

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[MULT_2] THEN DISCARD_STATE_TAC "s17" THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_ADD_CASES o rand o snd) THEN
  ASM_REWRITE_TAC[GSYM MULT_2] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  ABBREV_TAC `bb <=> p_25519 <= 2 * n` THEN
  EXPAND_TAC "n" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_25519] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `e * c + s:real = z ==> s = z - e * c`)) THEN
  ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
    MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_ARITH_TAC);;

let BIGNUM_DOUBLE_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x48) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p25519_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_25519
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_25519))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_DOUBLE_P25519_EXEC BIGNUM_DOUBLE_P25519_CORRECT);;
