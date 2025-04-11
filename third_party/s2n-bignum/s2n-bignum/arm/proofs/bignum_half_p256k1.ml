(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Halving modulo p_256k1, the field characteristic for secp256k1.           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_half_p256k1.o";;
 ****)

let bignum_half_p256k1_mc =
  define_assert_from_elf "bignum_half_p256k1_mc" "arm/secp256k1/bignum_half_p256k1.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd2807a26;       (* arm_MOV X6 (rvalue (word 977)) *)
  0xb26000c6;       (* arm_ORR X6 X6 (rvalue (word 4294967296)) *)
  0xf240005f;       (* arm_TST X2 (rvalue (word 1)) *)
  0x9a9f10c6;       (* arm_CSEL X6 X6 XZR Condition_NE *)
  0xeb060042;       (* arm_SUBS X2 X2 X6 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0x93c20462;       (* arm_EXTR X2 X3 X2 1 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0x93c30483;       (* arm_EXTR X3 X4 X3 1 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x93c404a4;       (* arm_EXTR X4 X5 X4 1 *)
  0xda1f00c6;       (* arm_SBC X6 X6 XZR *)
  0x93c504c5;       (* arm_EXTR X5 X6 X5 1 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_HALF_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_half_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_HALF_P256K1_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x48) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_half_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x44) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 2 * n) MOD p_256k1))
            (MAYCHANGE [PC; X2; X3; X4; X5; X6] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  ARM_STEPS_TAC BIGNUM_HALF_P256K1_EXEC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_1_BITVAL]) THEN
  SUBGOAL_THEN `bit 0 (n_0:int64) <=> ODD n` SUBST_ALL_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[BIT_LSB; ODD_ADD; ODD_MULT; ODD_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL; BITVAL_EQ_0; COND_SWAP]) THEN
    RULE_ASSUM_TAC(SIMP_RULE[BITVAL_CLAUSES])] THEN

  ARM_ACCSTEPS_TAC BIGNUM_HALF_P256K1_EXEC [7;8;10;12;14] (7--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(inverse_mod p_256k1 2 * n) MOD p_256k1 =
    (if ODD n then n + p_256k1 else n) DIV 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `n < p_256k1` THEN ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_DIV_COPRIME THEN
    REWRITE_TAC[COPRIME_2; DIVIDES_2; GSYM NOT_ODD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[p_256k1; ODD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
    REWRITE_TAC[COND_ID; NUMBER_RULE
     `(n + p:num == m) (mod p) <=> (n == m) (mod p)`] THEN
    MATCH_MP_TAC(NUMBER_RULE
       `(x * y == 1) (mod n) ==> (a == x * y * a) (mod n)`) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_2] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 4)` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[CONG_SYM]] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC
   `(bignum_of_wordlist [sum_s7; sum_s8; sum_s10; sum_s12; sum_s14])
    DIV 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[ARITH_RULE `2 * 2 EXP (64 * 4) = 2 EXP 257`] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    MATCH_MP_TAC(NUMBER_RULE
     `!d. n * d + b = a ==> (a == b) (mod n)`) THEN
    EXISTS_TAC `val(sum_s14:int64) DIV 2` THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[MATCH_MP VAL_WORD_SUBWORD_JOIN_64 (ARITH_RULE `1 <= 64`)] THEN
    ARITH_TAC]);;

let BIGNUM_HALF_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x58) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_half_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 2 * n) MOD p_256k1))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_HALF_P256K1_EXEC
    BIGNUM_HALF_P256K1_CORRECT);;
