(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Halving modulo p_384, the field characteristic for the NIST P-384 curve.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_half_p384.o";;
 ****)

let bignum_half_p384_mc = define_assert_from_elf "bignum_half_p384_mc" "arm/p384/bignum_half_p384.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9240004a;       (* arm_AND X10 X2 (rvalue (word 1)) *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x92407d4b;       (* arm_AND X11 X10 (rvalue (word 4294967295)) *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x92607d4b;       (* arm_AND X11 X10 (rvalue (word 18446744069414584320)) *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x927ff94b;       (* arm_AND X11 X10 (rvalue (word 18446744073709551614)) *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0x93c20462;       (* arm_EXTR X2 X3 X2 1 *)
  0x93c30483;       (* arm_EXTR X3 X4 X3 1 *)
  0x93c404a4;       (* arm_EXTR X4 X5 X4 1 *)
  0x93c504c5;       (* arm_EXTR X5 X6 X5 1 *)
  0x93c604e6;       (* arm_EXTR X6 X7 X6 1 *)
  0x93c70507;       (* arm_EXTR X7 X8 X7 1 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_HALF_P384_EXEC = ARM_MK_EXEC_RULE bignum_half_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_HALF_P384_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x64) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_half_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = word (pc + 0x60) /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 2 * n) MOD p_384))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  ARM_STEPS_TAC BIGNUM_HALF_P384_EXEC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_LZERO; WORD_AND_1_BITVAL]) THEN
  SUBGOAL_THEN `bit 0 (n_0:int64) <=> ODD n` SUBST_ALL_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[BIT_LSB; ODD_ADD; ODD_MULT; ODD_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_HALF_P384_EXEC (7--14) (7--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  SUBGOAL_THEN
   `(inverse_mod p_384 2 * n) MOD p_384 =
    (if ODD n then n + p_384 else n) DIV 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `n < p_384` THEN ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_DIV_COPRIME THEN
    REWRITE_TAC[COPRIME_2; DIVIDES_2; GSYM NOT_ODD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[p_384; ODD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
    REWRITE_TAC[COND_ID; NUMBER_RULE
     `(n + p:num == m) (mod p) <=> (n == m) (mod p)`] THEN
    MATCH_MP_TAC(NUMBER_RULE
       `(x * y == 1) (mod n) ==> (a == x * y * a) (mod n)`) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_2] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 384 * bitval(carry_s14) +
    bignum_of_wordlist [sum_s7; sum_s9; sum_s11; sum_s12; sum_s13; sum_s14] =
    if ODD n then n + p_384 else n`
  (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s24" THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
  REWRITE_TAC[MATCH_MP VAL_WORD_SUBWORD_JOIN_64 (ARITH_RULE `1 <= 64`)] THEN
  SIMP_TAC[VAL_WORD_BITVAL; ADD_CLAUSES; bignum_of_wordlist; MULT_CLAUSES;
           BITVAL_BOUND_ALT; MOD_LT; EXP_1] THEN
  ARITH_TAC);;

let BIGNUM_HALF_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x64) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_half_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 2 * n) MOD p_384))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_HALF_P384_EXEC
    BIGNUM_HALF_P384_CORRECT);;
