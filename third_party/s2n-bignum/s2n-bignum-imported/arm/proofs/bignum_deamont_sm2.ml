(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_sm2.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_deamont_sm2.o";;
 ****)

let bignum_deamont_sm2_mc =
  define_assert_from_elf "bignum_deamont_sm2_mc" "arm/sm2/bignum_deamont_sm2.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd3607c47;       (* arm_LSL X7 X2 32 *)
  0xd360fc46;       (* arm_LSR X6 X2 32 *)
  0xeb0200e9;       (* arm_SUBS X9 X7 X2 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa080084;       (* arm_SBCS X4 X4 X8 *)
  0xfa0700a5;       (* arm_SBCS X5 X5 X7 *)
  0xda060042;       (* arm_SBC X2 X2 X6 *)
  0xd3607c67;       (* arm_LSL X7 X3 32 *)
  0xd360fc66;       (* arm_LSR X6 X3 32 *)
  0xeb0300e9;       (* arm_SUBS X9 X7 X3 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xfa0800a5;       (* arm_SBCS X5 X5 X8 *)
  0xfa070042;       (* arm_SBCS X2 X2 X7 *)
  0xda060063;       (* arm_SBC X3 X3 X6 *)
  0xd3607c87;       (* arm_LSL X7 X4 32 *)
  0xd360fc86;       (* arm_LSR X6 X4 32 *)
  0xeb0400e9;       (* arm_SUBS X9 X7 X4 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb0900a5;       (* arm_SUBS X5 X5 X9 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xda060084;       (* arm_SBC X4 X4 X6 *)
  0xd3607ca7;       (* arm_LSL X7 X5 32 *)
  0xd360fca6;       (* arm_LSR X6 X5 32 *)
  0xeb0500e9;       (* arm_SUBS X9 X7 X5 *)
  0xda1f00c8;       (* arm_SBC X8 X6 XZR *)
  0xeb090042;       (* arm_SUBS X2 X2 X9 *)
  0xfa080063;       (* arm_SBCS X3 X3 X8 *)
  0xfa070084;       (* arm_SBCS X4 X4 X7 *)
  0xda0600a5;       (* arm_SBC X5 X5 X6 *)
  0xb1000446;       (* arm_ADDS X6 X2 (rvalue (word 1)) *)
  0xb2607fe7;       (* arm_MOV X7 (rvalue (word 18446744069414584320)) *)
  0xfa070067;       (* arm_SBCS X7 X3 X7 *)
  0xba1f0088;       (* arm_ADCS X8 X4 XZR *)
  0x92c00029;       (* arm_MOVN X9 (word 1) 32 *)
  0xfa0900a9;       (* arm_SBCS X9 X5 X9 *)
  0x9a863042;       (* arm_CSEL X2 X2 X6 Condition_CC *)
  0x9a873063;       (* arm_CSEL X3 X3 X7 Condition_CC *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEAMONT_SM2_EXEC = ARM_MK_EXEC_RULE bignum_deamont_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let BIGNUM_DEAMONT_SM2_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0xbc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0xb8) /\
                  bignum_from_memory (z,4) s =
                   (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_DEAMONT_SM2_EXEC (1--34) (1--34) THEN

  (*** Show that the pre-reduced dd satisfies the key congruence ***)

  ABBREV_TAC `dd = bignum_of_wordlist[sum_s31;sum_s32;sum_s33;sum_s34]` THEN
  SUBGOAL_THEN `(inverse_mod p_sm2 (2 EXP 256) * a == dd) (mod p_sm2)`
  MP_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `!e. (e * d == a) (mod p) /\ (e * i == 1) (mod p)
           ==> (i * a == d) (mod p)`) THEN
    EXISTS_TAC `2 EXP 256` THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN CONJ_TAC
    THENL [ALL_TAC; REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["dd"; "a"] THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[CONG] THEN
    DISCH_THEN SUBST1_TAC] THEN

  (*** The optional reduction ***)

  ARM_ACCSTEPS_TAC BIGNUM_DEAMONT_SM2_EXEC [35;37;38;40] (35--46) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
  SUBGOAL_THEN `carry_s40 <=> dd < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 4`; `if dd < p_sm2 then &dd:real else &(dd - p_sm2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOD_CASES THEN EXPAND_TAC "dd" THEN REWRITE_TAC[p_sm2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXPAND_TAC "dd" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_INTEGER_TAC;
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN EXPAND_TAC "dd" THEN
  REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DEAMONT_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0xbc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s =
                   (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DEAMONT_SM2_EXEC
    BIGNUM_DEAMONT_SM2_CORRECT);;
