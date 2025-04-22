(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_256.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p256/bignum_deamont_p256.o";;
 ****)

let bignum_deamont_p256_mc =
  define_assert_from_elf "bignum_deamont_p256_mc" "arm/p256/bignum_deamont_p256.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd3607c47;       (* arm_LSL X7 X2 (rvalue (word 32)) *)
  0xeb070048;       (* arm_SUBS X8 X2 X7 *)
  0xd360fc46;       (* arm_LSR X6 X2 (rvalue (word 32)) *)
  0xda060042;       (* arm_SBC X2 X2 X6 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9a1f0042;       (* arm_ADC X2 X2 XZR *)
  0xd3607c67;       (* arm_LSL X7 X3 (rvalue (word 32)) *)
  0xeb070068;       (* arm_SUBS X8 X3 X7 *)
  0xd360fc66;       (* arm_LSR X6 X3 (rvalue (word 32)) *)
  0xda060063;       (* arm_SBC X3 X3 X6 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0xba080042;       (* arm_ADCS X2 X2 X8 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xd3607c87;       (* arm_LSL X7 X4 (rvalue (word 32)) *)
  0xeb070088;       (* arm_SUBS X8 X4 X7 *)
  0xd360fc86;       (* arm_LSR X6 X4 (rvalue (word 32)) *)
  0xda060084;       (* arm_SBC X4 X4 X6 *)
  0xab0700a5;       (* arm_ADDS X5 X5 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0xd3607ca7;       (* arm_LSL X7 X5 (rvalue (word 32)) *)
  0xeb0700a8;       (* arm_SUBS X8 X5 X7 *)
  0xd360fca6;       (* arm_LSR X6 X5 (rvalue (word 32)) *)
  0xda0600a5;       (* arm_SBC X5 X5 X6 *)
  0xab070042;       (* arm_ADDS X2 X2 X7 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0xb26083e8;       (* arm_MOV X8 (rvalue (word 18446744069414584321)) *)
  0xb100045f;       (* arm_CMN X2 (rvalue (word 1)) *)
  0xfa07007f;       (* arm_SBCS XZR X3 X7 *)
  0xfa1f009f;       (* arm_SBCS XZR X4 XZR *)
  0xfa0800bf;       (* arm_SBCS XZR X5 X8 *)
  0xda9f33e6;       (* arm_CSETM X6 Condition_CS *)
  0xeb060042;       (* arm_SUBS X2 X2 X6 *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0x8a060108;       (* arm_AND X8 X8 X6 *)
  0xda0800a5;       (* arm_SBC X5 X5 X8 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEAMONT_P256_EXEC = ARM_MK_EXEC_RULE bignum_deamont_p256_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let BIGNUM_DEAMONT_P256_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0xc8) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0xc4) /\
                  bignum_from_memory (z,4) s =
                   (inverse_mod p_256 (2 EXP 256) * a) MOD p_256)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_DEAMONT_P256_EXEC (1--34) (1--34) THEN

  (*** Show that the pre-reduced dd satisfies the key congruence ***)

  ABBREV_TAC `dd = bignum_of_wordlist[sum_s31;sum_s32;sum_s33;sum_s34]` THEN
  SUBGOAL_THEN `(inverse_mod p_256 (2 EXP 256) * a == dd) (mod p_256)`
  MP_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `!e. (e * d == a) (mod p) /\ (e * i == 1) (mod p)
           ==> (i * a == d) (mod p)`) THEN
    EXISTS_TAC `2 EXP 256` THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN CONJ_TAC
    THENL [ALL_TAC; REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["dd"; "a"] THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[CONG] THEN
    DISCH_THEN SUBST1_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_DEAMONT_P256_EXEC
   [37;38;39;40;42;44;45;47] (35--49) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  SUBGOAL_THEN `~carry_s40 <=> p_256 <= dd` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s49" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; p_256] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN `dd MOD p_256 = if p_256 <= dd then dd - p_256 else dd`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN MATCH_MP_TAC MOD_CASES THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[p_256; bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[GSYM REAL_OF_NUM_SUB]] THEN
  ABBREV_TAC `q <=> p_256 <= dd` THEN
  EXPAND_TAC "dd" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DEAMONT_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0xc8) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s =
                   (inverse_mod p_256 (2 EXP 256) * a) MOD p_256)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DEAMONT_P256_EXEC
    BIGNUM_DEAMONT_P256_CORRECT);;
