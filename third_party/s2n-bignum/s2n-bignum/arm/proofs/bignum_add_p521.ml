(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition modulo p_521, the field characteristic for the NIST P-521 curve. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_add_p521.o";;
 ****)

let bignum_add_p521_mc = define_assert_from_elf "bignum_add_p521_mc" "arm/p521/bignum_add_p521.o"
[
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9401825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xba0400a5;       (* arm_ADCS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&16))) *)
  0xa9410c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422829;       (* arm_LDP X9 X10 X1 (Immediate_Offset (iword (&32))) *)
  0xa9420c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xa943302b;       (* arm_LDP X11 X12 X1 (Immediate_Offset (iword (&48))) *)
  0xa9430c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&48))) *)
  0xba04016b;       (* arm_ADCS X11 X11 X4 *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf940202d;       (* arm_LDR X13 X1 (Immediate_Offset (word 64)) *)
  0xf9402044;       (* arm_LDR X4 X2 (Immediate_Offset (word 64)) *)
  0x9a0401ad;       (* arm_ADC X13 X13 X4 *)
  0xf10801a4;       (* arm_SUBS X4 X13 (rvalue (word 512)) *)
  0xda9f33e4;       (* arm_CSETM X4 Condition_CS *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x92770084;       (* arm_AND X4 X4 (rvalue (word 512)) *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda0401ad;       (* arm_SBC X13 X13 X4 *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0xa903300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200d;       (* arm_STR X13 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_ADD_P521_EXEC = ARM_MK_EXEC_RULE bignum_add_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_ADD_P521_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x98) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read PC s = word (pc + 0x94) /\
                  (m < p_521 /\ n < p_521
                   ==> bignum_from_memory (z,9) s = (m + n) MOD p_521))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the m < p_521 /\ n < p_521 assumption ***)

  ASM_CASES_TAC `m < p_521 /\ n < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_ADD_P521_EXEC (1--37)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 9)) s0` THEN

  (*** Initial non-overflowing addition s = x + y + 1 ***)

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P521_EXEC [4;5;8;9;12;13;16;17;20] (1--20) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s4;sum_s5;sum_s8;sum_s9;sum_s12;sum_s13;sum_s16;sum_s17;sum_s20] =
    m + n + 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[p_521] THEN REAL_ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The net comparison s >= 2^521 <=> x + y >= p_521 ***)

  ARM_STEPS_TAC BIGNUM_ADD_P521_EXEC (21--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LT]) THEN
  SUBGOAL_THEN `512 <= val(sum_s20:int64) <=> p_521 <= m + n`
  SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS `512 <= (m + n + 1) DIV 2 EXP 512` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  ARM_ACCSTEPS_TAC BIGNUM_ADD_P521_EXEC (23::(25--32)) (23--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 9`;
    `if p_521 <= m + n then &(m + n + 1) - &2 pow 521
     else &(m + n + 1) - &1:real`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `s = m + n + 1` THEN POP_ASSUM(K ALL_TAC) THEN EXPAND_TAC "s" THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_ADD_P521_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x98) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_521 /\ n < p_521
                   ==> bignum_from_memory (z,9) s = (m + n) MOD p_521))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_P521_EXEC BIGNUM_ADD_P521_CORRECT);;
