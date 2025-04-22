(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Doubling modulo p_521, the field characteristic for the NIST P-521 curve. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_double_p521.o";;
 ****)

let bignum_double_p521_mc = define_assert_from_elf "bignum_double_p521_mc" "arm/p521/bignum_double_p521.o"
[
  0xf9402022;       (* arm_LDR X2 X1 (Immediate_Offset (word 64)) *)
  0xf104005f;       (* arm_CMP X2 (rvalue (word 256)) *)
  0xa9400c24;       (* arm_LDP X4 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xba030063;       (* arm_ADCS X3 X3 X3 *)
  0xa9000c04;       (* arm_STP X4 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9410c24;       (* arm_LDP X4 X3 X1 (Immediate_Offset (iword (&16))) *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xba030063;       (* arm_ADCS X3 X3 X3 *)
  0xa9010c04;       (* arm_STP X4 X3 X0 (Immediate_Offset (iword (&16))) *)
  0xa9420c24;       (* arm_LDP X4 X3 X1 (Immediate_Offset (iword (&32))) *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xba030063;       (* arm_ADCS X3 X3 X3 *)
  0xa9020c04;       (* arm_STP X4 X3 X0 (Immediate_Offset (iword (&32))) *)
  0xa9430c24;       (* arm_LDP X4 X3 X1 (Immediate_Offset (iword (&48))) *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xba030063;       (* arm_ADCS X3 X3 X3 *)
  0xa9030c04;       (* arm_STP X4 X3 X0 (Immediate_Offset (iword (&48))) *)
  0x9a020042;       (* arm_ADC X2 X2 X2 *)
  0x92402042;       (* arm_AND X2 X2 (rvalue (word 511)) *)
  0xf9002002;       (* arm_STR X2 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DOUBLE_P521_EXEC = ARM_MK_EXEC_RULE bignum_double_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_DOUBLE_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x58) (z,8 * 9) /\
        (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0x54) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (2 * n) MOD p_521))
          (MAYCHANGE [PC; X2; X3; X4] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_DOUBLE_P521_EXEC
   [4;5;8;9;12;13;16;17;19] (1--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** Confirm that the carry-in is the right condition ***)

  SUBGOAL_THEN `256 <= val (n_8:int64) <=> p_521 <= 2 * n` SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS `256 <= n DIV 2 EXP 512` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Hence show that we get the right result in 521 bits ***)

  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if p_521 <= 2 * n then &(2 * n) - &p_521 else &(2 * n):real`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MULT_2; MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `bb <=> p_521 <= 2 * n` THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DOUBLE_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x58) (z,8 * 9) /\
        (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_double_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (2 * n) MOD p_521))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_DOUBLE_P521_EXEC BIGNUM_DOUBLE_P521_CORRECT);;
