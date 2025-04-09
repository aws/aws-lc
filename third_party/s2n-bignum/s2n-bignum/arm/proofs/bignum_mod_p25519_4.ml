(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_25519, the field characteristic for curve25519.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_mod_p25519_4.o";;
 ****)

let bignum_mod_p25519_4_mc = define_assert_from_elf "bignum_mod_p25519_4_mc" "arm/curve25519/bignum_mod_p25519_4.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0xd37ffca6;       (* arm_LSR X6 X5 63 *)
  0x9b061ce6;       (* arm_MADD X6 X7 X6 X7 *)
  0xab060042;       (* arm_ADDS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xb24100a5;       (* arm_ORR X5 X5 (rvalue (word 9223372036854775808)) *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a9f30e6;       (* arm_CSEL X6 X7 XZR Condition_CC *)
  0xeb060042;       (* arm_SUBS X2 X2 X6 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_P25519_4_EXEC = ARM_MK_EXEC_RULE bignum_mod_p25519_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let BIGNUM_MOD_P25519_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x4c) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p25519_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = word (pc + 0x48) /\
                bignum_from_memory (z,4) s = n MOD p_25519)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** Since we tinker with the top bit a lot, give it a name ***)

  ABBREV_TAC `b <=> bit 63 (n_3:int64)` THEN

  SUBGOAL_THEN
   `val(n_3:int64) DIV 2 EXP 63 = bitval b /\
    n DIV 2 EXP 255 = bitval b`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[BIT_VAL] THEN
    SUBGOAL_THEN `val(n_3:int64) DIV 2 EXP 63 < 2` MP_TAC THENL
     [MP_TAC(SPEC `n_3:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SPEC_TAC(`val(n_3:int64) DIV 2 EXP 63`,`bb:num`)] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ARITH; BITVAL_CLAUSES];
    ALL_TAC] THEN

  (*** Simulate, with manual tweaks for the shr + madd combo ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P25519_4_EXEC
   [6;7;8;10;12;13;14;15] (1--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&(val(word(19 + 19 * val(word_ushr (n_3:int64) 63)):int64)):real =
    &19 * (&1 + &(bitval b))`
  SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Making arithmetical sense of the "or" ***)

  SUBGOAL_THEN
   `&(val(word_or n_3 (word 9223372036854775808):int64)):real =
    &(val n_3) + &2 pow 63 * (&1 - &(bitval b))`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the proof is as usual ***)

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s18" THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`255`;
    `if n < (bitval b + 1) * p_25519
     then &n - &(bitval b) * &p_25519
     else &n - (&(bitval b) + &1) * &p_25519:real`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[REAL_OF_NUM_MOD; EQT_ELIM
     ((REWRITE_CONV[p_25519] THENC (EQT_INTRO o ARITH_RULE))
      `n < 2 EXP (64 * 4)
       ==> n DIV p_25519 =
           if n < (n DIV 2 EXP 255 + 1) * p_25519
           then n DIV 2 EXP 255 else n DIV 2 EXP 255 + 1`)] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES]] THEN

  SUBGOAL_THEN `n < (bitval b + 1) * p_25519 <=> ~carry_s10` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[p_25519; bignum_of_wordlist] THEN
    REWRITE_TAC[REAL_BITVAL_NOT; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    EXPAND_TAC "n" THEN REWRITE_TAC[COND_SWAP; bignum_of_wordlist] THEN
    REWRITE_TAC[p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s10:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_MOD_P25519_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x4c) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p25519_4_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD p_25519)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_P25519_4_EXEC
    BIGNUM_MOD_P25519_4_CORRECT);;
