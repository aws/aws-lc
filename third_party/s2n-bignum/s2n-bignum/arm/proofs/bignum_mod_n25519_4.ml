(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_25519, the basepoint order for curve25519.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_mod_n25519_4.o";;
 ****)

let bignum_mod_n25519_4_mc = define_assert_from_elf "bignum_mod_n25519_4_mc" "arm/curve25519/bignum_mod_n25519_4.o"
[
  0xd29a7da2;       (* arm_MOV X2 (rvalue (word 54253)) *)
  0xf2ab9ea2;       (* arm_MOVK X2 (word 23797) 16 *)
  0xf2cc6342;       (* arm_MOVK X2 (word 25370) 32 *)
  0xf2eb0242;       (* arm_MOVK X2 (word 22546) 48 *)
  0xd2939ac3;       (* arm_MOV X3 (rvalue (word 40150)) *)
  0xf2b45ee3;       (* arm_MOVK X3 (word 41719) 16 *)
  0xf2df3bc3;       (* arm_MOVK X3 (word 63966) 32 *)
  0xf2e29bc3;       (* arm_MOVK X3 (word 5342) 48 *)
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xd37cfce8;       (* arm_LSR X8 X7 60 *)
  0x9240ece7;       (* arm_AND X7 X7 (rvalue (word 1152921504606846975)) *)
  0x9b087c49;       (* arm_MUL X9 X2 X8 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0x9bc87c4b;       (* arm_UMULH X11 X2 X8 *)
  0xab0b014a;       (* arm_ADDS X10 X10 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xfa0a00a5;       (* arm_SBCS X5 X5 X10 *)
  0xfa0b00c6;       (* arm_SBCS X6 X6 X11 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0x9a9f3042;       (* arm_CSEL X2 X2 XZR Condition_CC *)
  0x9a9f3063;       (* arm_CSEL X3 X3 XZR Condition_CC *)
  0xab020084;       (* arm_ADDS X4 X4 X2 *)
  0xba0300a5;       (* arm_ADCS X5 X5 X3 *)
  0x92440042;       (* arm_AND X2 X2 (rvalue (word 1152921504606846976)) *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a0200e7;       (* arm_ADC X7 X7 X2 *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_N25519_4_EXEC = ARM_MK_EXEC_RULE bignum_mod_n25519_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_25519 = define `n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989`;;

let BIGNUM_MOD_N25519_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x80) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n25519_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = word (pc + 0x7c) /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `m:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_MOD_N25519_4_EXEC
   [13;14;16;18; 19;20;21;22; 25;26;28;29] (1--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s31" THEN

  (*** Quotient and associated mangling ***)

  ABBREV_TAC `q:int64 = word_ushr m_3 60` THEN
  SUBGOAL_THEN
   `&(val(word_and (m_3:int64) (word 1152921504606846975))):real =
    &(val m_3) - &2 pow 60 * &(val(q:int64))`
  SUBST_ALL_TAC THENL [EXPAND_TAC "q" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN

  (*** Main reasoning including quotient estimate correctness ***)

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  EXISTS_TAC `256` THEN
  EXISTS_TAC
   `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
         &n_25519:real` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `m < val(q:int64) * n_25519 <=> carry_s22`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      EXPAND_TAC "m" THEN
      REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      BOOL_CASES_TAC `carry_s22:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    SUBGOAL_THEN `val(q:int64) = m DIV 2 EXP 252` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "q"] THEN
      CONV_TAC(RAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[VAL_WORD_USHR];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
    UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[n_25519; bitval] THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let BIGNUM_MOD_N25519_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x80) (z,8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n25519_4_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_N25519_4_EXEC
    BIGNUM_MOD_N25519_4_CORRECT);;
