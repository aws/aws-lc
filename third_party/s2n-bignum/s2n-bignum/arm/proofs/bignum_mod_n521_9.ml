(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_521, the order of the NIST curve P-521                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_mod_n521_9.o";;
 ****)

let bignum_mod_n521_9_mc =
  define_assert_from_elf "bignum_mod_n521_9_mc" "arm/p521/bignum_mod_n521_9.o"
[
  0xf940202e;       (* arm_LDR X14 X1 (Immediate_Offset (word 64)) *)
  0xd349fdcf;       (* arm_LSR X15 X14 (rvalue (word 9)) *)
  0x910005ef;       (* arm_ADD X15 X15 (rvalue (word 1)) *)
  0xd2937ee2;       (* arm_MOV X2 (rvalue (word 39927)) *)
  0xf2add8e2;       (* arm_MOVK X2 (word 28359) 16 *)
  0xf2c91c22;       (* arm_MOVK X2 (word 18657) 32 *)
  0xf2e89202;       (* arm_MOVK X2 (word 17552) 48 *)
  0x9b0f7c46;       (* arm_MUL X6 X2 X15 *)
  0xd2970a23;       (* arm_MOV X3 (rvalue (word 47185)) *)
  0xf2aecc63;       (* arm_MOVK X3 (word 30307) 16 *)
  0xf2c6c8e3;       (* arm_MOVK X3 (word 13895) 32 *)
  0xf2f88943;       (* arm_MOVK X3 (word 50250) 48 *)
  0x9b0f7c67;       (* arm_MUL X7 X3 X15 *)
  0xd28b45e4;       (* arm_MOV X4 (rvalue (word 23087)) *)
  0xf2a11ec4;       (* arm_MOVK X4 (word 2294) 16 *)
  0xf2dfd6e4;       (* arm_MOVK X4 (word 65207) 32 *)
  0xf2f00664;       (* arm_MOVK X4 (word 32819) 48 *)
  0x9b0f7c88;       (* arm_MUL X8 X4 X15 *)
  0xd28d3285;       (* arm_MOV X5 (rvalue (word 27028)) *)
  0xf2a81a05;       (* arm_MOVK X5 (word 16592) 16 *)
  0xf2cf0f85;       (* arm_MOVK X5 (word 30844) 32 *)
  0xf2f5cf25;       (* arm_MOVK X5 (word 44665) 48 *)
  0x9b0f7ca9;       (* arm_MUL X9 X5 X15 *)
  0xd37ef5ea;       (* arm_LSL X10 X15 (rvalue (word 2)) *)
  0x8b0f014a;       (* arm_ADD X10 X10 X15 *)
  0x9bcf7c4d;       (* arm_UMULH X13 X2 X15 *)
  0xab0d00e7;       (* arm_ADDS X7 X7 X13 *)
  0x9bcf7c6d;       (* arm_UMULH X13 X3 X15 *)
  0xba0d0108;       (* arm_ADCS X8 X8 X13 *)
  0x9bcf7c8d;       (* arm_UMULH X13 X4 X15 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0x9bcf7cad;       (* arm_UMULH X13 X5 X15 *)
  0x9a0d014a;       (* arm_ADC X10 X10 X13 *)
  0xa940342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&0))) *)
  0xab0c00c6;       (* arm_ADDS X6 X6 X12 *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xa941342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&16))) *)
  0xba0c0108;       (* arm_ADCS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xa9422c2d;       (* arm_LDP X13 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xb277d9ce;       (* arm_ORR X14 X14 (rvalue (word 18446744073709551104)) *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xda9f23ef;       (* arm_CSETM X15 Condition_CC *)
  0x8a0f0042;       (* arm_AND X2 X2 X15 *)
  0xeb0200c6;       (* arm_SUBS X6 X6 X2 *)
  0x8a0f0063;       (* arm_AND X3 X3 X15 *)
  0xfa0300e7;       (* arm_SBCS X7 X7 X3 *)
  0x8a0f0084;       (* arm_AND X4 X4 X15 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0x8a0f00a5;       (* arm_AND X5 X5 X15 *)
  0xfa050129;       (* arm_SBCS X9 X9 X5 *)
  0xd28000a2;       (* arm_MOV X2 (rvalue (word 5)) *)
  0x8a0f0042;       (* arm_AND X2 X2 X15 *)
  0xfa02014a;       (* arm_SBCS X10 X10 X2 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f01ce;       (* arm_SBC X14 X14 XZR *)
  0x924021ce;       (* arm_AND X14 X14 (rvalue (word 511)) *)
  0xa9001c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa903340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200e;       (* arm_STR X14 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_N521_9_EXEC = ARM_MK_EXEC_RULE bignum_mod_n521_9_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_521 = new_definition `n_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449`;;

let BIGNUM_MOD_N521_9_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x118) (z,8 * 9)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n521_9_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = word (pc + 0x114) /\
                bignum_from_memory (z,9) s = n MOD n_521)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `9` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  (*** Initial quotient approximation ***)

  ARM_STEPS_TAC BIGNUM_MOD_N521_9_EXEC (1--3) THEN
  SUBGOAL_THEN `n DIV 2 EXP 521 = val(n_8:int64) DIV 2 EXP 9` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q:int64 = word_add (word_ushr n_8 9) (word 1)` THEN
  SUBGOAL_THEN `val(n_8:int64) DIV 2 EXP 9 + 1 = val(q:int64)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR] THEN
    ASM_REWRITE_TAC[VAL_WORD_1; DIMINDEX_64] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPEC `n_8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(q:int64) <= 2 EXP 55` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MP_TAC(SPEC `n_8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Multiplication q * r_521 ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N521_9_EXEC
   [8; 13; 18; 23; 27; 29; 31; 33] (4--33) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s8;sum_s27;sum_s29;sum_s31;sum_s33] =
    val(q:int64) * (2 EXP 521 - n_521)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 5)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH];
      UNDISCH_TAC `val(q:int64) <= 2 EXP 55` THEN
      REWRITE_TAC[n_521] THEN ARITH_TAC;
      REWRITE_TAC[n_521; REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; DIMINDEX_64] THEN
      CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Initial reduction r = x - q * n_521, with 2^576 offset  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N521_9_EXEC
   [35; 36; 38; 39; 41; 42; 44; 45; 47] (34--47) THEN
  SUBGOAL_THEN
   `&2 pow 576 * &(bitval carry_s47) +
    &(bignum_of_wordlist
       [sum_s35; sum_s36; sum_s38; sum_s39;
        sum_s41; sum_s42; sum_s44; sum_s45; sum_s47]):real =
    &2 pow 576 + (&n - &(val(q:int64)) * &n_521)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&(val(q:int64)) * &n_521:real =
      &2 pow 521 * &(val q) - &(val q * (2 EXP 521 - n_521))`
    SUBST1_TAC THENL
     [REWRITE_TAC[n_521; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (funpow 5 RAND_CONV) [SYM th])] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    SUBGOAL_THEN
     `&(val(word_or n_8 (word 18446744073709551104):int64)):real =
      (&2 pow 64 - &2 pow 9) + &(val n_8 MOD 2 EXP 9)`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
       `word_or a b = word_or b (word_and a (word_not b))`] THEN
      SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
       `word_and x (word_and y (word_not x)) = word 0`] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; EQ_ADD_LCANCEL] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD];
      ALL_TAC] THEN
    EXPAND_TAC "n" THEN SUBST1_TAC(SYM(ASSUME
     `val(n_8:int64) DIV 2 EXP 9 + 1 = val(q:int64)`)) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD;
                n_521] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ****)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N521_9_EXEC
   [50; 52; 54; 56; 59; 60; 61; 62; 63] (48--69) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  EXISTS_TAC `521` THEN
  EXISTS_TAC
   `if n < val(q:int64) * n_521
    then (&n - &(val q) * &n_521) + &n_521
    else &n - &(val q) * &n_521:real` THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[n_521] THEN ARITH_TAC;
    REWRITE_TAC[n_521] THEN ARITH_TAC;
    ALL_TAC;
    UNDISCH_THEN `val(n_8:int64) DIV 2 EXP 9 + 1 = val(q:int64)`
     (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `n DIV 2 EXP 521 = val(n_8:int64) DIV 2 EXP 9`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH
     `x - (q + &1) * n + n = x - q * n`] THEN
    SUBGOAL_THEN `n DIV 2 EXP 521 * n_521 <= n` MP_TAC THENL
     [REWRITE_TAC[n_521] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `n < 2 EXP (64 * 9)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ; MOD_UNIQUE] THEN
    (CONJ_TAC THENL
      [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[n_521] THEN ARITH_TAC;
       ASM_SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB] THEN
       REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE])] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `e:real = &2 pow 576 + x ==> x = e - &2 pow 576`)) THEN
  SUBGOAL_THEN `n < val(q:int64) * n_521 <=> ~carry_s47` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `576` THEN
    ASM_REWRITE_TAC[REAL_BITVAL_NOT; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    BOUNDER_TAC[];
    ASM_REWRITE_TAC[COND_SWAP; bignum_of_wordlist] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES; n_521] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

let BIGNUM_MOD_N521_9_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x118) (z,8 * 9)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n521_9_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,9) s = n MOD n_521)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_MOD_N521_9_EXEC BIGNUM_MOD_N521_9_CORRECT);;
