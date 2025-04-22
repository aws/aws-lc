(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 4x4 -> 8 squaring, Karatsuba then simple recursion to schoolbook.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_4_8.o";;
 ****)

let bignum_sqr_4_8_mc = define_assert_from_elf "bignum_sqr_4_8_mc" "arm/fastmul/bignum_sqr_4_8.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9ba27c46;       (* arm_UMULL X6 W2 W2 *)
  0xd360fc50;       (* arm_LSR X16 X2 32 *)
  0x9bb07e07;       (* arm_UMULL X7 W16 W16 *)
  0x9bb07c50;       (* arm_UMULL X16 W2 W16 *)
  0xab1084c6;       (* arm_ADDS X6 X6 (Shiftedreg X16 LSL 33) *)
  0xd35ffe10;       (* arm_LSR X16 X16 31 *)
  0x9a1000e7;       (* arm_ADC X7 X7 X16 *)
  0x9ba37c68;       (* arm_UMULL X8 W3 W3 *)
  0xd360fc70;       (* arm_LSR X16 X3 32 *)
  0x9bb07e09;       (* arm_UMULL X9 W16 W16 *)
  0x9bb07c70;       (* arm_UMULL X16 W3 W16 *)
  0x9b037c4f;       (* arm_MUL X15 X2 X3 *)
  0x9bc37c4e;       (* arm_UMULH X14 X2 X3 *)
  0xab108508;       (* arm_ADDS X8 X8 (Shiftedreg X16 LSL 33) *)
  0xd35ffe10;       (* arm_LSR X16 X16 31 *)
  0x9a100129;       (* arm_ADC X9 X9 X16 *)
  0xab0f01ef;       (* arm_ADDS X15 X15 X15 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0x9ba47c8a;       (* arm_UMULL X10 W4 W4 *)
  0xd360fc90;       (* arm_LSR X16 X4 32 *)
  0x9bb07e0b;       (* arm_UMULL X11 W16 W16 *)
  0x9bb07c90;       (* arm_UMULL X16 W4 W16 *)
  0xab10854a;       (* arm_ADDS X10 X10 (Shiftedreg X16 LSL 33) *)
  0xd35ffe10;       (* arm_LSR X16 X16 31 *)
  0x9a10016b;       (* arm_ADC X11 X11 X16 *)
  0x9ba57cac;       (* arm_UMULL X12 W5 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9bb07e0d;       (* arm_UMULL X13 W16 W16 *)
  0x9bb07cb0;       (* arm_UMULL X16 W5 W16 *)
  0x9b057c8f;       (* arm_MUL X15 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab10858c;       (* arm_ADDS X12 X12 (Shiftedreg X16 LSL 33) *)
  0xd35ffe10;       (* arm_LSR X16 X16 31 *)
  0x9a1001ad;       (* arm_ADC X13 X13 X16 *)
  0xab0f01ef;       (* arm_ADDS X15 X15 X15 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xeb040042;       (* arm_SUBS X2 X2 X4 *)
  0xfa050063;       (* arm_SBCS X3 X3 X5 *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xca0e0042;       (* arm_EOR X2 X2 X14 *)
  0xeb0e0042;       (* arm_SUBS X2 X2 X14 *)
  0xca0e0063;       (* arm_EOR X3 X3 X14 *)
  0xda0e0063;       (* arm_SBC X3 X3 X14 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba09016b;       (* arm_ADCS X11 X11 X9 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0x9ba27c44;       (* arm_UMULL X4 W2 W2 *)
  0xd360fc49;       (* arm_LSR X9 X2 32 *)
  0x9ba97d25;       (* arm_UMULL X5 W9 W9 *)
  0x9ba97c49;       (* arm_UMULL X9 W2 W9 *)
  0xab098484;       (* arm_ADDS X4 X4 (Shiftedreg X9 LSL 33) *)
  0xd35ffd29;       (* arm_LSR X9 X9 31 *)
  0x9a0900a5;       (* arm_ADC X5 X5 X9 *)
  0x9ba37c6f;       (* arm_UMULL X15 W3 W3 *)
  0xd360fc69;       (* arm_LSR X9 X3 32 *)
  0x9ba97d30;       (* arm_UMULL X16 W9 W9 *)
  0x9ba97c69;       (* arm_UMULL X9 W3 W9 *)
  0x9b037c48;       (* arm_MUL X8 X2 X3 *)
  0x9bc37c4e;       (* arm_UMULH X14 X2 X3 *)
  0xab0985ef;       (* arm_ADDS X15 X15 (Shiftedreg X9 LSL 33) *)
  0xd35ffd29;       (* arm_LSR X9 X9 31 *)
  0x9a090210;       (* arm_ADC X16 X16 X9 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab0800a5;       (* arm_ADDS X5 X5 X8 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab0a00c8;       (* arm_ADDS X8 X6 X10 *)
  0xba0b00e9;       (* arm_ADCS X9 X7 X11 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb040108;       (* arm_SUBS X8 X8 X4 *)
  0xfa050129;       (* arm_SBCS X9 X9 X5 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xa9001c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa903340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_4_8_EXEC = ARM_MK_EXEC_RULE bignum_sqr_4_8_mc;;

(* ------------------------------------------------------------------------- *)
(* Lemmas to help with 32-bit breakdown of digits.                           *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_MADDL_0 = prove
 (`!x y. val(word(0 + val(x:int32) * val(y:int32)):int64) = val x * val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; VAL_WORD_EQ_EQ] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[GSYM DIMINDEX_32; VAL_BOUND]);;

let DIVMOD_33_31 = prove
 (`!n. (2 EXP 33 * n) MOD 2 EXP 64 = 2 EXP 33 * n MOD 2 EXP 31`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let VAL_WORD_SPLIT32 = prove
 (`!x. 2 EXP 32 * val(word_zx(word_ushr x 32):int32) + val(word_zx x:int32) =
       val(x:int64)`,
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM MOD_MULT_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND_64]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQR_4_8_CORRECT = prove
 (`!z x a pc.
      nonoverlapping (word pc,0x17c) (z,8 * 8)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_4_8_mc /\
                 read PC s = word pc /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc + 0x178) /\
               bignum_from_memory (z,8) s = a EXP 2)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
             MAYCHANGE [memory :> bytes(z,8 * 8)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Squaring the lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_EXEC
   [7;9;14;16;18;19;20;21;22;23;24] (1--24) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1] EXP 2 =
    bignum_of_wordlist[sum_s7; sum_s22; sum_s23; sum_s24]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `x_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Squaring the upper half ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_EXEC
   [29;31;36;38;40;41;42;43;44;45;46] (25--46) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[x_2; x_3] EXP 2 =
    bignum_of_wordlist[sum_s29; sum_s44; sum_s45; sum_s46]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_2:int64`; `x_3:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_EXEC [47;48;51;53] (47--53) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; WORD_UNMASK_64]) THEN
  SUBGOAL_THEN
   `abs(&(bignum_of_wordlist[x_0;x_1]) -
        &(bignum_of_wordlist[x_2;x_3])):real =
    &(bignum_of_wordlist[sum_s51;sum_s53])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_abs; REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN
     `bignum_of_wordlist [x_2; x_3] <= bignum_of_wordlist [x_0; x_1] <=>
      ~carry_s48`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
      EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      REWRITE_TAC[COND_SWAP] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
      REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; VAL_WORD_BITVAL] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The augmented H' = H + L_top computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_EXEC (54--57) (54--57) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s29; sum_s44; sum_s45; sum_s46]):real =
    &(bignum_of_wordlist[sum_s54; sum_s55; sum_s56; sum_s57]) -
    &(bignum_of_wordlist[sum_s23; sum_s24])`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
     (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
        MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Squaring the absolute difference ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_EXEC
   [62;64;69;71;73;74;75;76;77;78;79] (58--79) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[sum_s51;sum_s53] EXP 2 =
    bignum_of_wordlist[sum_s62; sum_s77; sum_s78; sum_s79]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`sum_s51:int64`; `sum_s53:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The overall Karatsuba composition ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_EXEC (80--90) (80--94) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
    [COND_SWAP; WORD_UNMASK_64; REAL_BITVAL_NOT; DIMINDEX_64;
     GSYM WORD_NOT_MASK; REAL_VAL_WORD_NOT;REAL_VAL_WORD_MASK]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s94" THEN EXPAND_TAC "a" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(2,2)] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_ARITH
   `(l + &2 pow 128 * h) pow 2 =
    &2 pow 256 * h pow 2 + l pow 2 +
    &2 pow 128 * (h pow 2 + l pow 2 - (l - h) pow 2)`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_SQR_4_8_SUBROUTINE_CORRECT = prove
 (`!z x a pc returnaddress.
      nonoverlapping (word pc,0x17c) (z,8 * 8)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_4_8_mc /\
                 read PC s = word pc /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,4) s = a)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,8) s = a EXP 2)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 8)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_SQR_4_8_EXEC BIGNUM_SQR_4_8_CORRECT);;
