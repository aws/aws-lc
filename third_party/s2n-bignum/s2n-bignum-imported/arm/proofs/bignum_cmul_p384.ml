(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_384 of a single word and a bignum < p_384.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_cmul_p384.o";;
 ****)

let bignum_cmul_p384_mc = define_assert_from_elf "bignum_cmul_p384_mc" "arm/p384/bignum_cmul_p384.o"
[
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0xa942344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&32))) *)
  0x9b087c22;       (* arm_MUL X2 X1 X8 *)
  0x9b097c23;       (* arm_MUL X3 X1 X9 *)
  0x9b0a7c24;       (* arm_MUL X4 X1 X10 *)
  0x9b0b7c25;       (* arm_MUL X5 X1 X11 *)
  0x9b0c7c26;       (* arm_MUL X6 X1 X12 *)
  0x9b0d7c27;       (* arm_MUL X7 X1 X13 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0x9bcb7c2b;       (* arm_UMULH X11 X1 X11 *)
  0x9bcc7c2c;       (* arm_UMULH X12 X1 X12 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0xba0c00e7;       (* arm_ADCS X7 X7 X12 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0x9100042c;       (* arm_ADD X12 X1 (rvalue (word 1)) *)
  0xaa2103ed;       (* arm_ORN X13 XZR X1 *)
  0xd3607da8;       (* arm_LSL X8 X13 (rvalue (word 32)) *)
  0x93cd8029;       (* arm_EXTR X9 X1 X13 (rvalue (word 32)) *)
  0xd360fc2a;       (* arm_LSR X10 X1 (rvalue (word 32)) *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0x9a1f03eb;       (* arm_ADC X11 XZR XZR *)
  0xab080042;       (* arm_ADDS X2 X2 X8 *)
  0xba090063;       (* arm_ADCS X3 X3 X9 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xda9f23e8;       (* arm_CSETM X8 Condition_CC *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xab090042;       (* arm_ADDS X2 X2 X9 *)
  0xca080129;       (* arm_EOR X9 X9 X8 *)
  0xba090063;       (* arm_ADCS X3 X3 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a0800e7;       (* arm_ADC X7 X7 X8 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMUL_P384_EXEC = ARM_MK_EXEC_RULE bignum_cmul_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let p384redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_384 - 1)
       ==> let q = n DIV 2 EXP 384 + 1 in
           q < 2 EXP 64 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let BIGNUM_CMUL_P384_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0xd0) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + 0xcc) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s = (val c * a) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
                         X9; X10; X11; X12; X13] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_384 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_CMUL_P384_EXEC (1--51)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Intermediate result from initial multiply ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P384_EXEC (1--21) (1--21) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [mullo_s4; sum_s16; sum_s17; sum_s18; sum_s19; sum_s20; sum_s21] =
    val(c:int64) * a`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`word(a):int64 = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The quotient approximation logic ***)

  MP_TAC(SPEC `val(c:int64) * a` p384redlemma) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    MP_TAC(ISPEC `c:int64` VAL_BOUND) THEN UNDISCH_TAC `a < p_384` THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
  SUBST1_TAC(SYM(ASSUME
   `bignum_of_wordlist
     [mullo_s4; sum_s16; sum_s17; sum_s18; sum_s19; sum_s20; sum_s21] =
    val(c:int64) * a`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** The initial reduction computation ***)

  ARM_STEPS_TAC BIGNUM_CMUL_P384_EXEC (22--26) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [WORD_RULE `word_add x (word 1) = word(val x + 1)`]) THEN
  MAP_EVERY REABBREV_TAC
   [`a0 = read X8 s26`; `a1 = read X9 s26`; `a2 = read X10 s26`] THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[a0; a1; a2]):real =
    (&2 pow 96 - &2 pow 32) * (&(val(sum_s21:int64)) + &1)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "a1"; "a2"] THEN
    REWRITE_TAC[bignum_of_wordlist; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    SIMP_TAC[VAL_WORD_SHL; VAL_WORD_USHR] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; REAL_VAL_WORD_NOT;
                VAL_WORD_0; DIMINDEX_64; ARITH_RULE
                 `(2 EXP 32 * x) DIV 2 EXP 64 = x DIV 2 EXP 32`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P384_EXEC (27--36) (27--36) THEN
  SUBGOAL_THEN
   `&(val(word(val(sum_s21:int64) + 1):int64)):real = &(val sum_s21) + &1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 384 * bitval carry_s36 +
    bignum_of_wordlist[sum_s31; sum_s32; sum_s33; sum_s34; sum_s35; sum_s36] +
    (val(sum_s21:int64) + 1) * p_384 =
    2 EXP 384 + val(c:int64) * a`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist
       [mullo_s4; sum_s16; sum_s17; sum_s18; sum_s19; sum_s20; sum_s21] =
      val(c:int64) * a`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a = (&2 pow 96 - &2 pow 32) * b
      ==> x = a + y - (&2 pow 96 - &2 pow 32) * b
          ==> x = y`)) THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P384_EXEC [40;42;45;46;47;48] (37--51) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s21:int64) + 1`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> val(c:int64) * a < (val(sum_s21:int64) + 1) * p_384` THEN
  REWRITE_TAC[p_384] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `carry_s36 <=> ~b` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(p ==> ~q) /\ (~p ==> q) ==> (p <=> ~q)`) THEN
    CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC
     `2 EXP 384 * bitval carry_s36 +
      bignum_of_wordlist[sum_s31; sum_s32; sum_s33; sum_s34; sum_s35; sum_s36] +
      (val(sum_s21:int64) + 1) * p_384 =
      2 EXP 384 + val(c:int64) * a` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[EQ_ADD_LCANCEL; NOT_LT] THENL
     [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `s:num < e ==> s + p = e + c ==> c < p`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `2 EXP 384 * bitval(~b) +
    bignum_of_wordlist[sum_s31; sum_s32; sum_s33; sum_s34; sum_s35; sum_s36] +
    (val(sum_s21:int64) + 1) * p_384 =
    2 EXP 384 + val(c:int64) * a` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP
   (REAL_ARITH `a:real = b + x ==> x = a - b`)) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_P384_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc returnaddress.
        nonoverlapping (word pc,0xd0) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s = (val c * a) MOD p_384))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMUL_P384_EXEC BIGNUM_CMUL_P384_CORRECT);;
