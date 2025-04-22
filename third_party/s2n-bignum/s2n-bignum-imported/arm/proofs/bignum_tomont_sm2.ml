(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 4-word (256-bit) bignum to Montgomery form modulo p_sm2.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_tomont_sm2.o";;
 ****)

let bignum_tomont_sm2_mc =
  define_assert_from_elf "bignum_tomont_sm2_mc" "arm/sm2/bignum_tomont_sm2.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xb1000441;       (* arm_ADDS X1 X2 (rvalue (word 1)) *)
  0xb2607fe6;       (* arm_MOV X6 (rvalue (word 18446744069414584320)) *)
  0xfa060066;       (* arm_SBCS X6 X3 X6 *)
  0xba1f0087;       (* arm_ADCS X7 X4 XZR *)
  0x92c00028;       (* arm_MOVN X8 (word 1) 32 *)
  0xfa0800a8;       (* arm_SBCS X8 X5 X8 *)
  0x9a813042;       (* arm_CSEL X2 X2 X1 Condition_CC *)
  0x9a863063;       (* arm_CSEL X3 X3 X6 Condition_CC *)
  0x9a873084;       (* arm_CSEL X4 X4 X7 Condition_CC *)
  0x9a8830a5;       (* arm_CSEL X5 X5 X8 Condition_CC *)
  0xab050088;       (* arm_ADDS X8 X4 X5 *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0x9a0700a6;       (* arm_ADC X6 X5 X7 *)
  0x8b4880a7;       (* arm_ADD X7 X5 (Shiftedreg X8 LSR 32) *)
  0xab4780c1;       (* arm_ADDS X1 X6 (Shiftedreg X7 LSR 32) *)
  0xda813021;       (* arm_CINV X1 X1 Condition_CS *)
  0xd3607c28;       (* arm_LSL X8 X1 32 *)
  0xeb010106;       (* arm_SUBS X6 X8 X1 *)
  0xd360fc29;       (* arm_LSR X9 X1 32 *)
  0xda1f0127;       (* arm_SBC X7 X9 XZR *)
  0xab0200c6;       (* arm_ADDS X6 X6 X2 *)
  0xcb0100a5;       (* arm_SUB X5 X5 X1 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0xba040108;       (* arm_ADCS X8 X8 X4 *)
  0x9a050129;       (* arm_ADC X9 X9 X5 *)
  0xab090022;       (* arm_ADDS X2 X1 X9 *)
  0x92607d21;       (* arm_AND X1 X9 (rvalue (word 18446744069414584320)) *)
  0xba0100c3;       (* arm_ADCS X3 X6 X1 *)
  0xba0900e4;       (* arm_ADCS X4 X7 X9 *)
  0x925ff921;       (* arm_AND X1 X9 (rvalue (word 18446744069414584319)) *)
  0x9a010105;       (* arm_ADC X5 X8 X1 *)
  0xab050088;       (* arm_ADDS X8 X4 X5 *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0x9a0700a6;       (* arm_ADC X6 X5 X7 *)
  0x8b4880a7;       (* arm_ADD X7 X5 (Shiftedreg X8 LSR 32) *)
  0xab4780c1;       (* arm_ADDS X1 X6 (Shiftedreg X7 LSR 32) *)
  0xda813021;       (* arm_CINV X1 X1 Condition_CS *)
  0xd3607c28;       (* arm_LSL X8 X1 32 *)
  0xeb010106;       (* arm_SUBS X6 X8 X1 *)
  0xd360fc29;       (* arm_LSR X9 X1 32 *)
  0xda1f0127;       (* arm_SBC X7 X9 XZR *)
  0xab0200c6;       (* arm_ADDS X6 X6 X2 *)
  0xcb0100a5;       (* arm_SUB X5 X5 X1 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0xba040108;       (* arm_ADCS X8 X8 X4 *)
  0x9a050129;       (* arm_ADC X9 X9 X5 *)
  0xab090022;       (* arm_ADDS X2 X1 X9 *)
  0x92607d21;       (* arm_AND X1 X9 (rvalue (word 18446744069414584320)) *)
  0xba0100c3;       (* arm_ADCS X3 X6 X1 *)
  0xba0900e4;       (* arm_ADCS X4 X7 X9 *)
  0x925ff921;       (* arm_AND X1 X9 (rvalue (word 18446744069414584319)) *)
  0x9a010105;       (* arm_ADC X5 X8 X1 *)
  0xab050088;       (* arm_ADDS X8 X4 X5 *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0x9a0700a6;       (* arm_ADC X6 X5 X7 *)
  0x8b4880a7;       (* arm_ADD X7 X5 (Shiftedreg X8 LSR 32) *)
  0xab4780c1;       (* arm_ADDS X1 X6 (Shiftedreg X7 LSR 32) *)
  0xda813021;       (* arm_CINV X1 X1 Condition_CS *)
  0xd3607c28;       (* arm_LSL X8 X1 32 *)
  0xeb010106;       (* arm_SUBS X6 X8 X1 *)
  0xd360fc29;       (* arm_LSR X9 X1 32 *)
  0xda1f0127;       (* arm_SBC X7 X9 XZR *)
  0xab0200c6;       (* arm_ADDS X6 X6 X2 *)
  0xcb0100a5;       (* arm_SUB X5 X5 X1 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0xba040108;       (* arm_ADCS X8 X8 X4 *)
  0x9a050129;       (* arm_ADC X9 X9 X5 *)
  0xab090022;       (* arm_ADDS X2 X1 X9 *)
  0x92607d21;       (* arm_AND X1 X9 (rvalue (word 18446744069414584320)) *)
  0xba0100c3;       (* arm_ADCS X3 X6 X1 *)
  0xba0900e4;       (* arm_ADCS X4 X7 X9 *)
  0x925ff921;       (* arm_AND X1 X9 (rvalue (word 18446744069414584319)) *)
  0x9a010105;       (* arm_ADC X5 X8 X1 *)
  0xab050088;       (* arm_ADDS X8 X4 X5 *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0x9a0700a6;       (* arm_ADC X6 X5 X7 *)
  0x8b4880a7;       (* arm_ADD X7 X5 (Shiftedreg X8 LSR 32) *)
  0xab4780c1;       (* arm_ADDS X1 X6 (Shiftedreg X7 LSR 32) *)
  0xda813021;       (* arm_CINV X1 X1 Condition_CS *)
  0xd3607c28;       (* arm_LSL X8 X1 32 *)
  0xeb010106;       (* arm_SUBS X6 X8 X1 *)
  0xd360fc29;       (* arm_LSR X9 X1 32 *)
  0xda1f0127;       (* arm_SBC X7 X9 XZR *)
  0xab0200c6;       (* arm_ADDS X6 X6 X2 *)
  0xcb0100a5;       (* arm_SUB X5 X5 X1 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0xba040108;       (* arm_ADCS X8 X8 X4 *)
  0x9a050129;       (* arm_ADC X9 X9 X5 *)
  0xab090022;       (* arm_ADDS X2 X1 X9 *)
  0x92607d21;       (* arm_AND X1 X9 (rvalue (word 18446744069414584320)) *)
  0xba0100c3;       (* arm_ADCS X3 X6 X1 *)
  0xba0900e4;       (* arm_ADCS X4 X7 X9 *)
  0x925ff921;       (* arm_AND X1 X9 (rvalue (word 18446744069414584319)) *)
  0x9a010105;       (* arm_ADC X5 X8 X1 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TOMONT_SM2_EXEC = ARM_MK_EXEC_RULE bignum_tomont_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let sm2longredlemma = prove
 (`!n. n < 2 EXP 64 * p_sm2
       ==> let q = MIN
                   ((n DIV 2 EXP 192 + (1 + 2 EXP 32) *
                     n DIV 2 EXP 256 + 2 EXP 64) DIV (2 EXP 64))
                   (2 EXP 64 - 1) in
          q < 2 EXP 64 /\
          q * p_sm2 <= n + p_sm2 /\
          n < q * p_sm2 + p_sm2`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC);;

let BIGNUM_TOMONT_SM2_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x18c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x188) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_sm2)
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initial reduction of the input mod p_sm2 ***)

  BIGNUM_TERMRANGE_TAC `4` `a:num` THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC (1--12) (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN `carry_s8 <=> a < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ABBREV_TAC
   `a1 = bignum_of_wordlist
          [read X2 s12; read X3 s12; read X4 s12; read X5 s12]` THEN
  SUBGOAL_THEN `a1 = a MOD p_sm2` SUBST_ALL_TAC THENL
   [EXPAND_TAC "a1" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `a < 2 EXP (64 * 4)` THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [EXPAND_TAC "a" THEN ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
      EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
        ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `x:real < y ==> x - &n < y`) THEN
        REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; p_sm2] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    POP_ASSUM MP_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`read X0 s12 = z`; `read PC s12 = word (pc + 48)`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read Xnn s = y`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl))) THEN
    DISCH_TAC THEN DISCH_TAC] THEN

  SUBGOAL_THEN
   `(2 EXP 256 * a) MOD p_sm2 = (2 EXP 256 * a MOD p_sm2) MOD p_sm2`
  SUBST1_TAC THENL [CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a MOD p_sm2 < p_sm2` MP_TAC THENL
   [REWRITE_TAC[p_sm2] THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`a MOD p_sm2`,`a:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`x_0 = read X2 s12`; `x_1 = read X3 s12`; `x_2 = read X4 s12`;
    `x_3 = read X5 s12`] THEN
  DISCH_TAC THEN

  (*** Break down the goal into 4 steps at the outset ***)

  SUBGOAL_THEN
   `(2 EXP 256 * a) MOD p_sm2 =
    (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * a)
     MOD p_sm2) MOD p_sm2) MOD p_sm2) MOD p_sm2`
  SUBST1_TAC THENL
   [CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Main 4-fold iteration of the same tactic ***)

  REPLICATE_TAC 4
 (
  SUBGOAL_THEN `2 EXP 64 * a < 2 EXP 64 * p_sm2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ABBREV_TAC `m = 2 EXP 64 * a` THEN

  (*** The computation of the quotient estimate q ***)

  MP_TAC(SPEC `m:num` sm2longredlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN

  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC [13;15;16;17] (13--17) THEN
  SUBGOAL_THEN
   `2 EXP 64 * bitval carry_s17 + val(sum_s17:int64) =
    (m DIV 2 EXP 192 + (1 + 2 EXP 32) * m DIV 2 EXP 256 + 2 EXP 64)
    DIV 2 EXP 64`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m";"a"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_ZAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `m < 2 EXP 64 * p_sm2 ==> m DIV 2 EXP 256 <= p_sm2 DIV 2 EXP 192`)) THEN
    MAP_EVERY EXPAND_TAC ["m";"a"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_ZAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_sm2] THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
    ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
      MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
    REWRITE_TAC[VAL_WORD_USHR; REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN

  ARM_STEPS_TAC BIGNUM_TOMONT_SM2_EXEC [18] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   `!q. read Xn s = (if c then x else y)
        ==> (if c then x else y) = q ==> read Xn s = q`)) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `2 EXP 64 * bitval carry_s17 + val(sum_s17:int64) <= 2 EXP 64`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `m < 2 EXP 64 * p_sm2` THEN
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "q" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (funpow 3 RAND_CONV o LAND_CONV) [SYM th]) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[COND_SWAP] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES; WORD_OR_0] THEN
    SIMP_TAC[VAL_BOUND_64; WORD_VAL; ARITH_RULE
     `n < 2 EXP 64 ==> MIN n (2 EXP 64 - 1) = n`] THEN
    SIMP_TAC[ARITH_RULE `a + b <= a <=> b = 0`; VAL_EQ_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    DISCH_TAC THEN VAL_INT64_TAC `q:num`] THEN

  (*** A bit of fiddle to make the accumulation tactics work ***)

  ABBREV_TAC `w:int64 = word q` THEN
  UNDISCH_THEN `val(w:int64) = q` (SUBST_ALL_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC o end_itlist CONJ) THEN

  (*** Main subtraction of q * p_sm2 ***)

  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC (20--27) (19--27) THEN
  MP_TAC(ISPECL
   [`sum_s27:int64`;
    `&(bignum_of_wordlist[w; sum_s23; sum_s25; sum_s26]):real`;
    `256`; `m:num`; `val(w:int64) * p_sm2`] MASK_AND_VALUE_FROM_CARRY_LT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(w:int64) * p_sm2 <= m + p_sm2`;
        `m < val(w:int64) * p_sm2 + p_sm2`] THEN
      REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["m"; "a"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REPEAT(MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC) THEN
    TRY REAL_INTEGER_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC [28;30;31;33] (28--33) THEN
  ABBREV_TAC `m' = bignum_of_wordlist[sum_s28; sum_s30; sum_s31; sum_s33]` THEN
  SUBGOAL_THEN `m MOD p_sm2 < p_sm2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; p_sm2; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `m MOD p_sm2 = m'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
    MAP_EVERY EXISTS_TAC [`val(w:int64)`; `256`] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `b <=> m < val(w:int64) * p_sm2` THEN
    REWRITE_TAC[REAL_ARITH
     `m - s - (w - b) * n:real = (m - w * n) + (b * n - s)`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[REAL_ADD_RID]
     `x = (if p then y + z else y) ==> x = y + (if p then z else &0)`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x:real = y + z <=> y = x - z`] THEN
    DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["m"; "m'"; "a"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Reset all the variables to match the initial expectations ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `w:int64`) o concl)) THEN

  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`s33:armstate`,`s12:armstate`) THEN
  SPEC_TAC(`sum_s28:int64`,`x_0:int64`) THEN
  SPEC_TAC(`sum_s30:int64`,`x_1:int64`) THEN
  SPEC_TAC(`sum_s31:int64`,`x_2:int64`) THEN
  SPEC_TAC(`sum_s33:int64`,`x_3:int64`) THEN
  SPEC_TAC(`m':num`,`a:num`) THEN REPEAT STRIP_TAC) THEN

  (*** Final writeback is all that is left ***)

  ARM_STEPS_TAC BIGNUM_TOMONT_SM2_EXEC (13--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[]);;

let BIGNUM_TOMONT_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x18c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_sm2)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TOMONT_SM2_EXEC
    BIGNUM_TOMONT_SM2_CORRECT);;
