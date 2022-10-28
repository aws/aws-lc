(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 *)

(* ========================================================================= *)
(* Squaring modulo p_25519, the field characteristic for curve25519.         *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/curve25519/bignum_sqr_p25519_alt.o";;
 ****)

let bignum_sqr_p25519_alt_mc = define_assert_from_elf "bignum_sqr_p25519_alt_mc" "arm/curve25519/bignum_sqr_p25519_alt.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab040129;       (* arm_ADDS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0xb241016b;       (* arm_ORR X11 X11 (rvalue (word 9223372036854775808)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b020c67;       (* arm_MADD X7 X3 X2 X3 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0x9a9f3063;       (* arm_CSEL X3 X3 XZR Condition_CC *)
  0xeb030108;       (* arm_SUBS X8 X8 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0xa9002408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_P25519_ALT_EXEC = ARM_MK_EXEC_RULE bignum_sqr_p25519_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let BIGNUM_SQR_P25519_ALT_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x144) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p25519_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word(pc + 0x140) /\
                  bignum_from_memory (z,4) s = (n EXP 2) MOD p_25519)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_ALT_EXEC (1--45) (1--45) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s31; sum_s33; sum_s35; sum_s37]`;
    `h = bignum_of_wordlist[sum_s39; sum_s41; sum_s43; sum_s45]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_ALT_EXEC (46--63) (46--63) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s49; sum_s60; sum_s61; sum_s62; sum_s63]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_ALT_EXEC (64--66) (64--66) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s49; sum_s60; sum_s61;word_or sum_s62 (word 9223372036854775808)]` THEN
    SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s49; sum_s60; sum_s61] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s66:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s64; sum_s66] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC BIGNUM_SQR_P25519_ALT_EXEC (67--68) THEN
  ABBREV_TAC `qm:int64 = word(19 + 19 * val(sum_s66:int64))` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(sum_s66:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `c + c * q = c * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s66:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_ALT_EXEC (69--80) (69--80) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s66:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(sum_s66:int64) + 1) * p_25519 <=> ~carry_s72`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s72:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_SQR_P25519_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x144) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p25519_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (n EXP 2) MOD p_25519)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_SQR_P25519_ALT_EXEC BIGNUM_SQR_P25519_ALT_CORRECT);;
