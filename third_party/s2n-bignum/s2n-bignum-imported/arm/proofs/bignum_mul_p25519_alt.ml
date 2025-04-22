(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_25519, the field characteristic for curve25519.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_mul_p25519_alt.o";;
 ****)

let bignum_mul_p25519_alt_mc = define_assert_from_elf "bignum_mul_p25519_alt_mc" "arm/curve25519/bignum_mul_p25519_alt.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bca7c83;       (* arm_UMULH X3 X4 X10 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9b077cab;       (* arm_MUL X11 X5 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7cab;       (* arm_MUL X11 X5 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bca7ca4;       (* arm_UMULH X4 X5 X10 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b077ccb;       (* arm_MUL X11 X6 X7 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b087ccb;       (* arm_MUL X11 X6 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097ccb;       (* arm_MUL X11 X6 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7ccb;       (* arm_MUL X11 X6 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9bca7cc5;       (* arm_UMULH X5 X6 X10 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0xb24101ef;       (* arm_ORR X15 X15 (rvalue (word 9223372036854775808)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b081ceb;       (* arm_MADD X11 X7 X8 X7 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9a9f30e7;       (* arm_CSEL X7 X7 XZR Condition_CC *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0xa900340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&0))) *)
  0xa9013c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_P25519_ALT_EXEC = ARM_MK_EXEC_RULE bignum_mul_p25519_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let BIGNUM_MUL_P25519_ALT_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x194) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p25519_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x190) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_25519)
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                      X13; X14; X15; X16] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_ALT_EXEC (1--67) (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
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

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_ALT_EXEC (68--92) (68--92) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s86:int64) + 1) <= 80 /\
    (val(sum_s86:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s86:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64)) +
        2 EXP 64 * val(mulhi_s69:int64) +
        2 EXP 128 * val(mulhi_s72:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  SUBGOAL_THEN
   `&(val(word(19 + 19 * val(sum_s86:int64)):int64)):real =
    &19 * (&(val(sum_s86:int64)) + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `19 * (x + 1) = 19 + 19 * x`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s86:int64) + 1 <= 80` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_or sum_s82 (word 9223372036854775808:int64))):real =
    &2 pow 63 + &(val(sum_s84:int64)) / &2`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or m (word_and x (word_not m))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and m (word_and x (word_not m)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s86:int64) + val(sum_s84:int64) =
      2 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 pow 256 * (&(bitval carry_s92) - &1:real) +
    &(bignum_of_wordlist[sum_s89; sum_s90; sum_s91; sum_s92]):real =
    &(38 * h + l) - &((val(sum_s86:int64) + 1) * p_25519)`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_ALT_EXEC (93--100) (93--100) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s86:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l < (val(sum_s86:int64) + 1) * p_25519 <=> ~carry_s92`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[REAL_BITVAL_NOT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x - y = &2 pow 256 * c + s`)) THEN
    BOUNDER_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x = &2 pow 256 * c + s + y`)) THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s92:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_MUL_P25519_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x194) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p25519_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory(x,4) s = m /\
                  bignum_from_memory(y,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (m * n) MOD p_25519)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_MUL_P25519_ALT_EXEC BIGNUM_MUL_P25519_ALT_CORRECT);;
