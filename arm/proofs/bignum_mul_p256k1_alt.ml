(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Multiplication modulo p_256k1, the field characteristic for secp256k1.    *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/secp256k1/bignum_mul_p256k1_alt.o";;
 ****)

let bignum_mul_p256k1_alt_mc = define_assert_from_elf "bignum_mul_p256k1_alt_mc" "arm/secp256k1/bignum_mul_p256k1_alt.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077c6d;       (* arm_MUL X13 X3 X7 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0x9b087c6c;       (* arm_MUL X12 X3 X8 *)
  0x9bc87c6f;       (* arm_UMULH X15 X3 X8 *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b097c6c;       (* arm_MUL X12 X3 X9 *)
  0x9bc97c70;       (* arm_UMULH X16 X3 X9 *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0x9b0a7c6c;       (* arm_MUL X12 X3 X10 *)
  0x9bca7c63;       (* arm_UMULH X3 X3 X10 *)
  0xba0c0210;       (* arm_ADCS X16 X16 X12 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077c8c;       (* arm_MUL X12 X4 X7 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8c;       (* arm_MUL X12 X4 X8 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8c;       (* arm_MUL X12 X4 X9 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7c8c;       (* arm_MUL X12 X4 X10 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0x9a1f0164;       (* arm_ADC X4 X11 XZR *)
  0x9b077cac;       (* arm_MUL X12 X5 X7 *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087cac;       (* arm_MUL X12 X5 X8 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b097cac;       (* arm_MUL X12 X5 X9 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9b0a7cac;       (* arm_MUL X12 X5 X10 *)
  0x9bca7cab;       (* arm_UMULH X11 X5 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0084;       (* arm_ADDS X4 X4 X12 *)
  0x9a1f0165;       (* arm_ADC X5 X11 XZR *)
  0x9b077ccc;       (* arm_MUL X12 X6 X7 *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9b097ccc;       (* arm_MUL X12 X6 X9 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0084;       (* arm_ADDS X4 X4 X12 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9b0a7ccc;       (* arm_MUL X12 X6 X10 *)
  0x9bca7ccb;       (* arm_UMULH X11 X6 X10 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c00a5;       (* arm_ADDS X5 X5 X12 *)
  0x9a1f0166;       (* arm_ADC X6 X11 XZR *)
  0xd2807a27;       (* arm_MOV X7 (rvalue (word 977)) *)
  0xb26000e7;       (* arm_ORR X7 X7 (rvalue (word 4294967296)) *)
  0x9b037cec;       (* arm_MUL X12 X7 X3 *)
  0x9bc37ceb;       (* arm_UMULH X11 X7 X3 *)
  0xab0c01ad;       (* arm_ADDS X13 X13 X12 *)
  0x9b047cec;       (* arm_MUL X12 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0c01ce;       (* arm_ADCS X14 X14 X12 *)
  0x9b057cec;       (* arm_MUL X12 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0x9b067cec;       (* arm_MUL X12 X7 X6 *)
  0x9bc67ce6;       (* arm_UMULH X6 X7 X6 *)
  0xba0c0210;       (* arm_ADCS X16 X16 X12 *)
  0x9a9f37e3;       (* arm_CSET X3 Condition_CS *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0xba0401ef;       (* arm_ADCS X15 X15 X4 *)
  0xba050210;       (* arm_ADCS X16 X16 X5 *)
  0x9a060063;       (* arm_ADC X3 X3 X6 *)
  0x91000468;       (* arm_ADD X8 X3 (rvalue (word 1)) *)
  0x9b087cec;       (* arm_MUL X12 X7 X8 *)
  0x9bc87ceb;       (* arm_UMULH X11 X7 X8 *)
  0xab0c01ad;       (* arm_ADDS X13 X13 X12 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0x9a9f30e7;       (* arm_CSEL X7 X7 XZR Condition_CC *)
  0xeb0701ad;       (* arm_SUBS X13 X13 X7 *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xa900380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&0))) *)
  0xa901400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_P256K1_ALT_EXEC = ARM_MK_EXEC_RULE bignum_mul_p256k1_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let p256k1redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256k1 - 1)
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let BIGNUM_MUL_P256K1_ALT_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x1ac) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p256k1_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x1a8) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_256k1)
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                      X13; X14; X15; X16] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8 ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_ALT_EXEC (1--73) (1--73) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s19; sum_s38; sum_s57]`;
    `h = bignum_of_wordlist[sum_s62; sum_s67; sum_s72; sum_s73]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_256k1 = (4294968273 * h + l) MOD p_256k1`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `4294968273 * h + l` p256k1redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_256k1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_ALT_EXEC (74--92) (74--92) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s78; sum_s89; sum_s90; sum_s91; sum_s92]` THEN
  SUBGOAL_THEN `(4294968273 * h + l) DIV 2 EXP 256 + 1 <= 2 EXP 33`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `4294968273 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s92:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN
  ARM_STEPS_TAC BIGNUM_MUL_P256K1_ALT_EXEC [93] THEN
  ABBREV_TAC `q:int64 = word_add sum_s92 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s92:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_ALT_EXEC (94--106) (94--106) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s99` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s92:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN
       `word_add sum_s92 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s99:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_MUL_P256K1_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x1ac) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p256k1_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory(x,4) s = m /\
                  bignum_from_memory(y,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (m * n) MOD p_256k1)
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_MUL_P256K1_ALT_EXEC BIGNUM_MUL_P256K1_ALT_CORRECT);;
