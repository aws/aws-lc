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
(* Multiplication modulo p_25519, the field characteristic for curve25519.   *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/curve25519/bignum_mul_p25519.o";;
 ****)

let bignum_mul_p25519_mc = define_assert_from_elf "bignum_mul_p25519_mc" "arm/curve25519/bignum_mul_p25519.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8c;       (* arm_MUL X12 X4 X8 *)
  0x9b097cad;       (* arm_MUL X13 X5 X9 *)
  0x9b0a7cce;       (* arm_MUL X14 X6 X10 *)
  0x9bc77c6f;       (* arm_UMULH X15 X3 X7 *)
  0xab0f018c;       (* arm_ADDS X12 X12 X15 *)
  0x9bc87c8f;       (* arm_UMULH X15 X4 X8 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0x9bc97caf;       (* arm_UMULH X15 X5 X9 *)
  0xba0f01ce;       (* arm_ADCS X14 X14 X15 *)
  0x9bca7ccf;       (* arm_UMULH X15 X6 X10 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xab0b0190;       (* arm_ADDS X16 X12 X11 *)
  0xba0c01ac;       (* arm_ADCS X12 X13 X12 *)
  0xba0d01cd;       (* arm_ADCS X13 X14 X13 *)
  0xba0e01ee;       (* arm_ADCS X14 X15 X14 *)
  0x9a0f03ef;       (* arm_ADC X15 XZR X15 *)
  0xab0b0181;       (* arm_ADDS X1 X12 X11 *)
  0xba1001a2;       (* arm_ADCS X2 X13 X16 *)
  0xba0c01cc;       (* arm_ADCS X12 X14 X12 *)
  0xba0d01ed;       (* arm_ADCS X13 X15 X13 *)
  0xba0e03ee;       (* arm_ADCS X14 XZR X14 *)
  0x9a0f03ef;       (* arm_ADC X15 XZR X15 *)
  0xeb0600b5;       (* arm_SUBS X21 X5 X6 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xeb090153;       (* arm_SUBS X19 X10 X9 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0x9b137eb4;       (* arm_MUL X20 X21 X19 *)
  0x9bd37eb3;       (* arm_UMULH X19 X21 X19 *)
  0xda912231;       (* arm_CINV X17 X17 Condition_CC *)
  0xb100063f;       (* arm_CMN X17 (rvalue (word 1)) *)
  0xca110294;       (* arm_EOR X20 X20 X17 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xca110273;       (* arm_EOR X19 X19 X17 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0x9a1101ef;       (* arm_ADC X15 X15 X17 *)
  0xeb040075;       (* arm_SUBS X21 X3 X4 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xeb070113;       (* arm_SUBS X19 X8 X7 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0x9b137eb4;       (* arm_MUL X20 X21 X19 *)
  0x9bd37eb3;       (* arm_UMULH X19 X21 X19 *)
  0xda912231;       (* arm_CINV X17 X17 Condition_CC *)
  0xb100063f;       (* arm_CMN X17 (rvalue (word 1)) *)
  0xca110294;       (* arm_EOR X20 X20 X17 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xca110273;       (* arm_EOR X19 X19 X17 *)
  0xba130021;       (* arm_ADCS X1 X1 X19 *)
  0xba110042;       (* arm_ADCS X2 X2 X17 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1101ce;       (* arm_ADCS X14 X14 X17 *)
  0x9a1101ef;       (* arm_ADC X15 X15 X17 *)
  0xeb060095;       (* arm_SUBS X21 X4 X6 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xeb080153;       (* arm_SUBS X19 X10 X8 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0x9b137eb4;       (* arm_MUL X20 X21 X19 *)
  0x9bd37eb3;       (* arm_UMULH X19 X21 X19 *)
  0xda912231;       (* arm_CINV X17 X17 Condition_CC *)
  0xb100063f;       (* arm_CMN X17 (rvalue (word 1)) *)
  0xca110294;       (* arm_EOR X20 X20 X17 *)
  0xba14018c;       (* arm_ADCS X12 X12 X20 *)
  0xca110273;       (* arm_EOR X19 X19 X17 *)
  0xba1301ad;       (* arm_ADCS X13 X13 X19 *)
  0xba1101ce;       (* arm_ADCS X14 X14 X17 *)
  0x9a1101ef;       (* arm_ADC X15 X15 X17 *)
  0xeb050075;       (* arm_SUBS X21 X3 X5 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xeb070133;       (* arm_SUBS X19 X9 X7 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0x9b137eb4;       (* arm_MUL X20 X21 X19 *)
  0x9bd37eb3;       (* arm_UMULH X19 X21 X19 *)
  0xda912231;       (* arm_CINV X17 X17 Condition_CC *)
  0xb100063f;       (* arm_CMN X17 (rvalue (word 1)) *)
  0xca110294;       (* arm_EOR X20 X20 X17 *)
  0xba140021;       (* arm_ADCS X1 X1 X20 *)
  0xca110273;       (* arm_EOR X19 X19 X17 *)
  0xba130042;       (* arm_ADCS X2 X2 X19 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1101ce;       (* arm_ADCS X14 X14 X17 *)
  0x9a1101ef;       (* arm_ADC X15 X15 X17 *)
  0xeb060075;       (* arm_SUBS X21 X3 X6 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xeb070153;       (* arm_SUBS X19 X10 X7 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0x9b137eb4;       (* arm_MUL X20 X21 X19 *)
  0x9bd37eb3;       (* arm_UMULH X19 X21 X19 *)
  0xda912231;       (* arm_CINV X17 X17 Condition_CC *)
  0xb100063f;       (* arm_CMN X17 (rvalue (word 1)) *)
  0xca110294;       (* arm_EOR X20 X20 X17 *)
  0xba140042;       (* arm_ADCS X2 X2 X20 *)
  0xca110273;       (* arm_EOR X19 X19 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1101ce;       (* arm_ADCS X14 X14 X17 *)
  0x9a1101ef;       (* arm_ADC X15 X15 X17 *)
  0xeb050095;       (* arm_SUBS X21 X4 X5 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xeb080133;       (* arm_SUBS X19 X9 X8 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0x9b137eb4;       (* arm_MUL X20 X21 X19 *)
  0x9bd37eb3;       (* arm_UMULH X19 X21 X19 *)
  0xda912231;       (* arm_CINV X17 X17 Condition_CC *)
  0xb100063f;       (* arm_CMN X17 (rvalue (word 1)) *)
  0xca110294;       (* arm_EOR X20 X20 X17 *)
  0xba140042;       (* arm_ADCS X2 X2 X20 *)
  0xca110273;       (* arm_EOR X19 X19 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1101ce;       (* arm_ADCS X14 X14 X17 *)
  0x9a1101ef;       (* arm_ADC X15 X15 X17 *)
  0xd28004d1;       (* arm_MOV X17 (rvalue (word 38)) *)
  0x92407d94;       (* arm_AND X20 X12 (rvalue (word 4294967295)) *)
  0xd360fd93;       (* arm_LSR X19 X12 32 *)
  0x9b147e34;       (* arm_MUL X20 X17 X20 *)
  0x9b137e33;       (* arm_MUL X19 X17 X19 *)
  0xab14016b;       (* arm_ADDS X11 X11 X20 *)
  0x92407db4;       (* arm_AND X20 X13 (rvalue (word 4294967295)) *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9b147e34;       (* arm_MUL X20 X17 X20 *)
  0x9b0d7e2d;       (* arm_MUL X13 X17 X13 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x92407dd4;       (* arm_AND X20 X14 (rvalue (word 4294967295)) *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9b147e34;       (* arm_MUL X20 X17 X20 *)
  0x9b0e7e2e;       (* arm_MUL X14 X17 X14 *)
  0xba140021;       (* arm_ADCS X1 X1 X20 *)
  0x92407df4;       (* arm_AND X20 X15 (rvalue (word 4294967295)) *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x9b147e34;       (* arm_MUL X20 X17 X20 *)
  0x9b0f7e2f;       (* arm_MUL X15 X17 X15 *)
  0xba140042;       (* arm_ADCS X2 X2 X20 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xd3607e74;       (* arm_LSL X20 X19 32 *)
  0xab14016b;       (* arm_ADDS X11 X11 X20 *)
  0x93d381b4;       (* arm_EXTR X20 X13 X19 32 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x93cd81d4;       (* arm_EXTR X20 X14 X13 32 *)
  0xba140021;       (* arm_ADCS X1 X1 X20 *)
  0x93ce81f4;       (* arm_EXTR X20 X15 X14 32 *)
  0xba140042;       (* arm_ADCS X2 X2 X20 *)
  0xd360fdf4;       (* arm_LSR X20 X15 32 *)
  0x9a14018c;       (* arm_ADC X12 X12 X20 *)
  0xab02005f;       (* arm_CMN X2 X2 *)
  0xb2410042;       (* arm_ORR X2 X2 (rvalue (word 9223372036854775808)) *)
  0x9a0c018f;       (* arm_ADC X15 X12 X12 *)
  0xd2800271;       (* arm_MOV X17 (rvalue (word 19)) *)
  0x9b0f4634;       (* arm_MADD X20 X17 X15 X17 *)
  0xab14016b;       (* arm_ADDS X11 X11 X20 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a9f3231;       (* arm_CSEL X17 X17 XZR Condition_CC *)
  0xeb11016b;       (* arm_SUBS X11 X11 X17 *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0x9240f842;       (* arm_AND X2 X2 (rvalue (word 9223372036854775807)) *)
  0xa900400b;       (* arm_STP X11 X16 X0 (Immediate_Offset (iword (&0))) *)
  0xa9010801;       (* arm_STP X1 X2 X0 (Immediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_P25519_EXEC = ARM_MK_EXEC_RULE bignum_mul_p25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 2 EXP 255 - 19`;;

let lemma1 = prove
 (`!(x0:num) x1 (y0:num) y1.
       (if y0 <= y1
        then if x1 <= x0 then word 0 else word 18446744073709551615
        else word_not
         (if x1 <= x0 then word 0 else word 18446744073709551615)):int64 =
   word_neg(word(bitval(y0 <= y1 <=> x0 < x1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let lemma2 = prove
 (`!(x0:int64) (x1:int64) (y0:int64) (y1:int64).
        &(val(if val x1 <= val x0 then word_sub x0 x1
              else word_neg (word_sub x0 x1))) *
        &(val(if val y0 <= val y1 then word_sub y1 y0
              else word_neg (word_sub y1 y0))):real =
        --(&1) pow bitval(val y0 <= val y1 <=> val x0 < val x1) *
        (&(val x0) - &(val x1)) * (&(val y1) - &(val y0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE; WORD_NEG_SUB] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(m:num <= n) ==> n <= m /\ ~(m <= n)`))) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let shiftandlemma = prove
 (`!x:int64. &(val(word_and x (word 4294967295))):real =
             &(val x) - &2 pow 32 * &(val(word_ushr x 32))`,
  GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[val_def; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ARITH_TAC);;

let BIGNUM_MUL_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x2c4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p25519_mc /\
                  read PC s = word(pc + 0x8) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x2b8) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_25519)
         (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                     X13; X14; X15; X16; X17; X19; X20; X21] ,,
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC
   [5; 6; 7; 8; 10; 12; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24;
    25; 26; 27; 33; 38; 40; 41; 47; 52; 54; 55; 56; 57; 58; 59;
    65; 70; 72; 73; 74; 80; 85; 87; 88; 89; 90; 91; 97; 102;
    104; 105; 106; 107; 113; 118; 120; 121; 122; 123]
   (1--123) THEN

  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s5; sum_s52; sum_s85; sum_s118]`;
    `h = bignum_of_wordlist[sum_s120; sum_s121; sum_s122; sum_s123]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT]) THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter(is_ratconst o rand o concl) o
               DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC
   [127;128;129;132;133;134;137;138;139;142;143;144;147;149;151;153;155]
   (124--155) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s147; sum_s149; sum_s151; sum_s153; sum_s155]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN

    TRANS_TAC EQ_TRANS
     `bignum_of_wordlist[sum_s129; sum_s134; sum_s139; sum_s144;
                       word(bitval carry_s144)] +
      2 EXP 32 *
      bignum_of_wordlist[mullo_s128; mullo_s133; mullo_s138; mullo_s143]` THEN
    CONJ_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THENL
     [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 snd o chop_list 5);
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 fst o chop_list 5)] THEN
    REWRITE_TAC[shiftandlemma] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_0] THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ARITH
      `x + --c * y:real = z <=> x = c * y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM ADD_ASSOC] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LT; ARITH_LE] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`; MOD_MULT2] THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC (156--158) (156--158) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s147; sum_s149; sum_s151;
    word_or sum_s153 (word 9223372036854775808)]` THEN
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
    SUBGOAL_THEN `bignum_of_wordlist [sum_s147; sum_s149; sum_s151] < 2 EXP 192`
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
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s158:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s156; sum_s158] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC BIGNUM_MUL_P25519_EXEC (159--160) THEN
  ABBREV_TAC `qm:int64 = word(19 + 19 * val(sum_s158:int64))` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(sum_s158:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `c + c * q = c * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s158:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC (161--172) (161--172) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s158:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(sum_s158:int64) + 1) * p_25519 <=> ~carry_s164`
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
    ASM_CASES_TAC `carry_s164:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_MUL_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,0x2c4) (z,8 * 4) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(x,8 * 4); (y,8 * 4); (z,8 * 4); (word pc,0x2c4)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p25519_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory(x,4) s = m /\
                  bignum_from_memory(y,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (m * n) MOD p_25519)
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 32),32)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_P25519_EXEC BIGNUM_MUL_P25519_CORRECT
    `[X19;X20;X21;X22]` 32);;
