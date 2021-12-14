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

(**** print_literal_from_elf "arm/secp256k1/bignum_mul_p256k1.o";;
 ****)

let bignum_mul_p256k1_mc = define_assert_from_elf "bignum_mul_p256k1_mc" "arm/secp256k1/bignum_mul_p256k1.o"
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
  0xd2807a35;       (* arm_MOV X21 (rvalue (word 977)) *)
  0xb26002b1;       (* arm_ORR X17 X21 (rvalue (word 4294967296)) *)
  0x9b0c7e23;       (* arm_MUL X3 X17 X12 *)
  0x9bcc7e27;       (* arm_UMULH X7 X17 X12 *)
  0x92407db4;       (* arm_AND X20 X13 (rvalue (word 4294967295)) *)
  0xd360fdb3;       (* arm_LSR X19 X13 32 *)
  0x9b147ea4;       (* arm_MUL X4 X21 X20 *)
  0x9b1352b4;       (* arm_MADD X20 X21 X19 X20 *)
  0xab148084;       (* arm_ADDS X4 X4 (Shiftedreg X20 LSL 32) *)
  0xd360fe94;       (* arm_LSR X20 X20 32 *)
  0x9a140268;       (* arm_ADC X8 X19 X20 *)
  0x9b0e7e25;       (* arm_MUL X5 X17 X14 *)
  0x9bce7e29;       (* arm_UMULH X9 X17 X14 *)
  0x92407df4;       (* arm_AND X20 X15 (rvalue (word 4294967295)) *)
  0xd360fdf3;       (* arm_LSR X19 X15 32 *)
  0x9b147ea6;       (* arm_MUL X6 X21 X20 *)
  0x9b1352b4;       (* arm_MADD X20 X21 X19 X20 *)
  0xab1480c6;       (* arm_ADDS X6 X6 (Shiftedreg X20 LSL 32) *)
  0xd360fe94;       (* arm_LSR X20 X20 32 *)
  0x9a14026a;       (* arm_ADC X10 X19 X20 *)
  0xab03016b;       (* arm_ADDS X11 X11 X3 *)
  0xba040210;       (* arm_ADCS X16 X16 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab070210;       (* arm_ADDS X16 X16 X7 *)
  0xba080021;       (* arm_ADCS X1 X1 X8 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0x9a0a018c;       (* arm_ADC X12 X12 X10 *)
  0x9100058f;       (* arm_ADD X15 X12 (rvalue (word 1)) *)
  0x9b0f7ea3;       (* arm_MUL X3 X21 X15 *)
  0xd360fde4;       (* arm_LSR X4 X15 32 *)
  0xab0f8063;       (* arm_ADDS X3 X3 (Shiftedreg X15 LSL 32) *)
  0x9a0403e4;       (* arm_ADC X4 XZR X4 *)
  0xab03016b;       (* arm_ADDS X11 X11 X3 *)
  0xba040210;       (* arm_ADCS X16 X16 X4 *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a9f3231;       (* arm_CSEL X17 X17 XZR Condition_CC *)
  0xeb11016b;       (* arm_SUBS X11 X11 X17 *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xa900400b;       (* arm_STP X11 X16 X0 (Immediate_Offset (iword (&0))) *)
  0xa9010801;       (* arm_STP X1 X2 X0 (Immediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_mul_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

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

let p256k1redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256k1 - 1)
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let BIGNUM_MUL_P256K1_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x2b4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p256k1_mc /\
                  read PC s = word(pc + 0x8) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x2a8) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_256k1)
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_EXEC
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

  (*** Reduction from 8 digits to 5 digits, with fiddly hybrid muls ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_EXEC [126;132;134] (124--134) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s134:int64)) + &(val(sum_s132:int64)):real =
    &4294968273 * &(val(sum_s121:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE o
        fst o chop_list 2) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SYM(DEPTH_CONV WORD_NUM_RED_CONV `word(2 EXP 32 - 1)`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; VAL_WORD; ADD_CLAUSES] THEN
    SIMP_TAC[DIMINDEX_64; VAL_BOUND_64; MOD_LT;
             ARITH_RULE `977 * x MOD 2 EXP 32 < 2 EXP 64`;
             ARITH_RULE `y < 2 EXP 64
                 ==> x MOD 2 EXP 32 + 977 * y DIV 2 EXP 32 < 2 EXP 64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    REWRITE_TAC[ARITH_RULE
     `(2 EXP 32 * x) DIV 2 EXP 64 = x DIV 2 EXP 32`] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST
     (MP_TAC o end_itlist CONJ o rev o  snd o chop_list 2) THEN
    STRIP_TAC THEN DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_EXEC [135; 141; 143] (135--143) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s143:int64)) + &(val(sum_s141:int64)):real =
    &4294968273 * &(val(sum_s123:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE o
        fst o chop_list 2) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SYM(DEPTH_CONV WORD_NUM_RED_CONV `word(2 EXP 32 - 1)`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; VAL_WORD; ADD_CLAUSES] THEN
    SIMP_TAC[DIMINDEX_64; VAL_BOUND_64; MOD_LT;
             ARITH_RULE `977 * x MOD 2 EXP 32 < 2 EXP 64`;
             ARITH_RULE `y < 2 EXP 64
                 ==> x MOD 2 EXP 32 + 977 * y DIV 2 EXP 32 < 2 EXP 64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    REWRITE_TAC[ARITH_RULE
     `(2 EXP 32 * x) DIV 2 EXP 64 = x DIV 2 EXP 32`] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST
     (MP_TAC o end_itlist CONJ o rev o  snd o chop_list 2) THEN
    STRIP_TAC THEN DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_EXEC [144;145;146;147;149;150;151;152]
   (144--152) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s144; sum_s149; sum_s150; sum_s151; sum_s152]` THEN
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

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s152:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN

  ARM_STEPS_TAC BIGNUM_MUL_P256K1_EXEC [153] THEN
  ABBREV_TAC `q:int64 = word_add sum_s152 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s152:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation, with more hybrid mul fiddling ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_EXEC (154--157) (154--157) THEN

  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s157:int64)) + &(val(sum_s156:int64)) =
    &4294968273 * &(val(q:int64))`
  MP_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN EXPAND_TAC "mullo_s154" THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `q <= 2 EXP 33 ==> 977 MOD 2 EXP 64 * q < 2 EXP 64`] THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P256K1_EXEC
    [158;159;160;161;163;164;165;166] (158--168) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s161` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s152:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN
       `word_add sum_s152 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
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
    ASM_CASES_TAC `carry_s161:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_MUL_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,0x2b4) (z,8 * 4) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(x,8 * 4); (y,8 * 4); (z,8 * 4); (word pc,0x2b4)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p256k1_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory(x,4) s = m /\
                  bignum_from_memory(y,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (m * n) MOD p_256k1)
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 32),32)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_P256K1_EXEC BIGNUM_MUL_P256K1_CORRECT
    `[X19;X20;X21;X22]` 32);;
