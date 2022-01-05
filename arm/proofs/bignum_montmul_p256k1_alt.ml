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
(* Montgomery multiply mod p_256k1, the field characteristic for secp256k1.  *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/secp256k1/bignum_montmul_p256k1_alt.o";;
 ****)

let bignum_montmul_p256k1_alt_mc =
  define_assert_from_elf "bignum_montmul_p256k1_alt_mc" "arm/secp256k1/bignum_montmul_p256k1_alt.o"
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
  0xd286a621;       (* arm_MOV X1 (rvalue (word 13617)) *)
  0xf2ba44a1;       (* arm_MOVK X1 (word 53797) 16 *)
  0xf2c123a1;       (* arm_MOVK X1 (word 2333) 32 *)
  0xf2fb0701;       (* arm_MOVK X1 (word 55352) 48 *)
  0xd2807a31;       (* arm_MOV X17 (rvalue (word 977)) *)
  0xb2600231;       (* arm_ORR X17 X17 (rvalue (word 4294967296)) *)
  0x9b0d7c2d;       (* arm_MUL X13 X1 X13 *)
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
  0x9bd17dac;       (* arm_UMULH X12 X13 X17 *)
  0xeb0c01ce;       (* arm_SUBS X14 X14 X12 *)
  0x9a9f27e2;       (* arm_CSET X2 Condition_CC *)
  0x9b077cac;       (* arm_MUL X12 X5 X7 *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087cac;       (* arm_MUL X12 X5 X8 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0x9b0e7c2e;       (* arm_MUL X14 X1 X14 *)
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
  0x9bd17dcc;       (* arm_UMULH X12 X14 X17 *)
  0x8b02018c;       (* arm_ADD X12 X12 X2 *)
  0xeb0c01ef;       (* arm_SUBS X15 X15 X12 *)
  0x9a9f27e2;       (* arm_CSET X2 Condition_CC *)
  0x9b077ccc;       (* arm_MUL X12 X6 X7 *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0063;       (* arm_ADDS X3 X3 X12 *)
  0x9b0f7c2f;       (* arm_MUL X15 X1 X15 *)
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
  0x9bd17dec;       (* arm_UMULH X12 X15 X17 *)
  0x8b02018c;       (* arm_ADD X12 X12 X2 *)
  0xeb0c0210;       (* arm_SUBS X16 X16 X12 *)
  0x9b107c30;       (* arm_MUL X16 X1 X16 *)
  0x9bd17e0c;       (* arm_UMULH X12 X16 X17 *)
  0xfa0c01ad;       (* arm_SBCS X13 X13 X12 *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xab0301ad;       (* arm_ADDS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba0501ef;       (* arm_ADCS X15 X15 X5 *)
  0x8a0f01ca;       (* arm_AND X10 X14 X15 *)
  0xba060210;       (* arm_ADCS X16 X16 X6 *)
  0x8a10014a;       (* arm_AND X10 X10 X16 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xab1101bf;       (* arm_CMN X13 X17 *)
  0xba1f015f;       (* arm_ADCS XZR X10 XZR *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a9f1231;       (* arm_CSEL X17 X17 XZR Condition_NE *)
  0xab1101ad;       (* arm_ADDS X13 X13 X17 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa900380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&0))) *)
  0xa901400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_P256K1_ALT_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p256k1_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(15580212934572586289 * val(x:int64)):int64)) * &4294968273
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(15580212934572586289 * val(x:int64)):int64)) *
            &4294968273`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; VAL_WORD_MUL; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_MONTMUL_P256K1_ALT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x1d0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    bignum_montmul_p256k1_alt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + 0x1cc) /\
                  (a * b <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a * b) MOD p_256k1))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_256k1  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_256k1` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTMUL_P256K1_ALT_EXEC (1--115)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN

  (*** The initial multiply block, very similar to bignum_sqr_4_8_alt ***)
  (*** Cut out initial modular muls in the Montgomery operations ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256K1_ALT_EXEC
   [3;5;7;9;11;12;14;15;24;26;27;28;30;31;32;33;35;36;37;38;
    40;41;42;43;44;46;48;49;50;52;53;55;56;58;59;60;61;63;64;65;
    66;67;68;70;72;73;74;76;77;79;80;82;83;84;85;87;88;89]
   (1--89) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  ABBREV_TAC
   `l = bignum_of_wordlist
         [mullo_s3;sum_s26;sum_s48;sum_s72;
           sum_s77;sum_s83;sum_s88;sum_s89]` THEN
  SUBGOAL_THEN `l = a * b` (SUBST_ALL_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["l"; "a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Now press on with the Montgomery steps ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256K1_ALT_EXEC
   [90;91;92;94;95;96;97;98;99;100;101;103] (90--105) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist[sum_s99; sum_s100; sum_s101; sum_s103;
                           word(bitval(carry_s103))]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256k1 /\ (2 EXP 256 * t == l) (mod p_256k1)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["l"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256k1; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["l"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Condensed comparison ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256K1_ALT_EXEC [106;107;108] (106--109) THEN
  SUBGOAL_THEN
   `val(word_add (word(bitval carry_s103))
                 (word(bitval carry_s107)):int64) = 0 <=>
    t < p_256k1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s103:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 256 <=
      bignum_of_wordlist[sum_s99;sum_s100;sum_s101;sum_s103] + 4294968273` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; p_256k1] THEN ARITH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 128 <=
      bignum_of_wordlist[sum_s99;
             word_and (word_and sum_s100 sum_s101) sum_s103] +
      4294968273` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP 64 /\ (a < 2 EXP 64 - 1 <=> h < 2 EXP 192 - 1) /\
      (~(h < 2 EXP 192 - 1)
       ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
            2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273))
      ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
           2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273)`) THEN
    SIMP_TAC[VAL_BOUND_64; BIGNUM_OF_WORDLIST_LT_MAX; LENGTH;
             ARITH_MULT; ARITH_ADD; ARITH_SUC; EX; DE_MORGAN_THM;
             WORD_BITWISE_RULE
              `word_and a b = word_not(word 0) <=>
               a = word_not(word 0) /\ b = word_not(word 0)`] THEN
    REWRITE_TAC[DISJ_ACI] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P256K1_ALT_EXEC (110--113) (110--115) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256k1` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == l) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * l) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256k1 then &t:real else &t - &p_256k1`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL; VAL_WORD_0] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTMUL_P256K1_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc returnaddress.
        nonoverlapping (word pc,0x1d0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    bignum_montmul_p256k1_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (a * b <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a * b) MOD p_256k1))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_P256K1_ALT_EXEC
    BIGNUM_MONTMUL_P256K1_ALT_CORRECT);;
