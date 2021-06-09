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
(* Almost-Montgomery squaring modulo p_256.                                  *)
(* ========================================================================= *)

(**** print_literal_from_elf "Arm/p256/bignum_amontsqr_p256.o";;
 ****)

let bignum_amontsqr_p256_mc =
  define_assert_from_elf "bignum_amontsqr_p256_mc" "Arm/p256/bignum_amontsqr_p256.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b027c4f;       (* arm_MUL X15 X2 X2 *)
  0x9b037c71;       (* arm_MUL X17 X3 X3 *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc27c50;       (* arm_UMULH X16 X2 X2 *)
  0x9bc37c61;       (* arm_UMULH X1 X3 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xd3607dec;       (* arm_LSL X12 X15 (rvalue (word 32)) *)
  0xeb0c01ed;       (* arm_SUBS X13 X15 X12 *)
  0xd360fdeb;       (* arm_LSR X11 X15 (rvalue (word 32)) *)
  0xda0b01ef;       (* arm_SBC X15 X15 X11 *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0xba0d0021;       (* arm_ADCS X1 X1 X13 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xd3607e0c;       (* arm_LSL X12 X16 (rvalue (word 32)) *)
  0xeb0c020d;       (* arm_SUBS X13 X16 X12 *)
  0xd360fe0b;       (* arm_LSR X11 X16 (rvalue (word 32)) *)
  0xda0b0210;       (* arm_SBC X16 X16 X11 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0xba0d01ef;       (* arm_ADCS X15 X15 X13 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xeb03004a;       (* arm_SUBS X10 X2 X3 *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0xda9f23ed;       (* arm_CSETM X13 Condition_CC *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x9b0c7d4b;       (* arm_MUL X11 X10 X12 *)
  0x9bcc7d4c;       (* arm_UMULH X12 X10 X12 *)
  0xda8d21ad;       (* arm_CINV X13 X13 Condition_CC *)
  0xca0d016b;       (* arm_EOR X11 X11 X13 *)
  0xca0d018c;       (* arm_EOR X12 X12 X13 *)
  0xab0800c7;       (* arm_ADDS X7 X6 X8 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0x9bc57c69;       (* arm_UMULH X9 X3 X5 *)
  0xab0e00e7;       (* arm_ADDS X7 X7 X14 *)
  0xba090108;       (* arm_ADCS X8 X8 X9 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0e0108;       (* arm_ADDS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xb10005bf;       (* arm_CMN X13 (rvalue (word 1)) *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0xba0c0108;       (* arm_ADCS X8 X8 X12 *)
  0x9a0d0129;       (* arm_ADC X9 X9 X13 *)
  0xab0600c6;       (* arm_ADDS X6 X6 X6 *)
  0xba0700e7;       (* arm_ADCS X7 X7 X7 *)
  0xba080108;       (* arm_ADCS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xab1100c6;       (* arm_ADDS X6 X6 X17 *)
  0xba0100e7;       (* arm_ADCS X7 X7 X1 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xd3607ccc;       (* arm_LSL X12 X6 (rvalue (word 32)) *)
  0xeb0c00cd;       (* arm_SUBS X13 X6 X12 *)
  0xd360fccb;       (* arm_LSR X11 X6 (rvalue (word 32)) *)
  0xda0b00c6;       (* arm_SBC X6 X6 X11 *)
  0xab0c00e7;       (* arm_ADDS X7 X7 X12 *)
  0xba0b0108;       (* arm_ADCS X8 X8 X11 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xd3607cec;       (* arm_LSL X12 X7 (rvalue (word 32)) *)
  0xeb0c00ed;       (* arm_SUBS X13 X7 X12 *)
  0xd360fceb;       (* arm_LSR X11 X7 (rvalue (word 32)) *)
  0xda0b00e7;       (* arm_SBC X7 X7 X11 *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0b0129;       (* arm_ADCS X9 X9 X11 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba0700c6;       (* arm_ADCS X6 X6 X7 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0x9b047c8b;       (* arm_MUL X11 X4 X4 *)
  0xab0b0108;       (* arm_ADDS X8 X8 X11 *)
  0x9b057cac;       (* arm_MUL X12 X5 X5 *)
  0x9bc47c8b;       (* arm_UMULH X11 X4 X4 *)
  0xba0b0129;       (* arm_ADCS X9 X9 X11 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0x9bc57cac;       (* arm_UMULH X12 X5 X5 *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0x9bc57c8c;       (* arm_UMULH X12 X4 X5 *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0x9a1f03ed;       (* arm_ADC X13 XZR XZR *)
  0xab0b0129;       (* arm_ADDS X9 X9 X11 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xcb0703e7;       (* arm_NEG X7 X7 *)
  0xeb070108;       (* arm_SUBS X8 X8 X7 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0x8a07016b;       (* arm_AND X11 X11 X7 *)
  0xfa0b0129;       (* arm_SBCS X9 X9 X11 *)
  0xb26083ec;       (* arm_MOV X12 (rvalue (word 18446744069414584321)) *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0x8a07018c;       (* arm_AND X12 X12 X7 *)
  0xda0c00c6;       (* arm_SBC X6 X6 X12 *)
  0xa9002408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa901180a;       (* arm_STP X10 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_AMONTSQR_P256_EXEC = ARM_MK_EXEC_RULE bignum_amontsqr_p256_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

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

let BIGNUM_AMONTSQR_P256_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x1c4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontsqr_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x1c0) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Squaring and partial Montgomery reduction of lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_AMONTSQR_P256_EXEC (1--30) (1--30) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s27; sum_s28; sum_s29; sum_s30] =
    bignum_of_wordlist[x_0;x_1] EXP 2 +
    p_256 * bignum_of_wordlist[mullo_s3; sum_s19]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_AMONTSQR_P256_EXEC
   [31;32;39;44;45;47;48;49;50;51;53;54;55] (31--55) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s31; sum_s53; sum_s54; sum_s55] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Remaining Montgomery reduction and addition of remaining high terms ***)

  ARM_ACCSTEPS_TAC BIGNUM_AMONTSQR_P256_EXEC (56--101) (56--101) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
        [sum_s85; sum_s98; sum_s99; sum_s100; sum_s101]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_256 /\ (2 EXP 256 * t == a EXP 2) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 256 * t =
      a EXP 2 +
      p_256 * bignum_of_wordlist [mullo_s3; sum_s19; sum_s61; sum_s70]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
       `(bignum_of_wordlist[x_0;x_1] EXP 2 +
         p_256 * bignum_of_wordlist[mullo_s3; sum_s19]) +
        2 * 2 EXP 128 *
            bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3] +
        2 EXP 256 * bignum_of_wordlist[x_2;x_3] EXP 2 +
        2 EXP 128 * p_256 * bignum_of_wordlist [sum_s61; sum_s70]` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o
                           RAND_CONV o RAND_CONV) [SYM th]);
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      MATCH_MP_TAC(ARITH_RULE `2 EXP 256 * x < 2 EXP 256 * y ==> x < y`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
      BOUNDER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN
  SUBGOAL_THEN `sum_s101:int64 = word(bitval(2 EXP 256 <= t))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 EXP 256 + p_256` THEN
      REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC];
    ABBREV_TAC `b <=> 2 EXP 256 <= t`] THEN

  ARM_ACCSTEPS_TAC BIGNUM_AMONTSQR_P256_EXEC [103;106;108;110] (102--112) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * a EXP 2) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval b` THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
   [EXPAND_TAC "b" THEN UNDISCH_TAC `t < 2 EXP 256 + p_256` THEN
    REWRITE_TAC[bitval; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES; p_256] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTSQR_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x1c4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontsqr_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_256 (2 EXP 256) * a EXP 2) (mod p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_AMONTSQR_P256_EXEC
    BIGNUM_AMONTSQR_P256_CORRECT);;
