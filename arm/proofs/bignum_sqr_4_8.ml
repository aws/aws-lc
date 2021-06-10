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
(* 4x4 -> 8 squaring, schoolbook sub-squares plus ADK cross-product.         *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_4_8.o";;
 ****)

let bignum_sqr_4_8_mc = define_assert_from_elf "bignum_sqr_4_8_mc" "arm/fastmul/bignum_sqr_4_8.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xeb030049;       (* arm_SUBS X9 X2 X3 *)
  0xda892529;       (* arm_CNEG X9 X9 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x9b0c7d2d;       (* arm_MUL X13 X9 X12 *)
  0x9bcc7d2c;       (* arm_UMULH X12 X9 X12 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0xab0800c7;       (* arm_ADDS X7 X6 X8 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0x9bc57c69;       (* arm_UMULH X9 X3 X5 *)
  0xab0e00e7;       (* arm_ADDS X7 X7 X14 *)
  0xba090108;       (* arm_ADCS X8 X8 X9 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0e0108;       (* arm_ADDS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xba0c0108;       (* arm_ADCS X8 X8 X12 *)
  0x9a0b0129;       (* arm_ADC X9 X9 X11 *)
  0xab0600c6;       (* arm_ADDS X6 X6 X6 *)
  0xba0700e7;       (* arm_ADCS X7 X7 X7 *)
  0xba080108;       (* arm_ADCS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x9b027c4c;       (* arm_MUL X12 X2 X2 *)
  0x9b037c6d;       (* arm_MUL X13 X3 X3 *)
  0x9b037c4f;       (* arm_MUL X15 X2 X3 *)
  0x9bc27c4b;       (* arm_UMULH X11 X2 X2 *)
  0x9bc37c6e;       (* arm_UMULH X14 X3 X3 *)
  0x9bc37c50;       (* arm_UMULH X16 X2 X3 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9002c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xab0d00c6;       (* arm_ADDS X6 X6 X13 *)
  0xba0e00e7;       (* arm_ADCS X7 X7 X14 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9b057cad;       (* arm_MUL X13 X5 X5 *)
  0x9b057c8f;       (* arm_MUL X15 X4 X5 *)
  0x9bc47c8b;       (* arm_UMULH X11 X4 X4 *)
  0x9bc57cae;       (* arm_UMULH X14 X5 X5 *)
  0x9bc57c90;       (* arm_UMULH X16 X4 X5 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0xba09016b;       (* arm_ADCS X11 X11 X9 *)
  0xa9022c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa903380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&48))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_4_8_EXEC = ARM_MK_EXEC_RULE bignum_sqr_4_8_mc;;

(* ------------------------------------------------------------------------- *)
(* Lemmas to halve the number of case splits, useful for efficiency.         *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQR_4_8_CORRECT = prove
 (`!z x a pc.
      nonoverlapping (word pc,0x118) (z,8 * 8)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_4_8_mc /\
                 read PC s = word pc /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,4) s = a)
          (\s. read PC s = word (pc + 0x114) /\
               bignum_from_memory (z,8) s = a EXP 2)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
             MAYCHANGE [memory :> bytes(z,8 * 8)] ,,
             MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQR_4_8_EXEC
   ([3; 4; 11; 16; 17; 19; 20; 21; 22; 23] @ (25--35) @
    (39--44) @ (46--50) @ [52;53;54] @ (58--65) @ [67;68])
   (1--69) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_SQR_4_8_SUBROUTINE_CORRECT = prove
 (`!z x a pc returnaddress.
      nonoverlapping (word pc,0x118) (z,8 * 8)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_4_8_mc /\
                 read PC s = word pc /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,4) s = a)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,8) s = a EXP 2)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
             MAYCHANGE [memory :> bytes(z,8 * 8)] ,,
             MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_SQR_4_8_EXEC BIGNUM_SQR_4_8_CORRECT);;
