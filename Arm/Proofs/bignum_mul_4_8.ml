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
(* 4x4 -> 8 multiply (arbitrary degree Karatsuba even at this small size).   *)
(* ========================================================================= *)

(**** print_literal_from_elf "Arm/fastmul/bignum_mul_4_8.o";;
 ****)

let bignum_mul_4_8_mc = define_assert_from_elf "bignum_mul_4_8_mc" "Arm/fastmul/bignum_mul_4_8.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
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
  0xf900000b;       (* arm_STR X11 X0 (Immediate_Offset (word 0)) *)
  0xab0b0181;       (* arm_ADDS X1 X12 X11 *)
  0xba1001a2;       (* arm_ADCS X2 X13 X16 *)
  0xba0c01cc;       (* arm_ADCS X12 X14 X12 *)
  0xba0d01ed;       (* arm_ADCS X13 X15 X13 *)
  0xba0e03ee;       (* arm_ADCS X14 XZR X14 *)
  0x9a0f03ef;       (* arm_ADC X15 XZR X15 *)
  0xeb0600b4;       (* arm_SUBS X20 X5 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb090151;       (* arm_SUBS X17 X10 X9 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117e93;       (* arm_MUL X19 X20 X17 *)
  0x9bd17e91;       (* arm_UMULH X17 X20 X17 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xca0b0273;       (* arm_EOR X19 X19 X11 *)
  0xba1301ad;       (* arm_ADCS X13 X13 X19 *)
  0xca0b0231;       (* arm_EOR X17 X17 X11 *)
  0xba1101ce;       (* arm_ADCS X14 X14 X17 *)
  0x9a0b01ef;       (* arm_ADC X15 X15 X11 *)
  0xeb040074;       (* arm_SUBS X20 X3 X4 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb070111;       (* arm_SUBS X17 X8 X7 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117e93;       (* arm_MUL X19 X20 X17 *)
  0x9bd17e91;       (* arm_UMULH X17 X20 X17 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xca0b0273;       (* arm_EOR X19 X19 X11 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0xca0b0231;       (* arm_EOR X17 X17 X11 *)
  0xba110021;       (* arm_ADCS X1 X1 X17 *)
  0xf9000410;       (* arm_STR X16 X0 (Immediate_Offset (word 8)) *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a0b01ef;       (* arm_ADC X15 X15 X11 *)
  0xeb060094;       (* arm_SUBS X20 X4 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb080151;       (* arm_SUBS X17 X10 X8 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117e93;       (* arm_MUL X19 X20 X17 *)
  0x9bd17e91;       (* arm_UMULH X17 X20 X17 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xca0b0273;       (* arm_EOR X19 X19 X11 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xca0b0231;       (* arm_EOR X17 X17 X11 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a0b01ef;       (* arm_ADC X15 X15 X11 *)
  0xeb050074;       (* arm_SUBS X20 X3 X5 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb070131;       (* arm_SUBS X17 X9 X7 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117e93;       (* arm_MUL X19 X20 X17 *)
  0x9bd17e91;       (* arm_UMULH X17 X20 X17 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xca0b0273;       (* arm_EOR X19 X19 X11 *)
  0xba130021;       (* arm_ADCS X1 X1 X19 *)
  0xca0b0231;       (* arm_EOR X17 X17 X11 *)
  0xba110042;       (* arm_ADCS X2 X2 X17 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a0b01ef;       (* arm_ADC X15 X15 X11 *)
  0xeb060074;       (* arm_SUBS X20 X3 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb070151;       (* arm_SUBS X17 X10 X7 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117e93;       (* arm_MUL X19 X20 X17 *)
  0x9bd17e91;       (* arm_UMULH X17 X20 X17 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xca0b0273;       (* arm_EOR X19 X19 X11 *)
  0xba130042;       (* arm_ADCS X2 X2 X19 *)
  0xca0b0231;       (* arm_EOR X17 X17 X11 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a0b01ef;       (* arm_ADC X15 X15 X11 *)
  0xeb050094;       (* arm_SUBS X20 X4 X5 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb080131;       (* arm_SUBS X17 X9 X8 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0x9b117e93;       (* arm_MUL X19 X20 X17 *)
  0x9bd17e91;       (* arm_UMULH X17 X20 X17 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xca0b0273;       (* arm_EOR X19 X19 X11 *)
  0xba130042;       (* arm_ADCS X2 X2 X19 *)
  0xca0b0231;       (* arm_EOR X17 X17 X11 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a0b01ef;       (* arm_ADC X15 X15 X11 *)
  0xa9010801;       (* arm_STP X1 X2 X0 (Immediate_Offset (iword (&16))) *)
  0xa902340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&32))) *)
  0xa9033c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&48))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_4_8_EXEC = ARM_MK_EXEC_RULE bignum_mul_4_8_mc;;

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
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUL_4_8_CORRECT = prove
 (`!z x y a b pc.
      nonoverlapping (word pc,0x20c) (z,8 * 8)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_mul_4_8_mc /\
                 read PC s = word(pc + 0x04) /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,4) s = a /\
                 bignum_from_memory (y,4) s = b)
            (\s. read PC s = word (pc + 0x204) /\
                 bignum_from_memory (z,8) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                        X12; X13; X14; X15; X16; X17; X19; X20] ,,
             MAYCHANGE [memory :> bytes(z,8 * 8)] ,,
             MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_4_8_EXEC
   [5;6;7;8;10;12;14;16;17;18;19;20;21;23;24;25;26;27;28;34;39;
    41;42;48;53;55;57;58;59;60;61;67;72;74;75;76;82;87;89;90;91;
    92;93;99;104;106;107;108;109;115;120;122;123;124;125]
   (1--128) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC; ALL_TAC]) THEN
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
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MUL_4_8_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,0x20c) (z,8 * 8) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,0x20c); (x,8 * 4); (y,8 * 4); (z,8 * 8)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_mul_4_8_mc /\
                   read PC s = word pc /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [z; x; y] s /\
                   bignum_from_memory (x,4) s = a /\
                   bignum_from_memory (y,4) s = b)
              (\s. read PC s = returnaddress /\
                   bignum_from_memory (z,8) s = a * b)
              (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                          X12; X13; X14; X15; X16; X17] ,,
               MAYCHANGE [memory :> bytes(z,8 * 8);
                       memory :> bytes(word_sub stackpointer (word 16),16)] ,,
               MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_4_8_EXEC BIGNUM_MUL_4_8_CORRECT
   `[X19;X20]` 16);;
