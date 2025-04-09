(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 6x6 -> 12 squaring, schoolbook sub-squares plus ADK cross-product.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_6_12.o";;
 ****)

let bignum_sqr_6_12_mc = define_assert_from_elf "bignum_sqr_6_12_mc" "arm/fastmul/bignum_sqr_6_12.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xf9000008;       (* arm_STR X8 X0 (Immediate_Offset (word 0)) *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9bc37c51;       (* arm_UMULH X17 X2 X3 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc47c51;       (* arm_UMULH X17 X2 X4 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc47c71;       (* arm_UMULH X17 X3 X4 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc27c49;       (* arm_UMULH X9 X2 X2 *)
  0x9bc37c6b;       (* arm_UMULH X11 X3 X3 *)
  0x9bc47c8d;       (* arm_UMULH X13 X4 X4 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xf9000409;       (* arm_STR X9 X0 (Immediate_Offset (word 8)) *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xf900080a;       (* arm_STR X10 X0 (Immediate_Offset (word 16)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xf9000c0b;       (* arm_STR X11 X0 (Immediate_Offset (word 24)) *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0xf900100c;       (* arm_STR X12 X0 (Immediate_Offset (word 32)) *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xf900140d;       (* arm_STR X13 X0 (Immediate_Offset (word 40)) *)
  0x9b067cae;       (* arm_MUL X14 X5 X6 *)
  0x9b077caf;       (* arm_MUL X15 X5 X7 *)
  0x9b077cd0;       (* arm_MUL X16 X6 X7 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xf9001808;       (* arm_STR X8 X0 (Immediate_Offset (word 48)) *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0x9b077cec;       (* arm_MUL X12 X7 X7 *)
  0x9bc67cb1;       (* arm_UMULH X17 X5 X6 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc77cb1;       (* arm_UMULH X17 X5 X7 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc77cd1;       (* arm_UMULH X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc57ca9;       (* arm_UMULH X9 X5 X5 *)
  0x9bc67ccb;       (* arm_UMULH X11 X6 X6 *)
  0x9bc77ced;       (* arm_UMULH X13 X7 X7 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xf9001c09;       (* arm_STR X9 X0 (Immediate_Offset (word 56)) *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xf900200a;       (* arm_STR X10 X0 (Immediate_Offset (word 64)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xf900240b;       (* arm_STR X11 X0 (Immediate_Offset (word 72)) *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0xf900280c;       (* arm_STR X12 X0 (Immediate_Offset (word 80)) *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xf9002c0d;       (* arm_STR X13 X0 (Immediate_Offset (word 88)) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c8d;       (* arm_UMULH X13 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba1101ab;       (* arm_ADCS X11 X13 X17 *)
  0x9a1f01ac;       (* arm_ADC X12 X13 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xeb030051;       (* arm_SUBS X17 X2 X3 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500cf;       (* arm_SUBS X15 X6 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040051;       (* arm_SUBS X17 X2 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500ef;       (* arm_SUBS X15 X7 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040071;       (* arm_SUBS X17 X3 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0600ef;       (* arm_SUBS X15 X7 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba0f018c;       (* arm_ADCS X12 X12 X15 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xf9400c02;       (* arm_LDR X2 X0 (Immediate_Offset (word 24)) *)
  0xab080042;       (* arm_ADDS X2 X2 X8 *)
  0xf9000c02;       (* arm_STR X2 X0 (Immediate_Offset (word 24)) *)
  0xf9401002;       (* arm_LDR X2 X0 (Immediate_Offset (word 32)) *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xf9001002;       (* arm_STR X2 X0 (Immediate_Offset (word 32)) *)
  0xf9401402;       (* arm_LDR X2 X0 (Immediate_Offset (word 40)) *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0xf9001402;       (* arm_STR X2 X0 (Immediate_Offset (word 40)) *)
  0xf9401802;       (* arm_LDR X2 X0 (Immediate_Offset (word 48)) *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0xf9001802;       (* arm_STR X2 X0 (Immediate_Offset (word 48)) *)
  0xf9401c02;       (* arm_LDR X2 X0 (Immediate_Offset (word 56)) *)
  0xba0c0042;       (* arm_ADCS X2 X2 X12 *)
  0xf9001c02;       (* arm_STR X2 X0 (Immediate_Offset (word 56)) *)
  0xf9402002;       (* arm_LDR X2 X0 (Immediate_Offset (word 64)) *)
  0xba0d0042;       (* arm_ADCS X2 X2 X13 *)
  0xf9002002;       (* arm_STR X2 X0 (Immediate_Offset (word 64)) *)
  0xf9402402;       (* arm_LDR X2 X0 (Immediate_Offset (word 72)) *)
  0xba110042;       (* arm_ADCS X2 X2 X17 *)
  0xf9002402;       (* arm_STR X2 X0 (Immediate_Offset (word 72)) *)
  0xf9402802;       (* arm_LDR X2 X0 (Immediate_Offset (word 80)) *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xf9002802;       (* arm_STR X2 X0 (Immediate_Offset (word 80)) *)
  0xf9402c02;       (* arm_LDR X2 X0 (Immediate_Offset (word 88)) *)
  0x9a1f0042;       (* arm_ADC X2 X2 XZR *)
  0xf9002c02;       (* arm_STR X2 X0 (Immediate_Offset (word 88)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_6_12_EXEC = ARM_MK_EXEC_RULE bignum_sqr_6_12_mc;;

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

let BIGNUM_SQR_6_12_CORRECT = prove
 (`!z x a pc.
      nonoverlapping (word pc,0x288) (z,8 * 12)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_6_12_mc /\
                 read PC s = word pc /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,6) s = a)
          (\s. read PC s = word (pc + 0x284) /\
               bignum_from_memory (z,12) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                        X11; X12; X13; X14; X15; X16; X17] ,,
             MAYCHANGE [memory :> bytes(z,8 * 12)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQR_6_12_EXEC
   ([4;5;6;7;9;10;12;14;16] @ (20--25) @ [27;29;31;33] @
    (35--38) @ [40;41;43;45;47] @ (51--56) @ [58;60;62;64] @
    [66;67;68] @ (72--82) @ [88] @ (94--98) @ [104] @ (110--113) @
    [119] @ (125--134) @ [136;139;142;145;148;151;154;157;160])
   (1--161) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`768`; `&0:real`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_SQR_6_12_SUBROUTINE_CORRECT = prove
 (`!z x a pc returnaddress.
      nonoverlapping (word pc,0x288) (z,8 * 12)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_6_12_mc /\
                 read PC s = word pc /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,6) s = a)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,12) s = a EXP 2)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 12)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_SQR_6_12_EXEC BIGNUM_SQR_6_12_CORRECT);;
