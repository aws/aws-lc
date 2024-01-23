(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_384.                                         *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/p384/bignum_montsqr_p384.o";;
 ****)

let bignum_montsqr_p384_mc =
  define_assert_from_elf "bignum_montsqr_p384_mc" "arm/p384/bignum_montsqr_p384.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
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
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607d10;       (* arm_LSL X16 X8 (rvalue (word 32)) *)
  0x8b080208;       (* arm_ADD X8 X16 X8 *)
  0xd360fd10;       (* arm_LSR X16 X8 (rvalue (word 32)) *)
  0xeb080210;       (* arm_SUBS X16 X16 X8 *)
  0xda1f010f;       (* arm_SBC X15 X8 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 (rvalue (word 32)) *)
  0xd360fdef;       (* arm_LSR X15 X15 (rvalue (word 32)) *)
  0xab0801ef;       (* arm_ADDS X15 X15 X8 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb100129;       (* arm_SUBS X9 X9 X16 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d30;       (* arm_LSL X16 X9 (rvalue (word 32)) *)
  0x8b090209;       (* arm_ADD X9 X16 X9 *)
  0xd360fd30;       (* arm_LSR X16 X9 (rvalue (word 32)) *)
  0xeb090210;       (* arm_SUBS X16 X16 X9 *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 (rvalue (word 32)) *)
  0xd360fdef;       (* arm_LSR X15 X15 (rvalue (word 32)) *)
  0xab0901ef;       (* arm_ADDS X15 X15 X9 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xfa0f016b;       (* arm_SBCS X11 X11 X15 *)
  0xfa0e018c;       (* arm_SBCS X12 X12 X14 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d50;       (* arm_LSL X16 X10 (rvalue (word 32)) *)
  0x8b0a020a;       (* arm_ADD X10 X16 X10 *)
  0xd360fd50;       (* arm_LSR X16 X10 (rvalue (word 32)) *)
  0xeb0a0210;       (* arm_SUBS X16 X16 X10 *)
  0xda1f014f;       (* arm_SBC X15 X10 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 (rvalue (word 32)) *)
  0xd360fdef;       (* arm_LSR X15 X15 (rvalue (word 32)) *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10016b;       (* arm_SUBS X11 X11 X16 *)
  0xfa0f018c;       (* arm_SBCS X12 X12 X15 *)
  0xfa0e01ad;       (* arm_SBCS X13 X13 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xa900300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&0))) *)
  0xa901200d;       (* arm_STP X13 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c81;       (* arm_UMULH X1 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba11002b;       (* arm_ADCS X11 X1 X17 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f002d;       (* arm_ADC X13 X1 XZR *)
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
  0xa9400c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xab020108;       (* arm_ADDS X8 X8 X2 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xa9410c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&16))) *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9420c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&32))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xd3607d04;       (* arm_LSL X4 X8 (rvalue (word 32)) *)
  0x8b080088;       (* arm_ADD X8 X4 X8 *)
  0xd360fd04;       (* arm_LSR X4 X8 (rvalue (word 32)) *)
  0xeb080084;       (* arm_SUBS X4 X4 X8 *)
  0xda1f0103;       (* arm_SBC X3 X8 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 (rvalue (word 32)) *)
  0xd360fc63;       (* arm_LSR X3 X3 (rvalue (word 32)) *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa02016b;       (* arm_SBCS X11 X11 X2 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d24;       (* arm_LSL X4 X9 (rvalue (word 32)) *)
  0x8b090089;       (* arm_ADD X9 X4 X9 *)
  0xd360fd24;       (* arm_LSR X4 X9 (rvalue (word 32)) *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xda1f0123;       (* arm_SBC X3 X9 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 (rvalue (word 32)) *)
  0xd360fc63;       (* arm_LSR X3 X3 (rvalue (word 32)) *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d44;       (* arm_LSL X4 X10 (rvalue (word 32)) *)
  0x8b0a008a;       (* arm_ADD X10 X4 X10 *)
  0xd360fd44;       (* arm_LSR X4 X10 (rvalue (word 32)) *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xda1f0143;       (* arm_SBC X3 X10 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 (rvalue (word 32)) *)
  0xd360fc63;       (* arm_LSR X3 X3 (rvalue (word 32)) *)
  0xab0a0063;       (* arm_ADDS X3 X3 X10 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa0201ad;       (* arm_SBCS X13 X13 X2 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab080231;       (* arm_ADDS X17 X17 X8 *)
  0xba1f0128;       (* arm_ADCS X8 X9 XZR *)
  0xba1f0149;       (* arm_ADCS X9 X10 XZR *)
  0xba1f03ea;       (* arm_ADCS X10 XZR XZR *)
  0x9b057ca1;       (* arm_MUL X1 X5 X5 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x9b067cce;       (* arm_MUL X14 X6 X6 *)
  0x9b077cef;       (* arm_MUL X15 X7 X7 *)
  0x9bc57ca1;       (* arm_UMULH X1 X5 X5 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0x9bc67cc1;       (* arm_UMULH X1 X6 X6 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9bc77ce1;       (* arm_UMULH X1 X7 X7 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9b067ca1;       (* arm_MUL X1 X5 X6 *)
  0x9b077cae;       (* arm_MUL X14 X5 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0xab1001ce;       (* arm_ADDS X14 X14 X16 *)
  0x9bc77cb0;       (* arm_UMULH X16 X5 X7 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab010021;       (* arm_ADDS X1 X1 X1 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb26083e1;       (* arm_MOV X1 (rvalue (word 18446744069414584321)) *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0xd280002f;       (* arm_MOV X15 (rvalue (word 1)) *)
  0xab01017f;       (* arm_CMN X11 X1 *)
  0xba0e019f;       (* arm_ADCS XZR X12 X14 *)
  0xba0f01bf;       (* arm_ADCS XZR X13 X15 *)
  0xba1f023f;       (* arm_ADCS XZR X17 XZR *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x8a0a0021;       (* arm_AND X1 X1 X10 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x8a0a01ce;       (* arm_AND X14 X14 X10 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xa900300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&0))) *)
  0xa901440d;       (* arm_STP X13 X17 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_P384_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

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

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(4294967297 * val x):int64)) * &18446744069414584321
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** Intricate Montgomery steps done generically ***)

let montred_tac execth regs n =
  let topflag,[d7;d6;d5;d4;d3;d2;d1;d0; t3;t2;t1] =
    let rlist = dest_list regs in
    if length rlist = 11 then true,rlist
    else false,`XZR`::rlist in
  let modterm = subst
   ([d0,`X2`; d1,`X3`; d2,`X4`; d3,`X5`; d4,`X6`; d5,`X7`; d6,`X1`; d7,`X0`;
     t1,`X10`; t2,`X9`; t3,`X8`] @
    (map (fun i -> mk_var("s"^string_of_int(i+n-3),`:armstate`),
                   mk_var("s"^string_of_int(i),`:armstate`))
         (3--20)) @
    [mk_var("sum_s"^string_of_int(7+n-3),`:int64`),
     mk_var("sum_s"^string_of_int(7),`:int64`);
     mk_var("sum_s"^string_of_int(8+n-3),`:int64`),
     mk_var("sum_s"^string_of_int(8),`:int64`)] @
    [mk_var("mvl_"^string_of_int n,`:num`),mk_var("mvl",`:num`);
     mk_var("nvl_"^string_of_int n,`:num`),mk_var("nvl",`:num`);
     mk_var("ww_"^string_of_int n,`:int64`),mk_var("w",`:int64`);
     mk_var("tt_"^string_of_int n,`:num`),mk_var("t",`:num`)])
  and modstring =
   C assoc
    (zip (statenames "s" (3--20)) (statenames "s" (n--(n+17))) @
    ["mvl","mvl_"^string_of_int n;
     "w","ww_"^string_of_int n;
     "t","tt_"^string_of_int n]) in
  (*** Abbreviate the input ***)
  ABBREV_TAC
   (modterm `mvl =
    bignum_of_wordlist[read X2 s3; read X3 s3; read X4 s3; read X5 s3;
                       read X6 s3; read X7 s3]`) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (if topflag then
     ABBREV_TAC
     (modterm `nvl =
      bignum_of_wordlist[read X2 s3; read X3 s3; read X4 s3; read X5 s3;
                         read X6 s3; read X7 s3; read X1 s3]`) THEN
     POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
   else ALL_TAC) THEN
  (*** Selection of the multiplier, similar to the x86 case ***)
  MAP_EVERY (ARM_SINGLE_STEP_TAC execth)
            (map modstring (statenames "s" (4--5))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
  REABBREV_TAC (modterm `w = read X2 s5`) THEN
  (*** Next three steps setting up [t2;t1] = 2^64 * w - w + w_hi ***)
  ARM_SINGLE_STEP_TAC execth (modstring "s6") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s7") THEN
  ACCUMULATE_ARITH_TAC (modstring "s7") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s8") THEN
  ACCUMULATE_ARITH_TAC (modstring "s8") THEN
  SUBGOAL_THEN
   (modterm `&2 pow 64 * &(val(read X9 s8)) + &(val(read X10 s8)):real =
    &2 pow 64 * &(val(w:int64)) - &(val w) + &(val w DIV 2 EXP 32)`)
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (*** Next four steps setting up
   *** [t3;t2;t1] = (2^128 + 2^96 - 2^32 + 1) * w - w MOD 2^32
   ***)
  ARM_SINGLE_STEP_TAC execth (modstring "s9") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s10") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s11") THEN
  ACCUMULATE_ARITH_TAC (modstring "s11") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s12") THEN
  (*** This is what we really want ***)
  ABBREV_TAC
   (modterm `t = 2 EXP 64 * val(sum_s8:int64) + val(sum_s7:int64)`) THEN
  SUBGOAL_THEN
   (modterm `&(bignum_of_wordlist
       [word(mvl MOD 2 EXP 64); read X10 s12; read X9 s12; read X8 s12]):real =
    (&2 pow 128 + &2 pow 96 - &2 pow 32 + &1) * &(val(w:int64))`)
  MP_TAC THEN
  EXPAND_TAC (modstring "mvl") THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD; WORD_VAL] THENL
   [TRANS_TAC EQ_TRANS
     (modterm `&2 pow 128 * &(val(w:int64)) +
      &2 pow 32 * &t + &(val w MOD 2 EXP 32)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL EQ_DIVMOD))));
      EXPAND_TAC (modstring "t") THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      REAL_ARITH_TAC] THEN
    EXISTS_TAC `2 EXP 64` THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[DIV_LT; VAL_BOUND_64; ADD_CLAUSES] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `(2 EXP 128 * w + 2 EXP 32 * t + r MOD 2 EXP 32) DIV 2 EXP 64 =
        2 EXP 64 * w + t DIV 2 EXP 32`];
      REWRITE_TAC[GSYM CONG; num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `!y:int. z = y /\ (y == x) (mod n)
                ==> (x == z) (mod n)`) THEN
      EXISTS_TAC
       (modterm `(&2 pow 128 + &2 pow 96 - &2 pow 32 + &1) *
                 &(val(w:int64)):int`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[int_eq; int_pow_th; int_mul_th; int_sub_th; int_add_th;
                    int_of_num_th] THEN
        EXPAND_TAC (modstring "t") THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check
         (can (term_match [] `word(4294967297 * x) = w`) o concl)) THEN
        REWRITE_TAC[GSYM INT_REM_EQ; VAL_WORD; DIMINDEX_64] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
        CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
        MATCH_MP_TAC(INTEGER_RULE
         `(a * b:int == &1) (mod p) ==> (a * b * x == x) (mod p)`) THEN
        REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV]] THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `s + 2 EXP 64 * c = 2 EXP 64 * c + s`] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT; VAL_WORD_USHR] THEN
    REWRITE_TAC[VAL_WORD_0] THEN EXPAND_TAC (modstring "t") THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  (*** The main accumulation of the same-size portion and adding to w ***)
  MAP_EVERY (fun s ->
        ARM_SINGLE_STEP_TAC execth s THEN
        ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
    (map modstring (statenames "s" (13--18))) THEN
  SUBGOAL_THEN
   (modterm
     (if topflag then
       `&2 pow 64 * &(bignum_of_wordlist[read X3 s18; read X4 s18; read X5 s18;
                                  read X6 s18; read X7 s18; read X2 s18]) =
        &mvl + &p_384 * &(val(w:int64))`
      else
       `&2 pow 64 * &(bignum_of_wordlist[read X3 s18; read X4 s18; read X5 s18;
                                  read X6 s18; read X7 s18; read X1 s18]) =
        &mvl + &p_384 * &(val(w:int64))`))
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    EXPAND_TAC(modstring "mvl") THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o RAND_CONV)
     [CONJUNCT2 bignum_of_wordlist]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `x + a:real = b ==> x = b - a`)) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_REWRITE_TAC[] THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  (*** Final little accumulation in the non-short case ***)
  (if topflag then
     DISCH_TAC THEN
     ARM_SINGLE_STEP_TAC execth (modstring "s19") THEN
     ACCUMULATE_ARITH_TAC (modstring "s19") THEN
     ARM_SINGLE_STEP_TAC execth (modstring "s20") THEN
     SUBGOAL_THEN (modterm
      `&2 pow 64 * &(bignum_of_wordlist[read X3 s20; read X4 s20; read X5 s20;
                       read X6 s20; read X7 s20; read X1 s20; read X0 s20]) =
        &nvl + &p_384 * &(val(w:int64))`)
     MP_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `x:real = m + p * w  ==> n - m = y - x ==> y = n + p * w`)) THEN
       FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
       FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
       REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN REAL_ARITH_TAC;
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
        `x:real = m + p * w ==> (y = n + p * w ==> q)
         ==> y = n + p * w ==> q`)) THEN
       ASM_REWRITE_TAC[ADD_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])]
   else ALL_TAC);;

let montred_subst_tac execth regs n =
  montred_tac execth regs n THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> b = a - c`));;

let BIGNUM_MONTSQR_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x414) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + 0x410) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_P384_EXEC (1--260)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Squaring of the lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (1--28) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 =
    bignum_of_wordlist [mullo_s7; sum_s24; sum_s25; sum_s26; sum_s27; sum_s28]`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three short Montgomery reductions ***)

  montred_tac BIGNUM_MONTSQR_P384_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X14;X15;X16]` 28 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X14;X15;X16]` 43 THEN
  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X14;X15;X16]` 58 THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Three stashing stores ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_EXEC [74;75;76] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC
   ([77;78;79] @ (83--93) @ [99] @ (105--109) @ [115] @
   (121--124) @ [130] @ (136--138)) (77--138) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0; x_1; x_2] * bignum_of_wordlist [x_3; x_4; x_5] =
    bignum_of_wordlist [mullo_s77; sum_s105; sum_s121;
                        sum_s136; sum_s137; sum_s138]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

 (*** Double the cross-product and add the Montgomerified lower square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (139--155) (139--155) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
    2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                    bignum_of_wordlist [x_3; x_4; x_5] +
    p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58] =
    2 EXP 192 *
    bignum_of_wordlist
     [sum_s147; sum_s148; sum_s150; sum_s151; sum_s153; sum_s154; sum_s155]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three more Montgomery reductions on that sum ***)

  montred_tac BIGNUM_MONTSQR_P384_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X2;X3;X4]` 155 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X2;X3;X4]` 170 THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X2;X3;X4]` 185 THEN

  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Montgomery accumulation and addition of the high square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (201--237) (201--237) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  (*** Main pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s206; sum_s232; sum_s233;
          sum_s234; sum_s235; sum_s236; sum_s237]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 384 * t =
      a EXP 2 +
      p_384 * bignum_of_wordlist
        [ww_28; ww_43; ww_58; ww_155; ww_170; ww_185]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
      `(bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
        2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                        bignum_of_wordlist [x_3; x_4; x_5] +
        p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58]) +
       2 EXP 384 * bignum_of_wordlist[x_3;x_4;x_5] EXP 2 +
       2 EXP 192 * p_384 *
       bignum_of_wordlist [ww_155; ww_170; ww_185]` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
         `x' - x:real = &(bignum_of_wordlist(CONS h t))
          ==> e * (&(bignum_of_wordlist(CONS h t')) -
                   &(bignum_of_wordlist(CONS h t))) = (w - e * (x' - x)) - z
              ==> w = e * &(bignum_of_wordlist(CONS h t')) + z`));
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

 (*** To make bounds reasoning more transparent, recast top as a bit ***)

  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(sum_s237:int64)` NUM_AS_BITVAL_ALT))) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN ANTS_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `topc:bool` SUBST_ALL_TAC)] THEN

  (*** Final comparison ****)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (238--247) (238--247) THEN
  SUBGOAL_THEN
   `sum_s247:int64 = word(bitval(p_384 <= t))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Corrective masked subtraction ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_EXEC [248] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word 0) x:int64 = word_neg x`]) THEN
  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (249--260) (249--260) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  ASM_SIMP_TAC[MOD_CASES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x414) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P384_EXEC
    BIGNUM_MONTSQR_P384_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 384 bits, may then not be fully reduced mod p_384.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTSQR_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x414) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + 0x410) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Squaring of the lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (1--28) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 =
    bignum_of_wordlist [mullo_s7; sum_s24; sum_s25; sum_s26; sum_s27; sum_s28]`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three short Montgomery reductions ***)

  montred_tac BIGNUM_MONTSQR_P384_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X14;X15;X16]` 28 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X14;X15;X16]` 43 THEN
  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X14;X15;X16]` 58 THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Three stashing stores ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_EXEC [74;75;76] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC
   ([77;78;79] @ (83--93) @ [99] @ (105--109) @ [115] @
   (121--124) @ [130] @ (136--138)) (77--138) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0; x_1; x_2] * bignum_of_wordlist [x_3; x_4; x_5] =
    bignum_of_wordlist [mullo_s77; sum_s105; sum_s121;
                        sum_s136; sum_s137; sum_s138]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

 (*** Double the cross-product and add the Montgomerified lower square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (139--155) (139--155) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
    2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                    bignum_of_wordlist [x_3; x_4; x_5] +
    p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58] =
    2 EXP 192 *
    bignum_of_wordlist
     [sum_s147; sum_s148; sum_s150; sum_s151; sum_s153; sum_s154; sum_s155]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three more Montgomery reductions on that sum ***)

  montred_tac BIGNUM_MONTSQR_P384_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X2;X3;X4]` 155 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X2;X3;X4]` 170 THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X2;X3;X4]` 185 THEN

  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Montgomery accumulation and addition of the high square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (201--237) (201--237) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  (*** Main pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s206; sum_s232; sum_s233;
          sum_s234; sum_s235; sum_s236; sum_s237]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 384 + p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 384 * t =
      a EXP 2 +
      p_384 * bignum_of_wordlist
        [ww_28; ww_43; ww_58; ww_155; ww_170; ww_185]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
      `(bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
        2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                        bignum_of_wordlist [x_3; x_4; x_5] +
        p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58]) +
       2 EXP 384 * bignum_of_wordlist[x_3;x_4;x_5] EXP 2 +
       2 EXP 192 * p_384 *
       bignum_of_wordlist [ww_155; ww_170; ww_185]` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
         `x' - x:real = &(bignum_of_wordlist(CONS h t))
          ==> e * (&(bignum_of_wordlist(CONS h t')) -
                   &(bignum_of_wordlist(CONS h t))) = (w - e * (x' - x)) - z
              ==> w = e * &(bignum_of_wordlist(CONS h t')) + z`));
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      MATCH_MP_TAC(ARITH_RULE `2 EXP 384 * x < 2 EXP 384 * y ==> x < y`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

 (*** To make bounds reasoning more transparent, recast top as a bit ***)

  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(sum_s237:int64)` NUM_AS_BITVAL_ALT))) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN ANTS_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 384 + p_384` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `topc:bool` SUBST_ALL_TAC)] THEN

  (*** Final comparison ****)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (238--247) (238--247) THEN
  SUBGOAL_THEN
   `sum_s247:int64 = word(bitval(p_384 <= t))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 EXP 384 + p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Corrective masked subtraction ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_EXEC [248] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word 0) x:int64 = word_neg x`]) THEN
  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_EXEC (249--260) (249--260) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * a EXP 2) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval(p_384 <= t)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 384 + p_384` THEN
    REWRITE_TAC[bitval; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_384] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTSQR_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x414) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P384_EXEC
    BIGNUM_AMONTSQR_P384_CORRECT);;
