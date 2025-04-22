(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 6x6 -> 12 multiply (pure Karatsuba and then ADK for the 3x3 bits).        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_mul_6_12.o";;
 ****)

let bignum_mul_6_12_mc = define_assert_from_elf "bignum_mul_6_12_mc" "arm/fastmul/bignum_mul_6_12.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&0))) *)
  0xf9400825;       (* arm_LDR X5 X1 (Immediate_Offset (word 16)) *)
  0xf9400848;       (* arm_LDR X8 X2 (Immediate_Offset (word 16)) *)
  0x9b067c74;       (* arm_MUL X20 X3 X6 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0x9bc67c6c;       (* arm_UMULH X12 X3 X6 *)
  0x9bc77c8d;       (* arm_UMULH X13 X4 X7 *)
  0x9bc87cae;       (* arm_UMULH X14 X5 X8 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018f;       (* arm_ADDS X15 X12 X20 *)
  0xba0c01b0;       (* arm_ADCS X16 X13 X12 *)
  0xba0d01d1;       (* arm_ADCS X17 X14 X13 *)
  0x9a1f01d3;       (* arm_ADC X19 X14 XZR *)
  0xab140210;       (* arm_ADDS X16 X16 X20 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x9a1f01c9;       (* arm_ADC X9 X14 XZR *)
  0xeb04006d;       (* arm_SUBS X13 X3 X4 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb0600eb;       (* arm_SUBS X11 X7 X6 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xeb05006d;       (* arm_SUBS X13 X3 X5 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb06010b;       (* arm_SUBS X11 X8 X6 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c0210;       (* arm_ADCS X16 X16 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xeb05008d;       (* arm_SUBS X13 X4 X5 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb07010b;       (* arm_SUBS X11 X8 X7 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xa9003c14;       (* arm_STP X20 X15 X0 (Immediate_Offset (iword (&0))) *)
  0xa9014410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022413;       (* arm_STP X19 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xa9419023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&24))) *)
  0xa9419c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&24))) *)
  0xf9401425;       (* arm_LDR X5 X1 (Immediate_Offset (word 40)) *)
  0xf9401448;       (* arm_LDR X8 X2 (Immediate_Offset (word 40)) *)
  0x9b067c74;       (* arm_MUL X20 X3 X6 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0x9bc67c6c;       (* arm_UMULH X12 X3 X6 *)
  0x9bc77c8d;       (* arm_UMULH X13 X4 X7 *)
  0x9bc87cae;       (* arm_UMULH X14 X5 X8 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018f;       (* arm_ADDS X15 X12 X20 *)
  0xba0c01b0;       (* arm_ADCS X16 X13 X12 *)
  0xba0d01d1;       (* arm_ADCS X17 X14 X13 *)
  0x9a1f01d3;       (* arm_ADC X19 X14 XZR *)
  0xab140210;       (* arm_ADDS X16 X16 X20 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x9a1f01c9;       (* arm_ADC X9 X14 XZR *)
  0xf9400c0c;       (* arm_LDR X12 X0 (Immediate_Offset (word 24)) *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0xa9422c0c;       (* arm_LDP X12 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0273;       (* arm_ADCS X19 X19 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xeb04006d;       (* arm_SUBS X13 X3 X4 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb0600eb;       (* arm_SUBS X11 X7 X6 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xeb05006d;       (* arm_SUBS X13 X3 X5 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb06010b;       (* arm_SUBS X11 X8 X6 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c0210;       (* arm_ADCS X16 X16 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xeb05008d;       (* arm_SUBS X13 X4 X5 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb07010b;       (* arm_SUBS X11 X8 X7 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xa9033c14;       (* arm_STP X20 X15 X0 (Immediate_Offset (iword (&48))) *)
  0xa9044410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&64))) *)
  0xa9052413;       (* arm_STP X19 X9 X0 (Immediate_Offset (iword (&80))) *)
  0xf940002d;       (* arm_LDR X13 X1 (Immediate_Offset (word 0)) *)
  0xeb0d0063;       (* arm_SUBS X3 X3 X13 *)
  0xf940042d;       (* arm_LDR X13 X1 (Immediate_Offset (word 8)) *)
  0xfa0d0084;       (* arm_SBCS X4 X4 X13 *)
  0xf940082d;       (* arm_LDR X13 X1 (Immediate_Offset (word 16)) *)
  0xfa0d00a5;       (* arm_SBCS X5 X5 X13 *)
  0xda9f23ed;       (* arm_CSETM X13 Condition_CC *)
  0xf9400041;       (* arm_LDR X1 X2 (Immediate_Offset (word 0)) *)
  0xeb060026;       (* arm_SUBS X6 X1 X6 *)
  0xf9400441;       (* arm_LDR X1 X2 (Immediate_Offset (word 8)) *)
  0xfa070027;       (* arm_SBCS X7 X1 X7 *)
  0xf9400841;       (* arm_LDR X1 X2 (Immediate_Offset (word 16)) *)
  0xfa080028;       (* arm_SBCS X8 X1 X8 *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xca0d0063;       (* arm_EOR X3 X3 X13 *)
  0xeb0d0063;       (* arm_SUBS X3 X3 X13 *)
  0xca0d0084;       (* arm_EOR X4 X4 X13 *)
  0xfa0d0084;       (* arm_SBCS X4 X4 X13 *)
  0xca0d00a5;       (* arm_EOR X5 X5 X13 *)
  0xda0d00a5;       (* arm_SBC X5 X5 X13 *)
  0xca0100c6;       (* arm_EOR X6 X6 X1 *)
  0xeb0100c6;       (* arm_SUBS X6 X6 X1 *)
  0xca0100e7;       (* arm_EOR X7 X7 X1 *)
  0xfa0100e7;       (* arm_SBCS X7 X7 X1 *)
  0xca010108;       (* arm_EOR X8 X8 X1 *)
  0xda010108;       (* arm_SBC X8 X8 X1 *)
  0xca0d0021;       (* arm_EOR X1 X1 X13 *)
  0x9b067c74;       (* arm_MUL X20 X3 X6 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0x9bc67c6c;       (* arm_UMULH X12 X3 X6 *)
  0x9bc77c8d;       (* arm_UMULH X13 X4 X7 *)
  0x9bc87cae;       (* arm_UMULH X14 X5 X8 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018f;       (* arm_ADDS X15 X12 X20 *)
  0xba0c01b0;       (* arm_ADCS X16 X13 X12 *)
  0xba0d01d1;       (* arm_ADCS X17 X14 X13 *)
  0x9a1f01d3;       (* arm_ADC X19 X14 XZR *)
  0xab140210;       (* arm_ADDS X16 X16 X20 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x9a1f01c9;       (* arm_ADC X9 X14 XZR *)
  0xeb04006d;       (* arm_SUBS X13 X3 X4 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb0600eb;       (* arm_SUBS X11 X7 X6 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c01ef;       (* arm_ADCS X15 X15 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xeb05006d;       (* arm_SUBS X13 X3 X5 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb06010b;       (* arm_SUBS X11 X8 X6 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c0210;       (* arm_ADCS X16 X16 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xeb05008d;       (* arm_SUBS X13 X4 X5 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb07010b;       (* arm_SUBS X11 X8 X7 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9b0b7dac;       (* arm_MUL X12 X13 X11 *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xa9401003;       (* arm_LDP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9431c06;       (* arm_LDP X6 X7 X0 (Immediate_Offset (iword (&48))) *)
  0xab060063;       (* arm_ADDS X3 X3 X6 *)
  0xba070084;       (* arm_ADCS X4 X4 X7 *)
  0xf9400805;       (* arm_LDR X5 X0 (Immediate_Offset (word 16)) *)
  0xa9442808;       (* arm_LDP X8 X10 X0 (Immediate_Offset (iword (&64))) *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xa945300b;       (* arm_LDP X11 X12 X0 (Immediate_Offset (iword (&80))) *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0xba0c0108;       (* arm_ADCS X8 X8 X12 *)
  0xba1f002d;       (* arm_ADCS X13 X1 XZR *)
  0x9a1f0022;       (* arm_ADC X2 X1 XZR *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xca010294;       (* arm_EOR X20 X20 X1 *)
  0xba030283;       (* arm_ADCS X3 X20 X3 *)
  0xca0101ef;       (* arm_EOR X15 X15 X1 *)
  0xba0401e4;       (* arm_ADCS X4 X15 X4 *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xba050205;       (* arm_ADCS X5 X16 X5 *)
  0xca010231;       (* arm_EOR X17 X17 X1 *)
  0xba060226;       (* arm_ADCS X6 X17 X6 *)
  0xca010273;       (* arm_EOR X19 X19 X1 *)
  0xba070267;       (* arm_ADCS X7 X19 X7 *)
  0xca010129;       (* arm_EOR X9 X9 X1 *)
  0xba080128;       (* arm_ADCS X8 X9 X8 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a02018c;       (* arm_ADC X12 X12 X2 *)
  0xf9000c03;       (* arm_STR X3 X0 (Immediate_Offset (word 24)) *)
  0xa9021404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&32))) *)
  0xa9031c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&48))) *)
  0xa9042808;       (* arm_STP X8 X10 X0 (Immediate_Offset (iword (&64))) *)
  0xa905300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&80))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_6_12_EXEC = ARM_MK_EXEC_RULE bignum_mul_6_12_mc;;

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

let ADK_36_TAC =
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
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;;

let BIGNUM_MUL_6_12_CORRECT = prove
 (`!z x y a b pc.
      ALL (nonoverlapping (z,8 * 12))
          [(word pc,0x440); (x,8 * 6); (y,8 * 6)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_mul_6_12_mc /\
                 read PC s = word(pc + 0x4) /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,6) s = a /\
                 bignum_from_memory (y,6) s = b)
            (\s. read PC s = word (pc + 0x438) /\
                 bignum_from_memory (z,12) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                        X12; X13; X14; X15; X16; X17; X19; X20] ,,
             MAYCHANGE [memory :> bytes(z,8 * 12)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN

  (*** First ADK block multiplying the lower halves ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_6_12_EXEC
   [5;6;7;11;12;13;14;15;16;17;18;19;20;21;27;32;34;35;36;37;
    43;48;50;51;52;58;63;65;66] (1--69) THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = bignum_of_wordlist[mullo_s5;sum_s32;sum_s48]`;
    `q1 = bignum_of_wordlist[sum_s63;sum_s65;sum_s66]`] THEN
  SUBGOAL_THEN
   `2 EXP 192 * q1 + q0 =
    bignum_of_wordlist [x_0;x_1;x_2] * bignum_of_wordlist[y_0;y_1;y_2]`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q0"; "q1"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_36_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Second ADK block multiplying the upper halves with q1 added ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_6_12_EXEC
   [74;75;76;80;81;82;83;84;85;86;87;88;89;90;92;94;95;96;97;98;
    104;109;111;112;113;114;120;125;127;128;129;135;140;142;143]
   (70--146) THEN

  MAP_EVERY ABBREV_TAC
   [`q2 = bignum_of_wordlist[sum_s92;sum_s109;sum_s125]`;
    `q3 = bignum_of_wordlist[sum_s140;sum_s142;sum_s143]`] THEN
  SUBGOAL_THEN
   `2 EXP 192 * q3 + q2 =
    bignum_of_wordlist [x_3;x_4;x_5] * bignum_of_wordlist[y_3;y_4;y_5] + q1`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "q2"; "q3"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_36_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The sign-magnitude difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_6_12_EXEC
    [148;150;152; 155;157;159; 162;164;166; 168;170;172]
    (147--172) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN

  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s159 <=> carry_s152)`;
   `xd = bignum_of_wordlist[sum_s162;sum_s164;sum_s166]`;
   `yd = bignum_of_wordlist[sum_s168;sum_s170;sum_s172]`] THEN

  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_3;x_4;x_5]) -
     &(bignum_of_wordlist[x_0;x_1;x_2])) *
    (&(bignum_of_wordlist[y_0;y_1;y_2]) -
     &(bignum_of_wordlist[y_3;y_4;y_5])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s152 * &xd) *
      (--(&1) pow bitval carry_s159 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s152 <=>
       bignum_of_wordlist[x_3;x_4;x_5] < bignum_of_wordlist[x_0;x_1;x_2]) /\
      (carry_s159 <=>
       bignum_of_wordlist[y_0;y_1;y_2] < bignum_of_wordlist[y_3;y_4;y_5])`
     (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `192` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    BINOP_TAC THEN REWRITE_TAC[bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = --(&1) pow 1 * z <=> y - x = z`] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`192`; `&0:real`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH
        `y:real <= x /\ (&0 <= x /\ x < e) /\ (&0 <= y /\ y < e)
         ==> &0 <= x - y /\ x - y < e`) THEN
       ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; LT_IMP_LE;
                    ARITH_RULE `~(a:num < b) ==> b <= a`] THEN
       REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
       CONJ_TAC THEN BOUNDER_TAC[];
       ALL_TAC] THEN
     MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
     REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
     CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[WORD_XOR_MASK] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Third ADK block multiplying the absolute differences ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_6_12_EXEC
   [174;175;176;180;181;182;183;184;185;186;187;188;189;190;
    196;201;203;204;205;206;212;217;219;220;221;227;232;234;235]
   (173--235) THEN

  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist[mullo_s174; sum_s201; sum_s217;
                         sum_s232; sum_s234; sum_s235])`
  SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_36_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Clean up the overall sign ***)

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_XOR_MASKS]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** Final accumulation simulation and 12-digit focusing ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_6_12_EXEC
   [238;239;242;243;245;246;247;248;251;253;255;257;259; 261;262;263;264]
   (236--269) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s269" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`768`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN

  (*** The core rearrangement we are using ***)

  SUBGOAL_THEN
   `&a * &b:real =
    (&1 + &2 pow 192) * (&q0 + &2 pow 192 * &q2 + &2 pow 384 * &q3) +
    &2 pow 192 *
    (&(bignum_of_wordlist [x_3; x_4; x_5]) -
     &(bignum_of_wordlist [x_0; x_1; x_2])) *
    (&(bignum_of_wordlist [y_0; y_1; y_2]) -
     &(bignum_of_wordlist [y_3; y_4; y_5]))`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`2 EXP 192 * q1 + q0 =
       bignum_of_wordlist[x_0; x_1; x_2] * bignum_of_wordlist[y_0; y_1; y_2]`;
      `2 EXP 192 * q3 + q2 =
       bignum_of_wordlist[x_3; x_4; x_5] * bignum_of_wordlist[y_3; y_4; y_5] +
       q1`] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[]] THEN

  MAP_EVERY EXPAND_TAC ["q0"; "q2"; "q3"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN DISCH_TAC THEN

  (*** A bit of manual logic for the carry connections in negative case ***)

  FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THENL
   [SUBGOAL_THEN
     `&(bitval carry_s248):real = &(bitval carry_s247)`
    SUBST1_TAC THENL [ALL_TAC; REAL_INTEGER_TAC] THEN
    POP_ASSUM MP_TAC THEN BOOL_CASES_TAC `carry_s247:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[REAL_RAT_REDUCE_CONV `(&2 pow 64 - &1) * &1 + &0`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o
    filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MUL_6_12_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 12) (word_sub stackpointer (word 16),16) /\
        ALLPAIRS nonoverlapping
          [(z,8 * 12); (word_sub stackpointer (word 16),16)]
          [(word pc,0x440); (x,8 * 6); (y,8 * 6)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_mul_6_12_mc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,6) s = a /\
                 bignum_from_memory (y,6) s = b)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,12) s = a * b)
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 12);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
 ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_6_12_EXEC BIGNUM_MUL_6_12_CORRECT
   `[X19;X20]` 16);;
