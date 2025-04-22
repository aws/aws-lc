(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mixed addition in Montgomery-Jacobian coordinates for CC SM2 curve.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/ccsm2.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/sm2/sm2_montjmixadd.o";;
 ****)

let sm2_montjmixadd_mc = define_assert_from_elf
  "sm2_montjmixadd_mc" "arm/sm2/sm2_montjmixadd.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10303ff;       (* arm_SUB SP SP (rvalue (word 192)) *)
  0xaa0003f1;       (* arm_MOV X17 X0 *)
  0xaa0103f3;       (* arm_MOV X19 X1 *)
  0xaa0203f4;       (* arm_MOV X20 X2 *)
  0xa9440e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&64))) *)
  0xa9451664;       (* arm_LDP X4 X5 X19 (Immediate_Offset (iword (&80))) *)
  0x9ba27c4f;       (* arm_UMULL X15 W2 W2 *)
  0xd360fc4b;       (* arm_LSR X11 X2 32 *)
  0x9bab7d70;       (* arm_UMULL X16 W11 W11 *)
  0x9bab7c4b;       (* arm_UMULL X11 W2 W11 *)
  0xab0b85ef;       (* arm_ADDS X15 X15 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0210;       (* arm_ADC X16 X16 X11 *)
  0x9ba37c60;       (* arm_UMULL X0 W3 W3 *)
  0xd360fc6b;       (* arm_LSR X11 X3 32 *)
  0x9bab7d61;       (* arm_UMULL X1 W11 W11 *)
  0x9bab7c6b;       (* arm_UMULL X11 W3 W11 *)
  0x9b037c4c;       (* arm_MUL X12 X2 X3 *)
  0x9bc37c4d;       (* arm_UMULH X13 X2 X3 *)
  0xab0b8400;       (* arm_ADDS X0 X0 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0d0000;       (* arm_ADCS X0 X0 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xd3607dec;       (* arm_LSL X12 X15 32 *)
  0xd360fdeb;       (* arm_LSR X11 X15 32 *)
  0xeb0f018e;       (* arm_SUBS X14 X12 X15 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0210;       (* arm_SUBS X16 X16 X14 *)
  0xfa0d0000;       (* arm_SBCS X0 X0 X13 *)
  0xfa0c0021;       (* arm_SBCS X1 X1 X12 *)
  0xda0b01ef;       (* arm_SBC X15 X15 X11 *)
  0xd3607e0c;       (* arm_LSL X12 X16 32 *)
  0xd360fe0b;       (* arm_LSR X11 X16 32 *)
  0xeb10018e;       (* arm_SUBS X14 X12 X16 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0000;       (* arm_SUBS X0 X0 X14 *)
  0xfa0d0021;       (* arm_SBCS X1 X1 X13 *)
  0xfa0c01ef;       (* arm_SBCS X15 X15 X12 *)
  0xda0b0210;       (* arm_SBC X16 X16 X11 *)
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
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xba0100e7;       (* arm_ADCS X7 X7 X1 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xd3607ccc;       (* arm_LSL X12 X6 32 *)
  0xd360fccb;       (* arm_LSR X11 X6 32 *)
  0xeb06018e;       (* arm_SUBS X14 X12 X6 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e00e7;       (* arm_SUBS X7 X7 X14 *)
  0xfa0d0108;       (* arm_SBCS X8 X8 X13 *)
  0xfa0c0129;       (* arm_SBCS X9 X9 X12 *)
  0xda0b00ce;       (* arm_SBC X14 X6 X11 *)
  0xab0e014a;       (* arm_ADDS X10 X10 X14 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xd3607cec;       (* arm_LSL X12 X7 32 *)
  0xd360fceb;       (* arm_LSR X11 X7 32 *)
  0xeb07018e;       (* arm_SUBS X14 X12 X7 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0108;       (* arm_SUBS X8 X8 X14 *)
  0xfa0d0129;       (* arm_SBCS X9 X9 X13 *)
  0xfa0c014a;       (* arm_SBCS X10 X10 X12 *)
  0xda0b00ee;       (* arm_SBC X14 X7 X11 *)
  0xab0e00c6;       (* arm_ADDS X6 X6 X14 *)
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
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0xb1000505;       (* arm_ADDS X5 X8 (rvalue (word 1)) *)
  0xfa0b012b;       (* arm_SBCS X11 X9 X11 *)
  0x92c0002d;       (* arm_MOVN X13 (word 1) 32 *)
  0xba1f014c;       (* arm_ADCS X12 X10 XZR *)
  0xfa0d00cd;       (* arm_SBCS X13 X6 X13 *)
  0xfa1f00ff;       (* arm_SBCS XZR X7 XZR *)
  0x9a8820a8;       (* arm_CSEL X8 X5 X8 Condition_CS *)
  0x9a892169;       (* arm_CSEL X9 X11 X9 Condition_CS *)
  0x9a8a218a;       (* arm_CSEL X10 X12 X10 Condition_CS *)
  0x9a8621a6;       (* arm_CSEL X6 X13 X6 Condition_CS *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9011bea;       (* arm_STP X10 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa9441263;       (* arm_LDP X3 X4 X19 (Immediate_Offset (iword (&64))) *)
  0xa9451a65;       (* arm_LDP X5 X6 X19 (Immediate_Offset (iword (&80))) *)
  0xa9422287;       (* arm_LDP X7 X8 X20 (Immediate_Offset (iword (&32))) *)
  0xa9432a89;       (* arm_LDP X9 X10 X20 (Immediate_Offset (iword (&48))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa9023bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&32))) *)
  0xa90333eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&48))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94207ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&32))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94327e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&48))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa9023bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&32))) *)
  0xa90313e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&48))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa9402287;       (* arm_LDP X7 X8 X20 (Immediate_Offset (iword (&0))) *)
  0xa9412a89;       (* arm_LDP X9 X10 X20 (Immediate_Offset (iword (&16))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa9043bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&64))) *)
  0xa90533eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&80))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94407ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&64))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94527e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&80))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa9043bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&64))) *)
  0xa90513e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&80))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0xa9432be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa9023bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&32))) *)
  0xa90333eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&48))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94207ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&32))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94327e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&48))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa9023bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&32))) *)
  0xa90313e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&48))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9400e64;       (* arm_LDP X4 X3 X19 (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9410e64;       (* arm_LDP X4 X3 X19 (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa90a1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa90b23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xa9421be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa9420e64;       (* arm_LDP X4 X3 X19 (Immediate_Offset (iword (&32))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa9430e64;       (* arm_LDP X4 X3 X19 (Immediate_Offset (iword (&48))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9021be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa90323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa94a0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&160))) *)
  0xa94b17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&176))) *)
  0x9ba27c4f;       (* arm_UMULL X15 W2 W2 *)
  0xd360fc4b;       (* arm_LSR X11 X2 32 *)
  0x9bab7d70;       (* arm_UMULL X16 W11 W11 *)
  0x9bab7c4b;       (* arm_UMULL X11 W2 W11 *)
  0xab0b85ef;       (* arm_ADDS X15 X15 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0210;       (* arm_ADC X16 X16 X11 *)
  0x9ba37c60;       (* arm_UMULL X0 W3 W3 *)
  0xd360fc6b;       (* arm_LSR X11 X3 32 *)
  0x9bab7d61;       (* arm_UMULL X1 W11 W11 *)
  0x9bab7c6b;       (* arm_UMULL X11 W3 W11 *)
  0x9b037c4c;       (* arm_MUL X12 X2 X3 *)
  0x9bc37c4d;       (* arm_UMULH X13 X2 X3 *)
  0xab0b8400;       (* arm_ADDS X0 X0 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0d0000;       (* arm_ADCS X0 X0 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xd3607dec;       (* arm_LSL X12 X15 32 *)
  0xd360fdeb;       (* arm_LSR X11 X15 32 *)
  0xeb0f018e;       (* arm_SUBS X14 X12 X15 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0210;       (* arm_SUBS X16 X16 X14 *)
  0xfa0d0000;       (* arm_SBCS X0 X0 X13 *)
  0xfa0c0021;       (* arm_SBCS X1 X1 X12 *)
  0xda0b01ef;       (* arm_SBC X15 X15 X11 *)
  0xd3607e0c;       (* arm_LSL X12 X16 32 *)
  0xd360fe0b;       (* arm_LSR X11 X16 32 *)
  0xeb10018e;       (* arm_SUBS X14 X12 X16 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0000;       (* arm_SUBS X0 X0 X14 *)
  0xfa0d0021;       (* arm_SBCS X1 X1 X13 *)
  0xfa0c01ef;       (* arm_SBCS X15 X15 X12 *)
  0xda0b0210;       (* arm_SBC X16 X16 X11 *)
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
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xba0100e7;       (* arm_ADCS X7 X7 X1 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xd3607ccc;       (* arm_LSL X12 X6 32 *)
  0xd360fccb;       (* arm_LSR X11 X6 32 *)
  0xeb06018e;       (* arm_SUBS X14 X12 X6 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e00e7;       (* arm_SUBS X7 X7 X14 *)
  0xfa0d0108;       (* arm_SBCS X8 X8 X13 *)
  0xfa0c0129;       (* arm_SBCS X9 X9 X12 *)
  0xda0b00ce;       (* arm_SBC X14 X6 X11 *)
  0xab0e014a;       (* arm_ADDS X10 X10 X14 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xd3607cec;       (* arm_LSL X12 X7 32 *)
  0xd360fceb;       (* arm_LSR X11 X7 32 *)
  0xeb07018e;       (* arm_SUBS X14 X12 X7 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0108;       (* arm_SUBS X8 X8 X14 *)
  0xfa0d0129;       (* arm_SBCS X9 X9 X13 *)
  0xfa0c014a;       (* arm_SBCS X10 X10 X12 *)
  0xda0b00ee;       (* arm_SBC X14 X7 X11 *)
  0xab0e00c6;       (* arm_ADDS X6 X6 X14 *)
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
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0xb1000505;       (* arm_ADDS X5 X8 (rvalue (word 1)) *)
  0xfa0b012b;       (* arm_SBCS X11 X9 X11 *)
  0x92c0002d;       (* arm_MOVN X13 (word 1) 32 *)
  0xba1f014c;       (* arm_ADCS X12 X10 XZR *)
  0xfa0d00cd;       (* arm_SBCS X13 X6 X13 *)
  0xfa1f00ff;       (* arm_SBCS XZR X7 XZR *)
  0x9a8820a8;       (* arm_CSEL X8 X5 X8 Condition_CS *)
  0x9a892169;       (* arm_CSEL X9 X11 X9 Condition_CS *)
  0x9a8a218a;       (* arm_CSEL X10 X12 X10 Condition_CS *)
  0x9a8621a6;       (* arm_CSEL X6 X13 X6 Condition_CS *)
  0xa90627e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&96))) *)
  0xa9071bea;       (* arm_STP X10 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa9420fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0xa94317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&48))) *)
  0x9ba27c4f;       (* arm_UMULL X15 W2 W2 *)
  0xd360fc4b;       (* arm_LSR X11 X2 32 *)
  0x9bab7d70;       (* arm_UMULL X16 W11 W11 *)
  0x9bab7c4b;       (* arm_UMULL X11 W2 W11 *)
  0xab0b85ef;       (* arm_ADDS X15 X15 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0210;       (* arm_ADC X16 X16 X11 *)
  0x9ba37c60;       (* arm_UMULL X0 W3 W3 *)
  0xd360fc6b;       (* arm_LSR X11 X3 32 *)
  0x9bab7d61;       (* arm_UMULL X1 W11 W11 *)
  0x9bab7c6b;       (* arm_UMULL X11 W3 W11 *)
  0x9b037c4c;       (* arm_MUL X12 X2 X3 *)
  0x9bc37c4d;       (* arm_UMULH X13 X2 X3 *)
  0xab0b8400;       (* arm_ADDS X0 X0 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0d0000;       (* arm_ADCS X0 X0 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xd3607dec;       (* arm_LSL X12 X15 32 *)
  0xd360fdeb;       (* arm_LSR X11 X15 32 *)
  0xeb0f018e;       (* arm_SUBS X14 X12 X15 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0210;       (* arm_SUBS X16 X16 X14 *)
  0xfa0d0000;       (* arm_SBCS X0 X0 X13 *)
  0xfa0c0021;       (* arm_SBCS X1 X1 X12 *)
  0xda0b01ef;       (* arm_SBC X15 X15 X11 *)
  0xd3607e0c;       (* arm_LSL X12 X16 32 *)
  0xd360fe0b;       (* arm_LSR X11 X16 32 *)
  0xeb10018e;       (* arm_SUBS X14 X12 X16 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0000;       (* arm_SUBS X0 X0 X14 *)
  0xfa0d0021;       (* arm_SBCS X1 X1 X13 *)
  0xfa0c01ef;       (* arm_SBCS X15 X15 X12 *)
  0xda0b0210;       (* arm_SBC X16 X16 X11 *)
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
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xba0100e7;       (* arm_ADCS X7 X7 X1 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xd3607ccc;       (* arm_LSL X12 X6 32 *)
  0xd360fccb;       (* arm_LSR X11 X6 32 *)
  0xeb06018e;       (* arm_SUBS X14 X12 X6 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e00e7;       (* arm_SUBS X7 X7 X14 *)
  0xfa0d0108;       (* arm_SBCS X8 X8 X13 *)
  0xfa0c0129;       (* arm_SBCS X9 X9 X12 *)
  0xda0b00ce;       (* arm_SBC X14 X6 X11 *)
  0xab0e014a;       (* arm_ADDS X10 X10 X14 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xd3607cec;       (* arm_LSL X12 X7 32 *)
  0xd360fceb;       (* arm_LSR X11 X7 32 *)
  0xeb07018e;       (* arm_SUBS X14 X12 X7 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0108;       (* arm_SUBS X8 X8 X14 *)
  0xfa0d0129;       (* arm_SBCS X9 X9 X13 *)
  0xfa0c014a;       (* arm_SBCS X10 X10 X12 *)
  0xda0b00ee;       (* arm_SBC X14 X7 X11 *)
  0xab0e00c6;       (* arm_ADDS X6 X6 X14 *)
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
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0xb1000505;       (* arm_ADDS X5 X8 (rvalue (word 1)) *)
  0xfa0b012b;       (* arm_SBCS X11 X9 X11 *)
  0x92c0002d;       (* arm_MOVN X13 (word 1) 32 *)
  0xba1f014c;       (* arm_ADCS X12 X10 XZR *)
  0xfa0d00cd;       (* arm_SBCS X13 X6 X13 *)
  0xfa1f00ff;       (* arm_SBCS XZR X7 XZR *)
  0x9a8820a8;       (* arm_CSEL X8 X5 X8 Condition_CS *)
  0x9a892169;       (* arm_CSEL X9 X11 X9 Condition_CS *)
  0x9a8a218a;       (* arm_CSEL X10 X12 X10 Condition_CS *)
  0x9a8621a6;       (* arm_CSEL X6 X13 X6 Condition_CS *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9011bea;       (* arm_STP X10 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa9402267;       (* arm_LDP X7 X8 X19 (Immediate_Offset (iword (&0))) *)
  0xa9412a69;       (* arm_LDP X9 X10 X19 (Immediate_Offset (iword (&16))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa9083bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&128))) *)
  0xa90933eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&144))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94807ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&128))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94927e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&144))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa9083bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&128))) *)
  0xa90913e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0xa9452be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa9043bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&64))) *)
  0xa90533eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&80))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94407ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&64))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94527e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&80))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa9043bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&64))) *)
  0xa90513e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&80))) *)
  0xa9401be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa9480fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&128))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9490fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&144))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9001be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa90123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9480fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&128))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9490fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&144))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9061be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&96))) *)
  0xa90723e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa9442267;       (* arm_LDP X7 X8 X19 (Immediate_Offset (iword (&64))) *)
  0xa9452a69;       (* arm_LDP X9 X10 X19 (Immediate_Offset (iword (&80))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa90a3bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&160))) *)
  0xa90b33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&176))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94a07ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&160))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94b27e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&176))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa90a3bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&160))) *)
  0xa90b13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&176))) *)
  0xa9401be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa9440fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&64))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9450fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&80))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9001be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa90123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa9422267;       (* arm_LDP X7 X8 X19 (Immediate_Offset (iword (&32))) *)
  0xa9432a69;       (* arm_LDP X9 X10 X19 (Immediate_Offset (iword (&48))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa9063bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&96))) *)
  0xa90733eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&112))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94607ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&96))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94727e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&112))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa9063bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&96))) *)
  0xa90713e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&112))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb04006f;       (* arm_SUBS X15 X3 X4 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xa9083bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&128))) *)
  0xa90933eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&144))) *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0x9b0a7ccd;       (* arm_MUL X13 X6 X10 *)
  0x9bc97cac;       (* arm_UMULH X12 X5 X9 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090140;       (* arm_SUBS X0 X10 X9 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0x9bc07de0;       (* arm_UMULH X0 X15 X0 *)
  0xda812021;       (* arm_CINV X1 X1 Condition_CC *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xca010000;       (* arm_EOR X0 X0 X1 *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0101ce;       (* arm_ADC X14 X14 X1 *)
  0xeb0300a3;       (* arm_SUBS X3 X5 X3 *)
  0xfa0400c4;       (* arm_SBCS X4 X6 X4 *)
  0xda1f03e5;       (* arm_NGC X5 XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca050063;       (* arm_EOR X3 X3 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xca050084;       (* arm_EOR X4 X4 X5 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0xfa0a0108;       (* arm_SBCS X8 X8 X10 *)
  0xda1f03e9;       (* arm_NGC X9 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca0900aa;       (* arm_EOR X10 X5 X9 *)
  0xa94807ef;       (* arm_LDP X15 X1 SP (Immediate_Offset (iword (&128))) *)
  0xab0f016f;       (* arm_ADDS X15 X11 X15 *)
  0xba010181;       (* arm_ADCS X1 X12 X1 *)
  0xa94927e5;       (* arm_LDP X5 X9 SP (Immediate_Offset (iword (&144))) *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8d;       (* arm_MUL X13 X4 X8 *)
  0x9bc77c6c;       (* arm_UMULH X12 X3 X7 *)
  0xab0d0170;       (* arm_ADDS X16 X11 X13 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0180;       (* arm_ADCS X0 X12 X14 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xeb040063;       (* arm_SUBS X3 X3 X4 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb070100;       (* arm_SUBS X0 X8 X7 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0x9b007c70;       (* arm_MUL X16 X3 X0 *)
  0x9bc07c60;       (* arm_UMULH X0 X3 X0 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xca040210;       (* arm_EOR X16 X16 X4 *)
  0xca040000;       (* arm_EOR X0 X0 X4 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0001ad;       (* arm_ADCS X13 X13 X0 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a016b;       (* arm_EOR X11 X11 X10 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xca0a018c;       (* arm_EOR X12 X12 X10 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0xca0a01ad;       (* arm_EOR X13 X13 X10 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca0a01ce;       (* arm_EOR X14 X14 X10 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0a0043;       (* arm_ADCS X3 X2 X10 *)
  0xba1f0144;       (* arm_ADCS X4 X10 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0f01ad;       (* arm_ADDS X13 X13 X15 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a02014a;       (* arm_ADC X10 X10 X2 *)
  0xd3607d70;       (* arm_LSL X16 X11 32 *)
  0xd360fd6f;       (* arm_LSR X15 X11 32 *)
  0xeb0b0201;       (* arm_SUBS X1 X16 X11 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb01018c;       (* arm_SUBS X12 X12 X1 *)
  0xfa0001ad;       (* arm_SBCS X13 X13 X0 *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xda0f016b;       (* arm_SBC X11 X11 X15 *)
  0xd3607d90;       (* arm_LSL X16 X12 32 *)
  0xd360fd8f;       (* arm_LSR X15 X12 32 *)
  0xeb0c0201;       (* arm_SUBS X1 X16 X12 *)
  0xda1f01e0;       (* arm_SBC X0 X15 XZR *)
  0xeb0101ad;       (* arm_SUBS X13 X13 X1 *)
  0xfa0001ce;       (* arm_SBCS X14 X14 X0 *)
  0xfa10016b;       (* arm_SBCS X11 X11 X16 *)
  0xda0f018c;       (* arm_SBC X12 X12 X15 *)
  0xab0b0063;       (* arm_ADDS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x91000542;       (* arm_ADD X2 X10 (rvalue (word 1)) *)
  0xd3607c4f;       (* arm_LSL X15 X2 32 *)
  0xcb0201f0;       (* arm_SUB X16 X15 X2 *)
  0xab0201ad;       (* arm_ADDS X13 X13 X2 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0x92607cf0;       (* arm_AND X16 X7 (rvalue (word 18446744069414584320)) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0x925ff8ef;       (* arm_AND X15 X7 (rvalue (word 18446744069414584319)) *)
  0x9a0f0084;       (* arm_ADC X4 X4 X15 *)
  0xa9083bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&128))) *)
  0xa90913e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa9460fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&96))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9470fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&112))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9440660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&64))) *)
  0xa9450e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&80))) *)
  0xaa010004;       (* arm_ORR X4 X0 X1 *)
  0xaa030045;       (* arm_ORR X5 X2 X3 *)
  0xaa050084;       (* arm_ORR X4 X4 X5 *)
  0xeb1f009f;       (* arm_CMP X4 XZR *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa940368c;       (* arm_LDP X12 X13 X20 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa941368c;       (* arm_LDP X12 X13 X20 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94817e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&128))) *)
  0xa942368c;       (* arm_LDP X12 X13 X20 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa9491fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&144))) *)
  0xa943368c;       (* arm_LDP X12 X13 X20 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94a27e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&160))) *)
  0xd280002c;       (* arm_MOV X12 (rvalue (word 1)) *)
  0xb2407fed;       (* arm_MOV X13 (rvalue (word 4294967295)) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94b2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0xd2c0002d;       (* arm_MOVZ X13 (word 1) 32 *)
  0x9a9f114a;       (* arm_CSEL X10 X10 XZR Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0xa9000620;       (* arm_STP X0 X1 X17 (Immediate_Offset (iword (&0))) *)
  0xa9010e22;       (* arm_STP X2 X3 X17 (Immediate_Offset (iword (&16))) *)
  0xa9021624;       (* arm_STP X4 X5 X17 (Immediate_Offset (iword (&32))) *)
  0xa9031e26;       (* arm_STP X6 X7 X17 (Immediate_Offset (iword (&48))) *)
  0xa9042628;       (* arm_STP X8 X9 X17 (Immediate_Offset (iword (&64))) *)
  0xa9052e2a;       (* arm_STP X10 X11 X17 (Immediate_Offset (iword (&80))) *)
  0x910303ff;       (* arm_ADD SP SP (rvalue (word 192)) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let SM2_MONTJMIXADD_EXEC = ARM_MK_EXEC_RULE sm2_montjmixadd_mc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let sm2shortishredlemma = prove
 (`!n. n < 24 * 2 EXP 256
       ==> let q = n DIV 2 EXP 256 + 1 in
           q <= 24 /\
           q < 2 EXP 64 /\
           q * p_sm2 <= n + p_sm2 /\
           n < q * p_sm2 + p_sm2`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let sm2shortintredlemma = prove
 (`!n. --(&p_sm2) <= n /\ n <= &4 * &2 pow 256
       ==> let q = (&2 pow 256 + n) div &2 pow 256 in
           &0 <= q /\ q < &6 /\
           q < &2 pow 64 /\
           q * &p_sm2 <= n + &p_sm2 /\
           n < q * &p_sm2 + &p_sm2`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 256 + n:int = &1 * &2 pow 256 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_sm2] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 256` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_sm2` THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_sm2` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_sm2] THEN INT_ARITH_TAC);;

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

let sm2shortredlemma = prove
 (`!n. n < 3 * p_sm2
       ==> let q = (n DIV 2 EXP 256) + 1 in
           q <= 3 /\
           q * p_sm2 <= n + p_sm2 /\
           n < q * p_sm2 + p_sm2`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC);;

let VAL_WORD_MADDL_0 = prove
 (`!x y. val(word(0 + val(x:int32) * val(y:int32)):int64) = val x * val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; VAL_WORD_EQ_EQ] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[GSYM DIMINDEX_32; VAL_BOUND]);;

let DIVMOD_33_31 = prove
 (`!n. (2 EXP 33 * n) MOD 2 EXP 64 = 2 EXP 33 * n MOD 2 EXP 31`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let VAL_WORD_SPLIT32 = prove
 (`!x. 2 EXP 32 * val(word_zx(word_ushr x 32):int32) + val(word_zx x:int32) =
       val(x:int64)`,
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM MOD_MULT_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND_64]);;

let lvs =
 ["x_1",[`X19`;`0`];
  "y_1",[`X19`;`32`];
  "z_1",[`X19`;`64`];
  "x_2",[`X20`;`0`];
  "y_2",[`X20`;`32`];
  "z_2",[`X20`;`64`];
  "x_3",[`X17`;`0`];
  "y_3",[`X17`;`32`];
  "z_3",[`X17`;`64`];
  "zp2",[`SP`;`0`];
  "ww",[`SP`;`0`];
  "resx",[`SP`;`0`];
  "yd",[`SP`;`32`];
  "y2a",[`SP`;`32`];
  "x2a",[`SP`;`64`];
  "zzx2",[`SP`;`64`];
  "zz",[`SP`;`96`];
  "t1",[`SP`;`96`];
  "t2",[`SP`;`128`];
  "zzx1",[`SP`;`128`];
  "resy",[`SP`;`128`];
  "xd",[`SP`;`160`];
  "resz",[`SP`;`160`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_SM2_TAC =
  ARM_MACRO_SIM_ABBREV_TAC sm2_montjmixadd_mc 126 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x1db8) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) sm2_montjmixadd_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X17 s = read X17 t /\
              read X19 s = read X19 t /\
              read X20 s = read X20 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a)
             (\s. read PC s = pcout /\
                  (a EXP 2 <= 2 EXP 256 * p_sm2
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 4)) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a EXP 2) MOD p_sm2))
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                       X11; X12; X13; X14; X15; X16] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC SM2_MONTJMIXADD_EXEC (1--126)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Squaring and Montgomery reduction of lower half ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC
   [7;9;14;16;18;19;20;21;22;23;24;
    25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40]
   (1--40) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s37; sum_s38; sum_s39; sum_s40] =
    bignum_of_wordlist[x_0;x_1] EXP 2 +
    p_sm2 * bignum_of_wordlist[sum_s7; sum_s29]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `x_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC
   [41;42;49;54;55;57;58;59;60;61;63;64;65] (41--65) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s41; sum_s63; sum_s64; sum_s65] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
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

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC (66--113) (66--113) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
        [sum_s97; sum_s110; sum_s111; sum_s112; sum_s113]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 256 * t =
      a EXP 2 +
      p_sm2 * bignum_of_wordlist [sum_s7; sum_s29; sum_s71; sum_s80]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
       `(bignum_of_wordlist[x_0;x_1] EXP 2 +
         p_sm2 * bignum_of_wordlist[sum_s7; sum_s29]) +
        2 * 2 EXP 128 *
            bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3] +
        2 EXP 256 * bignum_of_wordlist[x_2;x_3] EXP 2 +
        2 EXP 128 * p_sm2 * bignum_of_wordlist [sum_s71; sum_s80]` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o
                           RAND_CONV o RAND_CONV) [SYM th]);
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC
   [115;116;118;119;120] (114--126) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_sm2 then &t:real else &t - &p_sm2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s120 <=> t < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_SM2_TAC =
  ARM_MACRO_SIM_ABBREV_TAC sm2_montjmixadd_mc 170 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = b
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x1db8) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) sm2_montjmixadd_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X17 s = read X17 t /\
              read X19 s = read X19 t /\
              read X20 s = read X20 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              b)
             (\s. read PC s = pcout /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                        X11; X12; X13; X14; X15; X16] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC SM2_MONTJMIXADD_EXEC (1--170)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** First ADK block multiplying lower halves.
   ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC
   ([5;6;8] @ (10--14) @ [20] @ (26--28)) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s5; sum_s26; sum_s27; sum_s28] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[y_0;y_1]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
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

  (*** the two Montgomery steps on the low half ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC (29--46) (29--46) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s41; sum_s42; sum_s43; sum_s44] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[y_0;y_1] +
    p_sm2 * bignum_of_wordlist[mullo_s5; sum_s33]`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ABBREV_TAC `L' = bignum_of_wordlist[sum_s41; sum_s42; sum_s43; sum_s44]` THEN

  (*** Second ADK block multiplying upper halves. ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC
   ([47;48;50] @ (52--56) @ [62] @ (68--70)) (47--70) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s47; sum_s68; sum_s69; sum_s70] =
    bignum_of_wordlist[x_2;x_3] * bignum_of_wordlist[y_2;y_3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
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

  (*** First absolute difference computation ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC [71;72;76;78] (71--78) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s76;sum_s78]) =
    abs(&(bignum_of_wordlist[x_2;x_3]) - &(bignum_of_wordlist[x_0;x_1])) /\
    (carry_s72 <=> bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Second absolute difference computation ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC [79;80;84;86] (79--86) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s84;sum_s86]) =
    abs(&(bignum_of_wordlist[y_0;y_1]) - &(bignum_of_wordlist[y_2;y_3])) /\
    (carry_s80 <=> bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Collective sign-magnitude representation  of middle product ***)

  ARM_STEPS_TAC SM2_MONTJMIXADD_EXEC [87] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_MASKS]) THEN
  ABBREV_TAC
   `msgn <=> ~(bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1] <=>
               bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])` THEN
  SUBGOAL_THEN
   `--(&1) pow bitval msgn *
    &(bignum_of_wordlist[sum_s76;sum_s78] *
      bignum_of_wordlist[sum_s84;sum_s86]) =
    (&(bignum_of_wordlist[x_2;x_3]) - &(bignum_of_wordlist[x_0;x_1])) *
    (&(bignum_of_wordlist[y_0;y_1]) - &(bignum_of_wordlist[y_2;y_3]))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SGN_ABS] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_RING
     `(~(z = &0) ==> x = y) ==> x * z = y * z`) THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_ABS_ZERO; REAL_SUB_0; DE_MORGAN_THM] THEN
    EXPAND_TAC "msgn" THEN POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_BITVAL; REAL_POW_ONE] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(x - y) * (u - v):real = (y - x) * (v - u)`] THEN
    REWRITE_TAC[REAL_SGN_MUL; GSYM REAL_OF_NUM_LT; real_sgn; REAL_SUB_LT] THEN
    REWRITE_TAC[MESON[]
     `(if p <=> q then x else y) =
      (if p then if q then x else y else if q then y else x)`] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** the H + L' addition (a result that we then use twice) ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC (88--94) (88--94) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s89; sum_s90; sum_s92; sum_s93; word(bitval carry_s93)] =
    bignum_of_wordlist[x_2;x_3] * bignum_of_wordlist[y_2;y_3] + L'`
  ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Third and final ADK block computing the mid-product ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC
   ([95;96;98] @ (100--104) @ [110] @ (116--118)) (95--118) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s95; sum_s116; sum_s117; sum_s118] =
    bignum_of_wordlist[sum_s76;sum_s78] *
    bignum_of_wordlist[sum_s84;sum_s86]`
  (SUBST_ALL_TAC o SYM) THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
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

  (*** Big net accumulation computation absorbing cases over sign ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC
   ([121;123;125] @ (127--135)) (119--135) THEN
  SUBGOAL_THEN
   `2 EXP 128 *
    bignum_of_wordlist
      [sum_s121; sum_s123; sum_s131; sum_s132; sum_s133; sum_s134; sum_s135] =
    a * b + p_sm2 * (2 EXP 128 + 1) * bignum_of_wordlist[mullo_s5; sum_s33]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&a * &b +
      &p_sm2 * (&2 pow 128 + &1) * &(bignum_of_wordlist[mullo_s5; sum_s33]) =
      (&2 pow 128 + &1) *
      &(2 EXP 128 * bignum_of_wordlist
        [sum_s89; sum_s90; sum_s92; sum_s93; word(bitval carry_s93)]) +
      &2 pow 128 *
      -- &1 pow bitval msgn *
        &(bignum_of_wordlist[mullo_s95; sum_s116; sum_s117; sum_s118])`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[VAL_WORD_BITVAL]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    BOOL_CASES_TAC `msgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_XOR_NOT; WORD_XOR_0;
                SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Last two Montgomery steps to get the pre-reduced result ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC (136--154) (136--154) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s148; sum_s149; sum_s152; sum_s153; sum_s154]` THEN
  SUBGOAL_THEN
   `2 EXP 256 * t =
    a * b +
    p_sm2 * ((2 EXP 128 + 1) * bignum_of_wordlist[mullo_s5; sum_s33] +
             2 EXP 128 * bignum_of_wordlist[sum_s121; sum_s140])`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC
      (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
      [SYM th]) THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(MAP_EVERY SUBST1_TAC o
      filter (is_ratconst o rand o concl) o CONJUNCTS) THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN
   `t < 3 * p_sm2 /\ (2 EXP 256 * t == a * b) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `ab <= 2 EXP 256 * p
      ==> 2 EXP 256 * t < ab + 2 * 2 EXP 256 * p ==> t < 3 * p`)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
    ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = t DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 3 * p_sm2` THEN REWRITE_TAC[p_sm2] THEN
    EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s154:int64 = word h` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "t"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:num` sm2shortredlemma) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC THEN

  (*** Computation of t - (h + 1) * p_sm2 ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC (158--161) (155--162) THEN
  MP_TAC(SPECL
   [`word_neg(word(bitval(~carry_s161))):int64`;
    `&(bignum_of_wordlist[sum_s158; sum_s159; sum_s160; sum_s161]):real`;
    `256`; `t:num`; `(h + 1) * p_sm2`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_NOT_MASK; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_sm2 <= t + p_sm2`;
        `t < (h + 1) * p_sm2 + p_sm2`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist[sum_s148; sum_s149; sum_s152; sum_s153; word h] =
      t`)) THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REWRITE_TAC[REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    REWRITE_TAC[WORD_ARITH `word_neg x = word_neg y <=> val x = val y`] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; EQ_BITVAL] THEN
    REWRITE_TAC[TAUT `(~p <=> q) <=> (p <=> ~q)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP]) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC [163;165;166;168] (163--170) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> t < (h + 1) * p_sm2` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &t - y + z ==> &t = x + y - z`)) THEN
  REWRITE_TAC[p_sm2] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_SM2_TAC =
  ARM_MACRO_SIM_ABBREV_TAC sm2_montjmixadd_mc 17 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x1db8) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) sm2_montjmixadd_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X17 s = read X17 t /\
              read X19 s = read X19 t /\
              read X20 s = read X20 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < p_sm2 /\ n < p_sm2
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&m - &n) rem &p_sm2))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
           MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC (1--8) (1--8) THEN

  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ARM_STEPS_TAC SM2_MONTJMIXADD_EXEC [9] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_ACCSTEPS_TAC SM2_MONTJMIXADD_EXEC (10--17) (10--17) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s17" THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `--(&(bitval(m < n))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
  REWRITE_TAC[INT_ARITH `m - n:int = --b * p + z <=> z = b * p + m - n`] THEN
  REWRITE_TAC[int_eq; int_le; int_lt] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th; int_sub_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC(REAL_ARITH
  `!t:real. p < t /\
            (&0 <= a /\ a < p) /\
            (&0 <= z /\ z < t) /\
            ((&0 <= z /\ z < t) /\ (&0 <= a /\ a < t) ==> z = a)
            ==> z = a /\ &0 <= z /\ z < p`) THEN
  EXISTS_TAC `(&2:real) pow 256` THEN

  CONJ_TAC THENL [REWRITE_TAC[p_sm2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_sm2`; `n < p_sm2`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_sm2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; STRIP_TAC] THEN

  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_sm2] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_sm2 ==> x < p_sm2 /\ &x = &a rem &p_sm2`,
  REWRITE_TAC[INT_OF_NUM_REM; p_sm2] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_sm2 ==> x < p_sm2 /\ &x = a rem &p_sm2`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_sm2] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_sm2 = (&i * x rem &p_sm2 * y rem &p_sm2) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_sm2 = (&(NUMERAL n) * &x rem &p_sm2) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_sm2 (2 EXP 256)) *
    (&2 pow 256 * x) rem &p_sm2 * (&2 pow 256 * y) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * x * y) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_sm2] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 256 * x) rem &p_sm2 + (&2 pow 256 * y) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * (x + y)) rem &p_sm2 /\
   ((&2 pow 256 * x) rem &p_sm2 - (&2 pow 256 * y) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * (x - y)) rem &p_sm2 /\
   (&(NUMERAL n) * (&2 pow 256 * x) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * (&(NUMERAL n) * x)) rem &p_sm2`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_sm2 (2 EXP 256)) * (&2 pow 256 * x) rem &p_sm2) rem &p_sm2 =
   x rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_sm2
         ==> x =
             (2 EXP 256 * (inverse_mod p_sm2 (2 EXP 256) * x) MOD p_sm2) MOD
             p_sm2`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_affine_sm2 = prove
 (`weierstrass_of_jacobian (integer_mod_ring p_sm2)
                           (x rem &p_sm2,y rem &p_sm2,&1 rem &p_sm2) =
   SOME(x rem &p_sm2,y rem &p_sm2)`,
  MP_TAC(ISPEC `integer_mod_ring p_sm2` RING_INV_1) THEN
  REWRITE_TAC[weierstrass_of_jacobian; ring_div; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_sm2] THEN CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[GSYM p_sm2; option_INJ; PAIR_EQ; INT_MUL_RID; INT_REM_REM]);;

let weierstrass_of_jacobian_sm2_add = prove
 (`!P1 P2 x1 y1 z1 x2 y2 z2 x3 y3 z3.
        ~(weierstrass_of_jacobian (integer_mod_ring p_sm2)
           (x1 rem &p_sm2,y1 rem &p_sm2,z1 rem &p_sm2) =
          weierstrass_of_jacobian (integer_mod_ring p_sm2)
           (x2 rem &p_sm2,y2 rem &p_sm2,z2 rem &p_sm2)) /\
        jacobian_add_unexceptional ccsm2
         (x1 rem &p_sm2,y1 rem &p_sm2,z1 rem &p_sm2)
         (x2 rem &p_sm2,y2 rem &p_sm2,z2 rem &p_sm2) =
        (x3 rem &p_sm2,y3 rem &p_sm2,z3 rem &p_sm2)
        ==> weierstrass_of_jacobian (integer_mod_ring p_sm2)
                (x1 rem &p_sm2,y1 rem &p_sm2,z1 rem &p_sm2) = P1 /\
            weierstrass_of_jacobian (integer_mod_ring p_sm2)
                (x2 rem &p_sm2,y2 rem &p_sm2,z2 rem &p_sm2) = P2
            ==> weierstrass_of_jacobian (integer_mod_ring p_sm2)
                  (x3 rem &p_sm2,y3 rem &p_sm2,z3 rem &p_sm2) =
                group_mul sm2_group P1 P2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[ccsm2; SM2_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(MP_TAC o PART_MATCH (rand o rand) WEIERSTRASS_OF_JACOBIAN_EQ o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_PSM2] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_sm2; b_sm2] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_sm2 = new_definition
 `represents_sm2 P (x,y,z) <=>
        x < p_sm2 /\ y < p_sm2 /\ z < p_sm2 /\
        weierstrass_of_jacobian (integer_mod_ring p_sm2)
         (tripled (montgomery_decode (256,p_sm2)) (x,y,z)) = P`;;

let represents2_sm2 = new_definition
 `represents2_sm2 P (x,y) <=>
        x < p_sm2 /\ y < p_sm2 /\
        SOME(paired (montgomery_decode (256,p_sm2)) (x,y)) = P`;;

let SM2_MONTJMIXADD_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,192))
            [(word pc,0x1db8); (p1,96); (p2,64); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0x1db8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) sm2_montjmixadd_mc /\
                  read PC s = word(pc + 0x8) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_pair_from_memory (p2,4) s = t2)
             (\s. read PC s = word (pc + 0x1dac) /\
                  !P1 P2. represents_sm2 P1 t1 /\
                          represents2_sm2 P2 t2 /\
                          ~(P1 = P2)
                          ==> represents_sm2 (group_mul sm2_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`; `p2:int64`;
    `x2:num`; `y2:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ;
              bignum_pair_from_memory; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_SM2_TAC 3 ["zp2";"z_1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y2a";"z_1";"y_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["x2a";"zp2";"x_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y2a";"zp2";"y2a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["xd";"x2a";"x_1"] THEN
  LOCAL_SUB_SM2_TAC 0 ["yd";"y2a";"y_1"] THEN
  LOCAL_MONTSQR_SM2_TAC 0 ["zz";"xd"] THEN
  LOCAL_MONTSQR_SM2_TAC 0 ["ww";"yd"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["zzx1";"zz";"x_1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["zzx2";"zz";"x2a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["resx";"ww";"zzx1"] THEN
  LOCAL_SUB_SM2_TAC 0 ["t1";"zzx2";"zzx1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["resz";"xd";"z_1"] THEN
  LOCAL_SUB_SM2_TAC 0 ["resx";"resx";"zzx2"] THEN
  LOCAL_SUB_SM2_TAC 0 ["t2";"zzx1";"resx"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["t1";"t1";"y_1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["t2";"yd";"t2"] THEN
  LOCAL_SUB_SM2_TAC 0 ["resy";"t2";"t1"] THEN

  BIGNUM_LDIGITIZE_TAC "z1_"
   `read (memory :> bytes (word_add p1 (word 64),8 * 4)) s21` THEN
  BIGNUM_LDIGITIZE_TAC "x2_"
   `read (memory :> bytes (p2,8 * 4)) s21` THEN
  BIGNUM_LDIGITIZE_TAC "y2_"
   `read (memory :> bytes (word_add p2 (word 32),8 * 4)) s21` THEN
  BIGNUM_LDIGITIZE_TAC "resx_"
   `read (memory :> bytes (stackpointer,8 * 4)) s21` THEN
  BIGNUM_LDIGITIZE_TAC "resy_"
   `read (memory :> bytes (word_add stackpointer (word 128),8 * 4)) s21` THEN
  BIGNUM_LDIGITIZE_TAC "resz_"
   `read (memory :> bytes (word_add stackpointer (word 160),8 * 4)) s21` THEN
  ARM_STEPS_TAC SM2_MONTJMIXADD_EXEC (22--58) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s58" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  MAP_EVERY X_GEN_TAC [`P1:(int#int)option`; `P2:(int#int)option`] THEN
  REWRITE_TAC[represents_sm2; represents2_sm2; tripled; paired] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_sm2] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_sm2]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; INT_OF_NUM_EQ; WORD_OR_EQ_0] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MP_TAC(SPEC `[z1_0:int64;z1_1;z1_2;z1_3]` BIGNUM_OF_WORDLIST_EQ_0) THEN
  ASM_REWRITE_TAC[ALL; GSYM INT_OF_NUM_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONJ_TAC THENL [REWRITE_TAC[p_sm2] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p_sm2] THEN
    CONV_TAC(LAND_CONV(funpow 3 RAND_CONV
     (ONCE_DEPTH_CONV INVERSE_MOD_CONV))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ONCE_REWRITE_TAC[GSYM MOD_MOD_REFL] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    REWRITE_TAC[GSYM p_sm2; GSYM(NUM_REDUCE_CONV `2 EXP 256`)] THEN
    REWRITE_TAC[MOD_MOD_REFL] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[weierstrass_of_affine_sm2] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
    EXPAND_TAC "P1" THEN REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[SM2_GROUP; weierstrass_add];
    ALL_TAC] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma)
   [`y2:num`; `x2:num`; `z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_sm2 (2 EXP 256) * x1`;
    `y1d = inverse_mod p_sm2 (2 EXP 256) * y1`;
    `z1d = inverse_mod p_sm2 (2 EXP 256) * z1`;
    `x2d = inverse_mod p_sm2 (2 EXP 256) * x2`;
    `y2d = inverse_mod p_sm2 (2 EXP 256) * y2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REM_DOWN_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_ADD_REM; GSYM INT_SUB_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[lemont; demont]) THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_REM_REM] THEN
  REWRITE_TAC[pumont; dismont; unmont] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [GSYM
    weierstrass_of_affine_sm2]) THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_sm2_add THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_add_unexceptional; ccsm2;
                  INTEGER_MOD_RING_CLAUSES] THEN
  SUBGOAL_THEN `~(&z1d rem &p_sm2 = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(&z1:int = &0)` THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    REWRITE_TAC[INT_REM_EQ_0] THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[p_sm2] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_sm2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let SM2_MONTJMIXADD_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 208),208))
            [(word pc,0x1db8); (p1,96); (p2,64); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0x1db8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) sm2_montjmixadd_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_pair_from_memory (p2,4) s = t2)
             (\s. read PC s = returnaddress /\
                  !P1 P2. represents_sm2 P1 t1 /\
                          represents2_sm2 P2 t2 /\
                          ~(P1 = P2)
                          ==> represents_sm2 (group_mul sm2_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 208),208)])`,
  ARM_ADD_RETURN_STACK_TAC SM2_MONTJMIXADD_EXEC
   SM2_MONTJMIXADD_CORRECT `[X19; X20]` 208);;
