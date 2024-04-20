(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 8x8 -> 16 squaring, using Karatsuba reduction and nested ADK.             *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_8_16.o";;
 ****)

let bignum_sqr_8_16_mc = define_assert_from_elf "bignum_sqr_8_16_mc" "arm/fastmul/bignum_sqr_8_16.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x9b047c51;       (* arm_MUL X17 X2 X4 *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x9bc47c54;       (* arm_UMULH X20 X2 X4 *)
  0xeb030055;       (* arm_SUBS X21 X2 X3 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x9bc57c75;       (* arm_UMULH X21 X3 X5 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
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
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
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
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xa9022c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa903380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&48))) *)
  0x9b087cd1;       (* arm_MUL X17 X6 X8 *)
  0x9b097cee;       (* arm_MUL X14 X7 X9 *)
  0x9bc87cd4;       (* arm_UMULH X20 X6 X8 *)
  0xeb0700d5;       (* arm_SUBS X21 X6 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb08012c;       (* arm_SUBS X12 X9 X8 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x9bc97cf5;       (* arm_UMULH X21 X7 X9 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x9b067ccc;       (* arm_MUL X12 X6 X6 *)
  0x9b077ced;       (* arm_MUL X13 X7 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67ccb;       (* arm_UMULH X11 X6 X6 *)
  0x9bc77cee;       (* arm_UMULH X14 X7 X7 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9042c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&64))) *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa9054c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&80))) *)
  0x9b087d0c;       (* arm_MUL X12 X8 X8 *)
  0x9b097d2d;       (* arm_MUL X13 X9 X9 *)
  0x9b097d0f;       (* arm_MUL X15 X8 X9 *)
  0x9bc87d0b;       (* arm_UMULH X11 X8 X8 *)
  0x9bc97d2e;       (* arm_UMULH X14 X9 X9 *)
  0x9bc97d10;       (* arm_UMULH X16 X8 X9 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xa9062c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&96))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa907380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&112))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9b087c8f;       (* arm_MUL X15 X4 X8 *)
  0x9b097cb0;       (* arm_MUL X16 X5 X9 *)
  0x9bc67c51;       (* arm_UMULH X17 X2 X6 *)
  0xab1101ce;       (* arm_ADDS X14 X14 X17 *)
  0x9bc77c71;       (* arm_UMULH X17 X3 X7 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0x9bc87c91;       (* arm_UMULH X17 X4 X8 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc97cb1;       (* arm_UMULH X17 X5 X9 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab0a01cb;       (* arm_ADDS X11 X14 X10 *)
  0xba0e01ee;       (* arm_ADCS X14 X15 X14 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xab0a01cc;       (* arm_ADDS X12 X14 X10 *)
  0xba0b01ed;       (* arm_ADCS X13 X15 X11 *)
  0xba0e020e;       (* arm_ADCS X14 X16 X14 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba1003f0;       (* arm_ADCS X16 XZR X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xeb050096;       (* arm_SUBS X22 X4 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb080134;       (* arm_SUBS X20 X9 X8 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb030056;       (* arm_SUBS X22 X2 X3 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb0600f4;       (* arm_SUBS X20 X7 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba14018c;       (* arm_ADCS X12 X12 X20 *)
  0xba1301ad;       (* arm_ADCS X13 X13 X19 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050076;       (* arm_SUBS X22 X3 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070134;       (* arm_SUBS X20 X9 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040056;       (* arm_SUBS X22 X2 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060114;       (* arm_SUBS X20 X8 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15018c;       (* arm_ADCS X12 X12 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050056;       (* arm_SUBS X22 X2 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060134;       (* arm_SUBS X20 X9 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040076;       (* arm_SUBS X22 X3 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070114;       (* arm_SUBS X20 X8 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xab0a014a;       (* arm_ADDS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xa9420c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&32))) *)
  0xab02014a;       (* arm_ADDS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa9430c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&48))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xa903340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xa9440c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&64))) *)
  0xba0201ce;       (* arm_ADCS X14 X14 X2 *)
  0xba0301ef;       (* arm_ADCS X15 X15 X3 *)
  0xa9043c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&64))) *)
  0xa9450c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&80))) *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba030231;       (* arm_ADCS X17 X17 X3 *)
  0xa9054410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&80))) *)
  0xa9460c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xba130042;       (* arm_ADCS X2 X2 X19 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xa9060c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xa9470c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9070c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_8_16_EXEC = ARM_MK_EXEC_RULE bignum_sqr_8_16_mc;;

(* bignum_sqr_8_16 without callee-save register spilling. *)
let bignum_sqr_8_16_core_mc_def,
    bignum_sqr_8_16_core_mc,
    BIGNUM_SQR_8_16_CORE_EXEC =
  mk_sublist_of_mc "bignum_sqr_8_16_core_mc"
    bignum_sqr_8_16_mc
    (`8`,`LENGTH bignum_sqr_8_16_mc - 20`)
    BIGNUM_SQR_8_16_EXEC;;

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

let ADK_48_TAC =
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
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;;

let BIGNUM_SQR_8_16_CORE_CORRECT = prove
 (`!z x a pc.
      nonoverlapping (word pc,0x49c) (z,8 * 16)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word (pc + 0x8)) bignum_sqr_8_16_core_mc /\
                 read PC s = word(pc + 0x8) /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
          (\s. read PC s = word (pc + 0x490) /\
               bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  ABBREV_TAC `pc' = pc + 0x8` THEN
  SUBGOAL_THEN `pc+1168=pc'+1160` SUBST_ALL_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping_modulo (2 EXP 64) (val (z:int64),8 * 16) (pc',1172)`
  ASSUME_TAC THENL [EXPAND_TAC "pc'" THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN

  (*** First nested mini-ADK 4x4 squaring block ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_CORE_EXEC
   [5;6;13;18;19;21;22;23;24;25;27;28;29;30;31;32;33;34;35;36;37;
    41;42;43;44;45;46;48;49;50;51;52;54;55;56;60;61;62;63;64;65;
    66;67;69;70]
   (1--71) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2 =
    bignum_of_wordlist [mullo_s35; sum_s44; sum_s48; sum_s49;
                        sum_s66; sum_s67; sum_s69; sum_s70]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Second nested mini-ADK 4x4 squaring block ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_CORE_EXEC
   [72;73;80;85;86;88;89;90;91;92;94;95;96;97;98;99;100;101;102;103;
    104;108;109;110;111;112;113;115;116;117;118;119;121;122;123;127;
    128;129;130;131;132;133;134;136;137]
   (72--138) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2 =
    bignum_of_wordlist [mullo_s102;sum_s111;sum_s115;sum_s116;
                        sum_s133;sum_s134;sum_s136;sum_s137]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Nested ADK 4x4 multiplication block ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_CORE_EXEC
   [139;140;141;142;144;146;148;150;151;152;153;154;155;156;157;
    158;159;160;161;167;172;174;175;181;186;188;189;190;191;192;
    193;199;204;206;207;208;214;219;221;222;223;224;225;231;236;
    238;239;240;241;247;252;254;255;256;257]
   (139--257) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] *
    bignum_of_wordlist [x_4;x_5;x_6;x_7] =
    bignum_of_wordlist
     [mullo_s139; sum_s186; sum_s219; sum_s252;
      sum_s254; sum_s255; sum_s256; sum_s257]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Final accumulation simulation and 16-digit focusing ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_CORE_EXEC (258--290) (258--290) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s290" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`1024`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN

  (*** The core rearrangement we are using ***)

  SUBGOAL_THEN
   `(&a:real) pow 2 =
    &(bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2) +
    &2 pow 512 * &(bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2) +
    &2 pow 257 * &(bignum_of_wordlist [x_0;x_1;x_2;x_3] *
                   bignum_of_wordlist [x_4;x_5;x_6;x_7])`
  SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_SQR_8_16_CORRECT = prove(
  `!z x a pc.
      nonoverlapping (word pc,0x49c) (z,8 * 16)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_mc /\
                 read PC s = word(pc + 0x8) /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
          (\s. read PC s = word (pc + 0x490) /\
               bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP BIGNUM_SQR_8_16_CORE_CORRECT th)) THEN
  REWRITE_TAC[ensures] THEN
  DISCH_THEN (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
  EXISTS_TAC `x:int64` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bignum_sqr_8_16_core_mc_def;BIGNUM_SQR_8_16_EXEC;
      WORD_RULE`word (x+y)=word_add (word x) (word y)`] THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MATCH_MP_TAC ALIGNED_BYTES_LOADED_SUB_LIST THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_DIVIDES_CONV);;

let BIGNUM_SQR_8_16_SUBROUTINE_CORRECT = prove
 (`!z x a pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 16) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
          [(z,8 * 16); (word_sub stackpointer (word 32),32)]
          [(word pc,0x49c); (x,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_mc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
            (\s. read PC s = returnaddress /\
                 bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 16);
                     memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_SQR_8_16_EXEC BIGNUM_SQR_8_16_CORRECT
   `[X19;X20;X21;X22]` 32);;
