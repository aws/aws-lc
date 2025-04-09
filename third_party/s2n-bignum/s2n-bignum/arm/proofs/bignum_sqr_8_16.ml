(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 8x8 -> 16 squaring, using Karatsuba reduction and nested ADK.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* ------------------------------------------------------------------------- *)
(* Prove the functional correctness of unopt/bignum_sqr_8_16_base first.     *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/fastmul/unopt/bignum_sqr_8_16_base.o";;
 ****)

let bignum_sqr_8_16_unopt_mc = define_assert_from_elf "bignum_sqr_8_16_unopt_mc" "arm/fastmul/unopt/bignum_sqr_8_16_base.o"
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

let BIGNUM_SQR_8_16_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_sqr_8_16_unopt_mc;;

(* bignum_sqr_8_16 without callee-save register spilling. *)
let bignum_sqr_8_16_unopt_core_mc_def,
    bignum_sqr_8_16_unopt_core_mc,
    BIGNUM_SQR_8_16_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_sqr_8_16_unopt_core_mc"
    bignum_sqr_8_16_unopt_mc
    (`8`,`LENGTH bignum_sqr_8_16_unopt_mc - 20`)
    (fst BIGNUM_SQR_8_16_UNOPT_EXEC);;

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

let BIGNUM_SQR_8_16_UNOPT_CORE_CORRECT = prove
 (`!z x a pc.
      nonoverlapping (word pc,LENGTH bignum_sqr_8_16_unopt_core_mc) (z,8 * 16)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_unopt_core_mc /\
                 read PC s = word(pc) /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
          (\s. read PC s = word (pc + LENGTH bignum_sqr_8_16_unopt_core_mc) /\
               bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_SQR_8_16_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN

  (*** First nested mini-ADK 4x4 squaring block ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_UNOPT_CORE_EXEC (258--290) (258--290) THEN
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

let BIGNUM_SQR_8_16_UNOPT_CORRECT = prove(
  `!z x a pc.
      nonoverlapping (word pc,LENGTH bignum_sqr_8_16_unopt_mc) (z,8 * 16)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_unopt_mc /\
                 read PC s = word(pc + 0x8) /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
          (\s. read PC s = word ((pc + 0x8) + LENGTH bignum_sqr_8_16_unopt_core_mc) /\
               bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  ARM_SUB_LIST_OF_MC_TAC BIGNUM_SQR_8_16_UNOPT_CORE_CORRECT
      bignum_sqr_8_16_unopt_core_mc_def
      [fst BIGNUM_SQR_8_16_UNOPT_CORE_EXEC;fst BIGNUM_SQR_8_16_UNOPT_EXEC]);;

(* ------------------------------------------------------------------------- *)
(* Prove program equivalence and use it to prove full functional correctness *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_8_16.o";;
 ****)

let bignum_sqr_8_16_mc = define_assert_from_elf "bignum_sqr_8_16_mc"
    "arm/fastmul/bignum_sqr_8_16.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc00034;       (* arm_LDR Q20 X1 (Immediate_Offset (word 0)) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x3dc00435;       (* arm_LDR Q21 X1 (Immediate_Offset (word 16)) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x3dc00836;       (* arm_LDR Q22 X1 (Immediate_Offset (word 32)) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x3dc00c37;       (* arm_LDR Q23 X1 (Immediate_Offset (word 48)) *)
  0x6f00e5fe;       (* arm_MOVI Q30 (word 4294967295) *)
  0x9b047c51;       (* arm_MUL X17 X2 X4 *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x6e144281;       (* arm_EXT Q1 Q20 Q20 64 *)
  0x9bc47c54;       (* arm_UMULH X20 X2 X4 *)
  0x0f208682;       (* arm_SHRN Q2 Q20 32 32 *)
  0xeb030055;       (* arm_SUBS X21 X2 X3 *)
  0x0e813a80;       (* arm_ZIP1 Q0 Q20 Q1 32 64 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x6e1542a1;       (* arm_EXT Q1 Q21 Q21 64 *)
  0x9bc57c75;       (* arm_UMULH X21 X3 X5 *)
  0x0f2086a2;       (* arm_SHRN Q2 Q21 32 32 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x0e813aa0;       (* arm_ZIP1 Q0 Q21 Q1 32 64 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9b037c4f;       (* arm_MUL X15 X2 X3 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0x9bc37c50;       (* arm_UMULH X16 X2 X3 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9002c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&0))) *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x6e1642c1;       (* arm_EXT Q1 Q22 Q22 64 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x0f2086c2;       (* arm_SHRN Q2 Q22 32 32 *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
  0x0e813ac0;       (* arm_ZIP1 Q0 Q22 Q1 32 64 *)
  0x9b057c8f;       (* arm_MUL X15 X4 X5 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0x9bc57c90;       (* arm_UMULH X16 X4 X5 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xa9022c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&32))) *)
  0x6e1742e1;       (* arm_EXT Q1 Q23 Q23 64 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x0f2086e2;       (* arm_SHRN Q2 Q23 32 32 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x0e813ae0;       (* arm_ZIP1 Q0 Q23 Q1 32 64 *)
  0xa903380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&48))) *)
  0x9b087cd1;       (* arm_MUL X17 X6 X8 *)
  0x2ea2c050;       (* arm_UMULL_VEC Q16 Q2 Q2 32 *)
  0x9b097cee;       (* arm_MUL X14 X7 X9 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0x9bc87cd4;       (* arm_UMULH X20 X6 X8 *)
  0x2ea0c012;       (* arm_UMULL_VEC Q18 Q0 Q0 32 *)
  0xeb0700d5;       (* arm_SUBS X21 X6 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb08012c;       (* arm_SUBS X12 X9 X8 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x6f601641;       (* arm_USRA_VEC Q1 Q18 32 64 128 *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0x6f601490;       (* arm_USRA_VEC Q16 Q4 32 64 128 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x6f605492;       (* arm_SLI_VEC Q18 Q4 32 64 *)
  0x9bc97cf5;       (* arm_UMULH X21 X7 X9 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x6f601430;       (* arm_USRA_VEC Q16 Q1 32 64 128 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x4e975ab1;       (* arm_UZP2 Q17 Q21 Q23 32 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x0ea12ae4;       (* arm_XTN Q4 Q23 32 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x4e083e16;       (* arm_UMOV X22 Q16 0 8 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x0ea12aa5;       (* arm_XTN Q5 Q21 32 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4ea00aa1;       (* arm_REV64_VEC Q1 Q21 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9042c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&64))) *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0x4e183e4d;       (* arm_UMOV X13 Q18 1 8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x4e183e0e;       (* arm_UMOV X14 Q16 1 8 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0x4e083e4c;       (* arm_UMOV X12 Q18 0 8 *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0xa9054c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&80))) *)
  0x2eb1c087;       (* arm_UMULL_VEC Q7 Q4 Q17 32 *)
  0x9b097d0f;       (* arm_MUL X15 X8 X9 *)
  0x4e975af0;       (* arm_UZP2 Q16 Q23 Q23 32 *)
  0x9bc97d10;       (* arm_UMULH X16 X8 X9 *)
  0x4eb79c20;       (* arm_MUL_VEC Q0 Q1 Q23 32 *)
  0xab0f02cb;       (* arm_ADDS X11 X22 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x2eb1c201;       (* arm_UMULL_VEC Q1 Q16 Q17 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0x4e3e1ce2;       (* arm_AND_VEC Q2 Q7 Q30 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f605400;       (* arm_SHL_VEC Q0 Q0 32 64 *)
  0x6f6014e1;       (* arm_USRA_VEC Q1 Q7 32 64 128 *)
  0x2ea58080;       (* arm_UMLAL_VEC Q0 Q4 Q5 32 *)
  0x4e183c10;       (* arm_UMOV X16 Q0 1 8 *)
  0x4e083c0f;       (* arm_UMOV X15 Q0 0 8 *)
  0x6f601441;       (* arm_USRA_VEC Q1 Q2 32 64 128 *)
  0x4e083c34;       (* arm_UMOV X20 Q1 0 8 *)
  0x4e183c35;       (* arm_UMOV X21 Q1 1 8 *)
  0xa9062c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&96))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa907380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&112))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9bc67c51;       (* arm_UMULH X17 X2 X6 *)
  0xab1101ce;       (* arm_ADDS X14 X14 X17 *)
  0x9bc77c71;       (* arm_UMULH X17 X3 X7 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f02b1;       (* arm_ADC X17 X21 XZR *)
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

(* bignum_sqr_8_16_mc without ret. *)
let bignum_sqr_8_16_core_mc_def,
    bignum_sqr_8_16_core_mc,
    BIGNUM_SQR_8_16_CORE_EXEC =
  mk_sublist_of_mc "bignum_sqr_8_16_core_mc"
    bignum_sqr_8_16_mc
    (`8`,`LENGTH bignum_sqr_8_16_mc - 20`)
    (fst BIGNUM_SQR_8_16_EXEC);;

(** Equivalence relation at the begin and end of the two programs
    (after stack push/pops stripped **)

(* Equiv. states at the 'core' parts of (scalar v., neon v.).
    x and y are parameterized for nonoverlapping.
*)
let bignum_sqr_8_16_equiv_input_states = new_definition
  `!s1 s1' x z.
    (bignum_sqr_8_16_equiv_input_states:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
    (?a.
      C_ARGUMENTS [z; x] s1 /\
      C_ARGUMENTS [z; x] s1' /\
      bignum_from_memory (x,8) s1 = a /\
      bignum_from_memory (x,8) s1' = a)`;;

(* Equiv. states at the ends of 'core' parts of (scalar v., neon v.) *)
let bignum_sqr_8_16_equiv_output_states = new_definition
  `!s1 s1' x z.
    (bignum_sqr_8_16_equiv_output_states:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
    (?a c.
      bignum_from_memory (x,8) s1 = a /\
      bignum_from_memory (x,8) s1' = a /\
      bignum_from_memory (z,16) s1 = c /\
      bignum_from_memory (z,16) s1' = c)`;;

(* This diff is generated by
  'python3 gen-actions.py unopt/bignum_sqr_8_16_base.S bignum_sqr_8_16.S'
  where the two files are the disassemblied outputs from objdump.
*)

let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 2, 2, 3);
  ("insert", 2, 2, 3, 4);
  ("equal", 2, 3, 4, 5);
  ("insert", 3, 3, 5, 6);
  ("equal", 3, 4, 6, 7);
  ("insert", 4, 4, 7, 9);
  ("equal", 4, 6, 9, 11);
  ("insert", 6, 6, 11, 12);
  ("equal", 6, 7, 12, 13);
  ("insert", 7, 7, 13, 14);
  ("equal", 7, 8, 14, 15);
  ("insert", 8, 8, 15, 16);
  ("equal", 8, 9, 16, 17);
  ("insert", 9, 9, 17, 18);
  ("equal", 9, 10, 18, 19);
  ("insert", 10, 10, 19, 20);
  ("equal", 10, 11, 20, 21);
  ("insert", 11, 11, 21, 22);
  ("equal", 11, 12, 22, 23);
  ("insert", 12, 12, 23, 24);
  ("equal", 12, 13, 24, 25);
  ("insert", 13, 13, 25, 26);
  ("equal", 13, 14, 26, 27);
  ("insert", 14, 14, 27, 28);
  ("equal", 14, 15, 28, 29);
  ("insert", 15, 15, 29, 30);
  ("equal", 15, 16, 30, 31);
  ("insert", 16, 16, 31, 32);
  ("equal", 16, 17, 32, 33);
  ("insert", 17, 17, 33, 34);
  ("equal", 17, 18, 34, 35);
  ("insert", 18, 18, 35, 36);
  ("equal", 18, 19, 36, 37);
  ("insert", 19, 19, 37, 38);
  ("equal", 19, 20, 38, 39);
  ("insert", 20, 20, 39, 40);
  ("equal", 20, 21, 40, 41);
  ("insert", 21, 21, 41, 42);
  ("equal", 21, 27, 42, 48);
  ("insert", 27, 27, 48, 49);
  ("equal", 27, 28, 49, 50);
  ("insert", 28, 28, 50, 51);
  ("equal", 28, 29, 51, 52);
  ("insert", 29, 29, 52, 53);
  ("equal", 29, 30, 53, 54);
  ("insert", 30, 30, 54, 55);
  ("equal", 30, 31, 55, 56);
  ("insert", 31, 31, 56, 57);
  ("equal", 31, 32, 57, 58);
  ("insert", 32, 32, 58, 59);
  ("equal", 32, 33, 59, 60);
  ("insert", 33, 33, 60, 61);
  ("equal", 33, 34, 61, 62);
  ("replace", 34, 36, 62, 63);
  ("equal", 36, 37, 63, 64);
  ("replace", 37, 39, 64, 65);
  ("equal", 39, 40, 65, 66);
  ("replace", 40, 44, 66, 75);
  ("equal", 44, 47, 75, 78);
  ("insert", 47, 47, 78, 79);
  ("equal", 47, 48, 79, 80);
  ("insert", 48, 48, 80, 81);
  ("equal", 48, 49, 81, 82);
  ("insert", 49, 49, 82, 83);
  ("equal", 49, 50, 83, 84);
  ("insert", 50, 50, 84, 85);
  ("equal", 50, 51, 85, 86);
  ("insert", 51, 51, 86, 87);
  ("equal", 51, 52, 87, 88);
  ("insert", 52, 52, 88, 89);
  ("equal", 52, 53, 89, 90);
  ("replace", 53, 55, 90, 91);
  ("equal", 55, 56, 91, 92);
  ("replace", 56, 58, 92, 93);
  ("equal", 58, 59, 93, 94);
  ("replace", 59, 65, 94, 107);
  ("equal", 65, 66, 107, 108);
  ("insert", 66, 66, 108, 109);
  ("equal", 66, 67, 109, 110);
  ("insert", 67, 67, 110, 111);
  ("equal", 67, 68, 111, 112);
  ("insert", 68, 68, 112, 113);
  ("equal", 68, 69, 113, 114);
  ("replace", 69, 70, 114, 117);
  ("equal", 70, 72, 117, 119);
  ("insert", 72, 72, 119, 120);
  ("equal", 72, 73, 120, 121);
  ("insert", 73, 73, 121, 122);
  ("equal", 73, 74, 122, 123);
  ("insert", 74, 74, 123, 124);
  ("equal", 74, 76, 124, 126);
  ("insert", 76, 76, 126, 127);
  ("equal", 76, 79, 127, 130);
  ("insert", 79, 79, 130, 131);
  ("equal", 79, 80, 131, 132);
  ("insert", 80, 80, 132, 133);
  ("equal", 80, 81, 133, 134);
  ("insert", 81, 81, 134, 135);
  ("equal", 81, 84, 135, 138);
  ("insert", 84, 84, 138, 139);
  ("equal", 84, 86, 139, 141);
  ("insert", 86, 86, 141, 142);
  ("equal", 86, 91, 142, 147);
  ("insert", 91, 91, 147, 148);
  ("equal", 91, 94, 148, 151);
  ("insert", 94, 94, 151, 152);
  ("equal", 94, 95, 152, 153);
  ("insert", 95, 95, 153, 154);
  ("equal", 95, 96, 154, 155);
  ("insert", 96, 96, 155, 156);
  ("equal", 96, 98, 156, 158);
  ("insert", 98, 98, 158, 159);
  ("equal", 98, 101, 159, 162);
  ("replace", 101, 103, 162, 163);
  ("equal", 103, 104, 163, 164);
  ("replace", 104, 106, 164, 165);
  ("equal", 106, 107, 165, 166);
  ("replace", 107, 111, 166, 173);
  ("equal", 111, 115, 173, 177);
  ("insert", 115, 115, 177, 178);
  ("equal", 115, 116, 178, 179);
  ("insert", 116, 116, 179, 180);
  ("equal", 116, 117, 180, 181);
  ("insert", 117, 117, 181, 182);
  ("equal", 117, 119, 182, 184);
  ("insert", 119, 119, 184, 185);
  ("equal", 119, 120, 185, 186);
  ("replace", 120, 122, 186, 187);
  ("equal", 122, 123, 187, 188);
  ("replace", 123, 125, 188, 189);
  ("equal", 125, 126, 189, 190);
  ("replace", 126, 132, 190, 200);
  ("equal", 132, 134, 200, 202);
  ("insert", 134, 134, 202, 212);
  ("equal", 134, 140, 212, 218);
  ("delete", 140, 142, 218, 218);
];;

let actions2 = [
  ("equal", 142, 146, 218, 222);
  ("replace", 146, 150, 222, 224);
  ("equal", 150, 260, 224, 334);
  ("equal", 260, 290, 334, 364);
];;



let equiv_goal = mk_equiv_statement_simple
  `ALL (nonoverlapping (z,8 * 16)) [
    (word pc:int64,LENGTH bignum_sqr_8_16_unopt_core_mc);
    (word pc2:int64,LENGTH bignum_sqr_8_16_core_mc);
    (x,8 * 8)]`
  bignum_sqr_8_16_equiv_input_states
  bignum_sqr_8_16_equiv_output_states
  bignum_sqr_8_16_unopt_core_mc
  `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
              X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
   MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
  bignum_sqr_8_16_core_mc
  `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
              X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
   MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
              Q21; Q22; Q23; Q30] ,,
   MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_SQR64_HI; WORD_SQR64_LO;
                       WORD_MUL64_LO; WORD_MUL64_HI]] @ (!extra_word_CONV);;

let BIGNUM_SQR_8_16_CORE_EQUIV = time prove(equiv_goal,

  REWRITE_TAC[SOME_FLAGS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_SQR_8_16_UNOPT_CORE_EXEC;fst BIGNUM_SQR_8_16_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC bignum_sqr_8_16_equiv_input_states THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions BIGNUM_SQR_8_16_UNOPT_CORE_EXEC BIGNUM_SQR_8_16_CORE_EXEC THEN
  (* This is an unfortunate manual tweak because the word rule in neon_helper isn't
     exactly applied. This mismatch happened when the assembly was written by hand. *)
  SUBGOAL_THEN `val (a'_6:int64) * val (a'_2:int64) = val a'_2 * val a'_6`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (a'_7:int64) * val (a'_3:int64) = val a'_3 * val a'_7`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ARITH_TAC; ALL_TAC] THEN
  (* More steps *)
  EQUIV_STEPS_TAC actions2 BIGNUM_SQR_8_16_UNOPT_CORE_EXEC BIGNUM_SQR_8_16_CORE_EXEC THEN

  (* Finalize *)
  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[bignum_sqr_8_16_equiv_output_states;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,8) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[BIGNUM_EXPAND_CONV `bignum_from_memory (p,16) st`];

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV;;


let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
  `nonoverlapping (word pc:int64,
    LENGTH (APPEND bignum_sqr_8_16_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 16)`
  [`z:int64`;`x:int64`] bignum_sqr_8_16_unopt_core_mc
  `(\s0. C_ARGUMENTS [z;x] s0)`;;

let BIGNUM_SQR_8_16_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_SQR_8_16_UNOPT_CORE_EXEC;
                BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_sqr_8_16_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_SQR_8_16_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_SQR_8_16_UNOPT_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  (* nonoverlapping *)
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_SQR_8_16_UNOPT_CORE_EXEC);;


let BIGNUM_SQR_8_16_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_SQR_8_16_UNOPT_EXEC
    BIGNUM_SQR_8_16_UNOPT_CORE_EXEC
    BIGNUM_SQR_8_16_UNOPT_CORE_CORRECT
    BIGNUM_SQR_8_16_EVENTUALLY_N_AT_PC;;

let BIGNUM_SQR_8_16_CORE_CORRECT = prove(
  `!z x a pc2.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc2,LENGTH bignum_sqr_8_16_core_mc); (x,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_sqr_8_16_core_mc /\
                 read PC s = word(pc2) /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
          (\s. read PC s = word (pc2 + LENGTH bignum_sqr_8_16_core_mc) /\
               bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                        Q21; Q22; Q23; Q30] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  let mc_lengths_th =
    map fst [BIGNUM_SQR_8_16_UNOPT_CORE_EXEC; BIGNUM_SQR_8_16_CORE_EXEC] in
  REPEAT GEN_TAC THEN
  (* Prepare pc for the 'left' program that does not overlap with buffers z and
     x. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (z:int64,8 * 16) (word pc,
        LENGTH (APPEND bignum_sqr_8_16_unopt_core_mc barrier_inst_bytes)) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_sqr_8_16_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 8) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    (** SUBGOAL 1 **)
    REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_SQR_8_16_UNOPT_CORE_EXEC;BARRIER_INST_BYTES_LENGTH;
                  NONOVERLAPPING_CLAUSES;ALL] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  VCGEN_EQUIV_TAC BIGNUM_SQR_8_16_CORE_EQUIV BIGNUM_SQR_8_16_UNOPT_CORE_CORRECT_N
    mc_lengths_th THEN

  (* unfold definitions that may block further tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE([ALL;NONOVERLAPPING_CLAUSES] @ mc_lengths_th)) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[bignum_sqr_8_16_equiv_input_states] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND bignum_sqr_8_16_unopt_core_mc barrier_inst_bytes)))
          (APPEND bignum_sqr_8_16_unopt_core_mc barrier_inst_bytes)
          (write PC (word pc) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_SQR_8_16_UNOPT_CORE_EXEC THEN
    (* Now has only one subgoal: the equivalence! *)
    REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY EXISTS_TAC [`a:num`] THEN
    PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_SQR_8_16_UNOPT_CORE_EXEC THEN
    NO_TAC;

    (** SUBGOAL 2. Postcond **)
    MESON_TAC([bignum_sqr_8_16_equiv_output_states;BIGNUM_FROM_MEMORY_BYTES] @
      mc_lengths_th);

    (** SUBGOAL 3. Frame **)
    MESON_TAC[]
  ]);;

let BIGNUM_SQR_8_16_CORRECT = prove(
  `!z x a pc2.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc2,LENGTH bignum_sqr_8_16_mc); (x,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_sqr_8_16_mc /\
                 read PC s = word(pc2 + 0x8) /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
          (\s. read PC s = word (pc2 + (0x8 + LENGTH bignum_sqr_8_16_core_mc)) /\
               bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                        Q21; Q22; Q23; Q30] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_SQR_8_16_CORE_CORRECT
      bignum_sqr_8_16_core_mc_def
      [fst BIGNUM_SQR_8_16_EXEC;fst BIGNUM_SQR_8_16_CORE_EXEC]);;


let BIGNUM_SQR_8_16_SUBROUTINE_CORRECT = prove
 (`!z x a pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 16) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
          [(z,8 * 16); (word_sub stackpointer (word 32),32)]
          [(word pc, 1476); (x,8 * 8)]
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
   BIGNUM_SQR_8_16_EXEC
   ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst BIGNUM_SQR_8_16_EXEC;
                   fst BIGNUM_SQR_8_16_CORE_EXEC])
     BIGNUM_SQR_8_16_CORRECT)
   `[X19;X20;X21;X22]` 32);;
