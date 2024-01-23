(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 8x8 -> 16 squaring, using Karatsuba reduction and nested ADK.             *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_sqr_8_16_neon.o";;
 ****)

let bignum_sqr_8_16_neon_mc = define_assert_from_elf "bignum_sqr_8_16_neon_mc"
    "arm/fastmul/bignum_sqr_8_16_neon.o"
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

let BIGNUM_SQR_8_16_NEON_EXEC = ARM_MK_EXEC_RULE bignum_sqr_8_16_neon_mc;;

needs "arm/proofs/neon_helper.ml";;

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


(* Note that, unlike BIGNUM_SQR_8_16_CORRECT, BIGNUM_SQR_8_16_NEON_CORRECT
   assumes that z and x must not overlap. *)

let BIGNUM_SQR_8_16_NEON_CORRECT = prove(`!z x a pc.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc,1476); (x,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_neon_mc /\
                 read PC s = word(pc + 0x8) /\
                 C_ARGUMENTS [z; x] s /\
                 bignum_from_memory (x,8) s = a)
          (\s. read PC s = word (pc + 1464) /\
               bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                        Q21; Q22; Q23; Q30] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS)`,

  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 x) s0` `x_1:(64)word` `x_0:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 16:(64)word))) s0`
    `x_3:(64)word` `x_2:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 32:(64)word))) s0`
    `x_5:(64)word` `x_4:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 48:(64)word))) s0`
    `x_7:(64)word` `x_6:(64)word` THEN

  (*** First nested mini-ADK 4x4 squaring block ***)

  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_SQR_8_16_NEON_EXEC
    [49;51;53;55;79;81;83;85]
    [WORD_SQR64_HI; WORD_SQR64_LO]
    [10;11;25;35;37;41;43;44;45;46;48;49;50;52;53;54;56;58;60;62;
     64;68;70;72;74;76;77;80;81;82;84;85;86;88;92;96;98;100;102;104;
     106;108;110;114;116]
    (1--118) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2 =
    bignum_of_wordlist [mullo_s53; sum_s74; sum_s80; sum_s82;
                        sum_s108; sum_s110; sum_s114; sum_s116]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Second nested mini-ADK 4x4 squaring block ***)


  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_SQR_8_16_NEON_EXEC
   [148;152;154;156;167;178;180;182]
   [WORD_SQR64_HI; WORD_SQR64_LO]
   [119;121;132;140;141;144;145;146;147;149;151;153;155;157;158;160;161;
    162;154;152;164;168;169;171;172;174;175;177;179;181;183;184;182;178;
    188;192;193;195;196;198;199;201;202]
   (119--207) THEN
  RULE_ASSUM_TAC (REWRITE_RULE
      [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO]) THEN
  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_SQR_8_16_NEON_EXEC
   [208;209] [WORD_SQR64_HI; WORD_SQR64_LO] [208;209]
   (208--210) THEN
  RULE_ASSUM_TAC (REWRITE_RULE
      [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_HI]) THEN
  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_SQR_8_16_NEON_EXEC
   [211;212] [WORD_SQR64_HI; WORD_SQR64_LO] [211;212;214;215]
   (211--216) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2 =
    bignum_of_wordlist [mullo_s154;sum_s172;sum_s177;sum_s179;
                        sum_s201;sum_s202;sum_s214;sum_s215]`
  ASSUME_TAC THENL
    [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    let is_acc_thm_for_next acc_thm =
      List.exists (contains_str (string_of_term (concl acc_thm)))
        ["208";"209";"211";"212"] in
    let filter_acc_thms_for_next acc_thms =
      List.filter is_acc_thm_for_next acc_thms in
    let wpat = `word a = b` in
    ACCUMULATOR_POP_ASSUM_LIST(
      fun acc_thms ->
        let acc_thms = filter_acc_thms_for_next acc_thms in
        List.iter (fun t -> Printf.printf "assuming: %s\n" t)
          (List.map string_of_thm acc_thms);
        MAP_EVERY ASSUME_TAC acc_thms) THEN
    DISCARD_ASSUMPTIONS_TAC
      (fun th -> can (term_match [] wpat) (concl th) &&
                 not (is_acc_thm_for_next th))] THEN

  (*** Nested ADK 4x4 multiplication block ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_NEON_EXEC
   [217;218;220;222;223;224;225;226;227;228;229;230;231;232;233;
    234;235;241;246;248;249;255;260;262;263;264;265;266;267;273;278;
    280;281;282;288;293;295;296;297;298;299;305;310;312;313;314;315;
    321;326;328;329;330;331]
   (217--331) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] *
    bignum_of_wordlist [x_4;x_5;x_6;x_7] =
    bignum_of_wordlist
     [mullo_s217; sum_s260; sum_s293; sum_s326;
      sum_s328; sum_s329; sum_s330; sum_s331]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Final accumulation simulation and 16-digit focusing ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_8_16_NEON_EXEC (332--364) (332--364) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s364" THEN
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

let BIGNUM_SQR_8_16_NEON_SUBROUTINE_CORRECT = prove
 (`!z x a pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 16) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
          [(z,8 * 16); (word_sub stackpointer (word 32),32)]
          [(word pc, 1476); (x,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_sqr_8_16_neon_mc /\
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
   BIGNUM_SQR_8_16_NEON_EXEC BIGNUM_SQR_8_16_NEON_CORRECT
   `[X19;X20;X21;X22]` 32);;
