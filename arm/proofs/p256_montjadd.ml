(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point addition in Montgomery-Jacobian coordinates for NIST P-256 curve.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp256.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

needs "arm/proofs/bignum_montsqr_p256_neon.ml";;
needs "arm/proofs/bignum_montmul_p256_neon.ml";;
needs "arm/proofs/bignum_sub_p256.ml";;


(**** print_literal_from_elf "arm/p256/unopt/p256_montjadd.o";;
 ****)

let p256_montjadd_mc = define_assert_from_elf
  "p256_montjadd_mc" "arm/p256/unopt/p256_montjadd.o"
[
  0x3dc00054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 0)) *)
  0xa9404427;       (* arm_LDP X7 X17 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0xa9402846;       (* arm_LDP X6 X10 X2 (Immediate_Offset (iword (&0))) *)
  0xa9413c2b;       (* arm_LDP X11 X15 X1 (Immediate_Offset (iword (&16))) *)
  0x4ea00a90;       (* arm_REV64_VEC Q16 Q20 32 *)
  0xeb1100e4;       (* arm_SUBS X4 X7 X17 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xda84248d;       (* arm_CNEG X13 X4 Condition_CC *)
  0x4ea09e10;       (* arm_MUL_VEC Q16 Q16 Q0 32 128 *)
  0x9bca7e2c;       (* arm_UMULH X12 X17 X10 *)
  0x4e801a9c;       (* arm_UZP1 Q28 Q20 Q0 32 *)
  0xeb07016e;       (* arm_SUBS X14 X11 X7 *)
  0x3dc00454;       (* arm_LDR Q20 X2 (Immediate_Offset (word 16)) *)
  0xfa1101e5;       (* arm_SBCS X5 X15 X17 *)
  0xda1f03f1;       (* arm_NGC X17 XZR *)
  0xeb0f0168;       (* arm_SUBS X8 X11 X15 *)
  0x6ea02a1b;       (* arm_UADDLP Q27 Q16 32 *)
  0x9bc67ce4;       (* arm_UMULH X4 X7 X6 *)
  0x4e801815;       (* arm_UZP1 Q21 Q0 Q0 32 *)
  0xda88250b;       (* arm_CNEG X11 X8 Condition_CC *)
  0x4f605771;       (* arm_SHL_VEC Q17 Q27 32 64 128 *)
  0xda9f23ef;       (* arm_CSETM X15 Condition_CC *)
  0xeb060149;       (* arm_SUBS X9 X10 X6 *)
  0xca1101c7;       (* arm_EOR X7 X14 X17 *)
  0x2ebc82b1;       (* arm_UMLAL_VEC Q17 Q21 Q28 32 *)
  0xda892528;       (* arm_CNEG X8 X9 Condition_CC *)
  0xda832069;       (* arm_CINV X9 X3 Condition_CC *)
  0xb100063f;       (* arm_CMN X17 (rvalue (word 1)) *)
  0x3dc0043c;       (* arm_LDR Q28 X1 (Immediate_Offset (word 16)) *)
  0xba1f00ee;       (* arm_ADCS X14 X7 XZR *)
  0x9b087da7;       (* arm_MUL X7 X13 X8 *)
  0xca1100a1;       (* arm_EOR X1 X5 X17 *)
  0xba1f0025;       (* arm_ADCS X5 X1 XZR *)
  0x0ea12a81;       (* arm_XTN Q1 Q20 32 *)
  0x4e083e21;       (* arm_UMOV X1 Q17 0 8 *)
  0x4e183e23;       (* arm_UMOV X3 Q17 1 8 *)
  0x4e945a90;       (* arm_UZP2 Q16 Q20 Q20 32 *)
  0x9bc87db0;       (* arm_UMULH X16 X13 X8 *)
  0xca0900ed;       (* arm_EOR X13 X7 X9 *)
  0xab030028;       (* arm_ADDS X8 X1 X3 *)
  0xba0c0087;       (* arm_ADCS X7 X4 X12 *)
  0x0ea12b80;       (* arm_XTN Q0 Q28 32 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xab080088;       (* arm_ADDS X8 X4 X8 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xa9410847;       (* arm_LDP X7 X2 X2 (Immediate_Offset (iword (&16))) *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xba0d0108;       (* arm_ADCS X8 X8 X13 *)
  0xca09020d;       (* arm_EOR X13 X16 X9 *)
  0xba0d0070;       (* arm_ADCS X16 X3 X13 *)
  0xd3607c23;       (* arm_LSL X3 X1 32 *)
  0x9a09018d;       (* arm_ADC X13 X12 X9 *)
  0xeb0700cc;       (* arm_SUBS X12 X6 X7 *)
  0xfa020149;       (* arm_SBCS X9 X10 X2 *)
  0xd360fc2a;       (* arm_LSR X10 X1 32 *)
  0xda1f03e4;       (* arm_NGC X4 XZR *)
  0xeb070046;       (* arm_SUBS X6 X2 X7 *)
  0xda8f21e2;       (* arm_CINV X2 X15 Condition_CC *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xeb030027;       (* arm_SUBS X7 X1 X3 *)
  0xca040129;       (* arm_EOR X9 X9 X4 *)
  0xda0a0021;       (* arm_SBC X1 X1 X10 *)
  0xab03010f;       (* arm_ADDS X15 X8 X3 *)
  0xba0a0203;       (* arm_ADCS X3 X16 X10 *)
  0x9b067d70;       (* arm_MUL X16 X11 X6 *)
  0xba0701a8;       (* arm_ADCS X8 X13 X7 *)
  0xca04018d;       (* arm_EOR X13 X12 X4 *)
  0x9a1f002a;       (* arm_ADC X10 X1 XZR *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0x9bc67d66;       (* arm_UMULH X6 X11 X6 *)
  0xba1f01ab;       (* arm_ADCS X11 X13 XZR *)
  0xba1f0121;       (* arm_ADCS X1 X9 XZR *)
  0xd3607ded;       (* arm_LSL X13 X15 32 *)
  0xeb0d01ec;       (* arm_SUBS X12 X15 X13 *)
  0xd360fde7;       (* arm_LSR X7 X15 32 *)
  0xda0701ef;       (* arm_SBC X15 X15 X7 *)
  0xab0d0069;       (* arm_ADDS X9 X3 X13 *)
  0xba070103;       (* arm_ADCS X3 X8 X7 *)
  0x9bcb7dc8;       (* arm_UMULH X8 X14 X11 *)
  0x2ea1c015;       (* arm_UMULL_VEC Q21 Q0 Q1 32 *)
  0xba0c014c;       (* arm_ADCS X12 X10 X12 *)
  0x2eb0c003;       (* arm_UMULL_VEC Q3 Q0 Q16 32 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0x4ea00a98;       (* arm_REV64_VEC Q24 Q20 32 *)
  0xa9013c0c;       (* arm_STP X12 X15 X0 (Immediate_Offset (iword (&16))) *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x9b0b7dca;       (* arm_MUL X10 X14 X11 *)
  0x4ebc9f04;       (* arm_MUL_VEC Q4 Q24 Q28 32 128 *)
  0xeb0501cd;       (* arm_SUBS X13 X14 X5 *)
  0x4e9c5b93;       (* arm_UZP2 Q19 Q28 Q28 32 *)
  0xda9f23ef;       (* arm_CSETM X15 Condition_CC *)
  0x6f6016a3;       (* arm_USRA_VEC Q3 Q21 32 64 128 *)
  0x9b017ca7;       (* arm_MUL X7 X5 X1 *)
  0x2eb0c275;       (* arm_UMULL_VEC Q21 Q19 Q16 32 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x6ea02885;       (* arm_UADDLP Q5 Q4 32 *)
  0xeb0b002b;       (* arm_SUBS X11 X1 X11 *)
  0x4e221c70;       (* arm_AND_VEC Q16 Q3 Q2 128 *)
  0x9bc17ca5;       (* arm_UMULH X5 X5 X1 *)
  0x4f6054b8;       (* arm_SHL_VEC Q24 Q5 32 64 128 *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x2ea18270;       (* arm_UMLAL_VEC Q16 Q19 Q1 32 *)
  0xda8f21ec;       (* arm_CINV X12 X15 Condition_CC *)
  0x2ea18018;       (* arm_UMLAL_VEC Q24 Q0 Q1 32 *)
  0xab07014f;       (* arm_ADDS X15 X10 X7 *)
  0x9b0b7dae;       (* arm_MUL X14 X13 X11 *)
  0xca0200c1;       (* arm_EOR X1 X6 X2 *)
  0xba050106;       (* arm_ADCS X6 X8 X5 *)
  0xa9000c09;       (* arm_STP X9 X3 X0 (Immediate_Offset (iword (&0))) *)
  0x6f601475;       (* arm_USRA_VEC Q21 Q3 32 64 128 *)
  0xba1f00a9;       (* arm_ADCS X9 X5 XZR *)
  0x9bcb7dab;       (* arm_UMULH X11 X13 X11 *)
  0xab0f010f;       (* arm_ADDS X15 X8 X15 *)
  0xba0600e7;       (* arm_ADCS X7 X7 X6 *)
  0xca0c01c8;       (* arm_EOR X8 X14 X12 *)
  0x6f601615;       (* arm_USRA_VEC Q21 Q16 32 64 128 *)
  0xba1f012d;       (* arm_ADCS X13 X9 XZR *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0x4e183f09;       (* arm_UMOV X9 Q24 1 8 *)
  0xba0801ee;       (* arm_ADCS X14 X15 X8 *)
  0xca0c0166;       (* arm_EOR X6 X11 X12 *)
  0xba0600e6;       (* arm_ADCS X6 X7 X6 *)
  0x4e083f05;       (* arm_UMOV X5 Q24 0 8 *)
  0x4e183eab;       (* arm_UMOV X11 Q21 1 8 *)
  0x4e083ea7;       (* arm_UMOV X7 Q21 0 8 *)
  0x9a0c01a3;       (* arm_ADC X3 X13 X12 *)
  0xab0900ac;       (* arm_ADDS X12 X5 X9 *)
  0xba0b00ed;       (* arm_ADCS X13 X7 X11 *)
  0xa940200f;       (* arm_LDP X15 X8 X0 (Immediate_Offset (iword (&0))) *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xab0c00ec;       (* arm_ADDS X12 X7 X12 *)
  0xca020210;       (* arm_EOR X16 X16 X2 *)
  0xba0d0127;       (* arm_ADCS X7 X9 X13 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xb100045f;       (* arm_CMN X2 (rvalue (word 1)) *)
  0xa9413409;       (* arm_LDP X9 X13 X0 (Immediate_Offset (iword (&16))) *)
  0xba100190;       (* arm_ADCS X16 X12 X16 *)
  0xba0100e1;       (* arm_ADCS X1 X7 X1 *)
  0x9a020162;       (* arm_ADC X2 X11 X2 *)
  0xab0f00a7;       (* arm_ADDS X7 X5 X15 *)
  0xba08020f;       (* arm_ADCS X15 X16 X8 *)
  0xca040225;       (* arm_EOR X5 X17 X4 *)
  0xba090029;       (* arm_ADCS X9 X1 X9 *)
  0xca050141;       (* arm_EOR X1 X10 X5 *)
  0xba0d0050;       (* arm_ADCS X16 X2 X13 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xca0501cd;       (* arm_EOR X13 X14 X5 *)
  0xba07002e;       (* arm_ADCS X14 X1 X7 *)
  0xca0500c1;       (* arm_EOR X1 X6 X5 *)
  0xba0f01a6;       (* arm_ADCS X6 X13 X15 *)
  0xba09002a;       (* arm_ADCS X10 X1 X9 *)
  0xca050064;       (* arm_EOR X4 X3 X5 *)
  0xb2407fe1;       (* arm_MOV X1 (rvalue (word 4294967295)) *)
  0xba100088;       (* arm_ADCS X8 X4 X16 *)
  0xd360fdcd;       (* arm_LSR X13 X14 32 *)
  0xba050051;       (* arm_ADCS X17 X2 X5 *)
  0xba1f00ab;       (* arm_ADCS X11 X5 XZR *)
  0x9a1f00a4;       (* arm_ADC X4 X5 XZR *)
  0xab07014c;       (* arm_ADDS X12 X10 X7 *)
  0xba0f0107;       (* arm_ADCS X7 X8 X15 *)
  0xba090225;       (* arm_ADCS X5 X17 X9 *)
  0xba100169;       (* arm_ADCS X9 X11 X16 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0x9a02008a;       (* arm_ADC X10 X4 X2 *)
  0xeb0b01d1;       (* arm_SUBS X17 X14 X11 *)
  0xda0d01c4;       (* arm_SBC X4 X14 X13 *)
  0xab0b00cb;       (* arm_ADDS X11 X6 X11 *)
  0xba0d018c;       (* arm_ADCS X12 X12 X13 *)
  0xd3607d6f;       (* arm_LSL X15 X11 32 *)
  0xba1100f1;       (* arm_ADCS X17 X7 X17 *)
  0xd360fd67;       (* arm_LSR X7 X11 32 *)
  0x9a1f008d;       (* arm_ADC X13 X4 XZR *)
  0xeb0f0164;       (* arm_SUBS X4 X11 X15 *)
  0xda07016b;       (* arm_SBC X11 X11 X7 *)
  0xab0f0188;       (* arm_ADDS X8 X12 X15 *)
  0xba07022f;       (* arm_ADCS X15 X17 X7 *)
  0xba0401a4;       (* arm_ADCS X4 X13 X4 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0400a7;       (* arm_ADDS X7 X5 X4 *)
  0xba0b0131;       (* arm_ADCS X17 X9 X11 *)
  0x9a1f014d;       (* arm_ADC X13 X10 XZR *)
  0x910005ac;       (* arm_ADD X12 X13 (rvalue (word 1)) *)
  0xcb0c03eb;       (* arm_NEG X11 X12 *)
  0xd3607d84;       (* arm_LSL X4 X12 32 *)
  0xab040231;       (* arm_ADDS X17 X17 X4 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xeb0b010b;       (* arm_SUBS X11 X8 X11 *)
  0xfa0401e4;       (* arm_SBCS X4 X15 X4 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa0c0231;       (* arm_SBCS X17 X17 X12 *)
  0xfa0c01ad;       (* arm_SBCS X13 X13 X12 *)
  0xb26083ec;       (* arm_MOV X12 (rvalue (word 18446744069414584321)) *)
  0xab0d016b;       (* arm_ADDS X11 X11 X13 *)
  0x8a0d0021;       (* arm_AND X1 X1 X13 *)
  0xba010084;       (* arm_ADCS X4 X4 X1 *)
  0x8a0d0181;       (* arm_AND X1 X12 X13 *)
  0xa900100b;       (* arm_STP X11 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xba1f00e4;       (* arm_ADCS X4 X7 XZR *)
  0x9a010221;       (* arm_ADC X1 X17 X1 *)
  0xa9010404;       (* arm_STP X4 X1 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x3dc00033;       (* arm_LDR Q19 X1 (Immediate_Offset (word 0)) *)
  0xa9403429;       (* arm_LDP X9 X13 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc00437;       (* arm_LDR Q23 X1 (Immediate_Offset (word 16)) *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0xa9412821;       (* arm_LDP X1 X10 X1 (Immediate_Offset (iword (&16))) *)
  0x4e935a7d;       (* arm_UZP2 Q29 Q19 Q19 32 *)
  0x0ea12a64;       (* arm_XTN Q4 Q19 32 *)
  0x9bcd7d28;       (* arm_UMULH X8 X9 X13 *)
  0x4ea00af4;       (* arm_REV64_VEC Q20 Q23 32 *)
  0x2eb3c270;       (* arm_UMULL_VEC Q16 Q19 Q19 32 *)
  0x2ea4c3a1;       (* arm_UMULL_VEC Q1 Q29 Q4 32 *)
  0x4ea09e94;       (* arm_MUL_VEC Q20 Q20 Q0 32 128 *)
  0xeb0d012e;       (* arm_SUBS X14 X9 X13 *)
  0x9bc17d2f;       (* arm_UMULH X15 X9 X1 *)
  0x4e183e10;       (* arm_UMOV X16 Q16 1 8 *)
  0x6eb3c264;       (* arm_UMULL2_VEC Q4 Q19 Q19 32 *)
  0x4e083e04;       (* arm_UMOV X4 Q16 0 8 *)
  0x4e801af1;       (* arm_UZP1 Q17 Q23 Q0 32 *)
  0x6ea02a93;       (* arm_UADDLP Q19 Q20 32 *)
  0xd37ffd07;       (* arm_LSR X7 X8 63 *)
  0x9b0d7d2b;       (* arm_MUL X11 X9 X13 *)
  0x4e083c2c;       (* arm_UMOV X12 Q1 0 8 *)
  0xda9f23e5;       (* arm_CSETM X5 Condition_CC *)
  0xda8e25c6;       (* arm_CNEG X6 X14 Condition_CC *)
  0x4e183c83;       (* arm_UMOV X3 Q4 1 8 *)
  0x4e083c8e;       (* arm_UMOV X14 Q4 0 8 *)
  0xeb010142;       (* arm_SUBS X2 X10 X1 *)
  0x4e183c29;       (* arm_UMOV X9 Q1 1 8 *)
  0xda822451;       (* arm_CNEG X17 X2 Condition_CC *)
  0xda8520a2;       (* arm_CINV X2 X5 Condition_CC *)
  0xab0c8485;       (* arm_ADDS X5 X4 (Shiftedreg X12 LSL 33) *)
  0x93cbfd04;       (* arm_EXTR X4 X8 X11 63 *)
  0xd35ffd88;       (* arm_LSR X8 X12 31 *)
  0x4e801814;       (* arm_UZP1 Q20 Q0 Q0 32 *)
  0x4f605673;       (* arm_SHL_VEC Q19 Q19 32 64 128 *)
  0x9a080210;       (* arm_ADC X16 X16 X8 *)
  0xab0985c8;       (* arm_ADDS X8 X14 (Shiftedreg X9 LSL 33) *)
  0xd35ffd2e;       (* arm_LSR X14 X9 31 *)
  0xd3607ca9;       (* arm_LSL X9 X5 32 *)
  0x2eb18293;       (* arm_UMLAL_VEC Q19 Q20 Q17 32 *)
  0x9a0e006e;       (* arm_ADC X14 X3 X14 *)
  0xab0b0610;       (* arm_ADDS X16 X16 (Shiftedreg X11 LSL 1) *)
  0xd360fca3;       (* arm_LSR X3 X5 32 *)
  0x9bd17ccc;       (* arm_UMULH X12 X6 X17 *)
  0xba040104;       (* arm_ADCS X4 X8 X4 *)
  0x9a0701cb;       (* arm_ADC X11 X14 X7 *)
  0xeb0900a8;       (* arm_SUBS X8 X5 X9 *)
  0xda0300a5;       (* arm_SBC X5 X5 X3 *)
  0xab090210;       (* arm_ADDS X16 X16 X9 *)
  0x4e083e6e;       (* arm_UMOV X14 Q19 0 8 *)
  0x9b117cd1;       (* arm_MUL X17 X6 X17 *)
  0xba030083;       (* arm_ADCS X3 X4 X3 *)
  0xd3607e07;       (* arm_LSL X7 X16 32 *)
  0x9bca7dad;       (* arm_UMULH X13 X13 X10 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0xd360fe08;       (* arm_LSR X8 X16 32 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xeb070209;       (* arm_SUBS X9 X16 X7 *)
  0xda080210;       (* arm_SBC X16 X16 X8 *)
  0xab070067;       (* arm_ADDS X7 X3 X7 *)
  0x4e183e63;       (* arm_UMOV X3 Q19 1 8 *)
  0xba080166;       (* arm_ADCS X6 X11 X8 *)
  0x9bca7c2b;       (* arm_UMULH X11 X1 X10 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xca020188;       (* arm_EOR X8 X12 X2 *)
  0x9a1f0209;       (* arm_ADC X9 X16 XZR *)
  0xab0f01d0;       (* arm_ADDS X16 X14 X15 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xab03020c;       (* arm_ADDS X12 X16 X3 *)
  0xca020230;       (* arm_EOR X16 X17 X2 *)
  0x9b0a7c24;       (* arm_MUL X4 X1 X10 *)
  0xba0d01ef;       (* arm_ADCS X15 X15 X13 *)
  0x9a1f01b1;       (* arm_ADC X17 X13 XZR *)
  0xab0301ef;       (* arm_ADDS X15 X15 X3 *)
  0x9a1f0223;       (* arm_ADC X3 X17 XZR *)
  0xb100045f;       (* arm_CMN X2 (rvalue (word 1)) *)
  0x9b0a7d51;       (* arm_MUL X17 X10 X10 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba0801f0;       (* arm_ADCS X16 X15 X8 *)
  0x9bca7d4a;       (* arm_UMULH X10 X10 X10 *)
  0x9a020062;       (* arm_ADC X2 X3 X2 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba020042;       (* arm_ADCS X2 X2 X2 *)
  0x9a1f03ef;       (* arm_ADC X15 XZR XZR *)
  0xab0701ce;       (* arm_ADDS X14 X14 X7 *)
  0x9b017c23;       (* arm_MUL X3 X1 X1 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0xd360fdc7;       (* arm_LSR X7 X14 32 *)
  0xba050210;       (* arm_ADCS X16 X16 X5 *)
  0xd3607dc5;       (* arm_LSL X5 X14 32 *)
  0x9bc17c2d;       (* arm_UMULH X13 X1 X1 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xab040088;       (* arm_ADDS X8 X4 X4 *)
  0xba0b0161;       (* arm_ADCS X1 X11 X11 *)
  0xb26083eb;       (* arm_MOV X11 (rvalue (word 18446744069414584321)) *)
  0x9a1f03e4;       (* arm_ADC X4 XZR XZR *)
  0xeb0501c9;       (* arm_SUBS X9 X14 X5 *)
  0xda0701ce;       (* arm_SBC X14 X14 X7 *)
  0xab05018c;       (* arm_ADDS X12 X12 X5 *)
  0xba070210;       (* arm_ADCS X16 X16 X7 *)
  0xd3607d85;       (* arm_LSL X5 X12 32 *)
  0xd360fd87;       (* arm_LSR X7 X12 32 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba0e01ee;       (* arm_ADCS X14 X15 X14 *)
  0x9a1f03ef;       (* arm_ADC X15 XZR XZR *)
  0xeb050189;       (* arm_SUBS X9 X12 X5 *)
  0xda07018c;       (* arm_SBC X12 X12 X7 *)
  0xab050210;       (* arm_ADDS X16 X16 X5 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba0901ce;       (* arm_ADCS X14 X14 X9 *)
  0xba0c01ec;       (* arm_ADCS X12 X15 X12 *)
  0x9a1f03ef;       (* arm_ADC X15 XZR XZR *)
  0xab030210;       (* arm_ADDS X16 X16 X3 *)
  0xba0d0042;       (* arm_ADCS X2 X2 X13 *)
  0xba1101ce;       (* arm_ADCS X14 X14 X17 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xab080042;       (* arm_ADDS X2 X2 X8 *)
  0xba0101ce;       (* arm_ADCS X14 X14 X1 *)
  0xba04018c;       (* arm_ADCS X12 X12 X4 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xb1000603;       (* arm_ADDS X3 X16 (rvalue (word 1)) *)
  0xfa060045;       (* arm_SBCS X5 X2 X6 *)
  0xfa1f01c8;       (* arm_SBCS X8 X14 XZR *)
  0xfa0b018b;       (* arm_SBCS X11 X12 X11 *)
  0xfa1f01ff;       (* arm_SBCS XZR X15 XZR *)
  0x9a902070;       (* arm_CSEL X16 X3 X16 Condition_CS *)
  0x9a8e210e;       (* arm_CSEL X14 X8 X14 Condition_CS *)
  0x9a8c216c;       (* arm_CSEL X12 X11 X12 Condition_CS *)
  0x9a8220a2;       (* arm_CSEL X2 X5 X2 Condition_CS *)
  0xa901300e;       (* arm_STP X14 X12 X0 (Immediate_Offset (iword (&16))) *)
  0xa9000810;       (* arm_STP X16 X2 X0 (Immediate_Offset (iword (&0))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&16))) *)
  0xa9410c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92407c64;       (* arm_AND X4 X3 (rvalue (word 4294967295)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0x92608064;       (* arm_AND X4 X3 (rvalue (word 18446744069414584321)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf7;       (* arm_STP X23 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10383ff;       (* arm_SUB SP SP (rvalue (word 224)) *)
  0xaa0003f5;       (* arm_MOV X21 X0 *)
  0xaa0103f6;       (* arm_MOV X22 X1 *)
  0xaa0203f7;       (* arm_MOV X23 X2 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910102c1;       (* arm_ADD X1 X22 (rvalue (word 64)) *)
  0x97ffff5c;       (* arm_BL (word 268434800) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910102e1;       (* arm_ADD X1 X23 (rvalue (word 64)) *)
  0x97ffff59;       (* arm_BL (word 268434788) *)
  0x910303e0;       (* arm_ADD X0 SP (rvalue (word 192)) *)
  0x910102e1;       (* arm_ADD X1 X23 (rvalue (word 64)) *)
  0x910082c2;       (* arm_ADD X2 X22 (rvalue (word 32)) *)
  0x97fffe88;       (* arm_BL (word 268433952) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910102c1;       (* arm_ADD X1 X22 (rvalue (word 64)) *)
  0x910082e2;       (* arm_ADD X2 X23 (rvalue (word 32)) *)
  0x97fffe84;       (* arm_BL (word 268433936) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910002e2;       (* arm_ADD X2 X23 (rvalue (word 0)) *)
  0x97fffe80;       (* arm_BL (word 268433920) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x910002c2;       (* arm_ADD X2 X22 (rvalue (word 0)) *)
  0x97fffe7c;       (* arm_BL (word 268433904) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x97fffe78;       (* arm_BL (word 268433888) *)
  0x910303e0;       (* arm_ADD X0 SP (rvalue (word 192)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x910303e2;       (* arm_ADD X2 SP (rvalue (word 192)) *)
  0x97fffe74;       (* arm_BL (word 268433872) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x97ffffc6;       (* arm_BL (word 268435224) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910303e2;       (* arm_ADD X2 SP (rvalue (word 192)) *)
  0x97ffffc2;       (* arm_BL (word 268435208) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x97ffff36;       (* arm_BL (word 268434648) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x97ffff33;       (* arm_BL (word 268434636) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x97fffe62;       (* arm_BL (word 268433800) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x97fffe5e;       (* arm_BL (word 268433784) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x97ffffb0;       (* arm_BL (word 268435136) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x97ffffac;       (* arm_BL (word 268435120) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x910102c2;       (* arm_ADD X2 X22 (rvalue (word 64)) *)
  0x97fffe52;       (* arm_BL (word 268433736) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x97ffffa4;       (* arm_BL (word 268435088) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910203e1;       (* arm_ADD X1 SP (rvalue (word 128)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x97ffffa0;       (* arm_BL (word 268435072) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910303e2;       (* arm_ADD X2 SP (rvalue (word 192)) *)
  0x97fffe46;       (* arm_BL (word 268433688) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x910102e2;       (* arm_ADD X2 X23 (rvalue (word 64)) *)
  0x97fffe42;       (* arm_BL (word 268433672) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x97fffe3e;       (* arm_BL (word 268433656) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910203e1;       (* arm_ADD X1 SP (rvalue (word 128)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x97ffff90;       (* arm_BL (word 268435008) *)
  0xa94406c0;       (* arm_LDP X0 X1 X22 (Immediate_Offset (iword (&64))) *)
  0xa9450ec2;       (* arm_LDP X2 X3 X22 (Immediate_Offset (iword (&80))) *)
  0xaa01000c;       (* arm_ORR X12 X0 X1 *)
  0xaa03004d;       (* arm_ORR X13 X2 X3 *)
  0xaa0d018c;       (* arm_ORR X12 X12 X13 *)
  0xeb1f019f;       (* arm_CMP X12 XZR *)
  0x9a9f07ec;       (* arm_CSET X12 Condition_NE *)
  0xa94416e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&64))) *)
  0xa9451ee6;       (* arm_LDP X6 X7 X23 (Immediate_Offset (iword (&80))) *)
  0xaa05008d;       (* arm_ORR X13 X4 X5 *)
  0xaa0700ce;       (* arm_ORR X14 X6 X7 *)
  0xaa0e01ad;       (* arm_ORR X13 X13 X14 *)
  0xeb1f01bf;       (* arm_CMP X13 XZR *)
  0x9a9f07ed;       (* arm_CSET X13 Condition_NE *)
  0xeb0c01bf;       (* arm_CMP X13 X12 *)
  0xa94a27e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&160))) *)
  0x9a883008;       (* arm_CSEL X8 X0 X8 Condition_CC *)
  0x9a893029;       (* arm_CSEL X9 X1 X9 Condition_CC *)
  0x9a888088;       (* arm_CSEL X8 X4 X8 Condition_HI *)
  0x9a8980a9;       (* arm_CSEL X9 X5 X9 Condition_HI *)
  0xa94b2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0x9a8a304a;       (* arm_CSEL X10 X2 X10 Condition_CC *)
  0x9a8b306b;       (* arm_CSEL X11 X3 X11 Condition_CC *)
  0x9a8a80ca;       (* arm_CSEL X10 X6 X10 Condition_HI *)
  0x9a8b80eb;       (* arm_CSEL X11 X7 X11 Condition_HI *)
  0xa94036cc;       (* arm_LDP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0x9a803180;       (* arm_CSEL X0 X12 X0 Condition_CC *)
  0x9a8131a1;       (* arm_CSEL X1 X13 X1 Condition_CC *)
  0xa94036ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&0))) *)
  0x9a808180;       (* arm_CSEL X0 X12 X0 Condition_HI *)
  0x9a8181a1;       (* arm_CSEL X1 X13 X1 Condition_HI *)
  0xa94136cc;       (* arm_LDP X12 X13 X22 (Immediate_Offset (iword (&16))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0x9a823182;       (* arm_CSEL X2 X12 X2 Condition_CC *)
  0x9a8331a3;       (* arm_CSEL X3 X13 X3 Condition_CC *)
  0xa94136ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&16))) *)
  0x9a828182;       (* arm_CSEL X2 X12 X2 Condition_HI *)
  0x9a8381a3;       (* arm_CSEL X3 X13 X3 Condition_HI *)
  0xa94236cc;       (* arm_LDP X12 X13 X22 (Immediate_Offset (iword (&32))) *)
  0xa94817e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&128))) *)
  0x9a843184;       (* arm_CSEL X4 X12 X4 Condition_CC *)
  0x9a8531a5;       (* arm_CSEL X5 X13 X5 Condition_CC *)
  0xa94236ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&32))) *)
  0x9a848184;       (* arm_CSEL X4 X12 X4 Condition_HI *)
  0x9a8581a5;       (* arm_CSEL X5 X13 X5 Condition_HI *)
  0xa94336cc;       (* arm_LDP X12 X13 X22 (Immediate_Offset (iword (&48))) *)
  0xa9491fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&144))) *)
  0x9a863186;       (* arm_CSEL X6 X12 X6 Condition_CC *)
  0x9a8731a7;       (* arm_CSEL X7 X13 X7 Condition_CC *)
  0xa94336ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&48))) *)
  0x9a868186;       (* arm_CSEL X6 X12 X6 Condition_HI *)
  0x9a8781a7;       (* arm_CSEL X7 X13 X7 Condition_HI *)
  0xa90006a0;       (* arm_STP X0 X1 X21 (Immediate_Offset (iword (&0))) *)
  0xa9010ea2;       (* arm_STP X2 X3 X21 (Immediate_Offset (iword (&16))) *)
  0xa90216a4;       (* arm_STP X4 X5 X21 (Immediate_Offset (iword (&32))) *)
  0xa9031ea6;       (* arm_STP X6 X7 X21 (Immediate_Offset (iword (&48))) *)
  0xa90426a8;       (* arm_STP X8 X9 X21 (Immediate_Offset (iword (&64))) *)
  0xa9052eaa;       (* arm_STP X10 X11 X21 (Immediate_Offset (iword (&80))) *)
  0x910383ff;       (* arm_ADD SP SP (rvalue (word 224)) *)
  0xa8c17bf7;       (* arm_LDP X23 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P256_MONTJADD_EXEC = ARM_MK_EXEC_RULE p256_montjadd_mc;;

(* P256_MONTJADD_EXEC without callee save register reloads and ret.
   This truncation is for equivalence checking. *)
let p256_montjadd_core_mc_def,p256_montjadd_core_mc,
    P256_MONTJADD_CORE_EXEC =
  mk_sublist_of_mc "p256_montjadd_core_mc"
    p256_montjadd_mc (`0`,`LENGTH p256_montjadd_mc - 20`)
    (fst P256_MONTJADD_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p256shortishredlemma = prove
 (`!n. n < 24 * 2 EXP 256
       ==> let q = n DIV 2 EXP 256 + 1 in
           q <= 24 /\
           q < 2 EXP 64 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let p256shortintredlemma = prove
 (`!n. --(&p_256) <= n /\ n <= &4 * &2 pow 256
       ==> let q = (&2 pow 256 + n) div &2 pow 256 in
           &0 <= q /\ q < &6 /\
           q < &2 pow 64 /\
           q * &p_256 <= n + &p_256 /\
           n < q * &p_256 + &p_256`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 256 + n:int = &1 * &2 pow 256 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 256` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_256` THEN REWRITE_TAC[p_256] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_256` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_256] THEN INT_ARITH_TAC);;

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

let p256shortredlemma = prove
 (`!n. n < 3 * p_256
       ==> let q = (n DIV 2 EXP 256) + 1 in
           q <= 3 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

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
  "z1sq",[`SP`;`0`];
  "ww",[`SP`;`0`];
  "resx",[`SP`;`0`];
  "yd",[`SP`;`32`];
  "y2a",[`SP`;`32`];
  "x2a",[`SP`;`64`];
  "zzx2",[`SP`;`64`];
  "zz",[`SP`;`96`];
  "t1",[`SP`;`96`];
  "t2",[`SP`;`128`];
  "x1a",[`SP`;`128`];
  "zzx1",[`SP`;`128`];
  "resy",[`SP`;`128`];
  "xd",[`SP`;`160`];
  "z2sq",[`SP`;`160`];
  "resz",[`SP`;`160`];
  "y1a",[`SP`;`192`]];;


(* ------------------------------------------------------------------------- *)
(* Support interface of ARM_MACRO_SIM_ABBREV_TAC when using a subroutine.    *)
(* ------------------------------------------------------------------------- *)

let PROLOGUE_SUBROUTINE_SIM_TAC corth inargs outarg m inouts =
  let main_tac =
     ARM_SUBROUTINE_SIM_ABBREV_TAC
      (p256_montjadd_core_mc,P256_MONTJADD_CORE_EXEC,0,
       p256_montjadd_core_mc,corth)
      inargs outarg
  and k = length inouts + 1 in
  W(fun (asl,w) ->
    let dvar = mk_var(hd inouts,`:num`) in
    let dvar' =
      variant (rev_itlist (union o frees o concl o snd) asl []) dvar in
    let pcs = tryfind
      (find_term (can (term_match [] `read PC s`)) o concl o snd) asl in
    let sname = name_of(rand pcs) in
    let n = int_of_string (String.sub sname 1 (String.length sname - 1)) in
    ARM_STEPS_TAC P256_MONTJADD_CORE_EXEC ((n+1)--(n+m+k)) THEN
    main_tac (name_of dvar') (n+m+k+1));;


(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_P256_CORRECT =
  let lemma = prove(`!z x a pc.
        nonoverlapping (word pc,LENGTH p256_montjadd_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_core_mc /\
                  read PC s = word (pc + 0x334) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + (0x334 + LENGTH bignum_montsqr_p256_neon_core_mc)) /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
    SUBGOAL_THEN
      `bignum_montsqr_p256_neon_core_mc =
        SUB_LIST (0x334, LENGTH bignum_montsqr_p256_neon_core_mc)
                 p256_montjadd_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_MONTSQR_P256_NEON_CORE_EXEC;
                  bignum_montsqr_p256_neon_core_mc; p256_montjadd_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P256_NEON_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_MONTSQR_P256_NEON_CORE_EXEC] th)
        [fst BIGNUM_MONTSQR_P256_NEON_CORE_EXEC;
        fst P256_MONTJADD_CORE_EXEC])) in
  REWRITE_RULE [fst P256_MONTJADD_CORE_EXEC]
    (prove(`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH p256_montjadd_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_core_mc /\
                  read PC s = word (pc + 0x334) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
    REWRITE_TAC[fst P256_MONTJADD_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P256_MONTJADD_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P256_MONTJADD_CORE_EXEC;fst BIGNUM_MONTSQR_P256_NEON_CORE_EXEC])
     lemma)));;

let LOCAL_MONTSQR_P256_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_MONTSQR_P256_CORRECT
   [`read X0 s`; `read X1 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 4)) s'`;;


(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_P256_CORRECT =
  let lemma = prove(`!z x y a b pc.
        nonoverlapping (word pc,LENGTH p256_montjadd_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_neon_core_mc) /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
    SUBGOAL_THEN
      `bignum_montmul_p256_neon_core_mc =
        SUB_LIST (0, LENGTH bignum_montmul_p256_neon_core_mc) p256_montjadd_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_MONTMUL_P256_NEON_CORE_EXEC;
                  bignum_montmul_p256_neon_core_mc; p256_montjadd_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P256_NEON_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_MONTMUL_P256_NEON_CORE_EXEC] th)
        [fst BIGNUM_MONTMUL_P256_NEON_CORE_EXEC;
        fst P256_MONTJADD_CORE_EXEC])) in
  REWRITE_RULE [fst P256_MONTJADD_CORE_EXEC]
    (prove(`!z x y a b pc returnaddress.
        nonoverlapping (word pc,LENGTH p256_montjadd_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_core_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = returnaddress /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
    REWRITE_TAC[fst P256_MONTJADD_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P256_MONTJADD_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P256_MONTJADD_CORE_EXEC;fst BIGNUM_MONTMUL_P256_NEON_CORE_EXEC])
     lemma)));;

let LOCAL_MONTMUL_P256_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_MONTMUL_P256_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `read (memory :> bytes(read X2 s,8 * 4)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 4)) s'`;;


(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P256_CORRECT =
  let lemma = prove(`!z x y m n pc.
        nonoverlapping (word pc,LENGTH p256_montjadd_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_core_mc /\
                  read PC s = word (pc + 0x558) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + (0x558 + 0x44)) /\
                  (m < p_256 /\ n < p_256
                   ==> &(bignum_from_memory (z,4) s) = (&m - &n) rem &p_256))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,4)])`,
    SUBGOAL_THEN
      `bignum_sub_p256_mc = SUB_LIST (0x558, 0x48) p256_montjadd_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_SUB_P256_EXEC; bignum_sub_p256_mc; p256_montjadd_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_SUB_P256_CORRECT
        (REWRITE_RULE [fst BIGNUM_SUB_P256_EXEC] th)
        [fst BIGNUM_SUB_P256_EXEC; fst P256_MONTJADD_CORE_EXEC])) in
  REWRITE_RULE [fst P256_MONTJADD_CORE_EXEC] (prove(
    `!z x y m n pc returnaddress.
        nonoverlapping (word pc,LENGTH p256_montjadd_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_core_mc /\
                  read PC s = word (pc + 0x558) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_256 /\ n < p_256
                   ==> &(bignum_from_memory (z,4) s) = (&m - &n) rem &p_256))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,4)])`,
    REWRITE_TAC[fst P256_MONTJADD_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P256_MONTJADD_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P256_MONTJADD_CORE_EXEC;fst BIGNUM_SUB_P256_EXEC])
     lemma)));;

let LOCAL_SUB_P256_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_SUB_P256_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `read (memory :> bytes(read X2 s,8 * 4)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 4)) s'`;;


(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_256 ==> x < p_256 /\ &x = &a rem &p_256`,
  REWRITE_TAC[INT_OF_NUM_REM; p_256] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_256 ==> x < p_256 /\ &x = a rem &p_256`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_256] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_256 = (&i * x rem &p_256 * y rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_256 = (&(NUMERAL n) * &x rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) *
    (&2 pow 256 * x) rem &p_256 * (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * x * y) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_256] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 256 * x) rem &p_256 + (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x + y)) rem &p_256 /\
   ((&2 pow 256 * x) rem &p_256 - (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x - y)) rem &p_256 /\
   (&(NUMERAL n) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   (&2 pow 256 * (&(NUMERAL n) * x)) rem &p_256`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   x rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_256
         ==> x =
             (2 EXP 256 * (inverse_mod p_256 (2 EXP 256) * x) MOD p_256) MOD
             p_256`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_jacobian_p256_add = prove
 (`!P1 P2 x1 y1 z1 x2 y2 z2 x3 y3 z3.
        ~(weierstrass_of_jacobian (integer_mod_ring p_256)
           (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) =
          weierstrass_of_jacobian (integer_mod_ring p_256)
           (x2 rem &p_256,y2 rem &p_256,z2 rem &p_256)) /\
        jacobian_add_unexceptional nistp256
         (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256)
         (x2 rem &p_256,y2 rem &p_256,z2 rem &p_256) =
        (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256)
        ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) = P1 /\
            weierstrass_of_jacobian (integer_mod_ring p_256)
                (x2 rem &p_256,y2 rem &p_256,z2 rem &p_256) = P2
            ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                  (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256) =
                group_mul p256_group P1 P2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[nistp256; P256_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(MP_TAC o PART_MATCH (rand o rand) WEIERSTRASS_OF_JACOBIAN_EQ o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_256; b_256] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p256 = new_definition
 `represents_p256 P (x,y,z) <=>
        x < p_256 /\ y < p_256 /\ z < p_256 /\
        weierstrass_of_jacobian (integer_mod_ring p_256)
         (tripled (montgomery_decode (256,p_256)) (x,y,z)) = P`;;

let P256_MONTJADD_UNOPT_CORE_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,224))
            [(word pc,LENGTH p256_montjadd_core_mc); (p1,96); (p2,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,LENGTH p256_montjadd_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_core_mc /\
                  read PC s = word(pc + 0x5b0) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read PC s = word (pc + 0x808) /\
                  !P1 P2. represents_p256 P1 t1 /\ represents_p256 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p256 (group_mul p256_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                      X22; X23; X30] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,224)])`,
  REWRITE_TAC[FORALL_PAIR_THM;fst P256_MONTJADD_CORE_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`; `p2:int64`;
    `x2:num`; `y2:num`; `z2:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_P256_TAC 3 ["z1sq";"z_1"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["z2sq";"z_2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["y1a";"z_2";"y_1"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["y2a";"z_1";"y_2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["x2a";"z1sq";"x_2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["x1a";"z2sq";"x_1"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["y2a";"z1sq";"y2a"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["y1a";"z2sq";"y1a"] THEN
  LOCAL_SUB_P256_TAC 0 ["xd";"x2a";"x1a"] THEN
  LOCAL_SUB_P256_TAC 0 ["yd";"y2a";"y1a"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["zz";"xd"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["ww";"yd"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["zzx1";"zz";"x1a"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["zzx2";"zz";"x2a"] THEN
  LOCAL_SUB_P256_TAC 0 ["resx";"ww";"zzx1"] THEN
  LOCAL_SUB_P256_TAC 0 ["t1";"zzx2";"zzx1"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["xd";"xd";"z_1"] THEN
  LOCAL_SUB_P256_TAC 0 ["resx";"resx";"zzx2"] THEN
  LOCAL_SUB_P256_TAC 0 ["t2";"zzx1";"resx"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["t1";"t1";"y1a"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["resz";"xd";"z_2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["t2";"yd";"t2"] THEN
  LOCAL_SUB_P256_TAC 0 ["resy";"t2";"t1"] THEN

  BIGNUM_LDIGITIZE_TAC "x1_"
   `read (memory :> bytes (p1,8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "y1_"
   `read (memory :> bytes (word_add p1 (word 32),8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "z1_"
   `read (memory :> bytes (word_add p1 (word 64),8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "x2_"
   `read (memory :> bytes (p2,8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "y2_"
   `read (memory :> bytes (word_add p2 (word 32),8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "z2_"
   `read (memory :> bytes (word_add p2 (word 64),8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resx_"
   `read (memory :> bytes (stackpointer,8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resy_"
   `read (memory :> bytes (word_add stackpointer (word 128),8 * 4)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resz_"
   `read (memory :> bytes (word_add stackpointer (word 160),8 * 4)) s114` THEN
  ARM_STEPS_TAC P256_MONTJADD_CORE_EXEC (115--173) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s173" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  MAP_EVERY X_GEN_TAC [`P1:(int#int)option`; `P2:(int#int)option`] THEN
  REWRITE_TAC[represents_p256; tripled] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_256] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_256]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN

  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; INT_OF_NUM_EQ; WORD_OR_EQ_0] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MP_TAC(GEN_ALL(SPEC `[x0:int64;x1;x2;x3]` BIGNUM_OF_WORDLIST_EQ_0)) THEN
  ASM_REWRITE_TAC[ALL; GSYM INT_OF_NUM_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ASM_CASES_TAC [`&z1:int = &0`; `&z2:int = &0`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 256`)] THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["P1"; "P2"] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; INT_REM_ZERO;
                    GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P256_GROUP; weierstrass_add];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P1" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P256_GROUP; weierstrass_add];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P2" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P256_GROUP; weierstrass_add];
    ALL_TAC] THEN

  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma)
   [`z2:num`; `y2:num`; `x2:num`; `z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_256 (2 EXP 256) * x1`;
    `y1d = inverse_mod p_256 (2 EXP 256) * y1`;
    `z1d = inverse_mod p_256 (2 EXP 256) * z1`;
    `x2d = inverse_mod p_256 (2 EXP 256) * x2`;
    `y2d = inverse_mod p_256 (2 EXP 256) * y2`;
    `z2d = inverse_mod p_256 (2 EXP 256) * z2`] THEN
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
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl))) THEN
  REWRITE_TAC[IMP_IMP] THEN
  SUBGOAL_THEN `~(&z1d rem &p_256 = &0) /\ ~(&z2d rem &p_256 = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `~(&z1:int = &0)`; UNDISCH_TAC `~(&z2:int = &0)`] THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    REWRITE_TAC[INT_REM_EQ_0] THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p256_add THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM]) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "P2" THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; OPTION_DISTINCT];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[jacobian_add_unexceptional; nistp256;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;


let P256_MONTJADD_UNOPT_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,224))
            [(word pc,LENGTH p256_montjadd_mc); (p1,96); (p2,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,LENGTH p256_montjadd_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_mc /\
                  read PC s = word(pc + 0x5b0) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read PC s = word (pc + 0x808) /\
                  !P1 P2. represents_p256 P1 t1 /\ represents_p256 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p256 (group_mul p256_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                      X22; X23; X30] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,224)])`,
  ARM_SUB_LIST_OF_MC_TAC P256_MONTJADD_UNOPT_CORE_CORRECT
    p256_montjadd_core_mc_def
    [fst P256_MONTJADD_CORE_EXEC;fst P256_MONTJADD_EXEC]);;



(* ------------------------------------------------------------------------- *)
(* Prove the corectness of optimized p256_montjadd using equivalence checker *)
(* ------------------------------------------------------------------------- *)

let p256_montjadd_eqin = new_definition
  `!s1 s1' p1 p2 p3 stackpointer.
    (p256_montjadd_eqin:(armstate#armstate)->int64->int64->int64->int64->bool)
        (s1,s1') p1 p2 p3 stackpointer <=>
     (C_ARGUMENTS [p3; p1; p2] s1 /\
      C_ARGUMENTS [p3; p1; p2] s1' /\
      read SP s1 = stackpointer /\
      read SP s1' = stackpointer /\
      ?a. bignum_from_memory (p1,12) s1 = a /\
          bignum_from_memory (p1,12) s1' = a /\
      ?b. bignum_from_memory (p2,12) s1 = b /\
          bignum_from_memory (p2,12) s1' = b)`;;

let p256_montjadd_eqout = new_definition
  `!s1 s1' p3.
    (p256_montjadd_eqout:(armstate#armstate)->int64->bool) (s1,s1') p3 <=>
    (// 3 separate 4-word reads to make proving equality between
     // two bignum_triple_from_memory results straightforward
     ?a0. bignum_from_memory (p3,4) s1 = a0 /\
          bignum_from_memory (p3,4) s1' = a0 /\
     ?a1. bignum_from_memory (word_add p3 (word (8 * 4)),4) s1 = a1 /\
          bignum_from_memory (word_add p3 (word (8 * 4)),4) s1' = a1 /\
     ?a2. bignum_from_memory (word_add p3 (word (16 * 4)),4) s1 = a2 /\
          bignum_from_memory (word_add p3 (word (16 * 4)),4) s1' = a2)`;;


let count_insts (execth:thm*thm option array) =
  let length_th = fst execth in
  dest_small_numeral (snd (dest_eq (concl length_th))) / 4;;


(* ------------------------------------------------------------------------- *)
(* Building actions for proving correctness of inlining.                     *)
(* The inlined code is nor included in the repo or in this file.             *)
(* The functions were inlined by hand, not using a script.                   *)
(* ------------------------------------------------------------------------- *)

let code_blocks = [
  ("equal", Some 3);
  ("call montsqr_p256", None);
  ("call montsqr_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call sub_p256", None);
  ("call sub_p256", None);
  ("call montsqr_p256", None);
  ("call montsqr_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call sub_p256", None);
  ("call sub_p256", None);
  ("call montmul_p256", None);
  ("call sub_p256", None);
  ("call sub_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call montmul_p256", None);
  ("call sub_p256", None);
  ("equal", Some (162 - 103))
];;

(* The number of instructions of functions. *)

let len_montsqr_p256_neon, len_montmul_p256_neon, len_sub_p256 =
  count_insts BIGNUM_MONTSQR_P256_NEON_EXEC,
  count_insts BIGNUM_MONTMUL_P256_NEON_EXEC,
  count_insts BIGNUM_SUB_P256_EXEC;;

(* Build the actions. *)

let actions1 = ref [];;
let last_n1 = ref 0 and last_n2 = ref 0;;
List.iter (fun code_block ->
  let n1,n2 = !last_n1,!last_n2 in
  match code_block with
  | "equal", Some nsteps ->
    actions1 := !actions1 @ [("equal",n1,n1+nsteps,n2,n2+nsteps)];
    last_n1 := nsteps + n1;
    last_n2 := nsteps + n2
  | callfn, None ->
    (* nsteps_prologue = # fn arguments
       nsteps_fnbody = # insts of fn except last ret *)
    let nsteps_prologue, nsteps_fnbody = match callfn with
      | "call montsqr_p256" -> 2, len_montsqr_p256_neon - 1
      | "call montmul_p256" -> 3, len_montmul_p256_neon - 1
      | "call sub_p256" -> 3, len_sub_p256 - 1
      | _ -> failwith callfn in begin
    actions1 := !actions1 @
      [(* For argument assignments, use 'replace' not 'equiv' because
          the symbolic expression of memory addresses shouldn't be abbreviated.
          Otherwise symbolic simulator will be confused. *)
       ("replace",n1,n1+nsteps_prologue,n2,n2+nsteps_prologue)];
    let n1 = n1+nsteps_prologue and n2 = n2+nsteps_prologue in begin
    actions1 := !actions1 @
      [(* bl *)
       ("delete", n1, n1+1, n2, n2);
       (* fn body *)
       ("equal",  n1+1, n1+1+nsteps_fnbody,
                  n2, n2+nsteps_fnbody);
       (* ret *)
       ("delete", n1+1+nsteps_fnbody, n1+1+nsteps_fnbody+1,
                  n2+nsteps_fnbody, n2+nsteps_fnbody)];
    last_n1 := n1+1+nsteps_fnbody+1;
    last_n2 := n2+nsteps_fnbody
    end end)
  code_blocks;;


(* ------------------------------------------------------------------------- *)
(* Actions for proving correctness of memory optimizations.                  *)
(* To get this, trim the callee-save register spills & ret from the assembly *)
(* source files after the first stage and second stage, and run              *)
(* 'tools/get-actions.py <trimmed first asm> <trimmed second asm>'.          *)
(* ------------------------------------------------------------------------- *)

let actions2 = [
  ("equal", 0, 4, 0, 4);
  ("replace", 4, 10, 4, 9);
  ("equal", 10, 135, 9, 134);
  ("replace", 135, 136, 134, 135);
  ("equal", 136, 138, 135, 137);
  ("replace", 138, 139, 137, 138);
  ("equal", 139, 140, 138, 139);
  ("replace", 140, 148, 139, 145);
  ("equal", 148, 277, 145, 274);
  ("replace", 277, 287, 274, 281);
  ("equal", 287, 295, 281, 289);
  ("replace", 295, 296, 289, 290);
  ("equal", 296, 311, 290, 305);
  ("replace", 311, 312, 305, 306);
  ("equal", 312, 328, 306, 322);
  ("replace", 328, 329, 322, 323);
  ("equal", 329, 360, 323, 354);
  ("replace", 360, 362, 354, 356);
  ("equal", 362, 364, 356, 358);
  ("replace", 364, 365, 358, 359);
  ("equal", 365, 366, 359, 360);
  ("replace", 366, 367, 360, 361);
  ("equal", 367, 368, 361, 362);
  ("delete", 368, 369, 362, 362);
  ("equal", 369, 392, 362, 385);
  ("delete", 392, 393, 385, 385);
  ("equal", 393, 412, 385, 404);
  ("delete", 412, 413, 404, 404);
  ("equal", 413, 419, 404, 410);
  ("delete", 419, 420, 410, 410);
  ("equal", 420, 423, 410, 413);
  ("replace", 423, 425, 413, 415);
  ("equal", 425, 426, 415, 416);
  ("replace", 426, 427, 416, 417);
  ("equal", 427, 428, 417, 418);
  ("replace", 428, 429, 418, 419);
  ("equal", 429, 482, 419, 472);
  ("replace", 482, 483, 472, 473);
  ("equal", 483, 485, 473, 475);
  ("replace", 485, 494, 475, 481);
  ("equal", 494, 502, 481, 489);
  ("replace", 502, 503, 489, 490);
  ("equal", 503, 518, 490, 505);
  ("replace", 518, 519, 505, 506);
  ("equal", 519, 535, 506, 522);
  ("replace", 535, 536, 522, 523);
  ("equal", 536, 567, 523, 554);
  ("replace", 567, 569, 554, 556);
  ("equal", 569, 571, 556, 558);
  ("replace", 571, 572, 558, 559);
  ("equal", 572, 573, 559, 560);
  ("replace", 573, 574, 560, 561);
  ("equal", 574, 575, 561, 562);
  ("delete", 575, 576, 562, 562);
  ("equal", 576, 599, 562, 585);
  ("delete", 599, 600, 585, 585);
  ("equal", 600, 619, 585, 604);
  ("delete", 619, 620, 604, 604);
  ("equal", 620, 626, 604, 610);
  ("delete", 626, 627, 610, 610);
  ("equal", 627, 630, 610, 613);
  ("replace", 630, 632, 613, 615);
  ("equal", 632, 633, 615, 616);
  ("replace", 633, 634, 616, 617);
  ("equal", 634, 635, 617, 618);
  ("replace", 635, 636, 618, 619);
  ("equal", 636, 685, 619, 668);
  ("replace", 685, 686, 668, 669);
  ("equal", 686, 687, 669, 670);
  ("replace", 687, 688, 670, 671);
  ("equal", 688, 689, 671, 672);
  ("replace", 689, 690, 672, 673);
  ("equal", 690, 692, 673, 675);
  ("replace", 692, 694, 675, 676);
  ("equal", 694, 695, 676, 677);
  ("replace", 695, 698, 677, 678);
  ("equal", 698, 699, 678, 679);
  ("replace", 699, 700, 679, 680);
  ("equal", 700, 702, 680, 682);
  ("replace", 702, 703, 682, 683);
  ("equal", 703, 706, 683, 686);
  ("replace", 706, 707, 686, 687);
  ("equal", 707, 708, 687, 688);
  ("replace", 708, 711, 688, 691);
  ("equal", 711, 714, 691, 694);
  ("replace", 714, 715, 694, 695);
  ("equal", 715, 742, 695, 722);
  ("replace", 742, 743, 722, 723);
  ("equal", 743, 774, 723, 754);
  ("replace", 774, 776, 754, 756);
  ("equal", 776, 778, 756, 758);
  ("replace", 778, 779, 758, 759);
  ("equal", 779, 780, 759, 760);
  ("replace", 780, 781, 760, 761);
  ("equal", 781, 782, 761, 762);
  ("delete", 782, 783, 762, 762);
  ("equal", 783, 806, 762, 785);
  ("delete", 806, 807, 785, 785);
  ("equal", 807, 826, 785, 804);
  ("delete", 826, 827, 804, 804);
  ("equal", 827, 833, 804, 810);
  ("delete", 833, 834, 810, 810);
  ("equal", 834, 837, 810, 813);
  ("replace", 837, 839, 813, 815);
  ("equal", 839, 840, 815, 816);
  ("replace", 840, 841, 816, 817);
  ("equal", 841, 842, 817, 818);
  ("replace", 842, 843, 818, 819);
  ("equal", 843, 896, 819, 872);
  ("replace", 896, 897, 872, 873);
  ("equal", 897, 899, 873, 875);
  ("replace", 899, 908, 875, 881);
  ("equal", 908, 916, 881, 889);
  ("replace", 916, 917, 889, 890);
  ("equal", 917, 932, 890, 905);
  ("replace", 932, 933, 905, 906);
  ("equal", 933, 949, 906, 922);
  ("replace", 949, 950, 922, 923);
  ("equal", 950, 981, 923, 954);
  ("replace", 981, 983, 954, 956);
  ("equal", 983, 985, 956, 958);
  ("replace", 985, 986, 958, 959);
  ("equal", 986, 987, 959, 960);
  ("replace", 987, 988, 960, 961);
  ("equal", 988, 989, 961, 962);
  ("delete", 989, 990, 962, 962);
  ("equal", 990, 1013, 962, 985);
  ("delete", 1013, 1014, 985, 985);
  ("equal", 1014, 1033, 985, 1004);
  ("delete", 1033, 1034, 1004, 1004);
  ("equal", 1034, 1040, 1004, 1010);
  ("delete", 1040, 1041, 1010, 1010);
  ("equal", 1041, 1044, 1010, 1013);
  ("replace", 1044, 1046, 1013, 1015);
  ("equal", 1046, 1047, 1015, 1016);
  ("replace", 1047, 1048, 1016, 1017);
  ("equal", 1048, 1049, 1017, 1018);
  ("replace", 1049, 1050, 1018, 1019);
  ("equal", 1050, 1103, 1019, 1072);
  ("replace", 1103, 1104, 1072, 1073);
  ("equal", 1104, 1106, 1073, 1075);
  ("replace", 1106, 1108, 1075, 1076);
  ("equal", 1108, 1109, 1076, 1077);
  ("replace", 1109, 1111, 1077, 1078);
  ("equal", 1111, 1113, 1078, 1080);
  ("delete", 1113, 1114, 1080, 1080);
  ("equal", 1114, 1120, 1080, 1086);
  ("replace", 1120, 1121, 1086, 1087);
  ("equal", 1121, 1123, 1087, 1089);
  ("replace", 1123, 1124, 1089, 1090);
  ("equal", 1124, 1128, 1090, 1094);
  ("replace", 1128, 1129, 1094, 1095);
  ("equal", 1129, 1133, 1095, 1099);
  ("replace", 1133, 1134, 1099, 1100);
  ("equal", 1134, 1156, 1100, 1122);
  ("replace", 1156, 1157, 1122, 1123);
  ("equal", 1157, 1164, 1123, 1130);
  ("replace", 1164, 1166, 1130, 1132);
  ("equal", 1166, 1188, 1132, 1154);
  ("replace", 1188, 1190, 1154, 1156);
  ("equal", 1190, 1192, 1156, 1158);
  ("replace", 1192, 1193, 1158, 1159);
  ("equal", 1193, 1194, 1159, 1160);
  ("replace", 1194, 1195, 1160, 1161);
  ("equal", 1195, 1196, 1161, 1162);
  ("delete", 1196, 1197, 1162, 1162);
  ("equal", 1197, 1220, 1162, 1185);
  ("delete", 1220, 1221, 1185, 1185);
  ("equal", 1221, 1240, 1185, 1204);
  ("delete", 1240, 1241, 1204, 1204);
  ("equal", 1241, 1247, 1204, 1210);
  ("delete", 1247, 1248, 1210, 1210);
  ("equal", 1248, 1251, 1210, 1213);
  ("replace", 1251, 1253, 1213, 1215);
  ("equal", 1253, 1254, 1215, 1216);
  ("replace", 1254, 1255, 1216, 1217);
  ("equal", 1255, 1256, 1217, 1218);
  ("replace", 1256, 1257, 1218, 1219);
  ("equal", 1257, 1306, 1219, 1268);
  ("replace", 1306, 1307, 1268, 1269);
  ("equal", 1307, 1308, 1269, 1270);
  ("replace", 1308, 1309, 1270, 1271);
  ("equal", 1309, 1310, 1271, 1272);
  ("delete", 1310, 1311, 1272, 1272);
  ("equal", 1311, 1313, 1272, 1274);
  ("replace", 1313, 1322, 1274, 1280);
  ("equal", 1322, 1330, 1280, 1288);
  ("replace", 1330, 1331, 1288, 1289);
  ("equal", 1331, 1346, 1289, 1304);
  ("replace", 1346, 1347, 1304, 1305);
  ("equal", 1347, 1363, 1305, 1321);
  ("replace", 1363, 1364, 1321, 1322);
  ("equal", 1364, 1395, 1322, 1353);
  ("replace", 1395, 1397, 1353, 1355);
  ("equal", 1397, 1399, 1355, 1357);
  ("replace", 1399, 1400, 1357, 1358);
  ("equal", 1400, 1401, 1358, 1359);
  ("replace", 1401, 1402, 1359, 1360);
  ("equal", 1402, 1403, 1360, 1361);
  ("delete", 1403, 1404, 1361, 1361);
  ("equal", 1404, 1427, 1361, 1384);
  ("delete", 1427, 1428, 1384, 1384);
  ("equal", 1428, 1447, 1384, 1403);
  ("delete", 1447, 1448, 1403, 1403);
  ("equal", 1448, 1454, 1403, 1409);
  ("delete", 1454, 1455, 1409, 1409);
  ("equal", 1455, 1458, 1409, 1412);
  ("replace", 1458, 1460, 1412, 1414);
  ("equal", 1460, 1461, 1414, 1415);
  ("replace", 1461, 1462, 1415, 1416);
  ("equal", 1462, 1463, 1416, 1417);
  ("replace", 1463, 1464, 1417, 1418);
  ("equal", 1464, 1513, 1418, 1467);
  ("replace", 1513, 1514, 1467, 1468);
  ("equal", 1514, 1515, 1468, 1469);
  ("replace", 1515, 1516, 1469, 1470);
  ("equal", 1516, 1517, 1470, 1471);
  ("replace", 1517, 1526, 1471, 1477);
  ("equal", 1526, 1528, 1477, 1479);
  ("replace", 1528, 1530, 1479, 1481);
  ("equal", 1530, 1533, 1481, 1484);
  ("replace", 1533, 1534, 1484, 1485);
  ("equal", 1534, 1535, 1485, 1486);
  ("replace", 1535, 1537, 1486, 1488);
  ("equal", 1537, 1538, 1488, 1489);
  ("replace", 1538, 1552, 1489, 1497);
  ("equal", 1552, 1553, 1497, 1498);
  ("replace", 1553, 1554, 1498, 1499);
  ("equal", 1554, 1555, 1499, 1500);
  ("replace", 1555, 1556, 1500, 1501);
  ("equal", 1556, 1559, 1501, 1504);
  ("replace", 1559, 1568, 1504, 1509);
  ("equal", 1568, 1570, 1509, 1511);
  ("replace", 1570, 1571, 1511, 1512);
  ("equal", 1571, 1575, 1512, 1516);
  ("replace", 1575, 1577, 1516, 1518);
  ("equal", 1577, 1583, 1518, 1524);
  ("replace", 1583, 1584, 1524, 1525);
  ("equal", 1584, 1589, 1525, 1530);
  ("replace", 1589, 1590, 1530, 1531);
  ("equal", 1590, 1616, 1531, 1557);
  ("replace", 1616, 1617, 1557, 1558);
  ("equal", 1617, 1625, 1558, 1566);
  ("replace", 1625, 1626, 1566, 1567);
  ("equal", 1626, 1633, 1567, 1574);
  ("replace", 1633, 1634, 1574, 1575);
  ("equal", 1634, 1639, 1575, 1580);
  ("replace", 1639, 1640, 1580, 1581);
  ("equal", 1640, 1642, 1581, 1583);
  ("replace", 1642, 1643, 1583, 1584);
  ("equal", 1643, 1650, 1584, 1591);
  ("replace", 1650, 1651, 1591, 1592);
  ("equal", 1651, 1655, 1592, 1596);
  ("replace", 1655, 1656, 1596, 1597);
  ("equal", 1656, 1693, 1597, 1634);
  ("replace", 1693, 1699, 1634, 1640);
  ("equal", 1699, 1700, 1640, 1641);
  ("replace", 1700, 1706, 1641, 1645);
  ("equal", 1706, 1708, 1645, 1647);
  ("replace", 1708, 1709, 1647, 1648);
  ("equal", 1709, 1713, 1648, 1652);
  ("replace", 1713, 1715, 1652, 1654);
  ("equal", 1715, 1721, 1654, 1660);
  ("replace", 1721, 1722, 1660, 1661);
  ("equal", 1722, 1754, 1661, 1693);
  ("replace", 1754, 1755, 1693, 1694);
  ("equal", 1755, 1837, 1694, 1776);
  ("replace", 1837, 1845, 1776, 1779);
  ("equal", 1845, 1846, 1779, 1780);
  ("replace", 1846, 1847, 1780, 1781);
  ("equal", 1847, 1850, 1781, 1784);
  ("replace", 1850, 1851, 1784, 1785);
  ("equal", 1851, 1852, 1785, 1786);
  ("replace", 1852, 1855, 1786, 1789);
  ("equal", 1855, 1856, 1789, 1790);
  ("replace", 1856, 1857, 1790, 1791);
  ("equal", 1857, 1858, 1791, 1792);
  ("replace", 1858, 1859, 1792, 1793);
  ("equal", 1859, 1869, 1793, 1803);
  ("replace", 1869, 1870, 1803, 1804);
  ("equal", 1870, 1886, 1804, 1820);
  ("replace", 1886, 1887, 1820, 1821);
  ("equal", 1887, 1918, 1821, 1852);
  ("replace", 1918, 1920, 1852, 1854);
  ("equal", 1920, 1922, 1854, 1856);
  ("replace", 1922, 1923, 1856, 1857);
  ("equal", 1923, 1924, 1857, 1858);
  ("replace", 1924, 1925, 1858, 1859);
  ("equal", 1925, 1926, 1859, 1860);
  ("delete", 1926, 1927, 1860, 1860);
  ("equal", 1927, 1950, 1860, 1883);
  ("delete", 1950, 1951, 1883, 1883);
  ("equal", 1951, 1970, 1883, 1902);
  ("delete", 1970, 1971, 1902, 1902);
  ("equal", 1971, 1977, 1902, 1908);
  ("delete", 1977, 1978, 1908, 1908);
  ("equal", 1978, 1981, 1908, 1911);
  ("replace", 1981, 1983, 1911, 1913);
  ("equal", 1983, 1984, 1913, 1914);
  ("replace", 1984, 1985, 1914, 1915);
  ("equal", 1985, 1986, 1915, 1916);
  ("replace", 1986, 1987, 1916, 1917);
  ("equal", 1987, 2036, 1917, 1966);
  ("replace", 2036, 2037, 1966, 1967);
  ("equal", 2037, 2038, 1967, 1968);
  ("replace", 2038, 2039, 1968, 1969);
  ("equal", 2039, 2040, 1969, 1970);
  ("replace", 2040, 2041, 1970, 1971);
  ("equal", 2041, 2043, 1971, 1973);
  ("replace", 2043, 2052, 1973, 1978);
  ("equal", 2052, 2053, 1978, 1979);
  ("replace", 2053, 2054, 1979, 1980);
  ("equal", 2054, 2057, 1980, 1983);
  ("replace", 2057, 2058, 1983, 1984);
  ("equal", 2058, 2059, 1984, 1985);
  ("replace", 2059, 2062, 1985, 1988);
  ("equal", 2062, 2065, 1988, 1991);
  ("replace", 2065, 2066, 1991, 1992);
  ("equal", 2066, 2076, 1992, 2002);
  ("replace", 2076, 2077, 2002, 2003);
  ("equal", 2077, 2093, 2003, 2019);
  ("replace", 2093, 2094, 2019, 2020);
  ("equal", 2094, 2125, 2020, 2051);
  ("replace", 2125, 2127, 2051, 2053);
  ("equal", 2127, 2129, 2053, 2055);
  ("replace", 2129, 2130, 2055, 2056);
  ("equal", 2130, 2131, 2056, 2057);
  ("replace", 2131, 2132, 2057, 2058);
  ("equal", 2132, 2133, 2058, 2059);
  ("delete", 2133, 2134, 2059, 2059);
  ("equal", 2134, 2157, 2059, 2082);
  ("delete", 2157, 2158, 2082, 2082);
  ("equal", 2158, 2177, 2082, 2101);
  ("delete", 2177, 2178, 2101, 2101);
  ("equal", 2178, 2184, 2101, 2107);
  ("delete", 2184, 2185, 2107, 2107);
  ("equal", 2185, 2188, 2107, 2110);
  ("replace", 2188, 2190, 2110, 2112);
  ("equal", 2190, 2191, 2112, 2113);
  ("replace", 2191, 2192, 2113, 2114);
  ("equal", 2192, 2193, 2114, 2115);
  ("replace", 2193, 2194, 2115, 2116);
  ("equal", 2194, 2243, 2116, 2165);
  ("replace", 2243, 2244, 2165, 2166);
  ("equal", 2244, 2245, 2166, 2167);
  ("replace", 2245, 2246, 2167, 2168);
  ("equal", 2246, 2247, 2168, 2169);
  ("replace", 2247, 2251, 2169, 2173);
  ("equal", 2251, 2253, 2173, 2175);
  ("delete", 2253, 2254, 2175, 2175);
  ("equal", 2254, 2255, 2175, 2176);
  ("replace", 2255, 2258, 2176, 2178);
  ("equal", 2258, 2259, 2178, 2179);
  ("replace", 2259, 2260, 2179, 2180);
  ("equal", 2260, 2263, 2180, 2183);
  ("replace", 2263, 2264, 2183, 2184);
  ("equal", 2264, 2265, 2184, 2185);
  ("replace", 2265, 2266, 2185, 2186);
  ("equal", 2266, 2269, 2186, 2189);
  ("delete", 2269, 2270, 2189, 2189);
  ("equal", 2270, 2271, 2189, 2190);
  ("replace", 2271, 2282, 2190, 2195);
  ("equal", 2282, 2289, 2195, 2202);
  ("replace", 2289, 2299, 2202, 2209);
  ("equal", 2299, 2307, 2209, 2217);
  ("replace", 2307, 2308, 2217, 2218);
  ("equal", 2308, 2323, 2218, 2233);
  ("replace", 2323, 2324, 2233, 2234);
  ("equal", 2324, 2340, 2234, 2250);
  ("replace", 2340, 2341, 2250, 2251);
  ("equal", 2341, 2372, 2251, 2282);
  ("replace", 2372, 2374, 2282, 2284);
  ("equal", 2374, 2376, 2284, 2286);
  ("replace", 2376, 2377, 2286, 2287);
  ("equal", 2377, 2378, 2287, 2288);
  ("replace", 2378, 2379, 2288, 2289);
  ("equal", 2379, 2380, 2289, 2290);
  ("delete", 2380, 2381, 2290, 2290);
  ("equal", 2381, 2404, 2290, 2313);
  ("delete", 2404, 2405, 2313, 2313);
  ("equal", 2405, 2424, 2313, 2332);
  ("delete", 2424, 2425, 2332, 2332);
  ("equal", 2425, 2431, 2332, 2338);
  ("delete", 2431, 2432, 2338, 2338);
  ("equal", 2432, 2435, 2338, 2341);
  ("replace", 2435, 2437, 2341, 2343);
  ("equal", 2437, 2438, 2343, 2344);
  ("replace", 2438, 2439, 2344, 2345);
  ("equal", 2439, 2440, 2345, 2346);
  ("replace", 2440, 2441, 2346, 2347);
  ("equal", 2441, 2494, 2347, 2400);
  ("replace", 2494, 2498, 2400, 2404);
  ("equal", 2498, 2500, 2404, 2406);
  ("replace", 2500, 2505, 2406, 2409);
  ("equal", 2505, 2506, 2409, 2410);
  ("replace", 2506, 2507, 2410, 2411);
  ("equal", 2507, 2510, 2411, 2414);
  ("replace", 2510, 2511, 2414, 2415);
  ("equal", 2511, 2512, 2415, 2416);
  ("replace", 2512, 2514, 2416, 2418);
  ("equal", 2514, 2515, 2418, 2419);
  ("replace", 2515, 2528, 2419, 2427);
  ("equal", 2528, 2536, 2427, 2435);
  ("replace", 2536, 2546, 2435, 2442);
  ("equal", 2546, 2554, 2442, 2450);
  ("replace", 2554, 2555, 2450, 2451);
  ("equal", 2555, 2570, 2451, 2466);
  ("replace", 2570, 2571, 2466, 2467);
  ("equal", 2571, 2587, 2467, 2483);
  ("replace", 2587, 2588, 2483, 2484);
  ("equal", 2588, 2619, 2484, 2515);
  ("replace", 2619, 2621, 2515, 2517);
  ("equal", 2621, 2623, 2517, 2519);
  ("replace", 2623, 2624, 2519, 2520);
  ("equal", 2624, 2625, 2520, 2521);
  ("replace", 2625, 2626, 2521, 2522);
  ("equal", 2626, 2627, 2522, 2523);
  ("delete", 2627, 2628, 2523, 2523);
  ("equal", 2628, 2651, 2523, 2546);
  ("delete", 2651, 2652, 2546, 2546);
  ("equal", 2652, 2671, 2546, 2565);
  ("delete", 2671, 2672, 2565, 2565);
  ("equal", 2672, 2678, 2565, 2571);
  ("delete", 2678, 2679, 2571, 2571);
  ("equal", 2679, 2682, 2571, 2574);
  ("replace", 2682, 2684, 2574, 2576);
  ("equal", 2684, 2685, 2576, 2577);
  ("replace", 2685, 2686, 2577, 2578);
  ("equal", 2686, 2687, 2578, 2579);
  ("replace", 2687, 2688, 2579, 2580);
  ("equal", 2688, 2741, 2580, 2633);
  ("replace", 2741, 2742, 2633, 2634);
  ("equal", 2742, 2744, 2634, 2636);
  ("replace", 2744, 2753, 2636, 2641);
  ("equal", 2753, 2760, 2641, 2648);
  ("replace", 2760, 2763, 2648, 2651);
  ("equal", 2763, 2764, 2651, 2652);
  ("replace", 2764, 2765, 2652, 2653);
  ("equal", 2765, 2777, 2653, 2665);
  ("replace", 2777, 2778, 2665, 2666);
  ("equal", 2778, 2794, 2666, 2682);
  ("replace", 2794, 2795, 2682, 2683);
  ("equal", 2795, 2826, 2683, 2714);
  ("replace", 2826, 2828, 2714, 2716);
  ("equal", 2828, 2830, 2716, 2718);
  ("replace", 2830, 2831, 2718, 2719);
  ("equal", 2831, 2832, 2719, 2720);
  ("replace", 2832, 2833, 2720, 2721);
  ("equal", 2833, 2834, 2721, 2722);
  ("delete", 2834, 2835, 2722, 2722);
  ("equal", 2835, 2858, 2722, 2745);
  ("delete", 2858, 2859, 2745, 2745);
  ("equal", 2859, 2878, 2745, 2764);
  ("delete", 2878, 2879, 2764, 2764);
  ("equal", 2879, 2885, 2764, 2770);
  ("delete", 2885, 2886, 2770, 2770);
  ("equal", 2886, 2889, 2770, 2773);
  ("replace", 2889, 2891, 2773, 2775);
  ("equal", 2891, 2892, 2775, 2776);
  ("replace", 2892, 2893, 2776, 2777);
  ("equal", 2893, 2894, 2777, 2778);
  ("replace", 2894, 2895, 2778, 2779);
  ("equal", 2895, 2944, 2779, 2828);
  ("replace", 2944, 2945, 2828, 2829);
  ("equal", 2945, 2946, 2829, 2830);
  ("replace", 2946, 2947, 2830, 2831);
  ("equal", 2947, 2948, 2831, 2832);
  ("replace", 2948, 2949, 2832, 2833);
  ("equal", 2949, 2951, 2833, 2835);
  ("replace", 2951, 2960, 2835, 2841);
  ("equal", 2960, 2968, 2841, 2849);
  ("replace", 2968, 2969, 2849, 2850);
  ("equal", 2969, 2984, 2850, 2865);
  ("replace", 2984, 2985, 2865, 2866);
  ("equal", 2985, 3001, 2866, 2882);
  ("replace", 3001, 3002, 2882, 2883);
  ("equal", 3002, 3033, 2883, 2914);
  ("replace", 3033, 3035, 2914, 2916);
  ("equal", 3035, 3037, 2916, 2918);
  ("replace", 3037, 3038, 2918, 2919);
  ("equal", 3038, 3039, 2919, 2920);
  ("replace", 3039, 3040, 2920, 2921);
  ("equal", 3040, 3041, 2921, 2922);
  ("delete", 3041, 3042, 2922, 2922);
  ("equal", 3042, 3065, 2922, 2945);
  ("delete", 3065, 3066, 2945, 2945);
  ("equal", 3066, 3085, 2945, 2964);
  ("delete", 3085, 3086, 2964, 2964);
  ("equal", 3086, 3092, 2964, 2970);
  ("delete", 3092, 3093, 2970, 2970);
  ("equal", 3093, 3096, 2970, 2973);
  ("replace", 3096, 3098, 2973, 2975);
  ("equal", 3098, 3099, 2975, 2976);
  ("replace", 3099, 3100, 2976, 2977);
  ("equal", 3100, 3101, 2977, 2978);
  ("replace", 3101, 3102, 2978, 2979);
  ("equal", 3102, 3151, 2979, 3028);
  ("replace", 3151, 3152, 3028, 3029);
  ("equal", 3152, 3153, 3029, 3030);
  ("replace", 3153, 3154, 3030, 3031);
  ("equal", 3154, 3155, 3031, 3032);
  ("replace", 3155, 3164, 3032, 3035);
  ("equal", 3164, 3166, 3035, 3037);
  ("replace", 3166, 3168, 3037, 3038);
  ("equal", 3168, 3169, 3038, 3039);
  ("replace", 3169, 3170, 3039, 3040);
  ("equal", 3170, 3171, 3040, 3041);
  ("replace", 3171, 3172, 3041, 3042);
  ("equal", 3172, 3173, 3042, 3043);
  ("replace", 3173, 3175, 3043, 3045);
  ("equal", 3175, 3176, 3045, 3046);
  ("replace", 3176, 3179, 3046, 3049);
  ("equal", 3179, 3194, 3049, 3064);
  ("replace", 3194, 3197, 3064, 3066);
  ("equal", 3197, 3219, 3066, 3088);
  ("replace", 3219, 3222, 3088, 3090);
  ("equal", 3222, 3226, 3090, 3094);
  ("replace", 3226, 3229, 3094, 3096);
  ("equal", 3229, 3238, 3096, 3105);
];;


(* ------------------------------------------------------------------------- *)
(* Full actions.                                                             *)
(* ------------------------------------------------------------------------- *)

let actions_merged = merge_actions (!actions1,actions2);;


(* ------------------------------------------------------------------------- *)
(* Prove program equivalence between the base and optimized assemblies.      *)
(* ------------------------------------------------------------------------- *)

let p256_montjadd_opt_mc =
  define_from_elf "p256_montjadd_opt_mc" "arm/p256/p256_montjadd.o";;
let P256_MONTJADD_OPT_EXEC = ARM_MK_EXEC_RULE p256_montjadd_opt_mc;;

let len_p256_montjadd_opt = count_insts P256_MONTJADD_OPT_EXEC;;

let equiv_goal = mk_equiv_statement
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (stackpointer:int64,224))
            [(word pc,LENGTH p256_montjadd_core_mc);
             (word pc2,LENGTH p256_montjadd_opt_mc);
             (p1:int64,96); (p2:int64,96); (p3:int64,96)] /\
     ALL (nonoverlapping (p3,96))
       [(word pc,LENGTH p256_montjadd_core_mc);
        (word pc2,LENGTH p256_montjadd_opt_mc)]`
    p256_montjadd_eqin
    p256_montjadd_eqout
    p256_montjadd_core_mc 0x5b0 0x808
    `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                X22; X23; X30] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bytes(p3,96);
                memory :> bytes(stackpointer,224)]`
    p256_montjadd_opt_mc 0x18 0x309c
    `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                X22; X23; X24; X25; X26; X27; X30] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bytes(p3,96);
                memory :> bytes(stackpointer,224)]`
    (vsubst [mk_small_numeral(
        150 + len_montsqr_p256_neon * 4 + len_montmul_p256_neon * 12
            + len_sub_p256 * 7),`x:num`]
        `\(s:armstate). (x:num)`)
    (vsubst [mk_small_numeral(len_p256_montjadd_opt - 13),`x:num`]
        `\(s:armstate). (x:num)`);;


extra_early_rewrite_rules :=
  (hd (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))::
  !extra_early_rewrite_rules;;

let P256_MONTJADD_EQUIV = time prove(equiv_goal,

  CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    SOME_FLAGS;MODIFIABLE_SIMD_REGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst P256_MONTJADD_CORE_EXEC;
    fst P256_MONTJADD_OPT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC p256_montjadd_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC actions_merged P256_MONTJADD_CORE_EXEC P256_MONTJADD_OPT_EXEC THEN

  REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[p256_montjadd_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,4) state`;
                    C_ARGUMENTS] THEN
    (* Fold `word_add (word_add x c1) c2` and constant exprs that came from
       p256_montjadd_eqout *)
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    (* Prove eq. *)
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange left **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0':armstate` (concl th)) THEN
    MONOTONE_MAYCHANGE_TAC;

    (** SUBGOAL 3. Maychange right **)
    DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0:armstate` (concl th)) THEN
    MONOTONE_MAYCHANGE_TAC
  ]);;



let event_n_at_pc_goal = mk_eventually_n_at_pc_statement
    `aligned 16 (stackpointer:int64) /\
     ALL (nonoverlapping (stackpointer,224))
          [(word pc,LENGTH (APPEND p256_montjadd_core_mc barrier_inst_bytes));
           (p1,96); (p2,96); (p3,96)] /\
     nonoverlapping (p3,96)
        (word pc,LENGTH (APPEND p256_montjadd_core_mc barrier_inst_bytes))`
    [`p1:int64`;`p2:int64`;`p3:int64`;`stackpointer:int64`]
    p256_montjadd_core_mc `pc+0x5b0` `pc+0x808` `3284`
    `\s0. read SP s0 = stackpointer /\ C_ARGUMENTS [p3; p1; p2] s0`;;


let P256_MONTJADD_UNOPT_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,
  REWRITE_TAC[LENGTH_APPEND;fst P256_MONTJADD_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH p256_montjadd_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst P256_MONTJADD_CORE_EXEC]) THENL [
    REWRITE_TAC[fst P256_MONTJADD_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC P256_MONTJADD_CORE_EXEC);;

let P256_MONTJADD_UNOPT_CORE_CORRECT_N =
  prove_correct_n
    P256_MONTJADD_EXEC
    P256_MONTJADD_CORE_EXEC
    P256_MONTJADD_UNOPT_CORE_CORRECT
    P256_MONTJADD_UNOPT_EVENTUALLY_N_AT_PC;;


let P256_MONTJADD_CORRECT = prove(
  `!p3 p1 t1 p2 t2 pc2 stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,224))
            [(word pc2,LENGTH p256_montjadd_opt_mc); (p1,96); (p2,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc2,LENGTH p256_montjadd_opt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) p256_montjadd_opt_mc /\
                  read PC s = word(pc2 + 0x18) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read PC s = word (pc2 + 0x309c) /\
                  !P1 P2. represents_p256 P1 t1 /\ represents_p256 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p256 (group_mul p256_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                      X22; X23; X24; X25; X26; X27; X30] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,224)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      ALL (nonoverlapping
        (word pc,LENGTH (APPEND p256_montjadd_core_mc barrier_inst_bytes)))
        [(p1:int64,96);(p2:int64,96);(p3:int64,96);(stackpointer:int64,224)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst P256_MONTJADD_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    time FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  VCGEN_EQUIV_TAC P256_MONTJADD_EQUIV P256_MONTJADD_UNOPT_CORE_CORRECT_N
    [fst P256_MONTJADD_CORE_EXEC;fst P256_MONTJADD_OPT_EXEC] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[ALL;NONOVERLAPPING_CLAUSES;
      LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst P256_MONTJADD_CORE_EXEC; fst P256_MONTJADD_OPT_EXEC]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;bignum_triple_from_memory] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[p256_montjadd_eqin;C_ARGUMENTS] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND p256_montjadd_core_mc barrier_inst_bytes)))
          (APPEND p256_montjadd_core_mc barrier_inst_bytes)
          (write PC (word (pc + 0x5b0)) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    PROVE_CONJ_OF_EQ_READS_TAC P256_MONTJADD_CORE_EXEC THEN
    (* Now has only one subgoal: the input state equivalence! *)
    REPEAT (HINT_EXISTS_REFL_TAC THEN
        PROVE_CONJ_OF_EQ_READS_TAC P256_MONTJADD_CORE_EXEC);

    (** SUBGOAL 2. Postcond **)
    REWRITE_TAC[p256_montjadd_eqout;BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    MESON_TAC[fst P256_MONTJADD_CORE_EXEC; fst P256_MONTJADD_OPT_EXEC];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS]
  ]);;

let P256_MONTJADD_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 304),304))
            [(word pc,LENGTH p256_montjadd_opt_mc); (p1,96); (p2,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,LENGTH p256_montjadd_opt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjadd_opt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read PC s = returnaddress /\
                  !P1 P2. represents_p256 P1 t1 /\ represents_p256 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p256 (group_mul p256_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 304),304)])`,
  REWRITE_TAC[fst P256_MONTJADD_OPT_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC P256_MONTJADD_OPT_EXEC
    (REWRITE_RULE[fst P256_MONTJADD_OPT_EXEC]P256_MONTJADD_CORRECT)
    `[X19;X20;X21;X22;X23;X24;X25;X26;X27;X30]` 304);;
