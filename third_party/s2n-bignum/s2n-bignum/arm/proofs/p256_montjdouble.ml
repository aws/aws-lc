(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Montgomery-Jacobian coordinates for NIST P-256 curve.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp256.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

needs "arm/proofs/bignum_montsqr_p256.ml";;
needs "arm/proofs/bignum_montmul_p256.ml";;
needs "arm/proofs/bignum_sub_p256.ml";;
needs "arm/proofs/bignum_add_p256.ml";;

(**** print_literal_from_elf "arm/p256/p256_montjdouble.o";;
 ****)

let p256_montjdouble_mc = define_assert_from_elf
  "p256_montjdouble_mc" "arm/p256/unopt/p256_montjdouble.o"
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
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xab080084;       (* arm_ADDS X4 X4 X8 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xa9411c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xb1000488;       (* arm_ADDS X8 X4 (rvalue (word 1)) *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0xfa0900a9;       (* arm_SBCS X9 X5 X9 *)
  0xfa1f00ca;       (* arm_SBCS X10 X6 XZR *)
  0xb26083eb;       (* arm_MOV X11 (rvalue (word 18446744069414584321)) *)
  0xfa0b00eb;       (* arm_SBCS X11 X7 X11 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0x9a8a30c6;       (* arm_CSEL X6 X6 X10 Condition_CC *)
  0x9a8b30e7;       (* arm_CSEL X7 X7 X11 Condition_CC *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd10383ff;       (* arm_SUB SP SP (rvalue (word 224)) *)
  0xa90d7ffe;       (* arm_STP X30 XZR SP (Immediate_Offset (iword (&208))) *)
  0xa90c53f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&192))) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0xaa0103f4;       (* arm_MOV X20 X1 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x91010281;       (* arm_ADD X1 X20 (rvalue (word 64)) *)
  0x97ffff47;       (* arm_BL (word 268434716) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x91008281;       (* arm_ADD X1 X20 (rvalue (word 32)) *)
  0x97ffff44;       (* arm_BL (word 268434704) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x91000281;       (* arm_ADD X1 X20 (rvalue (word 0)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x97ffffc9;       (* arm_BL (word 268435236) *)
  0xa9401a85;       (* arm_LDP X5 X6 X20 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412287;       (* arm_LDP X7 X8 X20 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xda9f33e3;       (* arm_CSETM X3 Condition_CS *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0x92407c61;       (* arm_AND X1 X3 (rvalue (word 4294967295)) *)
  0xfa0100c6;       (* arm_SBCS X6 X6 X1 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0x92608062;       (* arm_AND X2 X3 (rvalue (word 18446744069414584321)) *)
  0xda020108;       (* arm_SBC X8 X8 X2 *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x97fffe5e;       (* arm_BL (word 268433784) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x91008281;       (* arm_ADD X1 X20 (rvalue (word 32)) *)
  0x91010282;       (* arm_ADD X2 X20 (rvalue (word 64)) *)
  0x97ffffc2;       (* arm_BL (word 268435208) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x91000281;       (* arm_ADD X1 X20 (rvalue (word 0)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x97fffe56;       (* arm_BL (word 268433752) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x97ffff20;       (* arm_BL (word 268434560) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x97ffff1d;       (* arm_BL (word 268434548) *)
  0xd2800121;       (* arm_MOV X1 (rvalue (word 9)) *)
  0x92800002;       (* arm_MOVN X2 (word 0) 0 *)
  0xa94a2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&160))) *)
  0xeb090049;       (* arm_SUBS X9 X2 X9 *)
  0xb2407fe2;       (* arm_MOV X2 (rvalue (word 4294967295)) *)
  0xfa0a004a;       (* arm_SBCS X10 X2 X10 *)
  0xa94b33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&176))) *)
  0xfa0b03eb;       (* arm_NGCS X11 X11 *)
  0xb26083e2;       (* arm_MOV X2 (rvalue (word 18446744069414584321)) *)
  0xda0c004c;       (* arm_SBC X12 X2 X12 *)
  0x9b097c23;       (* arm_MUL X3 X1 X9 *)
  0x9b0a7c24;       (* arm_MUL X4 X1 X10 *)
  0x9b0b7c25;       (* arm_MUL X5 X1 X11 *)
  0x9b0c7c26;       (* arm_MUL X6 X1 X12 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0x9bcb7c2b;       (* arm_UMULH X11 X1 X11 *)
  0x9bcc7c27;       (* arm_UMULH X7 X1 X12 *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xd2800181;       (* arm_MOV X1 (rvalue (word 12)) *)
  0xa9482be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&128))) *)
  0x9b017d28;       (* arm_MUL X8 X9 X1 *)
  0x9bc17d29;       (* arm_UMULH X9 X9 X1 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9b017d48;       (* arm_MUL X8 X10 X1 *)
  0x9bc17d4a;       (* arm_UMULH X10 X10 X1 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94933eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&144))) *)
  0x9b017d68;       (* arm_MUL X8 X11 X1 *)
  0x9bc17d6b;       (* arm_UMULH X11 X11 X1 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9b017d88;       (* arm_MUL X8 X12 X1 *)
  0x9bc17d8c;       (* arm_UMULH X12 X12 X1 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a0c00e7;       (* arm_ADC X7 X7 X12 *)
  0x910004e8;       (* arm_ADD X8 X7 (rvalue (word 1)) *)
  0xd3607d0a;       (* arm_LSL X10 X8 32 *)
  0xab0a00c6;       (* arm_ADDS X6 X6 X10 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xcb0803e9;       (* arm_NEG X9 X8 *)
  0xd100054a;       (* arm_SUB X10 X10 (rvalue (word 1)) *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa0a0084;       (* arm_SBCS X4 X4 X10 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa0800c6;       (* arm_SBCS X6 X6 X8 *)
  0xda0800e8;       (* arm_SBC X8 X7 X8 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x92407d09;       (* arm_AND X9 X8 (rvalue (word 4294967295)) *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xcb0903ea;       (* arm_NEG X10 X9 *)
  0x9a0a00c6;       (* arm_ADC X6 X6 X10 *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x97ffff65;       (* arm_BL (word 268434836) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x97fffed9;       (* arm_BL (word 268434276) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x97fffe08;       (* arm_BL (word 268433440) *)
  0x91010260;       (* arm_ADD X0 X19 (rvalue (word 64)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x97ffff5a;       (* arm_BL (word 268434792) *)
  0xa9480be1;       (* arm_LDP X1 X2 SP (Immediate_Offset (iword (&128))) *)
  0xd37ef420;       (* arm_LSL X0 X1 2 *)
  0xa94a1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&160))) *)
  0xeb060000;       (* arm_SUBS X0 X0 X6 *)
  0x93c1f841;       (* arm_EXTR X1 X2 X1 62 *)
  0xfa070021;       (* arm_SBCS X1 X1 X7 *)
  0xa94913e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0x93c2f862;       (* arm_EXTR X2 X3 X2 62 *)
  0xa94b1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&176))) *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0x93c3f883;       (* arm_EXTR X3 X4 X3 62 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xd37efc84;       (* arm_LSR X4 X4 62 *)
  0xda1f0084;       (* arm_SBC X4 X4 XZR *)
  0x91000485;       (* arm_ADD X5 X4 (rvalue (word 1)) *)
  0xd3607ca8;       (* arm_LSL X8 X5 32 *)
  0xeb0803e6;       (* arm_NEGS X6 X8 *)
  0xfa1f03e7;       (* arm_NGCS X7 XZR *)
  0xda050108;       (* arm_SBC X8 X8 X5 *)
  0xab050000;       (* arm_ADDS X0 X0 X5 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xda9f23e5;       (* arm_CSETM X5 Condition_CC *)
  0xab050000;       (* arm_ADDS X0 X0 X5 *)
  0x92407ca6;       (* arm_AND X6 X5 (rvalue (word 4294967295)) *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xcb0603e7;       (* arm_NEG X7 X6 *)
  0x9a070063;       (* arm_ADC X3 X3 X7 *)
  0xa9000660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&0))) *)
  0xa9010e62;       (* arm_STP X2 X3 X19 (Immediate_Offset (iword (&16))) *)
  0xd2800101;       (* arm_MOV X1 (rvalue (word 8)) *)
  0x92800002;       (* arm_MOVN X2 (word 0) 0 *)
  0xa9402be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&0))) *)
  0xeb090049;       (* arm_SUBS X9 X2 X9 *)
  0xb2407fe2;       (* arm_MOV X2 (rvalue (word 4294967295)) *)
  0xfa0a004a;       (* arm_SBCS X10 X2 X10 *)
  0xa94133eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&16))) *)
  0xfa0b03eb;       (* arm_NGCS X11 X11 *)
  0xb26083e2;       (* arm_MOV X2 (rvalue (word 18446744069414584321)) *)
  0xda0c004c;       (* arm_SBC X12 X2 X12 *)
  0xd37df123;       (* arm_LSL X3 X9 3 *)
  0x93c9f544;       (* arm_EXTR X4 X10 X9 61 *)
  0x93caf565;       (* arm_EXTR X5 X11 X10 61 *)
  0x93cbf586;       (* arm_EXTR X6 X12 X11 61 *)
  0xd37dfd87;       (* arm_LSR X7 X12 61 *)
  0xd2800061;       (* arm_MOV X1 (rvalue (word 3)) *)
  0xa9462be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&96))) *)
  0x9b017d28;       (* arm_MUL X8 X9 X1 *)
  0x9bc17d29;       (* arm_UMULH X9 X9 X1 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9b017d48;       (* arm_MUL X8 X10 X1 *)
  0x9bc17d4a;       (* arm_UMULH X10 X10 X1 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94733eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&112))) *)
  0x9b017d68;       (* arm_MUL X8 X11 X1 *)
  0x9bc17d6b;       (* arm_UMULH X11 X11 X1 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9b017d88;       (* arm_MUL X8 X12 X1 *)
  0x9bc17d8c;       (* arm_UMULH X12 X12 X1 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a0c00e7;       (* arm_ADC X7 X7 X12 *)
  0x910004e8;       (* arm_ADD X8 X7 (rvalue (word 1)) *)
  0xd3607d0a;       (* arm_LSL X10 X8 32 *)
  0xab0a00c6;       (* arm_ADDS X6 X6 X10 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xcb0803e9;       (* arm_NEG X9 X8 *)
  0xd100054a;       (* arm_SUB X10 X10 (rvalue (word 1)) *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa0a0084;       (* arm_SBCS X4 X4 X10 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa0800c6;       (* arm_SBCS X6 X6 X8 *)
  0xda0800e8;       (* arm_SBC X8 X7 X8 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x92407d09;       (* arm_AND X9 X8 (rvalue (word 4294967295)) *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xcb0903ea;       (* arm_NEG X10 X9 *)
  0x9a0a00c6;       (* arm_ADC X6 X6 X10 *)
  0xa9021263;       (* arm_STP X3 X4 X19 (Immediate_Offset (iword (&32))) *)
  0xa9031a65;       (* arm_STP X5 X6 X19 (Immediate_Offset (iword (&48))) *)
  0xa94c53f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&192))) *)
  0xa94d7ffe;       (* arm_LDP X30 XZR SP (Immediate_Offset (iword (&208))) *)
  0x910383ff;       (* arm_ADD SP SP (rvalue (word 224)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;


let P256_MONTJDOUBLE_EXEC = ARM_MK_EXEC_RULE p256_montjdouble_mc;;

(* P256_MONTJDOUBLE_EXEC without callee save register reloads and ret.
   This truncation is for equivalence checking. *)
let p256_montjdouble_core_mc_def,p256_montjdouble_core_mc,
    P256_MONTJDOUBLE_CORE_EXEC =
  mk_sublist_of_mc "p256_montjdouble_core_mc"
    p256_montjdouble_mc (`0`,`LENGTH p256_montjdouble_mc - 16`)
    (fst P256_MONTJDOUBLE_EXEC);;

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
 ["x_1",[`X20`; `0`];
  "y_1",[`X20`; `32`];
  "z_1",[`X20`; `64`];
  "x_3",[`X19`; `0`];
  "y_3",[`X19`; `32`];
  "z_3",[`X19`; `64`];
  "z2",[`SP`; `0`];
  "y4",[`SP`; `0`];
  "y2",[`SP`; `32`];
  "t1",[`SP`; `64`];
  "t2",[`SP`; `96`];
  "x2p",[`SP`; `96`];
  "dx2",[`SP`; `96`];
  "xy2",[`SP`; `128`];
  "x4p",[`SP`; `160`];
  "d",[`SP`; `160`]];;


(* ------------------------------------------------------------------------- *)
(* Support interface of ARM_MACRO_SIM_ABBREV_TAC when using a subroutine.    *)
(* ------------------------------------------------------------------------- *)

let PROLOGUE_SUBROUTINE_SIM_TAC corth inargs outarg m inouts =
  let main_tac =
     ARM_SUBROUTINE_SIM_ABBREV_TAC
      (p256_montjdouble_core_mc,P256_MONTJDOUBLE_CORE_EXEC,0,
       p256_montjdouble_core_mc,corth)
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
    ARM_STEPS_TAC P256_MONTJDOUBLE_CORE_EXEC ((n+1)--(n+m+k)) THEN
    main_tac (name_of dvar') (n+m+k+1));;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_P256_CORRECT =
  let lemma = prove(`!z x a pc.
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
                  read PC s = word (pc + 0x334) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + (0x334 + LENGTH bignum_montsqr_p256_core_mc)) /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    SUBGOAL_THEN
      `bignum_montsqr_p256_core_mc =
        SUB_LIST (0x334, LENGTH bignum_montsqr_p256_core_mc)
                 p256_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_MONTSQR_P256_CORE_EXEC;
                  bignum_montsqr_p256_core_mc; p256_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P256_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_MONTSQR_P256_CORE_EXEC] th)
        [fst BIGNUM_MONTSQR_P256_CORE_EXEC;
        fst P256_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC]
    (prove(`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
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
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst P256_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P256_MONTJDOUBLE_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC;fst BIGNUM_MONTSQR_P256_CORE_EXEC])
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
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p256_core_mc) /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    SUBGOAL_THEN
      `bignum_montmul_p256_core_mc =
        SUB_LIST (0, LENGTH bignum_montmul_p256_core_mc) p256_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_MONTMUL_P256_CORE_EXEC;
                  bignum_montmul_p256_core_mc; p256_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P256_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_MONTMUL_P256_CORE_EXEC] th)
        [fst BIGNUM_MONTMUL_P256_CORE_EXEC;
        fst P256_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC]
    (prove(`!z x y a b pc returnaddress.
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
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
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst P256_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P256_MONTJDOUBLE_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC;fst BIGNUM_MONTMUL_P256_CORE_EXEC])
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
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
                  read PC s = word (pc + 0x558) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + (0x558 + 0x44)) /\
                  (m < p_256 /\ n < p_256
                   ==> &(bignum_from_memory (z,4) s) = (&m - &n) rem &p_256))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,4)])`,
    SUBGOAL_THEN
      `bignum_sub_p256_mc = SUB_LIST (0x558, 0x48) p256_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_SUB_P256_EXEC; bignum_sub_p256_mc; p256_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_SUB_P256_CORRECT
        (REWRITE_RULE [fst BIGNUM_SUB_P256_EXEC] th)
        [fst BIGNUM_SUB_P256_EXEC; fst P256_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC] (prove(
    `!z x y m n pc returnaddress.
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
                  read PC s = word (pc + 0x558) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_256 /\ n < p_256
                   ==> &(bignum_from_memory (z,4) s) = (&m - &n) rem &p_256))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,4)])`,
    REWRITE_TAC[fst P256_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P256_MONTJDOUBLE_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC;fst BIGNUM_SUB_P256_EXEC])
     lemma)));;

let LOCAL_SUB_P256_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_SUB_P256_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `read (memory :> bytes(read X2 s,8 * 4)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 4)) s'`;;

(* ------------------------------------------------------------------------- *)
(* Instances of weakadd                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKADD_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_core_mc 17 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,2380) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X19 s = read X19 t /\
              read X20 s = read X20 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (m + n < 2 EXP 256 + p_256
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s < 2 EXP 256 /\
                       (&(read(memory :> bytes(word_add (read p3 t) (word n3),
                               8 * 4)) s):int == &m + &n) (mod &p_256)))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC P256_MONTJDOUBLE_CORE_EXEC [9] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC (10--17) (10--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!x. (x < 2 EXP 256 /\ P x) /\ y = x ==> y < 2 EXP 256 /\ P y`) THEN
  EXISTS_TAC `if m + n < 2 EXP 256 then m + n else (m + n) - p_256` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `m + n < 2 EXP 256 + p_256` THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_CONG_REFL] THEN
    MATCH_MP_TAC(INTEGER_RULE `y - p:int = x ==> (x == y) (mod p)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC INT_OF_NUM_SUB THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `b <=> 2 EXP 256 <= m + n` THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCARD_STATE_TAC "s27" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; COND_SWAP] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `m + n < 2 EXP 256 + p_256` THEN
    EXPAND_TAC "b" THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `&(if b then (m + n) - p_256 else m + n):real =
    if b then (&m + &n) - &p_256 else &m + &n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    UNDISCH_TAC `b:bool` THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P256_CORRECT =
  let lemma = prove(`!z x y m n pc.
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
                  read PC s = word (pc + 0x5a0) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + (0x5a0 + 0x58)) /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,4)])`,
    SUBGOAL_THEN
      `bignum_add_p256_mc = SUB_LIST (0x5a0, 92) p256_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_SUB_P256_EXEC; bignum_add_p256_mc;
                  p256_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_ADD_P256_CORRECT
        (REWRITE_RULE [fst BIGNUM_ADD_P256_EXEC] th)
        [fst BIGNUM_SUB_P256_EXEC; fst P256_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC] (prove(
    `!z x y m n pc returnaddress.
        nonoverlapping (word pc,LENGTH p256_montjdouble_core_mc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
                  read PC s = word (pc + 0x5a0) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
    REWRITE_TAC[fst P256_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P256_MONTJDOUBLE_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P256_MONTJDOUBLE_CORE_EXEC;fst BIGNUM_ADD_P256_EXEC])
     lemma)));;

let LOCAL_ADD_P256_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_ADD_P256_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `read (memory :> bytes(read X2 s,8 * 4)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 4)) s'`;;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_core_mc 61 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,2380) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X19 s = read X19 t /\
              read X20 s = read X20 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&12 * &m - &9 * &n) rem &p_256))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_CORE_EXEC (1--61)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_256 =
    (&12 * &m + &9 * (&p_256 - &n)) rem &p_256`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC (1--10) (1--10) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist[sum_s4; sum_s6; sum_s8; sum_s10]` THEN
  SUBGOAL_THEN `p_256 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_256]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The main multiply-add accumulation without the final bump ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC (11--42) (11--42) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s27; sum_s39; sum_s40; sum_s41; sum_s42]` THEN
  SUBGOAL_THEN `12 * m + 9 * n' < 24 * p_256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_256] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `12 * m + 9 * n' = ca` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "ca" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = ca DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 24` ASSUME_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `sum_s42:int64 = word h` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `ca:num` p256shortishredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of ca - (h + 1) * p_256 ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC (45::46::(49--53)) (43--53) THEN
  MP_TAC(SPECL
   [`sum_s53:int64`;
    `&(bignum_of_wordlist[sum_s49; sum_s50; sum_s51; sum_s52]):real`;
    `256`; `ca:num`; `(h + 1) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= ca + p_256`;
        `ca < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [sum_s27; sum_s39; sum_s40; sum_s41; word h] =
      ca`)) THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 24` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC [54;56;57;59] (54--61) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> ca < (h + 1) * p_256` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &ca - y + z ==> &ca = x + y - z`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub41_p256 (actually there is only one).                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_core_mc 32 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,2380) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X19 s = read X19 t /\
              read X20 s = read X20 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
         (\s. read PC s = pcout /\
              (n < p_256
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 4)) s) = (&4 * &m - &n) rem &p_256))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_256 assumption ***)

  ASM_CASES_TAC `n < p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_CORE_EXEC (1--32)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Instantiate the (integer) quotient approximation lemma ***)

  MP_TAC(SPEC `&4 * &m - &n:int` p256shortintredlemma) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_LT; INT_ARITH
     `n:int < p ==> --p <= &4 * &m - n`] THEN
    MATCH_MP_TAC(INT_ARITH `x:int <= a ==> x - &n <= a`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN EXPAND_TAC "m" THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Main shift-subtract block ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC [4;6;10;12;14;15] (1--15) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s4; sum_s6; sum_s10; sum_s12; sum_s15]` THEN
  SUBGOAL_THEN `&2 pow 256 + &4 * &m - &n:int = &ca`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_pow_th;
                int_mul_th; int_of_num_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`320`; `&0:real`] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "ca" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&4 * &m:real =
      &(bignum_of_wordlist
         [word_shl m_0 2;
          word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
          word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
          word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
          word_ushr m_3 62])`
    SUBST1_TAC THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
      REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                  BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_RING;
      MAP_EVERY EXPAND_TAC ["n"; "ca"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s15` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s15:int64` o concl))) THEN
  SUBGOAL_THEN `&ca div &2 pow 256 = &(val(q:int64))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV] THEN
    EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC
   [20;21;22;23; 25;27;28;30] (16--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED_MOD THEN
  MAP_EVERY EXISTS_TAC [`&(val(q:int64)):int`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; p_256] THEN BOUNDER_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `&4 * m - n:int = (&2 pow 256 + &4 * m - n) - &2 pow 256`] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Usual finale, but all split explicitly over q for simplicity ***)

  SUBGOAL_THEN
    `(&ca - &2 pow 256):int < &(val(q:int64)) * &p_256 <=> ~carry_s23`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_LT_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SUBST1_TAC(SYM(ISPEC `q:int64` WORD_VAL)) THEN
    UNDISCH_TAC `&(val(q:int64)):int < &6` THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    SPEC_TAC(`val(q:int64)`,`qv:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_RULE
     `(a:int == b + c - p) (mod p) <=> (a == b + c) (mod p)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    SUBST1_TAC(SYM(ISPEC `q:int64` WORD_VAL)) THEN
    UNDISCH_TAC `&(val(q:int64)):int < &6` THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    SPEC_TAC(`val(q:int64)`,`qv:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s23:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub38 (there is only one).                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_core_mc 54 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,2380) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X19 s = read X19 t /\
              read X20 s = read X20 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&3 * &m - &8 * &n) rem &p_256))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_CORE_EXEC (1--54)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) rem &p_256 =
    (&3 * &m + &8 * (&p_256 - &n)) rem &p_256`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC (1--10) (1--10) THEN
  ABBREV_TAC `n' = bignum_of_wordlist[sum_s4; sum_s6; sum_s8; sum_s10]` THEN
  SUBGOAL_THEN `p_256 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_256]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The main multiply-add accumulation without the final bump ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC
   [18;20;21;23;25;27;28;30;31;32;33;34;35] (11--35) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s20; sum_s32; sum_s33; sum_s34; sum_s35]` THEN
  SUBGOAL_THEN `3 * m + 8 * n' < 24 * p_256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_256] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `3 * m + 8 * n' = ca` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "ca" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `8 * n' =
      bignum_of_wordlist
       [word_shl sum_s4 3;
        word_subword ((word_join:int64->int64->int128) sum_s6 sum_s4) (61,64);
        word_subword ((word_join:int64->int64->int128) sum_s8 sum_s6) (61,64);
        word_subword ((word_join:int64->int64->int128) sum_s10 sum_s8) (61,64);
        word_ushr sum_s10 61]`
    SUBST1_TAC THENL
     [EXPAND_TAC "n'" THEN REWRITE_TAC[bignum_of_wordlist] THEN
      REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
      REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                  BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_RING;
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
      MAP_EVERY EXPAND_TAC ["m"; "ca"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = ca DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 24` ASSUME_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `sum_s35:int64 = word h` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `ca:num` p256shortishredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of ca - (h + 1) * p_256 ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC (38::39::(42--46)) (36--46) THEN
  MP_TAC(SPECL
   [`sum_s46:int64`;
    `&(bignum_of_wordlist[sum_s42; sum_s43; sum_s44; sum_s45]):real`;
    `256`; `ca:num`; `(h + 1) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= ca + p_256`;
        `ca < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [sum_s20; sum_s32; sum_s33; sum_s34; word h] =
      ca`)) THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 24` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_CORE_EXEC [47;49;50;52] (47--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> ca < (h + 1) * p_256` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &ca - y + z ==> &ca = x + y - z`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

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

let weierstrass_of_jacobian_p256_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp256
         (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) =
        (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256)
       ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                  (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256) =
                group_mul p256_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp256; P256_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
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

let P256_MONTJDOUBLE_UNOPT_CORE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,192))
            [(word pc,LENGTH p256_montjdouble_core_mc); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,LENGTH p256_montjdouble_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_core_mc /\
                  read PC s = word(pc + 0x608) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read PC s = word (pc + 0x94c) /\
                 !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20; X30] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM;fst P256_MONTJDOUBLE_CORE_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_P256_TAC 2 ["z2";"z_1"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["y2";"y_1"] THEN
  LOCAL_SUB_P256_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_WEAKADD_P256_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P256_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["t1";"t1"] THEN
  LOCAL_CMSUBC9_P256_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P256_TAC 0 ["t1";"t1";"z2"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["y4";"y2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_SUB_P256_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_CMSUB41_P256_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P256_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s61" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
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
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma) [`z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_256 (2 EXP 256) * x1`;
    `y1d = inverse_mod p_256 (2 EXP 256) * y1`;
    `z1d = inverse_mod p_256 (2 EXP 256) * z1`] THEN
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
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p256_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp256;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Prove the corectness of optimized p256_montjdouble using equiv. checker   *)
(* ------------------------------------------------------------------------- *)

let p256_montjdouble_eqin = new_definition
  `!s1 s1' p1 p3 stackpointer.
    (p256_montjdouble_eqin:(armstate#armstate)->int64->int64->int64->bool)
        (s1,s1') p1 p3 stackpointer <=>
     (C_ARGUMENTS [p3; p1] s1 /\
      C_ARGUMENTS [p3; p1] s1' /\
      read SP s1 = stackpointer /\
      read SP s1' = stackpointer /\
      ?a. bignum_from_memory (p1,12) s1 = a /\
          bignum_from_memory (p1,12) s1' = a)`;;

let p256_montjdouble_eqout = new_definition
  `!s1 s1' p3.
    (p256_montjdouble_eqout:(armstate#armstate)->int64->bool) (s1,s1') p3 <=>
    (// 3 separate 4-word reads to make proving equality between
     // two bignum_triple_from_memory results straightforward
     ?a0. bignum_from_memory (p3,4) s1 = a0 /\
          bignum_from_memory (p3,4) s1' = a0 /\
     ?a1. bignum_from_memory (word_add p3 (word (8 * 4)),4) s1 = a1 /\
          bignum_from_memory (word_add p3 (word (8 * 4)),4) s1' = a1 /\
     ?a2. bignum_from_memory (word_add p3 (word (16 * 4)),4) s1 = a2 /\
          bignum_from_memory (word_add p3 (word (16 * 4)),4) s1' = a2)`;;


(* ------------------------------------------------------------------------- *)
(* Load parameters that will be used by equivalence checking proofs.         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/p256_montjdouble_params.ml";;

(* ------------------------------------------------------------------------- *)
(* Prove program equivalence between the base and optimized assemblies.      *)
(* ------------------------------------------------------------------------- *)

let p256_montjdouble_opt_mc =
  define_from_elf "p256_montjdouble_opt_mc" "arm/p256/p256_montjdouble.o";;
let P256_MONTJDOUBLE_OPT_EXEC = ARM_MK_EXEC_RULE p256_montjdouble_opt_mc;;

let len_p256_montjdouble_opt = count_insts P256_MONTJDOUBLE_OPT_EXEC;;

let equiv_goal = mk_equiv_statement
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (stackpointer:int64,192))
            [(word pc,LENGTH p256_montjdouble_core_mc);
             (word pc2,LENGTH p256_montjdouble_opt_mc);
             (p1:int64,96); (p3:int64,96)] /\
     ALL (nonoverlapping (p3,96))
       [(word pc,LENGTH p256_montjdouble_core_mc);
        (word pc2,LENGTH p256_montjdouble_opt_mc)]`
    p256_montjdouble_eqin
    p256_montjdouble_eqout
    p256_montjdouble_core_mc 0x608 0x94c
    `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                X11; X12; X13; X14; X15; X16; X17; X19; X20; X30] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(p3,96);
                memory :> bytes(stackpointer,192)]`
    p256_montjdouble_opt_mc 0x18 0x1778
    `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                X22; X23; X24; X25; X26; X27] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(p3,96);
                memory :> bytes(stackpointer,192)]`
    (vsubst [mk_small_numeral(
        let _,_,n,_,_ = last !actions1 in n),`x:num`]
        `\(s:armstate). (x:num)`)
    (vsubst [mk_small_numeral(len_p256_montjdouble_opt - 6 - 7),`x:num`]
        `\(s:armstate). (x:num)`);;

extra_early_rewrite_rules :=
  (el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT))::
  !extra_early_rewrite_rules;;

let occ_cache_left:(term * ((term * thm) list ref)) list ref = ref []
    and occ_cache_right:(term * ((term * thm) list ref)) list ref = ref [];;
orthogonal_components_conv_custom_cache :=
  fun (l,r,eval) ->
    if not (is_const l || is_const r) then None else
    let cache,l,r = if is_const l
      then occ_cache_left,l,r
      else occ_cache_right,r,l in
    try
      let lref = assoc l !cache in
      try Some (assoc r !lref)
      with _ -> let newth = eval () in
        lref := (r,newth)::!lref; Some newth
    with _ -> let newth = eval () in
      cache := (l, ref [(r,newth)])::!cache; Some newth;;


let P256_MONTJDOUBLE_EQUIV = time prove(equiv_goal,

  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    SOME_FLAGS;MODIFIABLE_SIMD_REGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst P256_MONTJDOUBLE_CORE_EXEC;
    fst P256_MONTJDOUBLE_OPT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC p256_montjdouble_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC
    ~dead_value_info_left:p256_montjdouble_unopt_dead_value_info
    ~dead_value_info_right:p256_montjdouble_dead_value_info
    actions_merged P256_MONTJDOUBLE_CORE_EXEC P256_MONTJDOUBLE_OPT_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[p256_montjdouble_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,4) state`;
                    C_ARGUMENTS] THEN
    (* Fold `word_add (word_add x c1) c2` and constant exprs that came from
       p256_montjadd_eqout *)
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    (* Prove eq. *)
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

orthogonal_components_conv_custom_cache := fun _ -> None;;


let event_n_at_pc_goal = mk_eventually_n_at_pc_statement
    `aligned 16 (stackpointer:int64) /\
     ALL (nonoverlapping (stackpointer,192))
          [(word pc,LENGTH (APPEND p256_montjdouble_core_mc barrier_inst_bytes));
           (p1,96); (p3,96)] /\
     nonoverlapping (p3,96)
        (word pc,LENGTH (APPEND p256_montjdouble_core_mc barrier_inst_bytes))`
    [`p1:int64`;`p3:int64`;`stackpointer:int64`]
    p256_montjdouble_core_mc `pc+0x608` `pc+0x94c`
    (mk_small_numeral (let _,_,n,_,_ = last !actions1 in n))
    `\s0. read SP s0 = stackpointer /\ C_ARGUMENTS [p3; p1] s0`;;


let P256_MONTJDOUBLE_UNOPT_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,
  REWRITE_TAC[LENGTH_APPEND;fst P256_MONTJDOUBLE_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH p256_montjdouble_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst P256_MONTJDOUBLE_CORE_EXEC]) THENL [
    REWRITE_TAC[fst P256_MONTJDOUBLE_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC P256_MONTJDOUBLE_CORE_EXEC);;


let P256_MONTJDOUBLE_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    P256_MONTJDOUBLE_EXEC
    P256_MONTJDOUBLE_CORE_EXEC
    P256_MONTJDOUBLE_UNOPT_CORE_CORRECT
    P256_MONTJDOUBLE_UNOPT_EVENTUALLY_N_AT_PC;;

let P256_MONTJDOUBLE_CORRECT = prove(
  `!p3 p1 t1 pc2 stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,192))
            [(word pc2,LENGTH p256_montjdouble_opt_mc); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc2,LENGTH p256_montjdouble_opt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) p256_montjdouble_opt_mc /\
                  read PC s = word(pc2 + 0x18) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read PC s = word (pc2 + 0x1778) /\
                  !P. represents_p256 P t1
                          ==> represents_p256 (group_mul p256_group P P)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                      X22; X23; X24; X25; X26; X27] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,192)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      ALL (nonoverlapping
        (word pc,LENGTH (APPEND p256_montjdouble_core_mc barrier_inst_bytes)))
        [(p1:int64,96);(p3:int64,96);(stackpointer:int64,192)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst P256_MONTJDOUBLE_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    time FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  VCGEN_EQUIV_TAC P256_MONTJDOUBLE_EQUIV P256_MONTJDOUBLE_UNOPT_CORE_CORRECT_N
    [fst P256_MONTJDOUBLE_CORE_EXEC;fst P256_MONTJDOUBLE_OPT_EXEC] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[ALL;NONOVERLAPPING_CLAUSES;
      LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst P256_MONTJDOUBLE_CORE_EXEC; fst P256_MONTJDOUBLE_OPT_EXEC]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;bignum_triple_from_memory] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[p256_montjdouble_eqin;C_ARGUMENTS] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND p256_montjdouble_core_mc barrier_inst_bytes)))
          (APPEND p256_montjdouble_core_mc barrier_inst_bytes)
          (write PC (word (pc + 0x608)) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    PROVE_CONJ_OF_EQ_READS_TAC P256_MONTJDOUBLE_CORE_EXEC THEN
    (* Now has only one subgoal: the input state equivalence! *)
    REPEAT (HINT_EXISTS_REFL_TAC THEN
        PROVE_CONJ_OF_EQ_READS_TAC P256_MONTJDOUBLE_CORE_EXEC);

    (** SUBGOAL 2. Postcond **)
    REWRITE_TAC[p256_montjdouble_eqout;BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MESON_TAC[fst P256_MONTJDOUBLE_CORE_EXEC; fst P256_MONTJDOUBLE_OPT_EXEC];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS]
  ]);;

let P256_MONTJDOUBLE_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 272),272))
            [(word pc,LENGTH p256_montjdouble_opt_mc); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,LENGTH p256_montjdouble_opt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_opt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read PC s = returnaddress /\
                 !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 272),272)])`,
  REWRITE_TAC[fst P256_MONTJDOUBLE_OPT_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC P256_MONTJDOUBLE_OPT_EXEC
    (REWRITE_RULE[fst P256_MONTJDOUBLE_OPT_EXEC]P256_MONTJDOUBLE_CORRECT)
    `[X19;X20;X21;X22;X23;X24;X25;X26;X27]` 272);;
