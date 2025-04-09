(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Montgomery-Jacobian coordinates for NIST P-384 curve.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp384.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

needs "arm/proofs/bignum_montsqr_p384.ml";;
needs "arm/proofs/bignum_montmul_p384.ml";;
needs "arm/proofs/bignum_sub_p384.ml";;
needs "arm/proofs/bignum_add_p384.ml";;

(**** print_literal_from_elf "arm/p384/p384_montjdouble.o";;
 ****)

let p384_montjdouble_mc = define_assert_from_elf
  "p384_montjdouble_mc" "arm/p384/unopt/p384_montjdouble.o"
[
  0xd100c3ff;       (* arm_SUB SP SP (rvalue (word 48)) *)
  0xa90253f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&32))) *)
  0xa9015bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa90063f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&0))) *)
  0x3dc00023;       (* arm_LDR Q3 X1 (Immediate_Offset (word 0)) *)
  0x3dc00059;       (* arm_LDR Q25 X2 (Immediate_Offset (word 0)) *)
  0xa9405c4d;       (* arm_LDP X13 X23 X2 (Immediate_Offset (iword (&0))) *)
  0xa9405423;       (* arm_LDP X3 X21 X1 (Immediate_Offset (iword (&0))) *)
  0x4ea00b37;       (* arm_REV64_VEC Q23 Q25 32 *)
  0x4e831b31;       (* arm_UZP1 Q17 Q25 Q3 32 *)
  0x9bcd7c6f;       (* arm_UMULH X15 X3 X13 *)
  0x4ea39ee6;       (* arm_MUL_VEC Q6 Q23 Q3 32 128 *)
  0x4e831863;       (* arm_UZP1 Q3 Q3 Q3 32 *)
  0x3dc0085b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 32)) *)
  0xa9416028;       (* arm_LDP X8 X24 X1 (Immediate_Offset (iword (&16))) *)
  0xeb150066;       (* arm_SUBS X6 X3 X21 *)
  0x3dc00820;       (* arm_LDR Q0 X1 (Immediate_Offset (word 32)) *)
  0x6f00e5f7;       (* arm_MOVI Q23 (word 4294967295) *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0x9bd77eb3;       (* arm_UMULH X19 X21 X23 *)
  0x4ea00b64;       (* arm_REV64_VEC Q4 Q27 32 *)
  0x4e9b5b79;       (* arm_UZP2 Q25 Q27 Q27 32 *)
  0xda8624c4;       (* arm_CNEG X4 X6 Condition_CC *)
  0xeb0d02e7;       (* arm_SUBS X7 X23 X13 *)
  0x0ea12816;       (* arm_XTN Q22 Q0 32 *)
  0x0ea12b78;       (* arm_XTN Q24 Q27 32 *)
  0xda8724f4;       (* arm_CNEG X20 X7 Condition_CC *)
  0xa9413846;       (* arm_LDP X6 X14 X2 (Immediate_Offset (iword (&16))) *)
  0x4ea09c9b;       (* arm_MUL_VEC Q27 Q4 Q0 32 128 *)
  0x6ea028d4;       (* arm_UADDLP Q20 Q6 32 *)
  0xda8a2145;       (* arm_CINV X5 X10 Condition_CC *)
  0x9b147c90;       (* arm_MUL X16 X4 X20 *)
  0x4e805806;       (* arm_UZP2 Q6 Q0 Q0 32 *)
  0x2eb9c2d5;       (* arm_UMULL_VEC Q21 Q22 Q25 32 *)
  0x4f605680;       (* arm_SHL_VEC Q0 Q20 32 64 128 *)
  0x2eb18060;       (* arm_UMLAL_VEC Q0 Q3 Q17 32 *)
  0x9b067d16;       (* arm_MUL X22 X8 X6 *)
  0x2eb9c0c1;       (* arm_UMULL_VEC Q1 Q6 Q25 32 *)
  0xeb08006c;       (* arm_SUBS X12 X3 X8 *)
  0x2eb8c2d4;       (* arm_UMULL_VEC Q20 Q22 Q24 32 *)
  0xda8c2591;       (* arm_CNEG X17 X12 Condition_CC *)
  0x9bc67d09;       (* arm_UMULH X9 X8 X6 *)
  0x4e183c0c;       (* arm_UMOV X12 Q0 1 8 *)
  0xca05020b;       (* arm_EOR X11 X16 X5 *)
  0x4e083c07;       (* arm_UMOV X7 Q0 0 8 *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0x6f601695;       (* arm_USRA_VEC Q21 Q20 32 64 128 *)
  0xab0c01ef;       (* arm_ADDS X15 X15 X12 *)
  0xba16026c;       (* arm_ADCS X12 X19 X22 *)
  0x9bd47c94;       (* arm_UMULH X20 X4 X20 *)
  0x9a1f0133;       (* arm_ADC X19 X9 XZR *)
  0x6f6016a1;       (* arm_USRA_VEC Q1 Q21 32 64 128 *)
  0xab0701f6;       (* arm_ADDS X22 X15 X7 *)
  0x4e371eba;       (* arm_AND_VEC Q26 Q21 Q23 128 *)
  0xba0f0190;       (* arm_ADCS X16 X12 X15 *)
  0x6ea02b79;       (* arm_UADDLP Q25 Q27 32 *)
  0xba0c0269;       (* arm_ADCS X9 X19 X12 *)
  0x2eb880da;       (* arm_UMLAL_VEC Q26 Q6 Q24 32 *)
  0x9a1f0264;       (* arm_ADC X4 X19 XZR *)
  0xab070210;       (* arm_ADDS X16 X16 X7 *)
  0x4f60573b;       (* arm_SHL_VEC Q27 Q25 32 64 128 *)
  0xba0f0129;       (* arm_ADCS X9 X9 X15 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0xca05028c;       (* arm_EOR X12 X20 X5 *)
  0x9a1f026f;       (* arm_ADC X15 X19 XZR *)
  0xeb0d00d4;       (* arm_SUBS X20 X6 X13 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0x9b147e33;       (* arm_MUL X19 X17 X20 *)
  0xba0b02cb;       (* arm_ADCS X11 X22 X11 *)
  0xba0c020c;       (* arm_ADCS X12 X16 X12 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9bd47e31;       (* arm_UMULH X17 X17 X20 *)
  0xba050096;       (* arm_ADCS X22 X4 X5 *)
  0x9a0501e5;       (* arm_ADC X5 X15 X5 *)
  0xeb0802b0;       (* arm_SUBS X16 X21 X8 *)
  0xda902614;       (* arm_CNEG X20 X16 Condition_CC *)
  0xca0a0273;       (* arm_EOR X19 X19 X10 *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb1700d0;       (* arm_SUBS X16 X6 X23 *)
  0xda902610;       (* arm_CNEG X16 X16 Condition_CC *)
  0x2eb882db;       (* arm_UMLAL_VEC Q27 Q22 Q24 32 *)
  0x9b107e8f;       (* arm_MUL X15 X20 X16 *)
  0xda842084;       (* arm_CINV X4 X4 Condition_CC *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0x6f601741;       (* arm_USRA_VEC Q1 Q26 32 64 128 *)
  0xba130193;       (* arm_ADCS X19 X12 X19 *)
  0xca0a0231;       (* arm_EOR X17 X17 X10 *)
  0xba110129;       (* arm_ADCS X9 X9 X17 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0xd3607cec;       (* arm_LSL X12 X7 32 *)
  0x9bd07e94;       (* arm_UMULH X20 X20 X16 *)
  0xca0401f0;       (* arm_EOR X16 X15 X4 *)
  0xa942444f;       (* arm_LDP X15 X17 X2 (Immediate_Offset (iword (&32))) *)
  0x8b070182;       (* arm_ADD X2 X12 X7 *)
  0x9a0a00a7;       (* arm_ADC X7 X5 X10 *)
  0xa9422825;       (* arm_LDP X5 X10 X1 (Immediate_Offset (iword (&32))) *)
  0xd360fc41;       (* arm_LSR X1 X2 32 *)
  0xca04028c;       (* arm_EOR X12 X20 X4 *)
  0xeb020021;       (* arm_SUBS X1 X1 X2 *)
  0xda1f0054;       (* arm_SBC X20 X2 XZR *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0x93c18281;       (* arm_EXTR X1 X20 X1 32 *)
  0xd360fe94;       (* arm_LSR X20 X20 32 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0x9a0400f0;       (* arm_ADC X16 X7 X4 *)
  0xab02028c;       (* arm_ADDS X12 X20 X2 *)
  0x9bce7f07;       (* arm_UMULH X7 X24 X14 *)
  0x9a1f03e4;       (* arm_ADC X4 XZR XZR *)
  0xeb010161;       (* arm_SUBS X1 X11 X1 *)
  0xfa0c0274;       (* arm_SBCS X20 X19 X12 *)
  0xfa04012c;       (* arm_SBCS X12 X9 X4 *)
  0xd3607c29;       (* arm_LSL X9 X1 32 *)
  0x8b010121;       (* arm_ADD X1 X9 X1 *)
  0xfa1f02c9;       (* arm_SBCS X9 X22 XZR *)
  0x9b0e7f16;       (* arm_MUL X22 X24 X14 *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xd360fc24;       (* arm_LSR X4 X1 32 *)
  0xda1f0053;       (* arm_SBC X19 X2 XZR *)
  0xeb010084;       (* arm_SUBS X4 X4 X1 *)
  0xda1f002b;       (* arm_SBC X11 X1 XZR *)
  0x93c48162;       (* arm_EXTR X2 X11 X4 32 *)
  0xd360fd64;       (* arm_LSR X4 X11 32 *)
  0xab010084;       (* arm_ADDS X4 X4 X1 *)
  0x9a1f03eb;       (* arm_ADC X11 XZR XZR *)
  0xeb020282;       (* arm_SUBS X2 X20 X2 *)
  0xfa040184;       (* arm_SBCS X4 X12 X4 *)
  0xfa0b0134;       (* arm_SBCS X20 X9 X11 *)
  0xd3607c4c;       (* arm_LSL X12 X2 32 *)
  0x8b020182;       (* arm_ADD X2 X12 X2 *)
  0xfa1f0209;       (* arm_SBCS X9 X16 XZR *)
  0xd360fc4b;       (* arm_LSR X11 X2 32 *)
  0xfa1f0273;       (* arm_SBCS X19 X19 XZR *)
  0xda1f0021;       (* arm_SBC X1 X1 XZR *)
  0xeb020170;       (* arm_SUBS X16 X11 X2 *)
  0xda1f004c;       (* arm_SBC X12 X2 XZR *)
  0x93d08190;       (* arm_EXTR X16 X12 X16 32 *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0xab02018b;       (* arm_ADDS X11 X12 X2 *)
  0x9a1f03ec;       (* arm_ADC X12 XZR XZR *)
  0xeb100090;       (* arm_SUBS X16 X4 X16 *)
  0x4e083f64;       (* arm_UMOV X4 Q27 0 8 *)
  0xfa0b028b;       (* arm_SBCS X11 X20 X11 *)
  0xfa0c0134;       (* arm_SBCS X20 X9 X12 *)
  0xa9002c10;       (* arm_STP X16 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xfa1f026b;       (* arm_SBCS X11 X19 XZR *)
  0xfa1f0029;       (* arm_SBCS X9 X1 XZR *)
  0xa9012c14;       (* arm_STP X20 X11 X0 (Immediate_Offset (iword (&16))) *)
  0x4e083c21;       (* arm_UMOV X1 Q1 0 8 *)
  0xda1f0054;       (* arm_SBC X20 X2 XZR *)
  0xeb05030c;       (* arm_SUBS X12 X24 X5 *)
  0x4e183f6b;       (* arm_UMOV X11 Q27 1 8 *)
  0xda8c2590;       (* arm_CNEG X16 X12 Condition_CC *)
  0xda9f23e2;       (* arm_CSETM X2 Condition_CC *)
  0xeb0e01f3;       (* arm_SUBS X19 X15 X14 *)
  0x4e183c2c;       (* arm_UMOV X12 Q1 1 8 *)
  0xda822042;       (* arm_CINV X2 X2 Condition_CC *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0xa9025009;       (* arm_STP X9 X20 X0 (Immediate_Offset (iword (&32))) *)
  0x9b137e09;       (* arm_MUL X9 X16 X19 *)
  0xab0400e4;       (* arm_ADDS X4 X7 X4 *)
  0xba0b002b;       (* arm_ADCS X11 X1 X11 *)
  0x9a1f0181;       (* arm_ADC X1 X12 XZR *)
  0xab160094;       (* arm_ADDS X20 X4 X22 *)
  0x9bd37e13;       (* arm_UMULH X19 X16 X19 *)
  0xba040167;       (* arm_ADCS X7 X11 X4 *)
  0xca020130;       (* arm_EOR X16 X9 X2 *)
  0xba0b0029;       (* arm_ADCS X9 X1 X11 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab1600e7;       (* arm_ADDS X7 X7 X22 *)
  0xba040124;       (* arm_ADCS X4 X9 X4 *)
  0xba0b0189;       (* arm_ADCS X9 X12 X11 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xb100045f;       (* arm_CMN X2 (rvalue (word 1)) *)
  0xca020261;       (* arm_EOR X1 X19 X2 *)
  0xba10028b;       (* arm_ADCS X11 X20 X16 *)
  0xba0100f3;       (* arm_ADCS X19 X7 X1 *)
  0xba020081;       (* arm_ADCS X1 X4 X2 *)
  0xba020134;       (* arm_ADCS X20 X9 X2 *)
  0x9a020182;       (* arm_ADC X2 X12 X2 *)
  0xeb0a030c;       (* arm_SUBS X12 X24 X10 *)
  0xda8c2590;       (* arm_CNEG X16 X12 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb0e0229;       (* arm_SUBS X9 X17 X14 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xda892529;       (* arm_CNEG X9 X9 Condition_CC *)
  0xeb030303;       (* arm_SUBS X3 X24 X3 *)
  0xfa1500b5;       (* arm_SBCS X21 X5 X21 *)
  0x9b097e18;       (* arm_MUL X24 X16 X9 *)
  0xfa080144;       (* arm_SBCS X4 X10 X8 *)
  0xda1f03e8;       (* arm_NGC X8 XZR *)
  0xeb0a00aa;       (* arm_SUBS X10 X5 X10 *)
  0xca0c0305;       (* arm_EOR X5 X24 X12 *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xda8a2558;       (* arm_CNEG X24 X10 Condition_CC *)
  0xeb0f022a;       (* arm_SUBS X10 X17 X15 *)
  0xda8720e7;       (* arm_CINV X7 X7 Condition_CC *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0xeb0e01ae;       (* arm_SUBS X14 X13 X14 *)
  0xfa0f02ef;       (* arm_SBCS X15 X23 X15 *)
  0xca0802ad;       (* arm_EOR X13 X21 X8 *)
  0x9b0a7f17;       (* arm_MUL X23 X24 X10 *)
  0xfa1100d1;       (* arm_SBCS X17 X6 X17 *)
  0xca080066;       (* arm_EOR X6 X3 X8 *)
  0xda1f03f5;       (* arm_NGC X21 XZR *)
  0x9bc97e09;       (* arm_UMULH X9 X16 X9 *)
  0xb100051f;       (* arm_CMN X8 (rvalue (word 1)) *)
  0xca0702e3;       (* arm_EOR X3 X23 X7 *)
  0xba1f00d7;       (* arm_ADCS X23 X6 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xca080090;       (* arm_EOR X16 X4 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xca150224;       (* arm_EOR X4 X17 X21 *)
  0x9bca7f11;       (* arm_UMULH X17 X24 X10 *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1501d8;       (* arm_EOR X24 X14 X21 *)
  0xca1501e6;       (* arm_EOR X6 X15 X21 *)
  0xba1f030f;       (* arm_ADCS X15 X24 XZR *)
  0xba1f00ce;       (* arm_ADCS X14 X6 XZR *)
  0x9a1f0086;       (* arm_ADC X6 X4 XZR *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c0124;       (* arm_EOR X4 X9 X12 *)
  0xba050273;       (* arm_ADCS X19 X19 X5 *)
  0x9bcf7ee5;       (* arm_UMULH X5 X23 X15 *)
  0xba040021;       (* arm_ADCS X1 X1 X4 *)
  0xba0c028a;       (* arm_ADCS X10 X20 X12 *)
  0xca070224;       (* arm_EOR X4 X17 X7 *)
  0xa9402414;       (* arm_LDP X20 X9 X0 (Immediate_Offset (iword (&0))) *)
  0x9a0c0042;       (* arm_ADC X2 X2 X12 *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0xba03002c;       (* arm_ADCS X12 X1 X3 *)
  0xa9416011;       (* arm_LDP X17 X24 X0 (Immediate_Offset (iword (&16))) *)
  0x9b067e01;       (* arm_MUL X1 X16 X6 *)
  0xba040143;       (* arm_ADCS X3 X10 X4 *)
  0x9a070042;       (* arm_ADC X2 X2 X7 *)
  0xa9421007;       (* arm_LDP X7 X4 X0 (Immediate_Offset (iword (&32))) *)
  0xab1402d4;       (* arm_ADDS X20 X22 X20 *)
  0x9b0e7daa;       (* arm_MUL X10 X13 X14 *)
  0xba09016b;       (* arm_ADCS X11 X11 X9 *)
  0xca150109;       (* arm_EOR X9 X8 X21 *)
  0xba110275;       (* arm_ADCS X21 X19 X17 *)
  0xa9002c14;       (* arm_STP X20 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xba18018c;       (* arm_ADCS X12 X12 X24 *)
  0x9b0f7ee8;       (* arm_MUL X8 X23 X15 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xa9013015;       (* arm_STP X21 X12 X0 (Immediate_Offset (iword (&16))) *)
  0xba04004c;       (* arm_ADCS X12 X2 X4 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xeb1002f5;       (* arm_SUBS X21 X23 X16 *)
  0x9bc67e02;       (* arm_UMULH X2 X16 X6 *)
  0xa9023003;       (* arm_STP X3 X12 X0 (Immediate_Offset (iword (&32))) *)
  0xda9526a3;       (* arm_CNEG X3 X21 Condition_CC *)
  0xda9f23f8;       (* arm_CSETM X24 Condition_CC *)
  0x9bce7dab;       (* arm_UMULH X11 X13 X14 *)
  0xeb1001b5;       (* arm_SUBS X21 X13 X16 *)
  0xca090107;       (* arm_EOR X7 X8 X9 *)
  0xda9526b1;       (* arm_CNEG X17 X21 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xeb0f00d5;       (* arm_SUBS X21 X6 X15 *)
  0xda9526b6;       (* arm_CNEG X22 X21 Condition_CC *)
  0xda982315;       (* arm_CINV X21 X24 Condition_CC *)
  0xeb0d02f4;       (* arm_SUBS X20 X23 X13 *)
  0x9bd67c6c;       (* arm_UMULH X12 X3 X22 *)
  0xda942697;       (* arm_CNEG X23 X20 Condition_CC *)
  0xda9f23f8;       (* arm_CSETM X24 Condition_CC *)
  0xeb0f01d4;       (* arm_SUBS X20 X14 X15 *)
  0xda982318;       (* arm_CINV X24 X24 Condition_CC *)
  0x9b167c76;       (* arm_MUL X22 X3 X22 *)
  0xda942683;       (* arm_CNEG X3 X20 Condition_CC *)
  0xeb0e00cd;       (* arm_SUBS X13 X6 X14 *)
  0xda8d25b4;       (* arm_CNEG X20 X13 Condition_CC *)
  0xda90220f;       (* arm_CINV X15 X16 Condition_CC *)
  0xab0a00ad;       (* arm_ADDS X13 X5 X10 *)
  0x9b037ee4;       (* arm_MUL X4 X23 X3 *)
  0xba01016b;       (* arm_ADCS X11 X11 X1 *)
  0x9a1f004e;       (* arm_ADC X14 X2 XZR *)
  0xab0801a5;       (* arm_ADDS X5 X13 X8 *)
  0xba0d0170;       (* arm_ADCS X16 X11 X13 *)
  0x9bc37ef7;       (* arm_UMULH X23 X23 X3 *)
  0xba0b01c3;       (* arm_ADCS X3 X14 X11 *)
  0x9a1f01c1;       (* arm_ADC X1 X14 XZR *)
  0xab08020a;       (* arm_ADDS X10 X16 X8 *)
  0xba0d0066;       (* arm_ADCS X6 X3 X13 *)
  0xba0b0028;       (* arm_ADCS X8 X1 X11 *)
  0x9bd47e2d;       (* arm_UMULH X13 X17 X20 *)
  0xca180081;       (* arm_EOR X1 X4 X24 *)
  0x9a1f01c4;       (* arm_ADC X4 X14 XZR *)
  0xb100071f;       (* arm_CMN X24 (rvalue (word 1)) *)
  0xba0100a1;       (* arm_ADCS X1 X5 X1 *)
  0xca1802f0;       (* arm_EOR X16 X23 X24 *)
  0xca09002b;       (* arm_EOR X11 X1 X9 *)
  0xba100157;       (* arm_ADCS X23 X10 X16 *)
  0xca1502c2;       (* arm_EOR X2 X22 X21 *)
  0xba1800c3;       (* arm_ADCS X3 X6 X24 *)
  0x9b147e2e;       (* arm_MUL X14 X17 X20 *)
  0xca0f01b1;       (* arm_EOR X17 X13 X15 *)
  0xba18010d;       (* arm_ADCS X13 X8 X24 *)
  0x9a180088;       (* arm_ADC X8 X4 X24 *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xba0202e6;       (* arm_ADCS X6 X23 X2 *)
  0x92800030;       (* arm_MOVN X16 (word 1) 0 *)
  0xca150194;       (* arm_EOR X20 X12 X21 *)
  0xba140074;       (* arm_ADCS X20 X3 X20 *)
  0xca0f01d7;       (* arm_EOR X23 X14 X15 *)
  0xba1501a2;       (* arm_ADCS X2 X13 X21 *)
  0x9a150108;       (* arm_ADC X8 X8 X21 *)
  0xb10005ff;       (* arm_CMN X15 (rvalue (word 1)) *)
  0xa9401005;       (* arm_LDP X5 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9413015;       (* arm_LDP X21 X12 X0 (Immediate_Offset (iword (&16))) *)
  0xba170296;       (* arm_ADCS X22 X20 X23 *)
  0xca0902d7;       (* arm_EOR X23 X22 X9 *)
  0xba110051;       (* arm_ADCS X17 X2 X17 *)
  0x9a0f0116;       (* arm_ADC X22 X8 X15 *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xba0500ef;       (* arm_ADCS X15 X7 X5 *)
  0xa942380a;       (* arm_LDP X10 X14 X0 (Immediate_Offset (iword (&32))) *)
  0xca0900c1;       (* arm_EOR X1 X6 X9 *)
  0xd3607de2;       (* arm_LSL X2 X15 32 *)
  0xba040168;       (* arm_ADCS X8 X11 X4 *)
  0xba15002d;       (* arm_ADCS X13 X1 X21 *)
  0xca0902c1;       (* arm_EOR X1 X22 X9 *)
  0xba0c02f8;       (* arm_ADCS X24 X23 X12 *)
  0xca09022b;       (* arm_EOR X11 X17 X9 *)
  0xba0a0177;       (* arm_ADCS X23 X11 X10 *)
  0xba0e0027;       (* arm_ADCS X7 X1 X14 *)
  0xba130131;       (* arm_ADCS X17 X9 X19 *)
  0xba1f0134;       (* arm_ADCS X20 X9 XZR *)
  0x8b0f0041;       (* arm_ADD X1 X2 X15 *)
  0xd360fc23;       (* arm_LSR X3 X1 32 *)
  0xba1f012b;       (* arm_ADCS X11 X9 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xeb010063;       (* arm_SUBS X3 X3 X1 *)
  0xda1f0026;       (* arm_SBC X6 X1 XZR *)
  0xab050318;       (* arm_ADDS X24 X24 X5 *)
  0xba0402e4;       (* arm_ADCS X4 X23 X4 *)
  0x93c380c3;       (* arm_EXTR X3 X6 X3 32 *)
  0xd360fcc6;       (* arm_LSR X6 X6 32 *)
  0xba1500f5;       (* arm_ADCS X21 X7 X21 *)
  0xba0c022f;       (* arm_ADCS X15 X17 X12 *)
  0xba0a0287;       (* arm_ADCS X7 X20 X10 *)
  0xba0e0174;       (* arm_ADCS X20 X11 X14 *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0x9a130136;       (* arm_ADC X22 X9 X19 *)
  0xab0100cc;       (* arm_ADDS X12 X6 X1 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xeb030103;       (* arm_SUBS X3 X8 X3 *)
  0xfa0c01ac;       (* arm_SBCS X12 X13 X12 *)
  0xd3607c69;       (* arm_LSL X9 X3 32 *)
  0x8b030123;       (* arm_ADD X3 X9 X3 *)
  0xfa0a030a;       (* arm_SBCS X10 X24 X10 *)
  0xfa1f0098;       (* arm_SBCS X24 X4 XZR *)
  0xd360fc69;       (* arm_LSR X9 X3 32 *)
  0xfa1f02b5;       (* arm_SBCS X21 X21 XZR *)
  0xda1f0021;       (* arm_SBC X1 X1 XZR *)
  0xeb030129;       (* arm_SUBS X9 X9 X3 *)
  0xda1f006d;       (* arm_SBC X13 X3 XZR *)
  0x93c981a9;       (* arm_EXTR X9 X13 X9 32 *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0xab0301ad;       (* arm_ADDS X13 X13 X3 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xeb09018c;       (* arm_SUBS X12 X12 X9 *)
  0xfa0d0151;       (* arm_SBCS X17 X10 X13 *)
  0xd3607d82;       (* arm_LSL X2 X12 32 *)
  0xfa06030a;       (* arm_SBCS X10 X24 X6 *)
  0x8b0c0049;       (* arm_ADD X9 X2 X12 *)
  0xfa1f02a6;       (* arm_SBCS X6 X21 XZR *)
  0xd360fd25;       (* arm_LSR X5 X9 32 *)
  0xfa1f0035;       (* arm_SBCS X21 X1 XZR *)
  0xda1f006d;       (* arm_SBC X13 X3 XZR *)
  0xeb0900a8;       (* arm_SUBS X8 X5 X9 *)
  0xda1f0133;       (* arm_SBC X19 X9 XZR *)
  0xd360fe6c;       (* arm_LSR X12 X19 32 *)
  0x93c88263;       (* arm_EXTR X3 X19 X8 32 *)
  0xab090188;       (* arm_ADDS X8 X12 X9 *)
  0x9a1f03e1;       (* arm_ADC X1 XZR XZR *)
  0xeb030222;       (* arm_SUBS X2 X17 X3 *)
  0xfa08014c;       (* arm_SBCS X12 X10 X8 *)
  0xfa0100c5;       (* arm_SBCS X5 X6 X1 *)
  0xfa1f02a3;       (* arm_SBCS X3 X21 XZR *)
  0xfa1f01b3;       (* arm_SBCS X19 X13 XZR *)
  0xda1f0138;       (* arm_SBC X24 X9 XZR *)
  0xab0301f7;       (* arm_ADDS X23 X15 X3 *)
  0xba1300e8;       (* arm_ADCS X8 X7 X19 *)
  0xba18028b;       (* arm_ADCS X11 X20 X24 *)
  0x9a1f02c9;       (* arm_ADC X9 X22 XZR *)
  0x91000538;       (* arm_ADD X24 X9 (rvalue (word 1)) *)
  0xd3607f07;       (* arm_LSL X7 X24 32 *)
  0xeb070315;       (* arm_SUBS X21 X24 X7 *)
  0xda1f00ea;       (* arm_SBC X10 X7 XZR *)
  0xab150046;       (* arm_ADDS X6 X2 X21 *)
  0xba0a0187;       (* arm_ADCS X7 X12 X10 *)
  0xba1800b8;       (* arm_ADCS X24 X5 X24 *)
  0xba1f02ed;       (* arm_ADCS X13 X23 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f016f;       (* arm_ADCS X15 X11 XZR *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0x8a17020b;       (* arm_AND X11 X16 X23 *)
  0x8a1701d4;       (* arm_AND X20 X14 X23 *)
  0xab1400d6;       (* arm_ADDS X22 X6 X20 *)
  0xca170283;       (* arm_EOR X3 X20 X23 *)
  0xba0300e5;       (* arm_ADCS X5 X7 X3 *)
  0xba0b030e;       (* arm_ADCS X14 X24 X11 *)
  0xa9001416;       (* arm_STP X22 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xba1701a5;       (* arm_ADCS X5 X13 X23 *)
  0xba170115;       (* arm_ADCS X21 X8 X23 *)
  0xa901140e;       (* arm_STP X14 X5 X0 (Immediate_Offset (iword (&16))) *)
  0x9a1701ec;       (* arm_ADC X12 X15 X23 *)
  0xa9023015;       (* arm_STP X21 X12 X0 (Immediate_Offset (iword (&32))) *)
  0xa94063f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&0))) *)
  0xa9415bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa94253f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&32))) *)
  0x9100c3ff;       (* arm_ADD SP SP (rvalue (word 48)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x3dc00021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 0)) *)
  0xa9400829;       (* arm_LDP X9 X2 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0xa9411824;       (* arm_LDP X4 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x4ea00835;       (* arm_REV64_VEC Q21 Q1 32 *)
  0x4e81583c;       (* arm_UZP2 Q28 Q1 Q1 32 *)
  0x9bc27d27;       (* arm_UMULH X7 X9 X2 *)
  0x0ea12831;       (* arm_XTN Q17 Q1 32 *)
  0x4ea09ebb;       (* arm_MUL_VEC Q27 Q21 Q0 32 128 *)
  0x3dc00834;       (* arm_LDR Q20 X1 (Immediate_Offset (word 32)) *)
  0x0ea1281e;       (* arm_XTN Q30 Q0 32 *)
  0x3dc00821;       (* arm_LDR Q1 X1 (Immediate_Offset (word 32)) *)
  0x4e80581f;       (* arm_UZP2 Q31 Q0 Q0 32 *)
  0xa9422825;       (* arm_LDP X5 X10 X1 (Immediate_Offset (iword (&32))) *)
  0x9bc47d28;       (* arm_UMULH X8 X9 X4 *)
  0x6ea02b63;       (* arm_UADDLP Q3 Q27 32 *)
  0x2eb1c3d0;       (* arm_UMULL_VEC Q16 Q30 Q17 32 *)
  0x9b047d30;       (* arm_MUL X16 X9 X4 *)
  0x2ebcc3db;       (* arm_UMULL_VEC Q27 Q30 Q28 32 *)
  0x0f208680;       (* arm_SHRN Q0 Q20 32 32 *)
  0x0ea12a87;       (* arm_XTN Q7 Q20 32 *)
  0x4f605474;       (* arm_SHL_VEC Q20 Q3 32 64 128 *)
  0x2ebcc3e3;       (* arm_UMULL_VEC Q3 Q31 Q28 32 *)
  0x9b047c43;       (* arm_MUL X3 X2 X4 *)
  0x2eb183d4;       (* arm_UMLAL_VEC Q20 Q30 Q17 32 *)
  0x2ea0c0f6;       (* arm_UMULL_VEC Q22 Q7 Q0 32 *)
  0x6f60161b;       (* arm_USRA_VEC Q27 Q16 32 64 128 *)
  0x9bc47c4b;       (* arm_UMULH X11 X2 X4 *)
  0x6f00e5f5;       (* arm_MOVI Q21 (word 4294967295) *)
  0x4e81583c;       (* arm_UZP2 Q28 Q1 Q1 32 *)
  0xab07020f;       (* arm_ADDS X15 X16 X7 *)
  0x4e351f65;       (* arm_AND_VEC Q5 Q27 Q21 128 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0x6f601763;       (* arm_USRA_VEC Q3 Q27 32 64 128 *)
  0x4e080cdd;       (* arm_DUP_GEN Q29 X6 *)
  0xba1f0170;       (* arm_ADCS X16 X11 XZR *)
  0x4e083e8e;       (* arm_UMOV X14 Q20 0 8 *)
  0x2eb183e5;       (* arm_UMLAL_VEC Q5 Q31 Q17 32 *)
  0x9b027d28;       (* arm_MUL X8 X9 X2 *)
  0x4e183e87;       (* arm_UMOV X7 Q20 1 8 *)
  0x4f6156d3;       (* arm_SHL_VEC Q19 Q22 33 64 128 *)
  0x0ea12bb9;       (* arm_XTN Q25 Q29 32 *)
  0x4ea0083f;       (* arm_REV64_VEC Q31 Q1 32 *)
  0xd3607dcd;       (* arm_LSL X13 X14 32 *)
  0x4e9d5ba6;       (* arm_UZP2 Q6 Q29 Q29 32 *)
  0x2ea780f3;       (* arm_UMLAL_VEC Q19 Q7 Q7 32 *)
  0x6f6014a3;       (* arm_USRA_VEC Q3 Q5 32 64 128 *)
  0xab080101;       (* arm_ADDS X1 X8 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0x8b0e01ac;       (* arm_ADD X12 X13 X14 *)
  0x4ebd9ff1;       (* arm_MUL_VEC Q17 Q31 Q29 32 128 *)
  0x0ea12824;       (* arm_XTN Q4 Q1 32 *)
  0xba0f01ee;       (* arm_ADCS X14 X15 X15 *)
  0xd360fd8d;       (* arm_LSR X13 X12 32 *)
  0xba03006f;       (* arm_ADCS X15 X3 X3 *)
  0x2ebcc33f;       (* arm_UMULL_VEC Q31 Q25 Q28 32 *)
  0xba10020b;       (* arm_ADCS X11 X16 X16 *)
  0x2ea4c335;       (* arm_UMULL_VEC Q21 Q25 Q4 32 *)
  0x4e083c71;       (* arm_UMOV X17 Q3 0 8 *)
  0x2ebcc0d2;       (* arm_UMULL_VEC Q18 Q6 Q28 32 *)
  0x9a1f0110;       (* arm_ADC X16 X8 XZR *)
  0x6ea02a30;       (* arm_UADDLP Q16 Q17 32 *)
  0x6f00e5e1;       (* arm_MOVI Q1 (word 4294967295) *)
  0xeb0c01ad;       (* arm_SUBS X13 X13 X12 *)
  0x6f6016bf;       (* arm_USRA_VEC Q31 Q21 32 64 128 *)
  0xda1f0188;       (* arm_SBC X8 X12 XZR *)
  0xab010231;       (* arm_ADDS X17 X17 X1 *)
  0x9b047c81;       (* arm_MUL X1 X4 X4 *)
  0x4f60561c;       (* arm_SHL_VEC Q28 Q16 32 64 128 *)
  0x4e183c63;       (* arm_UMOV X3 Q3 1 8 *)
  0xba0e00ee;       (* arm_ADCS X14 X7 X14 *)
  0x93cd8107;       (* arm_EXTR X7 X8 X13 32 *)
  0xba0f006d;       (* arm_ADCS X13 X3 X15 *)
  0x4e211fe3;       (* arm_AND_VEC Q3 Q31 Q1 128 *)
  0xba0b002b;       (* arm_ADCS X11 X1 X11 *)
  0xd360fd01;       (* arm_LSR X1 X8 32 *)
  0x2ea480c3;       (* arm_UMLAL_VEC Q3 Q6 Q4 32 *)
  0x6f6017f2;       (* arm_USRA_VEC Q18 Q31 32 64 128 *)
  0x9a1f0203;       (* arm_ADC X3 X16 XZR *)
  0xab0c0021;       (* arm_ADDS X1 X1 X12 *)
  0x2ea4833c;       (* arm_UMLAL_VEC Q28 Q25 Q4 32 *)
  0x9a1f03f0;       (* arm_ADC X16 XZR XZR *)
  0xeb07022f;       (* arm_SUBS X15 X17 X7 *)
  0xfa0101c7;       (* arm_SBCS X7 X14 X1 *)
  0xd3607de1;       (* arm_LSL X1 X15 32 *)
  0xfa1001b0;       (* arm_SBCS X16 X13 X16 *)
  0x8b0f0028;       (* arm_ADD X8 X1 X15 *)
  0x6f601472;       (* arm_USRA_VEC Q18 Q3 32 64 128 *)
  0xfa1f016e;       (* arm_SBCS X14 X11 XZR *)
  0xd360fd01;       (* arm_LSR X1 X8 32 *)
  0xfa1f0071;       (* arm_SBCS X17 X3 XZR *)
  0xda1f018b;       (* arm_SBC X11 X12 XZR *)
  0xeb08002d;       (* arm_SUBS X13 X1 X8 *)
  0x9bca7c8c;       (* arm_UMULH X12 X4 X10 *)
  0xda1f0101;       (* arm_SBC X1 X8 XZR *)
  0x93cd802d;       (* arm_EXTR X13 X1 X13 32 *)
  0xd360fc21;       (* arm_LSR X1 X1 32 *)
  0xab08002f;       (* arm_ADDS X15 X1 X8 *)
  0x9a1f03e1;       (* arm_ADC X1 XZR XZR *)
  0xeb0d00e7;       (* arm_SUBS X7 X7 X13 *)
  0xfa0f020d;       (* arm_SBCS X13 X16 X15 *)
  0xd3607ce3;       (* arm_LSL X3 X7 32 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0xfa0101cf;       (* arm_SBCS X15 X14 X1 *)
  0x8b070067;       (* arm_ADD X7 X3 X7 *)
  0xfa1f0223;       (* arm_SBCS X3 X17 XZR *)
  0xd360fce1;       (* arm_LSR X1 X7 32 *)
  0xfa1f016e;       (* arm_SBCS X14 X11 XZR *)
  0xda1f010b;       (* arm_SBC X11 X8 XZR *)
  0xeb070028;       (* arm_SUBS X8 X1 X7 *)
  0xda1f00e1;       (* arm_SBC X1 X7 XZR *)
  0x93c88028;       (* arm_EXTR X8 X1 X8 32 *)
  0xd360fc21;       (* arm_LSR X1 X1 32 *)
  0xab070021;       (* arm_ADDS X1 X1 X7 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0x9bc67d28;       (* arm_UMULH X8 X9 X6 *)
  0xfa0101e1;       (* arm_SBCS X1 X15 X1 *)
  0xfa11006f;       (* arm_SBCS X15 X3 X17 *)
  0xfa1f01c3;       (* arm_SBCS X3 X14 XZR *)
  0x9b057c51;       (* arm_MUL X17 X2 X5 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xa900040d;       (* arm_STP X13 X1 X0 (Immediate_Offset (iword (&0))) *)
  0xda1f00ee;       (* arm_SBC X14 X7 XZR *)
  0x9b0a7c87;       (* arm_MUL X7 X4 X10 *)
  0xeb020121;       (* arm_SUBS X1 X9 X2 *)
  0xa9010c0f;       (* arm_STP X15 X3 X0 (Immediate_Offset (iword (&16))) *)
  0xda9f23ef;       (* arm_CSETM X15 Condition_CC *)
  0xda812421;       (* arm_CNEG X1 X1 Condition_CC *)
  0xa902380b;       (* arm_STP X11 X14 X0 (Immediate_Offset (iword (&32))) *)
  0x9b067d2e;       (* arm_MUL X14 X9 X6 *)
  0xab110111;       (* arm_ADDS X17 X8 X17 *)
  0xba070207;       (* arm_ADCS X7 X16 X7 *)
  0x9a1f018d;       (* arm_ADC X13 X12 XZR *)
  0xeb0600ac;       (* arm_SUBS X12 X5 X6 *)
  0xda8c2583;       (* arm_CNEG X3 X12 Condition_CC *)
  0xda8f21f0;       (* arm_CINV X16 X15 Condition_CC *)
  0x9b037c28;       (* arm_MUL X8 X1 X3 *)
  0x9bc37c21;       (* arm_UMULH X1 X1 X3 *)
  0xca10010c;       (* arm_EOR X12 X8 X16 *)
  0xab0e022b;       (* arm_ADDS X11 X17 X14 *)
  0xba1100e3;       (* arm_ADCS X3 X7 X17 *)
  0xba0701af;       (* arm_ADCS X15 X13 X7 *)
  0x9a1f01a8;       (* arm_ADC X8 X13 XZR *)
  0xab0e0063;       (* arm_ADDS X3 X3 X14 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0xba070111;       (* arm_ADCS X17 X8 X7 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xda9f23e8;       (* arm_CSETM X8 Condition_CC *)
  0xda892529;       (* arm_CNEG X9 X9 Condition_CC *)
  0xeb040044;       (* arm_SUBS X4 X2 X4 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xeb060142;       (* arm_SUBS X2 X10 X6 *)
  0xda882108;       (* arm_CINV X8 X8 Condition_CC *)
  0xda822442;       (* arm_CNEG X2 X2 Condition_CC *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xba0c016b;       (* arm_ADCS X11 X11 X12 *)
  0x9b027d2c;       (* arm_MUL X12 X9 X2 *)
  0xba010063;       (* arm_ADCS X3 X3 X1 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc27d29;       (* arm_UMULH X9 X9 X2 *)
  0xba100231;       (* arm_ADCS X17 X17 X16 *)
  0x9a1001ad;       (* arm_ADC X13 X13 X16 *)
  0xeb050141;       (* arm_SUBS X1 X10 X5 *)
  0xda8720e2;       (* arm_CINV X2 X7 Condition_CC *)
  0xda812421;       (* arm_CNEG X1 X1 Condition_CC *)
  0xca080129;       (* arm_EOR X9 X9 X8 *)
  0xb100051f;       (* arm_CMN X8 (rvalue (word 1)) *)
  0xca080187;       (* arm_EOR X7 X12 X8 *)
  0x9b017c8c;       (* arm_MUL X12 X4 X1 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xba0901e7;       (* arm_ADCS X7 X15 X9 *)
  0xba08022f;       (* arm_ADCS X15 X17 X8 *)
  0xa9414409;       (* arm_LDP X9 X17 X0 (Immediate_Offset (iword (&16))) *)
  0x9bc17c84;       (* arm_UMULH X4 X4 X1 *)
  0x9a0801a8;       (* arm_ADC X8 X13 X8 *)
  0xb100045f;       (* arm_CMN X2 (rvalue (word 1)) *)
  0xca020181;       (* arm_EOR X1 X12 X2 *)
  0xba0100e1;       (* arm_ADCS X1 X7 X1 *)
  0xa9404007;       (* arm_LDP X7 X16 X0 (Immediate_Offset (iword (&0))) *)
  0xca02008c;       (* arm_EOR X12 X4 X2 *)
  0xba0c01e4;       (* arm_ADCS X4 X15 X12 *)
  0xa942300f;       (* arm_LDP X15 X12 X0 (Immediate_Offset (iword (&32))) *)
  0x9a020108;       (* arm_ADC X8 X8 X2 *)
  0xab0e01cd;       (* arm_ADDS X13 X14 X14 *)
  0x9bca7cae;       (* arm_UMULH X14 X5 X10 *)
  0xba0b0162;       (* arm_ADCS X2 X11 X11 *)
  0xba030063;       (* arm_ADCS X3 X3 X3 *)
  0xba010021;       (* arm_ADCS X1 X1 X1 *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xba08010b;       (* arm_ADCS X11 X8 X8 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xab0701ad;       (* arm_ADDS X13 X13 X7 *)
  0xba100042;       (* arm_ADCS X2 X2 X16 *)
  0x9b0a7cb0;       (* arm_MUL X16 X5 X10 *)
  0xba090063;       (* arm_ADCS X3 X3 X9 *)
  0xba110021;       (* arm_ADCS X1 X1 X17 *)
  0x9bc57ca5;       (* arm_UMULH X5 X5 X5 *)
  0xd3607da9;       (* arm_LSL X9 X13 32 *)
  0x8b0d0129;       (* arm_ADD X9 X9 X13 *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0x4e183f8d;       (* arm_UMOV X13 Q28 1 8 *)
  0xba0c016f;       (* arm_ADCS X15 X11 X12 *)
  0xd360fd27;       (* arm_LSR X7 X9 32 *)
  0x9a1f010b;       (* arm_ADC X11 X8 XZR *)
  0xeb0900e7;       (* arm_SUBS X7 X7 X9 *)
  0x9bca7d4a;       (* arm_UMULH X10 X10 X10 *)
  0xda1f0131;       (* arm_SBC X17 X9 XZR *)
  0x93c78227;       (* arm_EXTR X7 X17 X7 32 *)
  0xd360fe31;       (* arm_LSR X17 X17 32 *)
  0xab090231;       (* arm_ADDS X17 X17 X9 *)
  0x9a1f03ec;       (* arm_ADC X12 XZR XZR *)
  0xeb070048;       (* arm_SUBS X8 X2 X7 *)
  0xfa110071;       (* arm_SBCS X17 X3 X17 *)
  0xd3607d07;       (* arm_LSL X7 X8 32 *)
  0xfa0c0022;       (* arm_SBCS X2 X1 X12 *)
  0x8b0800e3;       (* arm_ADD X3 X7 X8 *)
  0xfa1f008c;       (* arm_SBCS X12 X4 XZR *)
  0xd360fc61;       (* arm_LSR X1 X3 32 *)
  0xfa1f01e7;       (* arm_SBCS X7 X15 XZR *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0xeb030021;       (* arm_SUBS X1 X1 X3 *)
  0xda1f0064;       (* arm_SBC X4 X3 XZR *)
  0xd360fc89;       (* arm_LSR X9 X4 32 *)
  0x93c18088;       (* arm_EXTR X8 X4 X1 32 *)
  0xab030129;       (* arm_ADDS X9 X9 X3 *)
  0x9a1f03e4;       (* arm_ADC X4 XZR XZR *)
  0xeb080221;       (* arm_SUBS X1 X17 X8 *)
  0xd3607c31;       (* arm_LSL X17 X1 32 *)
  0xfa090048;       (* arm_SBCS X8 X2 X9 *)
  0xfa040189;       (* arm_SBCS X9 X12 X4 *)
  0x8b010231;       (* arm_ADD X17 X17 X1 *)
  0x4e183e41;       (* arm_UMOV X1 Q18 1 8 *)
  0xd360fe22;       (* arm_LSR X2 X17 32 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0x4e083e4c;       (* arm_UMOV X12 Q18 0 8 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0063;       (* arm_SBC X3 X3 XZR *)
  0xeb110044;       (* arm_SUBS X4 X2 X17 *)
  0xda1f0222;       (* arm_SBC X2 X17 XZR *)
  0xab0c01ac;       (* arm_ADDS X12 X13 X12 *)
  0xba010210;       (* arm_ADCS X16 X16 X1 *)
  0xd360fc4d;       (* arm_LSR X13 X2 32 *)
  0x93c48041;       (* arm_EXTR X1 X2 X4 32 *)
  0x9a1f01c2;       (* arm_ADC X2 X14 XZR *)
  0xab1101a4;       (* arm_ADDS X4 X13 X17 *)
  0x9b067ccd;       (* arm_MUL X13 X6 X6 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb010101;       (* arm_SUBS X1 X8 X1 *)
  0xfa040124;       (* arm_SBCS X4 X9 X4 *)
  0x4e083f89;       (* arm_UMOV X9 Q28 0 8 *)
  0xfa0e00e7;       (* arm_SBCS X7 X7 X14 *)
  0xfa1f01e8;       (* arm_SBCS X8 X15 XZR *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xda1f022e;       (* arm_SBC X14 X17 XZR *)
  0xab090131;       (* arm_ADDS X17 X9 X9 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0x4e083e6f;       (* arm_UMOV X15 Q19 0 8 *)
  0xba100209;       (* arm_ADCS X9 X16 X16 *)
  0x9bc67cc6;       (* arm_UMULH X6 X6 X6 *)
  0xba020050;       (* arm_ADCS X16 X2 X2 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xba1f03e8;       (* arm_ADCS X8 XZR XZR *)
  0xab0d002d;       (* arm_ADDS X13 X1 X13 *)
  0x4e183e61;       (* arm_UMOV X1 Q19 1 8 *)
  0xba060086;       (* arm_ADCS X6 X4 X6 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0xba0f00ef;       (* arm_ADCS X15 X7 X15 *)
  0xba050167;       (* arm_ADCS X7 X11 X5 *)
  0xba010061;       (* arm_ADCS X1 X3 X1 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9a1f010b;       (* arm_ADC X11 X8 XZR *)
  0xab1100c6;       (* arm_ADDS X6 X6 X17 *)
  0xba0c01e8;       (* arm_ADCS X8 X15 X12 *)
  0xba0900e3;       (* arm_ADCS X3 X7 X9 *)
  0xba10002f;       (* arm_ADCS X15 X1 X16 *)
  0xb26083f0;       (* arm_MOV X16 (rvalue (word 18446744069414584321)) *)
  0xba0201ce;       (* arm_ADCS X14 X14 X2 *)
  0xd2800022;       (* arm_MOV X2 (rvalue (word 1)) *)
  0x9a1f0171;       (* arm_ADC X17 X11 XZR *)
  0xab1001bf;       (* arm_CMN X13 X16 *)
  0xba0400df;       (* arm_ADCS XZR X6 X4 *)
  0xba02011f;       (* arm_ADCS XZR X8 X2 *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f01df;       (* arm_ADCS XZR X14 XZR *)
  0x9a1f0221;       (* arm_ADC X1 X17 XZR *)
  0xcb0103e9;       (* arm_NEG X9 X1 *)
  0x8a090201;       (* arm_AND X1 X16 X9 *)
  0xab0101ab;       (* arm_ADDS X11 X13 X1 *)
  0x8a09008d;       (* arm_AND X13 X4 X9 *)
  0xba0d00c5;       (* arm_ADCS X5 X6 X13 *)
  0x8a090041;       (* arm_AND X1 X2 X9 *)
  0xba010107;       (* arm_ADCS X7 X8 X1 *)
  0xa900140b;       (* arm_STP X11 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xba1f006b;       (* arm_ADCS X11 X3 XZR *)
  0xba1f01e2;       (* arm_ADCS X2 X15 XZR *)
  0xa9012c07;       (* arm_STP X7 X11 X0 (Immediate_Offset (iword (&16))) *)
  0x9a1f01d1;       (* arm_ADC X17 X14 XZR *)
  0xa9024402;       (* arm_STP X2 X17 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&16))) *)
  0xa9410c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9422829;       (* arm_LDP X9 X10 X1 (Immediate_Offset (iword (&32))) *)
  0xa9420c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9a03014a;       (* arm_ADC X10 X10 X3 *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&16))) *)
  0xa9410c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422829;       (* arm_LDP X9 X10 X1 (Immediate_Offset (iword (&32))) *)
  0xa9420c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0xeb0400bf;       (* arm_CMP X5 X4 *)
  0xb2607fe4;       (* arm_MOV X4 (rvalue (word 18446744069414584320)) *)
  0xfa0400df;       (* arm_SBCS XZR X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0xfa0400ff;       (* arm_SBCS XZR X7 X4 *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0xba1f015f;       (* arm_ADCS XZR X10 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xfa0400c6;       (* arm_SBCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xda03014a;       (* arm_SBC X10 X10 X3 *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd10683ff;       (* arm_SUB SP SP (rvalue (word 416)) *)
  0xa91553f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&336))) *)
  0xa9165bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&352))) *)
  0xa91763f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&368))) *)
  0xa9186bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&384))) *)
  0xa9197ffe;       (* arm_STP X30 XZR SP (Immediate_Offset (iword (&400))) *)
  0xaa0003f9;       (* arm_MOV X25 X0 *)
  0xaa0103fa;       (* arm_MOV X26 X1 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x91018341;       (* arm_ADD X1 X26 (rvalue (word 96)) *)
  0x97fffe80;       (* arm_BL (word 268433920) *)
  0x9100c3e0;       (* arm_ADD X0 SP (rvalue (word 48)) *)
  0x9100c341;       (* arm_ADD X1 X26 (rvalue (word 48)) *)
  0x97fffe7d;       (* arm_BL (word 268433908) *)
  0xa9401b45;       (* arm_LDP X5 X6 X26 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412347;       (* arm_LDP X7 X8 X26 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422b49;       (* arm_LDP X9 X10 X26 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xda9f33e3;       (* arm_CSETM X3 Condition_CS *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xfa0400c6;       (* arm_SBCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xda03014a;       (* arm_SBC X10 X10 X3 *)
  0xa90f1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa91023e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xa9112be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0x910303e0;       (* arm_ADD X0 SP (rvalue (word 192)) *)
  0x91000341;       (* arm_ADD X1 X26 (rvalue (word 0)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x97ffff91;       (* arm_BL (word 268435012) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x9103c3e1;       (* arm_ADD X1 SP (rvalue (word 240)) *)
  0x910303e2;       (* arm_ADD X2 SP (rvalue (word 192)) *)
  0x97fffcbb;       (* arm_BL (word 268432108) *)
  0x9103c3e0;       (* arm_ADD X0 SP (rvalue (word 240)) *)
  0x9100c341;       (* arm_ADD X1 X26 (rvalue (word 48)) *)
  0x91018342;       (* arm_ADD X2 X26 (rvalue (word 96)) *)
  0x97ffffa5;       (* arm_BL (word 268435092) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x97fffe53;       (* arm_BL (word 268433740) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x91000341;       (* arm_ADD X1 X26 (rvalue (word 0)) *)
  0x9100c3e2;       (* arm_ADD X2 SP (rvalue (word 48)) *)
  0x97fffcb0;       (* arm_BL (word 268432064) *)
  0x910303e0;       (* arm_ADD X0 SP (rvalue (word 192)) *)
  0x9103c3e1;       (* arm_ADD X1 SP (rvalue (word 240)) *)
  0x97fffe4c;       (* arm_BL (word 268433712) *)
  0xa95207e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0xeb0000c6;       (* arm_SUBS X6 X6 X0 *)
  0xb2607fe7;       (* arm_MOV X7 (rvalue (word 18446744069414584320)) *)
  0xfa0100e7;       (* arm_SBCS X7 X7 X1 *)
  0xa95307e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&304))) *)
  0x92800028;       (* arm_MOVN X8 (word 1) 0 *)
  0xfa000108;       (* arm_SBCS X8 X8 X0 *)
  0x9280000d;       (* arm_MOVN X13 (word 0) 0 *)
  0xfa0101a9;       (* arm_SBCS X9 X13 X1 *)
  0xa95407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&320))) *)
  0xfa0001aa;       (* arm_SBCS X10 X13 X0 *)
  0xda0101ab;       (* arm_SBC X11 X13 X1 *)
  0xd280012c;       (* arm_MOV X12 (rvalue (word 9)) *)
  0x9b067d80;       (* arm_MUL X0 X12 X6 *)
  0x9b077d81;       (* arm_MUL X1 X12 X7 *)
  0x9b087d82;       (* arm_MUL X2 X12 X8 *)
  0x9b097d83;       (* arm_MUL X3 X12 X9 *)
  0x9b0a7d84;       (* arm_MUL X4 X12 X10 *)
  0x9b0b7d85;       (* arm_MUL X5 X12 X11 *)
  0x9bc67d86;       (* arm_UMULH X6 X12 X6 *)
  0x9bc77d87;       (* arm_UMULH X7 X12 X7 *)
  0x9bc87d88;       (* arm_UMULH X8 X12 X8 *)
  0x9bc97d89;       (* arm_UMULH X9 X12 X9 *)
  0x9bca7d8a;       (* arm_UMULH X10 X12 X10 *)
  0x9bcb7d8c;       (* arm_UMULH X12 X12 X11 *)
  0xab060021;       (* arm_ADDS X1 X1 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0x9a060186;       (* arm_ADC X6 X12 X6 *)
  0xa94927e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&144))) *)
  0xa94a2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&160))) *)
  0xa94b37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&176))) *)
  0xd280018e;       (* arm_MOV X14 (rvalue (word 12)) *)
  0x9b087dcf;       (* arm_MUL X15 X14 X8 *)
  0x9bc87dc8;       (* arm_UMULH X8 X14 X8 *)
  0xab0f0000;       (* arm_ADDS X0 X0 X15 *)
  0x9b097dcf;       (* arm_MUL X15 X14 X9 *)
  0x9bc97dc9;       (* arm_UMULH X9 X14 X9 *)
  0xba0f0021;       (* arm_ADCS X1 X1 X15 *)
  0x9b0a7dcf;       (* arm_MUL X15 X14 X10 *)
  0x9bca7dca;       (* arm_UMULH X10 X14 X10 *)
  0xba0f0042;       (* arm_ADCS X2 X2 X15 *)
  0x9b0b7dcf;       (* arm_MUL X15 X14 X11 *)
  0x9bcb7dcb;       (* arm_UMULH X11 X14 X11 *)
  0xba0f0063;       (* arm_ADCS X3 X3 X15 *)
  0x9b0c7dcf;       (* arm_MUL X15 X14 X12 *)
  0x9bcc7dcc;       (* arm_UMULH X12 X14 X12 *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0x9b0d7dcf;       (* arm_MUL X15 X14 X13 *)
  0x9bcd7dcd;       (* arm_UMULH X13 X14 X13 *)
  0xba0f00a5;       (* arm_ADCS X5 X5 X15 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab080021;       (* arm_ADDS X1 X1 X8 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0xba0c00a5;       (* arm_ADCS X5 X5 X12 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0xd3607cc7;       (* arm_LSL X7 X6 32 *)
  0xeb0700c8;       (* arm_SUBS X8 X6 X7 *)
  0xda1f00e7;       (* arm_SBC X7 X7 XZR *)
  0xab080000;       (* arm_ADDS X0 X0 X8 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xda9f23e6;       (* arm_CSETM X6 Condition_CC *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0xca0600e7;       (* arm_EOR X7 X7 X6 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0x92800027;       (* arm_MOVN X7 (word 1) 0 *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0x9a0600a5;       (* arm_ADC X5 X5 X6 *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa9130fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&304))) *)
  0xa91417e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&320))) *)
  0x9103c3e0;       (* arm_ADD X0 SP (rvalue (word 240)) *)
  0x910303e1;       (* arm_ADD X1 SP (rvalue (word 192)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x97ffff25;       (* arm_BL (word 268434580) *)
  0x910303e0;       (* arm_ADD X0 SP (rvalue (word 192)) *)
  0x9100c3e1;       (* arm_ADD X1 SP (rvalue (word 48)) *)
  0x97fffdef;       (* arm_BL (word 268433340) *)
  0x91018320;       (* arm_ADD X0 X25 (rvalue (word 96)) *)
  0x9103c3e1;       (* arm_ADD X1 SP (rvalue (word 240)) *)
  0x9100c3e2;       (* arm_ADD X2 SP (rvalue (word 48)) *)
  0x97ffff1e;       (* arm_BL (word 268434552) *)
  0x9103c3e0;       (* arm_ADD X0 SP (rvalue (word 240)) *)
  0x910483e1;       (* arm_ADD X1 SP (rvalue (word 288)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x97fffc48;       (* arm_BL (word 268431648) *)
  0xa9490be1;       (* arm_LDP X1 X2 SP (Immediate_Offset (iword (&144))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xd37ef420;       (* arm_LSL X0 X1 2 *)
  0xa95223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&288))) *)
  0xeb070000;       (* arm_SUBS X0 X0 X7 *)
  0x93c1f841;       (* arm_EXTR X1 X2 X1 62 *)
  0xfa080021;       (* arm_SBCS X1 X1 X8 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0x93c2f862;       (* arm_EXTR X2 X3 X2 62 *)
  0xfa070042;       (* arm_SBCS X2 X2 X7 *)
  0x93c3f883;       (* arm_EXTR X3 X4 X3 62 *)
  0xfa080063;       (* arm_SBCS X3 X3 X8 *)
  0x93c4f8a4;       (* arm_EXTR X4 X5 X4 62 *)
  0xa95423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&320))) *)
  0xfa070084;       (* arm_SBCS X4 X4 X7 *)
  0x93c5f8c5;       (* arm_EXTR X5 X6 X5 62 *)
  0xfa0800a5;       (* arm_SBCS X5 X5 X8 *)
  0xd37efcc6;       (* arm_LSR X6 X6 62 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xd3607cc7;       (* arm_LSL X7 X6 32 *)
  0xeb0700c8;       (* arm_SUBS X8 X6 X7 *)
  0xda1f00e7;       (* arm_SBC X7 X7 XZR *)
  0xab080000;       (* arm_ADDS X0 X0 X8 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xda9f23e8;       (* arm_CSETM X8 Condition_CC *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xab090000;       (* arm_ADDS X0 X0 X9 *)
  0xca080129;       (* arm_EOR X9 X9 X8 *)
  0xba090021;       (* arm_ADCS X1 X1 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0x9a0800a5;       (* arm_ADC X5 X5 X8 *)
  0xa9000720;       (* arm_STP X0 X1 X25 (Immediate_Offset (iword (&0))) *)
  0xa9010f22;       (* arm_STP X2 X3 X25 (Immediate_Offset (iword (&16))) *)
  0xa9021724;       (* arm_STP X4 X5 X25 (Immediate_Offset (iword (&32))) *)
  0xa94c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0xeb0000c6;       (* arm_SUBS X6 X6 X0 *)
  0xb2607fe7;       (* arm_MOV X7 (rvalue (word 18446744069414584320)) *)
  0xfa0100e7;       (* arm_SBCS X7 X7 X1 *)
  0xa94d07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&208))) *)
  0x92800028;       (* arm_MOVN X8 (word 1) 0 *)
  0xfa000108;       (* arm_SBCS X8 X8 X0 *)
  0x9280000d;       (* arm_MOVN X13 (word 0) 0 *)
  0xfa0101a9;       (* arm_SBCS X9 X13 X1 *)
  0xa94e07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&224))) *)
  0xfa0001aa;       (* arm_SBCS X10 X13 X0 *)
  0xda0101ab;       (* arm_SBC X11 X13 X1 *)
  0xd37df0c0;       (* arm_LSL X0 X6 3 *)
  0x93c6f4e1;       (* arm_EXTR X1 X7 X6 61 *)
  0x93c7f502;       (* arm_EXTR X2 X8 X7 61 *)
  0x93c8f523;       (* arm_EXTR X3 X9 X8 61 *)
  0x93c9f544;       (* arm_EXTR X4 X10 X9 61 *)
  0x93caf565;       (* arm_EXTR X5 X11 X10 61 *)
  0xd37dfd66;       (* arm_LSR X6 X11 61 *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xa94f27e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&240))) *)
  0xa9502fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&256))) *)
  0xa95137ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&272))) *)
  0xd280006e;       (* arm_MOV X14 (rvalue (word 3)) *)
  0x9b087dcf;       (* arm_MUL X15 X14 X8 *)
  0x9bc87dc8;       (* arm_UMULH X8 X14 X8 *)
  0xab0f0000;       (* arm_ADDS X0 X0 X15 *)
  0x9b097dcf;       (* arm_MUL X15 X14 X9 *)
  0x9bc97dc9;       (* arm_UMULH X9 X14 X9 *)
  0xba0f0021;       (* arm_ADCS X1 X1 X15 *)
  0x9b0a7dcf;       (* arm_MUL X15 X14 X10 *)
  0x9bca7dca;       (* arm_UMULH X10 X14 X10 *)
  0xba0f0042;       (* arm_ADCS X2 X2 X15 *)
  0x9b0b7dcf;       (* arm_MUL X15 X14 X11 *)
  0x9bcb7dcb;       (* arm_UMULH X11 X14 X11 *)
  0xba0f0063;       (* arm_ADCS X3 X3 X15 *)
  0x9b0c7dcf;       (* arm_MUL X15 X14 X12 *)
  0x9bcc7dcc;       (* arm_UMULH X12 X14 X12 *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0x9b0d7dcf;       (* arm_MUL X15 X14 X13 *)
  0x9bcd7dcd;       (* arm_UMULH X13 X14 X13 *)
  0xba0f00a5;       (* arm_ADCS X5 X5 X15 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab080021;       (* arm_ADDS X1 X1 X8 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0xba0c00a5;       (* arm_ADCS X5 X5 X12 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0xd3607cc7;       (* arm_LSL X7 X6 32 *)
  0xeb0700c8;       (* arm_SUBS X8 X6 X7 *)
  0xda1f00e7;       (* arm_SBC X7 X7 XZR *)
  0xab080000;       (* arm_ADDS X0 X0 X8 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xda9f23e6;       (* arm_CSETM X6 Condition_CC *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0xca0600e7;       (* arm_EOR X7 X7 X6 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0x92800027;       (* arm_MOVN X7 (word 1) 0 *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0x9a0600a5;       (* arm_ADC X5 X5 X6 *)
  0xa9030720;       (* arm_STP X0 X1 X25 (Immediate_Offset (iword (&48))) *)
  0xa9040f22;       (* arm_STP X2 X3 X25 (Immediate_Offset (iword (&64))) *)
  0xa9051724;       (* arm_STP X4 X5 X25 (Immediate_Offset (iword (&80))) *)
  0xa95553f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&336))) *)
  0xa9565bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&352))) *)
  0xa95763f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&368))) *)
  0xa9586bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&384))) *)
  0xa9597ffe;       (* arm_LDP X30 XZR SP (Immediate_Offset (iword (&400))) *)
  0x910683ff;       (* arm_ADD SP SP (rvalue (word 416)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P384_MONTJDOUBLE_EXEC = ARM_MK_EXEC_RULE p384_montjdouble_mc;;

(* P384_MONTJDOUBLE_EXEC without sp add, callee save register reloads and ret.
   This truncation is for equivalence checking. *)
let p384_montjdouble_core_mc_def,p384_montjdouble_core_mc,
    P384_MONTJDOUBLE_CORE_EXEC =
  mk_sublist_of_mc "p384_montjdouble_core_mc"
    p384_montjdouble_mc (`0`,`LENGTH p384_montjdouble_mc - 28`)
    (fst P384_MONTJDOUBLE_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p384shortishredlemma = prove
 (`!n. n <= 24 * (p_384 - 1)
       ==> let q = n DIV 2 EXP 384 + 1 in
           q < 25 /\
           q < 2 EXP 64 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let p384shortintredlemma = prove
 (`!n. --(&p_384) <= n /\ n <= &5 * &p_384
       ==> let q = (&2 pow 384 + n) div &2 pow 384 in
           &0 <= q /\ q < &25 /\
           q < &2 pow 64 /\
           q * &p_384 <= n + &p_384 /\
           n < q * &p_384 + &p_384`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 384 + n:int = &1 * &2 pow 384 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 384` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_384` THEN REWRITE_TAC[p_384] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_384` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_384] THEN INT_ARITH_TAC);;

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

let p384shortredlemma = prove
 (`!n. n < 3 * p_384
       ==> let q = (n DIV 2 EXP 384) + 1 in
           q <= 3 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

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

let lvs =
 ["x_1",[`X26`; `0`];
  "y_1",[`X26`; `48`];
  "z_1",[`X26`; `96`];
  "x_3",[`X25`; `0`];
  "y_3",[`X25`; `48`];
  "z_3",[`X25`; `96`];
  "z2",[`SP`; `0`];
  "y2",[`SP`; `48`];
  "x2p",[`SP`; `96`];
  "xy2",[`SP`; `144`];
  "y4",[`SP`; `192`];
  "t2",[`SP`; `192`];
  "dx2",[`SP`; `240`];
  "t1",[`SP`; `240`];
  "d",[`SP`; `288`];
  "x4p",[`SP`; `288`]];;

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Support interface of ARM_MACRO_SIM_ABBREV_TAC when using a subroutine.    *)
(* ------------------------------------------------------------------------- *)

let PROLOGUE_SUBROUTINE_SIM_TAC corth inargs outarg m inouts =
  let main_tac =
     ARM_SUBROUTINE_SIM_ABBREV_TAC
      (p384_montjdouble_core_mc,P384_MONTJDOUBLE_CORE_EXEC,0,
       p384_montjdouble_core_mc,corth)
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
    ARM_STEPS_TAC P384_MONTJDOUBLE_CORE_EXEC ((n+1)--(n+m+k)) THEN
    main_tac (name_of dvar') (n+m+k+1));;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_P384_CORRECT =
  let lemma = prove(`!z x a pc.
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc + 0x67c) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + (0x67c + LENGTH bignum_montsqr_p384_core_mc)) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    SUBGOAL_THEN
      `bignum_montsqr_p384_core_mc =
        SUB_LIST (0x67c, LENGTH bignum_montsqr_p384_core_mc)
                 p384_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_MONTSQR_P384_CORE_EXEC;
                  bignum_montsqr_p384_core_mc; p384_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC; ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P384_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_MONTSQR_P384_CORE_EXEC] th)
        [fst BIGNUM_MONTSQR_P384_CORE_EXEC;
        fst P384_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P384_MONTJDOUBLE_CORE_EXEC]
    (prove(`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc + 0x67c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst P384_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
      P384_MONTJDOUBLE_CORE_EXEC
      ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
        REWRITE_RULE [fst P384_MONTJDOUBLE_CORE_EXEC;fst BIGNUM_MONTSQR_P384_CORE_EXEC])
      lemma)));;

let LOCAL_MONTSQR_P384_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_MONTSQR_P384_CORRECT
   [`read X0 s`; `read X1 s`;
    `read (memory :> bytes(read X1 s,8 * 6)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 6)) s'`;;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_P384_CORRECT =
  let lemma = prove(`!z x y a b pc.
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc+16) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + (16 + LENGTH bignum_montmul_p384_core_mc)) /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    SUBGOAL_THEN
      `bignum_montmul_p384_core_mc =
        SUB_LIST (16, LENGTH bignum_montmul_p384_core_mc)
                 p384_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_MONTMUL_P384_CORE_EXEC;
                  bignum_montmul_p384_core_mc; p384_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC; ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
      ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P384_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_MONTMUL_P384_CORE_EXEC] th)
        [fst BIGNUM_MONTMUL_P384_CORE_EXEC;fst P384_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P384_MONTJDOUBLE_CORE_EXEC]
    (prove(`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH p384_montjdouble_core_mc); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = returnaddress /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                         memory :> bytes(word_sub stackpointer (word 48),48)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
    REWRITE_TAC[fst P384_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_STACK_TAC
      ~pre_post_nsteps:(4,4)
      P384_MONTJDOUBLE_CORE_EXEC
      (let th = REWRITE_RULE [
            fst BIGNUM_MONTMUL_P384_CORE_EXEC;
            fst P384_MONTJDOUBLE_CORE_EXEC] lemma in
        CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
      `[X19;X20;X21;X22;X23;X24]` 48));;

let LOCAL_MONTMUL_P384_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_MONTMUL_P384_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 6)) s`;
    `read (memory :> bytes(read X2 s,8 * 6)) s`;
    `pc:num`; `read SP s`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 6)) s'`;;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P384_CORRECT =
  let lemma = prove(`!z x y m n pc.
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc + 0xb48) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = m /\
                  bignum_from_memory (y,6) s = n)
             (\s. read PC s = word (pc + (0xb48 + 108)) /\
                  (m < p_384 /\ n < p_384
                   ==> &(bignum_from_memory (z,6) s) = (&m - &n) rem &p_384))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,6)])`,
    SUBGOAL_THEN
      `bignum_sub_p384_mc = SUB_LIST (0xb48, 112) p384_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_SUB_P384_EXEC; bignum_sub_p384_mc; p384_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_SUB_P384_CORRECT
        (REWRITE_RULE [fst BIGNUM_SUB_P384_EXEC] th)
        [fst BIGNUM_SUB_P384_EXEC; fst P384_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P384_MONTJDOUBLE_CORE_EXEC] (prove(
    `!z x y m n pc returnaddress.
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc + 0xb48) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = m /\
                  bignum_from_memory (y,6) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_384 /\ n < p_384
                   ==> &(bignum_from_memory (z,6) s) = (&m - &n) rem &p_384))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
    REWRITE_TAC[fst P384_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P384_MONTJDOUBLE_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P384_MONTJDOUBLE_CORE_EXEC;fst BIGNUM_SUB_P384_EXEC])
     lemma)));;

let LOCAL_SUB_P384_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_SUB_P384_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 6)) s`;
    `read (memory :> bytes(read X2 s,8 * 6)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 6)) s'`;;

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P384_CORRECT =
  let lemma = prove(`!z x y m n pc.
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc + 0xbb8) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = m /\
                  bignum_from_memory (y,6) s = n)
             (\s. read PC s = word (pc + (0xbb8 + 152)) /\
                  (m < p_384 /\ n < p_384
                   ==> bignum_from_memory (z,6) s = (m + n) MOD p_384))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,6)])`,
    SUBGOAL_THEN
      `bignum_add_p384_mc = SUB_LIST (0xbb8, 156) p384_montjdouble_core_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_ADD_P384_EXEC; bignum_add_p384_mc;
                  p384_montjdouble_core_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
    ARM_SUB_LIST_OF_MC_TAC BIGNUM_ADD_P384_CORRECT
        (REWRITE_RULE [fst BIGNUM_ADD_P384_EXEC] th)
        [fst BIGNUM_ADD_P384_EXEC; fst P384_MONTJDOUBLE_CORE_EXEC])) in
  REWRITE_RULE [fst P384_MONTJDOUBLE_CORE_EXEC] (prove(
    `!z x y m n pc returnaddress.
        nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc + 0xbb8) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = m /\
                  bignum_from_memory (y,6) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_384 /\ n < p_384
                   ==> bignum_from_memory (z,6) s = (m + n) MOD p_384))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
    REWRITE_TAC[fst P384_MONTJDOUBLE_CORE_EXEC] THEN
    ARM_ADD_RETURN_NOSTACK_TAC
    P384_MONTJDOUBLE_CORE_EXEC
    ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o
     REWRITE_RULE [fst P384_MONTJDOUBLE_CORE_EXEC;fst BIGNUM_ADD_P384_EXEC])
     lemma)));;

let LOCAL_ADD_P384_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_ADD_P384_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 6)) s`;
    `read (memory :> bytes(read X2 s,8 * 6)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 6)) s'`;;

(* ------------------------------------------------------------------------- *)
(* Instances of weakadd                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKADD_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_core_mc 27 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc)
                   (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read PC s = pcout /\
                  (m + n < 2 EXP 384 + p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s < 2 EXP 384 /\
                       (&(read(memory :> bytes(word_add (read p3 t) (word n3),
                               8 * 6)) s):int == &m + &n) (mod &p_384)))
            (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst P384_MONTJDOUBLE_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`] (1--12) (1--12) THEN
  SUBGOAL_THEN `carry_s12 <=> 2 EXP 384 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [13] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`] (14--27) (14--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!x. (x < 2 EXP 384 /\ P x) /\ y = x ==> y < 2 EXP 384 /\ P y`) THEN
  EXISTS_TAC `if m + n < 2 EXP 384 then m + n else (m + n) - p_384` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `m + n < 2 EXP 384 + p_384` THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_CONG_REFL] THEN
    MATCH_MP_TAC(INTEGER_RULE `y - p:int = x ==> (x == y) (mod p)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC INT_OF_NUM_SUB THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 384`)]) THEN
  ABBREV_TAC `b <=> 2 EXP 384 <= m + n` THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCARD_STATE_TAC "s27" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; COND_SWAP] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `m + n < 2 EXP 384 + p_384` THEN
    EXPAND_TAC "b" THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `&(if b then (m + n) - p_384 else m + n):real =
    if b then (&m + &n) - &p_384 else &m + &n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    UNDISCH_TAC `b:bool` THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_core_mc 86 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,4284)
                   (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_384
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s) = (&12 * &m - &9 * &n) rem &p_384))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst P384_MONTJDOUBLE_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_CORE_EXEC (1--86)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_384 =
    (&12 * &m + &9 * (&p_384 - &n)) rem &p_384`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`] (1--13) (1--13) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
           [sum_s3; sum_s5; sum_s8; sum_s10; sum_s12; sum_s13]` THEN
  SUBGOAL_THEN `p_384 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `12 * m + 9 * n'` p384shortishredlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_384] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `x DIV 2 EXP 384 + 1 = (2 EXP 384 + x) DIV 2 EXP 384`]) THEN

  (*** Main sum of products computation +1 ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`] (14--62) (14--62) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s40; sum_s57; sum_s58; sum_s59; sum_s60; sum_s61; sum_s62]` THEN
  SUBGOAL_THEN `2 EXP 384 + 12 * m + 9 * n'= ca` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
       SUBST_ALL_TAC th THEN ASSUME_TAC th THEN DISCH_TAC) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s62` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s46:int64` o concl))) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 384 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`]
    [64;65;66;67;68;69;70;71; 75;77;80;81;82;83]
    (63--86) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `384`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Explicitly observe that the small quotient mul works ***)

  SUBGOAL_THEN `&(val (word_shl q 32)):real = &2 pow 32 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_SHL; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `12 * m + 9 * n' < val(q:int64) * p_384 <=> ~carry_s71`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 384 + a < b + 2 EXP 384`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
     `&(12 * m + 9 * n'):real =
      (&2 pow 384 + &(12 * m + 9 * n')) - &2 pow 384`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s71:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub41_p384 (actually there is only one).                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_core_mc 44 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc)
                   (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
         (\s. read PC s = pcout /\
              (n <= p_384
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 6)) s) = (&4 * &m - &n) rem &p_384))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst P384_MONTJDOUBLE_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n <= p_384 assumption ***)

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_CORE_EXEC (1--44)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Instantiate the (integer) quotient approximation lemma ***)

  MP_TAC(SPEC `&4 * &m - &n:int` p384shortintredlemma) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      INT_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[p_384] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Main shift-subtract block ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`] [6;8;11;13;16;18;20] (1--20) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s6; sum_s8; sum_s11; sum_s13; sum_s16; sum_s18; sum_s20]` THEN
  SUBGOAL_THEN `&2 pow 384 + &4 * &m - &n:int = &ca`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_pow_th;
                int_mul_th; int_of_num_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&4 * &m:real =
      &(bignum_of_wordlist
         [word_shl m_0 2;
          word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
          word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
          word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
          word_subword ((word_join:int64->int64->int128) m_4 m_3) (62,64);
          word_subword ((word_join:int64->int64->int128) m_5 m_4) (62,64);
          word_ushr m_5 62])`
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s20` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s20:int64` o concl))) THEN
  SUBGOAL_THEN `&ca div &2 pow 384 = &(val(q:int64))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV] THEN
    EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`]
    [22;23;24;25;26;27;28;29; 33;35;38;39;40;41]
    (21--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED_MOD THEN
  MAP_EVERY EXISTS_TAC [`&(val(q:int64)):int`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; p_384] THEN BOUNDER_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `&4 * m - n:int = (&2 pow 384 + &4 * m - n) - &2 pow 384`] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Explicitly observe that the small quotient mul works ***)

  SUBGOAL_THEN `&(val (word_shl q 32)):real = &2 pow 32 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_SHL; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN
    `(&ca - &2 pow 384):int < &(val(q:int64)) * &p_384 <=> ~carry_s29`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_LT_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_RULE
     `(a:int == b + c - p) (mod p) <=> (a == b + c) (mod p)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s29:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub38 (there is only one).                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_core_mc 74 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p384_montjdouble_core_mc)
                   (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_384
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s) = (&3 * &m - &8 * &n) rem &p_384))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst P384_MONTJDOUBLE_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_CORE_EXEC (1--74)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) rem &p_384 =
    (&3 * &m + &8 * (&p_384 - &n)) rem &p_384`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`] (1--13) (1--13) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
           [sum_s3; sum_s5; sum_s8; sum_s10; sum_s12; sum_s13]` THEN
  SUBGOAL_THEN `p_384 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `3 * m + 8 * n'` p384shortishredlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_384] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `x DIV 2 EXP 384 + 1 = (2 EXP 384 + x) DIV 2 EXP 384`]) THEN

  (*** Main sum of products computation +1 ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`]
   [21; 26; 28; 29; 31; 32; 34; 35; 37; 38;
    40; 41; 43; 44; 45; 46; 47; 48; 49; 50]
   (14--50) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s28; sum_s45; sum_s46; sum_s47; sum_s48; sum_s49; sum_s50]` THEN
  SUBGOAL_THEN `2 EXP 384 + 3 * m + 8 * n'= ca` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&8 * &n':real =
      &(bignum_of_wordlist
      [word_shl sum_s3 3;
       word_subword ((word_join:int64->int64->int128) sum_s5 sum_s3) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s8 sum_s5) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s10 sum_s8) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s12 sum_s10) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s13 sum_s12) (61,64);
       word_ushr sum_s13 61])`
    SUBST1_TAC THENL
     [EXPAND_TAC "n'" THEN
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
      MAP_EVERY EXPAND_TAC ["m"; "ca"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
      DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
        SUBST_ALL_TAC th THEN ASSUME_TAC th THEN DISCH_TAC) THEN
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s50` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s50:int64` o concl))) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 384 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_XACCSTEPS_TAC P384_MONTJDOUBLE_CORE_EXEC [`SP`]
   [52; 53; 54; 55; 56; 57; 58; 59;  63; 65; 68; 69; 70; 71]
   (51--74) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `384`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Explicitly observe that the small quotient mul works ***)

  SUBGOAL_THEN `&(val (word_shl q 32)):real = &2 pow 32 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_SHL; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `3 * m + 8 * n' < val(q:int64) * p_384 <=> ~carry_s59`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 384 + a < b + 2 EXP 384`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
     `&(3 * m + 8 * n'):real =
      (&2 pow 384 + &(3 * m + 8 * n')) - &2 pow 384`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s59:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_384 ==> x < p_384 /\ &x = &a rem &p_384`,
  REWRITE_TAC[INT_OF_NUM_REM; p_384] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_384 ==> x < p_384 /\ &x = a rem &p_384`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_384] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_384 = (&i * x rem &p_384 * y rem &p_384) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_384 = (&(NUMERAL n) * &x rem &p_384) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_384 (2 EXP 384)) *
    (&2 pow 384 * x) rem &p_384 * (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * x * y) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_384] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 384 * x) rem &p_384 + (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * (x + y)) rem &p_384 /\
   ((&2 pow 384 * x) rem &p_384 - (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * (x - y)) rem &p_384 /\
  (&(NUMERAL n) * (&2 pow 384 * x) rem &p_384) rem &p_384 =
   (&2 pow 384 * (&(NUMERAL n) * x)) rem &p_384`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_384 (2 EXP 384)) * (&2 pow 384 * x) rem &p_384) rem &p_384 =
   x rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_384
         ==> x =
             (2 EXP 384 * (inverse_mod p_384 (2 EXP 384) * x) MOD p_384) MOD
             p_384`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_jacobian_p384_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp384
         (x1 rem &p_384,y1 rem &p_384,z1 rem &p_384) =
        (x3 rem &p_384,y3 rem &p_384,z3 rem &p_384)
       ==> weierstrass_of_jacobian (integer_mod_ring p_384)
                (x1 rem &p_384,y1 rem &p_384,z1 rem &p_384) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_384)
                  (x3 rem &p_384,y3 rem &p_384,z3 rem &p_384) =
                group_mul p384_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp384; P384_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P384] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_384; b_384] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p384 = new_definition
 `represents_p384 P (x,y,z) <=>
        x < p_384 /\ y < p_384 /\ z < p_384 /\
        weierstrass_of_jacobian (integer_mod_ring p_384)
         (tripled (montgomery_decode (384,p_384)) (x,y,z)) = P`;;

let P384_MONTJDOUBLE_UNOPT_CORE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,384))
            [(word pc,LENGTH p384_montjdouble_core_mc); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc,LENGTH p384_montjdouble_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word(pc + 0xc6c) /\
                  read SP s = (word_add stackpointer (word 48)) /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read PC s = word (pc + 0x10bc) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X30] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(stackpointer,384)])`,
  REWRITE_TAC[FORALL_PAIR_THM;fst P384_MONTJDOUBLE_CORE_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_P384_TAC 2 ["z2";"z_1"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["y2";"y_1"] THEN
  LOCAL_WEAKADD_P384_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_SUB_P384_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P384_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["t2";"t1"] THEN
  LOCAL_CMSUBC9_P384_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P384_TAC 0 ["t1";"t2";"z2"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["y4";"y2"] THEN
  LOCAL_SUB_P384_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_CMSUB41_P384_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P384_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s61" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p384; tripled] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_384] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_384]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma) [`z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_384 (2 EXP 384) * x1`;
    `y1d = inverse_mod p_384 (2 EXP 384) * y1`;
    `z1d = inverse_mod p_384 (2 EXP 384) * z1`] THEN
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
  MATCH_MP_TAC weierstrass_of_jacobian_p384_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp384;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Prove the corectness of optimized p384_montjdouble using equiv. checker   *)
(* ------------------------------------------------------------------------- *)

let p384_montjdouble_eqin = new_definition
  `!s1 s1' p1 p3 stackpointer.
    (p384_montjdouble_eqin:(armstate#armstate)->int64->int64->int64->bool)
        (s1,s1') p1 p3 stackpointer <=>
     (C_ARGUMENTS [p3; p1] s1 /\
      C_ARGUMENTS [p3; p1] s1' /\
      // 48 is the amount used by montmul_p384
      read SP s1 = word_add stackpointer (word 48) /\
      read SP s1' = word_add stackpointer (word 48) /\
      ?a. bignum_from_memory (p1,18) s1 = a /\
          bignum_from_memory (p1,18) s1' = a)`;;

let p384_montjdouble_eqout = new_definition
  `!s1 s1' p3 stackpointer.
    (p384_montjdouble_eqout:(armstate#armstate)->int64->int64->bool)
        (s1,s1') p3 stackpointer <=>
    (// 48 is the amount used by montmul_p384
     // keep track of the SP values to remove MAYCHANGE SP later.
     read SP s1 = word_add stackpointer (word 48) /\
     read SP s1' = word_add stackpointer (word 48) /\
     // 3 separate 4-word reads to make proving equality between
     // two bignum_triple_from_memory results straightforward
     ?a0. bignum_from_memory (p3,6) s1 = a0 /\
          bignum_from_memory (p3,6) s1' = a0 /\
     ?a1. bignum_from_memory (word_add p3 (word (8 * 6)),6) s1 = a1 /\
          bignum_from_memory (word_add p3 (word (8 * 6)),6) s1' = a1 /\
     ?a2. bignum_from_memory (word_add p3 (word (16 * 6)),6) s1 = a2 /\
          bignum_from_memory (word_add p3 (word (16 * 6)),6) s1' = a2)`;;

(* ------------------------------------------------------------------------- *)
(* Load parameters that will be used by equivalence checking proofs.         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/p384_montjdouble_params.ml";;

(* ------------------------------------------------------------------------- *)
(* Prove program equivalence between the base and optimized assemblies.      *)
(* ------------------------------------------------------------------------- *)

let p384_montjdouble_opt_mc =
  define_from_elf "p384_montjdouble_opt_mc" "arm/p384/p384_montjdouble.o";;
let P384_MONTJDOUBLE_OPT_EXEC = ARM_MK_EXEC_RULE p384_montjdouble_opt_mc;;

let len_p384_montjdouble_opt = count_insts P384_MONTJDOUBLE_OPT_EXEC;;

let equiv_goal = mk_equiv_statement
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (stackpointer:int64,384))
            [(word pc,LENGTH p384_montjdouble_core_mc);
             (word pc2,LENGTH p384_montjdouble_opt_mc);
             (p1:int64,144); (p3:int64,144)] /\
     ALL (nonoverlapping (p3,144))
       [(word pc,LENGTH p384_montjdouble_core_mc);
        (word pc2,LENGTH p384_montjdouble_opt_mc)]`
    p384_montjdouble_eqin
    p384_montjdouble_eqout
    p384_montjdouble_core_mc 0xc6c 0x10bc
    `MAYCHANGE [PC; SP; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                X11; X12; X13; X14; X15; X16; X17; X19; X20;
                X21; X22; X23; X24; X25; X26; X30] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(p3,144);
                memory :> bytes(stackpointer,384)]`
    p384_montjdouble_opt_mc 0x18 0x3050
    `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                X22; X23; X24; X25; X26; X27] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(p3,144);
                memory :> bytes(stackpointer,384)]`
    (vsubst [mk_small_numeral(
        let _,_,n,_,_ = last !actions1 in n),`x:num`]
        `\(s:armstate). (x:num)`)
    (vsubst [mk_small_numeral(len_p384_montjdouble_opt - 6 - 7),`x:num`]
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


let P384_MONTJDOUBLE_EQUIV = time prove(equiv_goal,

  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    SOME_FLAGS;MODIFIABLE_SIMD_REGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst P384_MONTJDOUBLE_CORE_EXEC;
    fst P384_MONTJDOUBLE_OPT_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC p384_montjdouble_eqin THEN
  REPEAT (FIRST_X_ASSUM BIGNUM_EXPAND_AND_DIGITIZE_TAC) THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN

  (* Start *)
  EQUIV_STEPS_TAC
    ~dead_value_info_left:p384_montjdouble_unopt_dead_value_info
    ~dead_value_info_right:p384_montjdouble_dead_value_info
    actions_merged P384_MONTJDOUBLE_CORE_EXEC P384_MONTJDOUBLE_OPT_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[p384_montjdouble_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,6) state`;
                    C_ARGUMENTS] THEN
    (* Fold `word_add (word_add x c1) c2` and constant exprs that came from
       p384_montjadd_eqout *)
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
     ALL (nonoverlapping (stackpointer,384))
          [(word pc,LENGTH (APPEND p384_montjdouble_core_mc barrier_inst_bytes));
           (p1,144); (p3,144)] /\
     nonoverlapping (p3,144)
        (word pc,LENGTH (APPEND p384_montjdouble_core_mc barrier_inst_bytes))`
    [`p1:int64`;`p3:int64`;`stackpointer:int64`]
    p384_montjdouble_core_mc `pc+0xc6c` `pc+0x10bc`
    (mk_small_numeral (let _,_,n,_,_ = last !actions1 in n))
    `\s0. read SP s0 = word_add stackpointer (word 48) /\ C_ARGUMENTS [p3; p1] s0`;;


let P384_MONTJDOUBLE_UNOPT_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,
  REWRITE_TAC[LENGTH_APPEND;fst P384_MONTJDOUBLE_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH p384_montjdouble_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst P384_MONTJDOUBLE_CORE_EXEC]) THENL [
    REWRITE_TAC[fst P384_MONTJDOUBLE_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC P384_MONTJDOUBLE_CORE_EXEC);;

(* P384_MONTJDOUBLE_UNOPT_CORE_CORRECT, but with stackpointer preservation
   added to the postcondition whereas SP added to MAYCHANGE.
   This definition is syntactically consistent with equiv_goal. *)

let P384_MONTJDOUBLE_UNOPT_CORE_CORRECT_SP = time prove
 (`!p3 p1 t1 pc stackpointer.
         aligned 16 stackpointer /\
         ALL (nonoverlapping (stackpointer,384))
         [word pc,LENGTH p384_montjdouble_core_mc; p1,144; p3,144] /\
         nonoverlapping (p3,144) (word pc,LENGTH p384_montjdouble_core_mc)
         ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_core_mc /\
                  read PC s = word (pc + 3180) /\
                  read SP s = word_add stackpointer (word 48) /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read PC s = word (pc + 4284) /\
                  read SP s = (word_add stackpointer (word 48)) /\
                  (!P. represents_p384 P t1
                       ==> represents_p384 (group_mul p384_group P P)
                           (bignum_triple_from_memory (p3,6) s)))
             (MAYCHANGE
              [PC; SP; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
               X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25;
               X26; X30] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE
              [memory :> bytes (p3,144); memory :> bytes (stackpointer,384)])`,

  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC_ALL P384_MONTJDOUBLE_UNOPT_CORE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
    (* MAYCHANGE *)
    REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS] THEN
    SUBSUMED_MAYCHANGE_TAC;

    (* Post /\ Frame ==> Post' *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `read SP s = read SP s'` MP_TAC THENL [
      FIRST_X_ASSUM MP_TAC THEN
      REWRITE_TAC[SOME_FLAGS;MODIFIABLE_SIMD_REGS] THEN
      REWRITE_TAC[MAYCHANGE;SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN REWRITE_TAC[ASSIGNS_SEQ] THEN
      REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONV_TAC(RAND_CONV(DEPTH_CONV
        COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
      REFL_TAC;

      ALL_TAC
    ] THEN
    ASM_MESON_TAC[]
  ]);;


let P384_MONTJDOUBLE_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    P384_MONTJDOUBLE_EXEC
    P384_MONTJDOUBLE_CORE_EXEC
    P384_MONTJDOUBLE_UNOPT_CORE_CORRECT_SP
    P384_MONTJDOUBLE_UNOPT_EVENTUALLY_N_AT_PC;;

let P384_MONTJDOUBLE_CORRECT = prove(
  `!p3 p1 t1 pc2 stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,384))
            [(word pc2,LENGTH p384_montjdouble_opt_mc); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc2,LENGTH p384_montjdouble_opt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) p384_montjdouble_opt_mc /\
                  read PC s = word(pc2 + 0x18) /\
                  read SP s = (word_add stackpointer (word 48)) /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read PC s = word (pc2 + 0x3050) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                      X22; X23; X24; X25; X26; X27] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(stackpointer,384)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      ALL (nonoverlapping
        (word pc,LENGTH (APPEND p384_montjdouble_core_mc barrier_inst_bytes)))
        [(p1:int64,144);(p3:int64,144);(stackpointer:int64,384)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst P384_MONTJDOUBLE_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL] THEN
    time FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  VCGEN_EQUIV_TAC P384_MONTJDOUBLE_EQUIV P384_MONTJDOUBLE_UNOPT_CORE_CORRECT_N
    [fst P384_MONTJDOUBLE_CORE_EXEC;fst P384_MONTJDOUBLE_OPT_EXEC] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[ALL;NONOVERLAPPING_CLAUSES;
      LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH;
      fst P384_MONTJDOUBLE_CORE_EXEC; fst P384_MONTJDOUBLE_OPT_EXEC]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;bignum_triple_from_memory] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[p384_montjdouble_eqin;C_ARGUMENTS] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND p384_montjdouble_core_mc barrier_inst_bytes)))
          (APPEND p384_montjdouble_core_mc barrier_inst_bytes)
          (write PC (word (pc + 0xc6c)) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    PROVE_CONJ_OF_EQ_READS_TAC P384_MONTJDOUBLE_CORE_EXEC THEN
    (* Now has only one subgoal: the input state equivalence! *)
    REPEAT (HINT_EXISTS_REFL_TAC THEN
        PROVE_CONJ_OF_EQ_READS_TAC P384_MONTJDOUBLE_CORE_EXEC);

    (** SUBGOAL 2. Postcond **)
    REWRITE_TAC[p384_montjdouble_eqout;BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MESON_TAC[fst P384_MONTJDOUBLE_CORE_EXEC; fst P384_MONTJDOUBLE_OPT_EXEC];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS]
  ]);;

let P384_MONTJDOUBLE_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 464),464))
            [(word pc,LENGTH p384_montjdouble_opt_mc); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc,LENGTH p384_montjdouble_opt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_opt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read PC s = returnaddress /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(word_sub stackpointer (word 464),464)])`,
  ARM_ADD_RETURN_STACK_TAC P384_MONTJDOUBLE_OPT_EXEC
   P384_MONTJDOUBLE_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27]` 464);;
