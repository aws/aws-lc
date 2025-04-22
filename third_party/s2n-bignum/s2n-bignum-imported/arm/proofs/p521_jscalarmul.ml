(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication for NIST P-521.                                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp521.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

needs "arm/proofs/bignum_mul_p521.ml";;
needs "arm/proofs/bignum_sqr_p521.ml";;
needs "arm/proofs/bignum_mod_n521_9.ml";;
needs "arm/proofs/bignum_mod_p521_9.ml";;

(* ------------------------------------------------------------------------- *)
(* Code.                                                                     *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/p521/p521_jscalarmul.o";;
 ****)

let p521_jscalarmul_mc = define_assert_from_elf
  "p521_jscalarmul_mc" "arm/p521/p521_jscalarmul.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf5;       (* arm_STP X21 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd13e03ff;       (* arm_SUB SP SP (rvalue (word 3968)) *)
  0xaa0003f4;       (* arm_MOV X20 X0 *)
  0xaa0203f3;       (* arm_MOV X19 X2 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x940004a2;       (* arm_BL (word 4744) *)
  0xaa1303e2;       (* arm_MOV X2 X19 *)
  0x9107e3e0;       (* arm_ADD X0 SP (rvalue (word 504)) *)
  0xaa1303e1;       (* arm_MOV X1 X19 *)
  0x9400047d;       (* arm_BL (word 4596) *)
  0x910903e0;       (* arm_ADD X0 SP (rvalue (word 576)) *)
  0x91012261;       (* arm_ADD X1 X19 (rvalue (word 72)) *)
  0x9400047a;       (* arm_BL (word 4584) *)
  0x910a23e0;       (* arm_ADD X0 SP (rvalue (word 648)) *)
  0x91024261;       (* arm_ADD X1 X19 (rvalue (word 144)) *)
  0x94000477;       (* arm_BL (word 4572) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xd28c812a;       (* arm_MOV X10 (rvalue (word 25609)) *)
  0xf2b2270a;       (* arm_MOVK X10 (word 37176) 16 *)
  0xf2d6e3ca;       (* arm_MOVK X10 (word 46878) 32 *)
  0xf2f76dea;       (* arm_MOVK X10 (word 47983) 48 *)
  0xeb00014a;       (* arm_SUBS X10 X10 X0 *)
  0xd288f5cb;       (* arm_MOV X11 (rvalue (word 18350)) *)
  0xf2b1338b;       (* arm_MOVK X11 (word 35228) 16 *)
  0xf2d9370b;       (* arm_MOVK X11 (word 51640) 32 *)
  0xf2e776ab;       (* arm_MOVK X11 (word 15285) 48 *)
  0xfa01016b;       (* arm_SBCS X11 X11 X1 *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xd294ba0c;       (* arm_MOV X12 (rvalue (word 42448)) *)
  0xf2bee12c;       (* arm_MOVK X12 (word 63241) 16 *)
  0xf2c0290c;       (* arm_MOVK X12 (word 328) 32 *)
  0xf2eff98c;       (* arm_MOVK X12 (word 32716) 48 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xd292cd6d;       (* arm_MOV X13 (rvalue (word 38507)) *)
  0xf2b7e5ed;       (* arm_MOVK X13 (word 48943) 16 *)
  0xf2d0f06d;       (* arm_MOVK X13 (word 34691) 32 *)
  0xf2ea30cd;       (* arm_MOVK X13 (word 20870) 48 *)
  0xfa0301ad;       (* arm_SBCS X13 X13 X3 *)
  0xa94217e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0x928000ae;       (* arm_MOVN X14 (word 5) 0 *)
  0xfa0401ce;       (* arm_SBCS X14 X14 X4 *)
  0x9280000f;       (* arm_MOVN X15 (word 0) 0 *)
  0xfa0501ef;       (* arm_SBCS X15 X15 X5 *)
  0xa9431fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0x92800010;       (* arm_MOVN X16 (word 0) 0 *)
  0xfa060210;       (* arm_SBCS X16 X16 X6 *)
  0x92800011;       (* arm_MOVN X17 (word 0) 0 *)
  0xfa070231;       (* arm_SBCS X17 X17 X7 *)
  0xf94023e8;       (* arm_LDR X8 SP (Immediate_Offset (word 64)) *)
  0xd2803ff3;       (* arm_MOV X19 (rvalue (word 511)) *)
  0xda080273;       (* arm_SBC X19 X19 X8 *)
  0xf278011f;       (* arm_TST X8 (rvalue (word 256)) *)
  0xda9f03e9;       (* arm_CSETM X9 Condition_NE *)
  0x9a801140;       (* arm_CSEL X0 X10 X0 Condition_NE *)
  0x9a811161;       (* arm_CSEL X1 X11 X1 Condition_NE *)
  0x9a821182;       (* arm_CSEL X2 X12 X2 Condition_NE *)
  0x9a8311a3;       (* arm_CSEL X3 X13 X3 Condition_NE *)
  0x9a8411c4;       (* arm_CSEL X4 X14 X4 Condition_NE *)
  0x9a8511e5;       (* arm_CSEL X5 X15 X5 Condition_NE *)
  0x9a861206;       (* arm_CSEL X6 X16 X6 Condition_NE *)
  0x9a871227;       (* arm_CSEL X7 X17 X7 Condition_NE *)
  0x9a881268;       (* arm_CSEL X8 X19 X8 Condition_NE *)
  0xa90007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9010fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa90217e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa9031fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0xf90023e8;       (* arm_STR X8 SP (Immediate_Offset (word 64)) *)
  0x9107e3ef;       (* arm_ADD X15 SP (rvalue (word 504)) *)
  0xa94485e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&72))) *)
  0xa9458de2;       (* arm_LDP X2 X3 X15 (Immediate_Offset (iword (&88))) *)
  0xa94695e4;       (* arm_LDP X4 X5 X15 (Immediate_Offset (iword (&104))) *)
  0xa9479de6;       (* arm_LDP X6 X7 X15 (Immediate_Offset (iword (&120))) *)
  0xf94045e8;       (* arm_LDR X8 X15 (Immediate_Offset (word 136)) *)
  0xaa01000a;       (* arm_ORR X10 X0 X1 *)
  0xaa03004b;       (* arm_ORR X11 X2 X3 *)
  0xaa05008c;       (* arm_ORR X12 X4 X5 *)
  0xaa0700cd;       (* arm_ORR X13 X6 X7 *)
  0xaa0b014a;       (* arm_ORR X10 X10 X11 *)
  0xaa0d018c;       (* arm_ORR X12 X12 X13 *)
  0xaa08018c;       (* arm_ORR X12 X12 X8 *)
  0xaa0c014a;       (* arm_ORR X10 X10 X12 *)
  0xeb1f015f;       (* arm_CMP X10 XZR *)
  0x9a9f1129;       (* arm_CSEL X9 X9 XZR Condition_NE *)
  0xca090000;       (* arm_EOR X0 X0 X9 *)
  0xca090021;       (* arm_EOR X1 X1 X9 *)
  0xca090042;       (* arm_EOR X2 X2 X9 *)
  0xca090063;       (* arm_EOR X3 X3 X9 *)
  0xca090084;       (* arm_EOR X4 X4 X9 *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xca0900c6;       (* arm_EOR X6 X6 X9 *)
  0xca0900e7;       (* arm_EOR X7 X7 X9 *)
  0x92402129;       (* arm_AND X9 X9 (rvalue (word 511)) *)
  0xca090108;       (* arm_EOR X8 X8 X9 *)
  0xa90485e0;       (* arm_STP X0 X1 X15 (Immediate_Offset (iword (&72))) *)
  0xa9058de2;       (* arm_STP X2 X3 X15 (Immediate_Offset (iword (&88))) *)
  0xa90695e4;       (* arm_STP X4 X5 X15 (Immediate_Offset (iword (&104))) *)
  0xa9079de6;       (* arm_STP X6 X7 X15 (Immediate_Offset (iword (&120))) *)
  0xf90045e8;       (* arm_STR X8 X15 (Immediate_Offset (word 136)) *)
  0x910b43e0;       (* arm_ADD X0 SP (rvalue (word 720)) *)
  0x9107e3e1;       (* arm_ADD X1 SP (rvalue (word 504)) *)
  0x94000584;       (* arm_BL (word 5648) *)
  0x910ea3e0;       (* arm_ADD X0 SP (rvalue (word 936)) *)
  0x910b43e1;       (* arm_ADD X1 SP (rvalue (word 720)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000485;       (* arm_BL (word 4628) *)
  0x911203e0;       (* arm_ADD X0 SP (rvalue (word 1152)) *)
  0x910b43e1;       (* arm_ADD X1 SP (rvalue (word 720)) *)
  0x9400057d;       (* arm_BL (word 5620) *)
  0x911563e0;       (* arm_ADD X0 SP (rvalue (word 1368)) *)
  0x911203e1;       (* arm_ADD X1 SP (rvalue (word 1152)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x9400047e;       (* arm_BL (word 4600) *)
  0x9118c3e0;       (* arm_ADD X0 SP (rvalue (word 1584)) *)
  0x910ea3e1;       (* arm_ADD X1 SP (rvalue (word 936)) *)
  0x94000576;       (* arm_BL (word 5592) *)
  0x911c23e0;       (* arm_ADD X0 SP (rvalue (word 1800)) *)
  0x9118c3e1;       (* arm_ADD X1 SP (rvalue (word 1584)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000477;       (* arm_BL (word 4572) *)
  0x911f83e0;       (* arm_ADD X0 SP (rvalue (word 2016)) *)
  0x911203e1;       (* arm_ADD X1 SP (rvalue (word 1152)) *)
  0x9400056f;       (* arm_BL (word 5564) *)
  0x9122e3e0;       (* arm_ADD X0 SP (rvalue (word 2232)) *)
  0x911f83e1;       (* arm_ADD X1 SP (rvalue (word 2016)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000470;       (* arm_BL (word 4544) *)
  0x912643e0;       (* arm_ADD X0 SP (rvalue (word 2448)) *)
  0x911563e1;       (* arm_ADD X1 SP (rvalue (word 1368)) *)
  0x94000568;       (* arm_BL (word 5536) *)
  0x9129a3e0;       (* arm_ADD X0 SP (rvalue (word 2664)) *)
  0x912643e1;       (* arm_ADD X1 SP (rvalue (word 2448)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000469;       (* arm_BL (word 4516) *)
  0x912d03e0;       (* arm_ADD X0 SP (rvalue (word 2880)) *)
  0x9118c3e1;       (* arm_ADD X1 SP (rvalue (word 1584)) *)
  0x94000561;       (* arm_BL (word 5508) *)
  0x913063e0;       (* arm_ADD X0 SP (rvalue (word 3096)) *)
  0x912d03e1;       (* arm_ADD X1 SP (rvalue (word 2880)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000462;       (* arm_BL (word 4488) *)
  0x9133c3e0;       (* arm_ADD X0 SP (rvalue (word 3312)) *)
  0x911c23e1;       (* arm_ADD X1 SP (rvalue (word 1800)) *)
  0x9400055a;       (* arm_BL (word 5480) *)
  0x913723e0;       (* arm_ADD X0 SP (rvalue (word 3528)) *)
  0x9133c3e1;       (* arm_ADD X1 SP (rvalue (word 3312)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x9400045b;       (* arm_BL (word 4460) *)
  0x913a83e0;       (* arm_ADD X0 SP (rvalue (word 3744)) *)
  0x911f83e1;       (* arm_ADD X1 SP (rvalue (word 2016)) *)
  0x94000553;       (* arm_BL (word 5452) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa94217e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa9431fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0xf94023e8;       (* arm_LDR X8 SP (Immediate_Offset (word 64)) *)
  0xd290842a;       (* arm_MOV X10 (rvalue (word 33825)) *)
  0xf2a8420a;       (* arm_MOVK X10 (word 16912) 16 *)
  0xf2c4210a;       (* arm_MOVK X10 (word 8456) 32 *)
  0xf2e2108a;       (* arm_MOVK X10 (word 4228) 48 *)
  0xab4a0400;       (* arm_ADDS X0 X0 (Shiftedreg X10 LSR 1) *)
  0xba0a0021;       (* arm_ADCS X1 X1 X10 *)
  0xd37ff94a;       (* arm_LSL X10 X10 1 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0xd37ff94a;       (* arm_LSL X10 X10 1 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xd37ff94a;       (* arm_LSL X10 X10 1 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0xd344fd4b;       (* arm_LSR X11 X10 4 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0xd343fd4a;       (* arm_LSR X10 X10 3 *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xd37ff94a;       (* arm_LSL X10 X10 1 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xd37ff94a;       (* arm_LSL X10 X10 1 *)
  0x92401d4a;       (* arm_AND X10 X10 (rvalue (word 255)) *)
  0x9a0a0108;       (* arm_ADC X8 X8 X10 *)
  0xd348fd10;       (* arm_LSR X16 X8 8 *)
  0x93c72108;       (* arm_EXTR X8 X8 X7 8 *)
  0x93c620e7;       (* arm_EXTR X7 X7 X6 8 *)
  0x93c520c6;       (* arm_EXTR X6 X6 X5 8 *)
  0x93c420a5;       (* arm_EXTR X5 X5 X4 8 *)
  0x93c32084;       (* arm_EXTR X4 X4 X3 8 *)
  0x93c22063;       (* arm_EXTR X3 X3 X2 8 *)
  0x93c12042;       (* arm_EXTR X2 X2 X1 8 *)
  0x93c02021;       (* arm_EXTR X1 X1 X0 8 *)
  0xd3481c00;       (* arm_LSL X0 X0 56 *)
  0xa90007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9010fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa90217e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa9031fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0xf90023e8;       (* arm_STR X8 SP (Immediate_Offset (word 64)) *)
  0x9107e3ef;       (* arm_ADD X15 SP (rvalue (word 504)) *)
  0xeb1f021f;       (* arm_CMP X16 XZR *)
  0xa94005e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&0))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90487e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&72))) *)
  0xa94105e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&16))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90587e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&88))) *)
  0xa94205e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&32))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90687e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&104))) *)
  0xa94305e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&48))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90787e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&120))) *)
  0xa94405e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&64))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90887e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&136))) *)
  0xa94505e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&80))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90987e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&152))) *)
  0xa94605e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&96))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90a87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&168))) *)
  0xa94705e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&112))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90b87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&184))) *)
  0xa94805e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&128))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90c87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&200))) *)
  0xa94905e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&144))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90d87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&216))) *)
  0xa94a05e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&160))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90e87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&232))) *)
  0xa94b05e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&176))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa90f87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&248))) *)
  0xa94c05e0;       (* arm_LDP X0 X1 X15 (Immediate_Offset (iword (&192))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa91087e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&264))) *)
  0xf94069e0;       (* arm_LDR X0 X15 (Immediate_Offset (word 208)) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0xf9008fe0;       (* arm_STR X0 SP (Immediate_Offset (word 280)) *)
  0xd2804113;       (* arm_MOV X19 (rvalue (word 520)) *)
  0xd1001673;       (* arm_SUB X19 X19 (rvalue (word 5)) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x940004ec;       (* arm_BL (word 5040) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x940004e9;       (* arm_BL (word 5028) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x940004e6;       (* arm_BL (word 5016) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x940004e3;       (* arm_BL (word 5004) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x940004e0;       (* arm_BL (word 4992) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa94217e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa9431fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0xf94023e8;       (* arm_LDR X8 SP (Immediate_Offset (word 64)) *)
  0xd37bfd10;       (* arm_LSR X16 X8 59 *)
  0x93c7ed08;       (* arm_EXTR X8 X8 X7 59 *)
  0x93c6ece7;       (* arm_EXTR X7 X7 X6 59 *)
  0x93c5ecc6;       (* arm_EXTR X6 X6 X5 59 *)
  0x93c4eca5;       (* arm_EXTR X5 X5 X4 59 *)
  0x93c3ec84;       (* arm_EXTR X4 X4 X3 59 *)
  0x93c2ec63;       (* arm_EXTR X3 X3 X2 59 *)
  0x93c1ec42;       (* arm_EXTR X2 X2 X1 59 *)
  0x93c0ec21;       (* arm_EXTR X1 X1 X0 59 *)
  0xd37be800;       (* arm_LSL X0 X0 5 *)
  0xa90007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9010fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa90217e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa9031fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0xf90023e8;       (* arm_STR X8 SP (Immediate_Offset (word 64)) *)
  0xf1004210;       (* arm_SUBS X16 X16 (rvalue (word 16)) *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xda902610;       (* arm_CNEG X16 X16 Condition_CC *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xaa1f03e1;       (* arm_MOV X1 XZR *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0x9107e3ef;       (* arm_ADD X15 SP (rvalue (word 504)) *)
  0xf100061f;       (* arm_CMP X16 (rvalue (word 1)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1000a1f;       (* arm_CMP X16 (rvalue (word 2)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1000e1f;       (* arm_CMP X16 (rvalue (word 3)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100121f;       (* arm_CMP X16 (rvalue (word 4)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100161f;       (* arm_CMP X16 (rvalue (word 5)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1001a1f;       (* arm_CMP X16 (rvalue (word 6)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1001e1f;       (* arm_CMP X16 (rvalue (word 7)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100221f;       (* arm_CMP X16 (rvalue (word 8)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100261f;       (* arm_CMP X16 (rvalue (word 9)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1002a1f;       (* arm_CMP X16 (rvalue (word 10)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1002e1f;       (* arm_CMP X16 (rvalue (word 11)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100321f;       (* arm_CMP X16 (rvalue (word 12)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100361f;       (* arm_CMP X16 (rvalue (word 13)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1003a1f;       (* arm_CMP X16 (rvalue (word 14)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1003e1f;       (* arm_CMP X16 (rvalue (word 15)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100421f;       (* arm_CMP X16 (rvalue (word 16)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa9130fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&304))) *)
  0xa91417e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&320))) *)
  0xa9151fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&336))) *)
  0xf900b3e8;       (* arm_STR X8 SP (Immediate_Offset (word 352)) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xaa1f03e1;       (* arm_MOV X1 XZR *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0x910a23ef;       (* arm_ADD X15 SP (rvalue (word 648)) *)
  0xf100061f;       (* arm_CMP X16 (rvalue (word 1)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1000a1f;       (* arm_CMP X16 (rvalue (word 2)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1000e1f;       (* arm_CMP X16 (rvalue (word 3)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100121f;       (* arm_CMP X16 (rvalue (word 4)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100161f;       (* arm_CMP X16 (rvalue (word 5)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1001a1f;       (* arm_CMP X16 (rvalue (word 6)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1001e1f;       (* arm_CMP X16 (rvalue (word 7)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100221f;       (* arm_CMP X16 (rvalue (word 8)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100261f;       (* arm_CMP X16 (rvalue (word 9)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1002a1f;       (* arm_CMP X16 (rvalue (word 10)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1002e1f;       (* arm_CMP X16 (rvalue (word 11)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100321f;       (* arm_CMP X16 (rvalue (word 12)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100361f;       (* arm_CMP X16 (rvalue (word 13)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1003a1f;       (* arm_CMP X16 (rvalue (word 14)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1003e1f;       (* arm_CMP X16 (rvalue (word 15)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100421f;       (* arm_CMP X16 (rvalue (word 16)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xa91b07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&432))) *)
  0xa91c0fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&448))) *)
  0xa91d17e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&464))) *)
  0xa91e1fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&480))) *)
  0xf900fbe8;       (* arm_STR X8 SP (Immediate_Offset (word 496)) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xaa1f03e1;       (* arm_MOV X1 XZR *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0x910903ef;       (* arm_ADD X15 SP (rvalue (word 576)) *)
  0xf100061f;       (* arm_CMP X16 (rvalue (word 1)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1000a1f;       (* arm_CMP X16 (rvalue (word 2)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1000e1f;       (* arm_CMP X16 (rvalue (word 3)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100121f;       (* arm_CMP X16 (rvalue (word 4)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100161f;       (* arm_CMP X16 (rvalue (word 5)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1001a1f;       (* arm_CMP X16 (rvalue (word 6)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1001e1f;       (* arm_CMP X16 (rvalue (word 7)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100221f;       (* arm_CMP X16 (rvalue (word 8)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100261f;       (* arm_CMP X16 (rvalue (word 9)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1002a1f;       (* arm_CMP X16 (rvalue (word 10)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1002e1f;       (* arm_CMP X16 (rvalue (word 11)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100321f;       (* arm_CMP X16 (rvalue (word 12)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100361f;       (* arm_CMP X16 (rvalue (word 13)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1003a1f;       (* arm_CMP X16 (rvalue (word 14)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf1003e1f;       (* arm_CMP X16 (rvalue (word 15)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xf100421f;       (* arm_CMP X16 (rvalue (word 16)) *)
  0xa9402dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&0))) *)
  0x9a800140;       (* arm_CSEL X0 X10 X0 Condition_EQ *)
  0x9a810161;       (* arm_CSEL X1 X11 X1 Condition_EQ *)
  0xa9412dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&16))) *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0xa9422dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&32))) *)
  0x9a840144;       (* arm_CSEL X4 X10 X4 Condition_EQ *)
  0x9a850165;       (* arm_CSEL X5 X11 X5 Condition_EQ *)
  0xa9432dea;       (* arm_LDP X10 X11 X15 (Immediate_Offset (iword (&48))) *)
  0x9a860146;       (* arm_CSEL X6 X10 X6 Condition_EQ *)
  0x9a870167;       (* arm_CSEL X7 X11 X7 Condition_EQ *)
  0xf94021ea;       (* arm_LDR X10 X15 (Immediate_Offset (word 64)) *)
  0x9a880148;       (* arm_CSEL X8 X10 X8 Condition_EQ *)
  0x910361ef;       (* arm_ADD X15 X15 (rvalue (word 216)) *)
  0xaa01000a;       (* arm_ORR X10 X0 X1 *)
  0xaa03004b;       (* arm_ORR X11 X2 X3 *)
  0xaa05008c;       (* arm_ORR X12 X4 X5 *)
  0xaa0700cd;       (* arm_ORR X13 X6 X7 *)
  0xaa0b014a;       (* arm_ORR X10 X10 X11 *)
  0xaa0d018c;       (* arm_ORR X12 X12 X13 *)
  0xaa08018c;       (* arm_ORR X12 X12 X8 *)
  0xaa0c014a;       (* arm_ORR X10 X10 X12 *)
  0xeb1f015f;       (* arm_CMP X10 XZR *)
  0x9a9f1231;       (* arm_CSEL X17 X17 XZR Condition_NE *)
  0xca110000;       (* arm_EOR X0 X0 X17 *)
  0xca110021;       (* arm_EOR X1 X1 X17 *)
  0xca110042;       (* arm_EOR X2 X2 X17 *)
  0xca110063;       (* arm_EOR X3 X3 X17 *)
  0xca110084;       (* arm_EOR X4 X4 X17 *)
  0xca1100a5;       (* arm_EOR X5 X5 X17 *)
  0xca1100c6;       (* arm_EOR X6 X6 X17 *)
  0xca1100e7;       (* arm_EOR X7 X7 X17 *)
  0x92402231;       (* arm_AND X17 X17 (rvalue (word 511)) *)
  0xca110108;       (* arm_EOR X8 X8 X17 *)
  0xa91687e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&360))) *)
  0xa9178fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&376))) *)
  0xa91897e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&392))) *)
  0xa9199fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&408))) *)
  0xf900d7e8;       (* arm_STR X8 SP (Immediate_Offset (word 424)) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000089;       (* arm_BL (word 548) *)
  0xb5ff9293;       (* arm_CBNZ X19 (word 2093648) *)
  0xa94487e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&72))) *)
  0xa9000680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&0))) *)
  0xa94587e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&88))) *)
  0xa9010680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&16))) *)
  0xa94687e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&104))) *)
  0xa9020680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&32))) *)
  0xa94787e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&120))) *)
  0xa9030680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&48))) *)
  0xa94887e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&136))) *)
  0xa9040680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&64))) *)
  0xa94987e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&152))) *)
  0xa9050680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&80))) *)
  0xa94a87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&168))) *)
  0xa9060680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&96))) *)
  0xa94b87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&184))) *)
  0xa9070680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&112))) *)
  0xa94c87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&200))) *)
  0xa9080680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&128))) *)
  0xa94d87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&216))) *)
  0xa9090680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&144))) *)
  0xa94e87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&232))) *)
  0xa90a0680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&160))) *)
  0xa94f87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&248))) *)
  0xa90b0680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&176))) *)
  0xa95087e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&264))) *)
  0xa90c0680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&192))) *)
  0xf9408fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 280)) *)
  0xf9006a80;       (* arm_STR X0 X20 (Immediate_Offset (word 208)) *)
  0x913e03ff;       (* arm_ADD SP SP (rvalue (word 3968)) *)
  0xa8c17bf5;       (* arm_LDP X21 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xf940202c;       (* arm_LDR X12 X1 (Immediate_Offset (word 64)) *)
  0xd349fd82;       (* arm_LSR X2 X12 9 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xba02009f;       (* arm_ADCS XZR X4 X2 *)
  0xba1f00bf;       (* arm_ADCS XZR X5 XZR *)
  0xa9411c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0x8a0700c3;       (* arm_AND X3 X6 X7 *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xa9422428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&32))) *)
  0x8a090103;       (* arm_AND X3 X8 X9 *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xa9432c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&48))) *)
  0x8a0b0143;       (* arm_AND X3 X10 X11 *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xb277d983;       (* arm_ORR X3 X12 (rvalue (word 18446744073709551104)) *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9240218c;       (* arm_AND X12 X12 (rvalue (word 511)) *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200c;       (* arm_STR X12 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xf940202e;       (* arm_LDR X14 X1 (Immediate_Offset (word 64)) *)
  0xd349fdcf;       (* arm_LSR X15 X14 9 *)
  0x910005ef;       (* arm_ADD X15 X15 (rvalue (word 1)) *)
  0xd2937ee2;       (* arm_MOV X2 (rvalue (word 39927)) *)
  0xf2add8e2;       (* arm_MOVK X2 (word 28359) 16 *)
  0xf2c91c22;       (* arm_MOVK X2 (word 18657) 32 *)
  0xf2e89202;       (* arm_MOVK X2 (word 17552) 48 *)
  0x9b0f7c46;       (* arm_MUL X6 X2 X15 *)
  0xd2970a23;       (* arm_MOV X3 (rvalue (word 47185)) *)
  0xf2aecc63;       (* arm_MOVK X3 (word 30307) 16 *)
  0xf2c6c8e3;       (* arm_MOVK X3 (word 13895) 32 *)
  0xf2f88943;       (* arm_MOVK X3 (word 50250) 48 *)
  0x9b0f7c67;       (* arm_MUL X7 X3 X15 *)
  0xd28b45e4;       (* arm_MOV X4 (rvalue (word 23087)) *)
  0xf2a11ec4;       (* arm_MOVK X4 (word 2294) 16 *)
  0xf2dfd6e4;       (* arm_MOVK X4 (word 65207) 32 *)
  0xf2f00664;       (* arm_MOVK X4 (word 32819) 48 *)
  0x9b0f7c88;       (* arm_MUL X8 X4 X15 *)
  0xd28d3285;       (* arm_MOV X5 (rvalue (word 27028)) *)
  0xf2a81a05;       (* arm_MOVK X5 (word 16592) 16 *)
  0xf2cf0f85;       (* arm_MOVK X5 (word 30844) 32 *)
  0xf2f5cf25;       (* arm_MOVK X5 (word 44665) 48 *)
  0x9b0f7ca9;       (* arm_MUL X9 X5 X15 *)
  0xd37ef5ea;       (* arm_LSL X10 X15 2 *)
  0x8b0f014a;       (* arm_ADD X10 X10 X15 *)
  0x9bcf7c4d;       (* arm_UMULH X13 X2 X15 *)
  0xab0d00e7;       (* arm_ADDS X7 X7 X13 *)
  0x9bcf7c6d;       (* arm_UMULH X13 X3 X15 *)
  0xba0d0108;       (* arm_ADCS X8 X8 X13 *)
  0x9bcf7c8d;       (* arm_UMULH X13 X4 X15 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0x9bcf7cad;       (* arm_UMULH X13 X5 X15 *)
  0x9a0d014a;       (* arm_ADC X10 X10 X13 *)
  0xa940342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&0))) *)
  0xab0c00c6;       (* arm_ADDS X6 X6 X12 *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xa941342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&16))) *)
  0xba0c0108;       (* arm_ADCS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xa9422c2d;       (* arm_LDP X13 X11 X1 (Immediate_Offset (iword (&32))) *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa943342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&48))) *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xb277d9ce;       (* arm_ORR X14 X14 (rvalue (word 18446744073709551104)) *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xda9f23ef;       (* arm_CSETM X15 Condition_CC *)
  0x8a0f0042;       (* arm_AND X2 X2 X15 *)
  0xeb0200c6;       (* arm_SUBS X6 X6 X2 *)
  0x8a0f0063;       (* arm_AND X3 X3 X15 *)
  0xfa0300e7;       (* arm_SBCS X7 X7 X3 *)
  0x8a0f0084;       (* arm_AND X4 X4 X15 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0x8a0f00a5;       (* arm_AND X5 X5 X15 *)
  0xfa050129;       (* arm_SBCS X9 X9 X5 *)
  0xd28000a2;       (* arm_MOV X2 (rvalue (word 5)) *)
  0x8a0f0042;       (* arm_AND X2 X2 X15 *)
  0xfa02014a;       (* arm_SBCS X10 X10 X2 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f01ce;       (* arm_SBC X14 X14 XZR *)
  0x924021ce;       (* arm_AND X14 X14 (rvalue (word 511)) *)
  0xa9001c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa903340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200e;       (* arm_STR X14 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf73fb;       (* arm_STP X27 X28 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10903ff;       (* arm_SUB SP SP (rvalue (word 576)) *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xaa0103fb;       (* arm_MOV X27 X1 *)
  0xaa0203fc;       (* arm_MOV X28 X2 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x91024361;       (* arm_ADD X1 X27 (rvalue (word 144)) *)
  0x94000564;       (* arm_BL (word 5520) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x91024381;       (* arm_ADD X1 X28 (rvalue (word 144)) *)
  0x94000561;       (* arm_BL (word 5508) *)
  0x9107e3e0;       (* arm_ADD X0 SP (rvalue (word 504)) *)
  0x91024381;       (* arm_ADD X1 X28 (rvalue (word 144)) *)
  0x91012362;       (* arm_ADD X2 X27 (rvalue (word 72)) *)
  0x940002ba;       (* arm_BL (word 2792) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x91024361;       (* arm_ADD X1 X27 (rvalue (word 144)) *)
  0x91012382;       (* arm_ADD X2 X28 (rvalue (word 72)) *)
  0x940002b6;       (* arm_BL (word 2776) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x91000382;       (* arm_ADD X2 X28 (rvalue (word 0)) *)
  0x940002b2;       (* arm_BL (word 2760) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91000362;       (* arm_ADD X2 X27 (rvalue (word 0)) *)
  0x940002ae;       (* arm_BL (word 2744) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910123e2;       (* arm_ADD X2 SP (rvalue (word 72)) *)
  0x940002aa;       (* arm_BL (word 2728) *)
  0x9107e3e0;       (* arm_ADD X0 SP (rvalue (word 504)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x940002a6;       (* arm_BL (word 2712) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x9400075b;       (* arm_BL (word 7532) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000757;       (* arm_BL (word 7516) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x9400053e;       (* arm_BL (word 5368) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x9400053b;       (* arm_BL (word 5356) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000294;       (* arm_BL (word 2640) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x910243e2;       (* arm_ADD X2 SP (rvalue (word 144)) *)
  0x94000290;       (* arm_BL (word 2624) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000745;       (* arm_BL (word 7444) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000741;       (* arm_BL (word 7428) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91024362;       (* arm_ADD X2 X27 (rvalue (word 144)) *)
  0x94000284;       (* arm_BL (word 2576) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910243e2;       (* arm_ADD X2 SP (rvalue (word 144)) *)
  0x94000739;       (* arm_BL (word 7396) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910483e1;       (* arm_ADD X1 SP (rvalue (word 288)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x94000735;       (* arm_BL (word 7380) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000278;       (* arm_BL (word 2528) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91024382;       (* arm_ADD X2 X28 (rvalue (word 144)) *)
  0x94000274;       (* arm_BL (word 2512) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000270;       (* arm_BL (word 2496) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910483e1;       (* arm_ADD X1 SP (rvalue (word 288)) *)
  0x910363e2;       (* arm_ADD X2 SP (rvalue (word 216)) *)
  0x94000725;       (* arm_BL (word 7316) *)
  0xa9490760;       (* arm_LDP X0 X1 X27 (Immediate_Offset (iword (&144))) *)
  0xa94a0f62;       (* arm_LDP X2 X3 X27 (Immediate_Offset (iword (&160))) *)
  0xa94b1764;       (* arm_LDP X4 X5 X27 (Immediate_Offset (iword (&176))) *)
  0xa94c1f66;       (* arm_LDP X6 X7 X27 (Immediate_Offset (iword (&192))) *)
  0xf9406b68;       (* arm_LDR X8 X27 (Immediate_Offset (word 208)) *)
  0xaa010014;       (* arm_ORR X20 X0 X1 *)
  0xaa030055;       (* arm_ORR X21 X2 X3 *)
  0xaa050096;       (* arm_ORR X22 X4 X5 *)
  0xaa0700d7;       (* arm_ORR X23 X6 X7 *)
  0xaa150294;       (* arm_ORR X20 X20 X21 *)
  0xaa1702d6;       (* arm_ORR X22 X22 X23 *)
  0xaa080294;       (* arm_ORR X20 X20 X8 *)
  0xaa160294;       (* arm_ORR X20 X20 X22 *)
  0xeb1f029f;       (* arm_CMP X20 XZR *)
  0x9a9f07f4;       (* arm_CSET X20 Condition_NE *)
  0xa9492f8a;       (* arm_LDP X10 X11 X28 (Immediate_Offset (iword (&144))) *)
  0xa94a378c;       (* arm_LDP X12 X13 X28 (Immediate_Offset (iword (&160))) *)
  0xa94b3f8e;       (* arm_LDP X14 X15 X28 (Immediate_Offset (iword (&176))) *)
  0xa94c4790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&192))) *)
  0xf9406b93;       (* arm_LDR X19 X28 (Immediate_Offset (word 208)) *)
  0xaa0b0155;       (* arm_ORR X21 X10 X11 *)
  0xaa0d0196;       (* arm_ORR X22 X12 X13 *)
  0xaa0f01d7;       (* arm_ORR X23 X14 X15 *)
  0xaa110218;       (* arm_ORR X24 X16 X17 *)
  0xaa1602b5;       (* arm_ORR X21 X21 X22 *)
  0xaa1802f7;       (* arm_ORR X23 X23 X24 *)
  0xaa1302b5;       (* arm_ORR X21 X21 X19 *)
  0xaa1702b5;       (* arm_ORR X21 X21 X23 *)
  0x9a8a1000;       (* arm_CSEL X0 X0 X10 Condition_NE *)
  0x9a8b1021;       (* arm_CSEL X1 X1 X11 Condition_NE *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0x9a8e1084;       (* arm_CSEL X4 X4 X14 Condition_NE *)
  0x9a8f10a5;       (* arm_CSEL X5 X5 X15 Condition_NE *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0x9a931108;       (* arm_CSEL X8 X8 X19 Condition_NE *)
  0xeb1f02bf;       (* arm_CMP X21 XZR *)
  0x9a9f07f5;       (* arm_CSET X21 Condition_NE *)
  0xeb1402bf;       (* arm_CMP X21 X20 *)
  0xa956afea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&360))) *)
  0xa957b7ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&376))) *)
  0xa958bfee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&392))) *)
  0xa959c7f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&408))) *)
  0xf940d7f3;       (* arm_LDR X19 SP (Immediate_Offset (word 424)) *)
  0x9a8a1000;       (* arm_CSEL X0 X0 X10 Condition_NE *)
  0x9a8b1021;       (* arm_CSEL X1 X1 X11 Condition_NE *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0x9a8e1084;       (* arm_CSEL X4 X4 X14 Condition_NE *)
  0x9a8f10a5;       (* arm_CSEL X5 X5 X15 Condition_NE *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0x9a931108;       (* arm_CSEL X8 X8 X19 Condition_NE *)
  0xa91687e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&360))) *)
  0xa9178fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&376))) *)
  0xa91897e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&392))) *)
  0xa9199fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&408))) *)
  0xf900d7e8;       (* arm_STR X8 SP (Immediate_Offset (word 424)) *)
  0xa9405774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&0))) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0x9a803280;       (* arm_CSEL X0 X20 X0 Condition_CC *)
  0x9a8132a1;       (* arm_CSEL X1 X21 X1 Condition_CC *)
  0xa9405794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&0))) *)
  0x9a808280;       (* arm_CSEL X0 X20 X0 Condition_HI *)
  0x9a8182a1;       (* arm_CSEL X1 X21 X1 Condition_HI *)
  0xa9415774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&16))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0x9a823282;       (* arm_CSEL X2 X20 X2 Condition_CC *)
  0x9a8332a3;       (* arm_CSEL X3 X21 X3 Condition_CC *)
  0xa9415794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&16))) *)
  0x9a828282;       (* arm_CSEL X2 X20 X2 Condition_HI *)
  0x9a8382a3;       (* arm_CSEL X3 X21 X3 Condition_HI *)
  0xa9425774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&32))) *)
  0xa94217e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0x9a843284;       (* arm_CSEL X4 X20 X4 Condition_CC *)
  0x9a8532a5;       (* arm_CSEL X5 X21 X5 Condition_CC *)
  0xa9425794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&32))) *)
  0x9a848284;       (* arm_CSEL X4 X20 X4 Condition_HI *)
  0x9a8582a5;       (* arm_CSEL X5 X21 X5 Condition_HI *)
  0xa9435774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&48))) *)
  0xa9431fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0x9a863286;       (* arm_CSEL X6 X20 X6 Condition_CC *)
  0x9a8732a7;       (* arm_CSEL X7 X21 X7 Condition_CC *)
  0xa9435794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&48))) *)
  0x9a868286;       (* arm_CSEL X6 X20 X6 Condition_HI *)
  0x9a8782a7;       (* arm_CSEL X7 X21 X7 Condition_HI *)
  0xf9402374;       (* arm_LDR X20 X27 (Immediate_Offset (word 64)) *)
  0xf94023e8;       (* arm_LDR X8 SP (Immediate_Offset (word 64)) *)
  0x9a883288;       (* arm_CSEL X8 X20 X8 Condition_CC *)
  0xf9402395;       (* arm_LDR X21 X28 (Immediate_Offset (word 64)) *)
  0x9a8882a8;       (* arm_CSEL X8 X21 X8 Condition_HI *)
  0xa944d774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&72))) *)
  0xa9522fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&288))) *)
  0x9a8a328a;       (* arm_CSEL X10 X20 X10 Condition_CC *)
  0x9a8b32ab;       (* arm_CSEL X11 X21 X11 Condition_CC *)
  0xa944d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&72))) *)
  0x9a8a828a;       (* arm_CSEL X10 X20 X10 Condition_HI *)
  0x9a8b82ab;       (* arm_CSEL X11 X21 X11 Condition_HI *)
  0xa945d774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&88))) *)
  0xa95337ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&304))) *)
  0x9a8c328c;       (* arm_CSEL X12 X20 X12 Condition_CC *)
  0x9a8d32ad;       (* arm_CSEL X13 X21 X13 Condition_CC *)
  0xa945d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&88))) *)
  0x9a8c828c;       (* arm_CSEL X12 X20 X12 Condition_HI *)
  0x9a8d82ad;       (* arm_CSEL X13 X21 X13 Condition_HI *)
  0xa946d774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&104))) *)
  0xa9543fee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&320))) *)
  0x9a8e328e;       (* arm_CSEL X14 X20 X14 Condition_CC *)
  0x9a8f32af;       (* arm_CSEL X15 X21 X15 Condition_CC *)
  0xa946d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&104))) *)
  0x9a8e828e;       (* arm_CSEL X14 X20 X14 Condition_HI *)
  0x9a8f82af;       (* arm_CSEL X15 X21 X15 Condition_HI *)
  0xa947d774;       (* arm_LDP X20 X21 X27 (Immediate_Offset (iword (&120))) *)
  0xa95547f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&336))) *)
  0x9a903290;       (* arm_CSEL X16 X20 X16 Condition_CC *)
  0x9a9132b1;       (* arm_CSEL X17 X21 X17 Condition_CC *)
  0xa947d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&120))) *)
  0x9a908290;       (* arm_CSEL X16 X20 X16 Condition_HI *)
  0x9a9182b1;       (* arm_CSEL X17 X21 X17 Condition_HI *)
  0xf9404774;       (* arm_LDR X20 X27 (Immediate_Offset (word 136)) *)
  0xf940b3f3;       (* arm_LDR X19 SP (Immediate_Offset (word 352)) *)
  0x9a933293;       (* arm_CSEL X19 X20 X19 Condition_CC *)
  0xf9404795;       (* arm_LDR X21 X28 (Immediate_Offset (word 136)) *)
  0x9a9382b3;       (* arm_CSEL X19 X21 X19 Condition_HI *)
  0xa9000740;       (* arm_STP X0 X1 X26 (Immediate_Offset (iword (&0))) *)
  0xa9010f42;       (* arm_STP X2 X3 X26 (Immediate_Offset (iword (&16))) *)
  0xa9021744;       (* arm_STP X4 X5 X26 (Immediate_Offset (iword (&32))) *)
  0xa9031f46;       (* arm_STP X6 X7 X26 (Immediate_Offset (iword (&48))) *)
  0xf9002348;       (* arm_STR X8 X26 (Immediate_Offset (word 64)) *)
  0xa95687e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&360))) *)
  0xa9578fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&376))) *)
  0xa95897e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&392))) *)
  0xa9599fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&408))) *)
  0xf940d7e8;       (* arm_LDR X8 SP (Immediate_Offset (word 424)) *)
  0xa904af4a;       (* arm_STP X10 X11 X26 (Immediate_Offset (iword (&72))) *)
  0xa905b74c;       (* arm_STP X12 X13 X26 (Immediate_Offset (iword (&88))) *)
  0xa906bf4e;       (* arm_STP X14 X15 X26 (Immediate_Offset (iword (&104))) *)
  0xa907c750;       (* arm_STP X16 X17 X26 (Immediate_Offset (iword (&120))) *)
  0xf9004753;       (* arm_STR X19 X26 (Immediate_Offset (word 136)) *)
  0xa9090740;       (* arm_STP X0 X1 X26 (Immediate_Offset (iword (&144))) *)
  0xa90a0f42;       (* arm_STP X2 X3 X26 (Immediate_Offset (iword (&160))) *)
  0xa90b1744;       (* arm_STP X4 X5 X26 (Immediate_Offset (iword (&176))) *)
  0xa90c1f46;       (* arm_STP X6 X7 X26 (Immediate_Offset (iword (&192))) *)
  0xf9006b48;       (* arm_STR X8 X26 (Immediate_Offset (word 208)) *)
  0x910903ff;       (* arm_ADD SP SP (rvalue (word 576)) *)
  0xa8c17bfd;       (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf73fb;       (* arm_STP X27 X28 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10803ff;       (* arm_SUB SP SP (rvalue (word 512)) *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xaa0103fb;       (* arm_MOV X27 X1 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x91024361;       (* arm_ADD X1 X27 (rvalue (word 144)) *)
  0x9400046a;       (* arm_BL (word 4520) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x91012361;       (* arm_ADD X1 X27 (rvalue (word 72)) *)
  0x94000467;       (* arm_BL (word 4508) *)
  0xa9401b65;       (* arm_LDP X5 X6 X27 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412367;       (* arm_LDP X7 X8 X27 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9422b69;       (* arm_LDP X9 X10 X27 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xa943336b;       (* arm_LDP X11 X12 X27 (Immediate_Offset (iword (&48))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf940236d;       (* arm_LDR X13 X27 (Immediate_Offset (word 64)) *)
  0xf94023e4;       (* arm_LDR X4 SP (Immediate_Offset (word 64)) *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa90d9be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&216))) *)
  0xa90ea3e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&232))) *)
  0xa90fabe9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&248))) *)
  0xa910b3eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&264))) *)
  0xf9008fed;       (* arm_STR X13 SP (Immediate_Offset (word 280)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9401b65;       (* arm_LDP X5 X6 X27 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xba0400a5;       (* arm_ADCS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412367;       (* arm_LDP X7 X8 X27 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422b69;       (* arm_LDP X9 X10 X27 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xa943336b;       (* arm_LDP X11 X12 X27 (Immediate_Offset (iword (&48))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xba04016b;       (* arm_ADCS X11 X11 X4 *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf940236d;       (* arm_LDR X13 X27 (Immediate_Offset (word 64)) *)
  0xf94023e4;       (* arm_LDR X4 SP (Immediate_Offset (word 64)) *)
  0x9a0401ad;       (* arm_ADC X13 X13 X4 *)
  0xf10801a4;       (* arm_SUBS X4 X13 (rvalue (word 512)) *)
  0xda9f33e4;       (* arm_CSETM X4 Condition_CS *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x92770084;       (* arm_AND X4 X4 (rvalue (word 512)) *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda0401ad;       (* arm_SBC X13 X13 X4 *)
  0xa9091be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa90a23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xf9006bed;       (* arm_STR X13 SP (Immediate_Offset (word 208)) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x910363e2;       (* arm_ADD X2 SP (rvalue (word 216)) *)
  0x94000179;       (* arm_BL (word 1508) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9449b65;       (* arm_LDP X5 X6 X27 (Immediate_Offset (iword (&72))) *)
  0xa9490f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&144))) *)
  0xba0400a5;       (* arm_ADCS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa945a367;       (* arm_LDP X7 X8 X27 (Immediate_Offset (iword (&88))) *)
  0xa94a0f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&160))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa946ab69;       (* arm_LDP X9 X10 X27 (Immediate_Offset (iword (&104))) *)
  0xa94b0f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&176))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xa947b36b;       (* arm_LDP X11 X12 X27 (Immediate_Offset (iword (&120))) *)
  0xa94c0f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&192))) *)
  0xba04016b;       (* arm_ADCS X11 X11 X4 *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf940476d;       (* arm_LDR X13 X27 (Immediate_Offset (word 136)) *)
  0xf9406b64;       (* arm_LDR X4 X27 (Immediate_Offset (word 208)) *)
  0x9a0401ad;       (* arm_ADC X13 X13 X4 *)
  0xf10801a4;       (* arm_SUBS X4 X13 (rvalue (word 512)) *)
  0xda9f33e4;       (* arm_CSETM X4 Condition_CS *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x92770084;       (* arm_AND X4 X4 (rvalue (word 512)) *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda0401ad;       (* arm_SBC X13 X13 X4 *)
  0xa9091be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa90a23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xf9006bed;       (* arm_STR X13 SP (Immediate_Offset (word 208)) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x91000361;       (* arm_ADD X1 X27 (rvalue (word 0)) *)
  0x910123e2;       (* arm_ADD X2 SP (rvalue (word 72)) *)
  0x94000150;       (* arm_BL (word 1344) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x940003f0;       (* arm_BL (word 4032) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x940003ed;       (* arm_BL (word 4020) *)
  0xa9521fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&288))) *)
  0xd2800181;       (* arm_MOV X1 (rvalue (word 12)) *)
  0x9b067c23;       (* arm_MUL X3 X1 X6 *)
  0x9b077c24;       (* arm_MUL X4 X1 X7 *)
  0x9bc67c26;       (* arm_UMULH X6 X1 X6 *)
  0xab060084;       (* arm_ADDS X4 X4 X6 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0xa95327e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&304))) *)
  0x9b087c25;       (* arm_MUL X5 X1 X8 *)
  0x9b097c26;       (* arm_MUL X6 X1 X9 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xa9542fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&320))) *)
  0x9b0a7c27;       (* arm_MUL X7 X1 X10 *)
  0x9b0b7c28;       (* arm_MUL X8 X1 X11 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xba0900e7;       (* arm_ADCS X7 X7 X9 *)
  0x9bcb7c2b;       (* arm_UMULH X11 X1 X11 *)
  0xba0a0108;       (* arm_ADCS X8 X8 X10 *)
  0xa95537ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&336))) *)
  0x9b0c7c29;       (* arm_MUL X9 X1 X12 *)
  0x9b0d7c2a;       (* arm_MUL X10 X1 X13 *)
  0x9bcc7c2c;       (* arm_UMULH X12 X1 X12 *)
  0xba0b0129;       (* arm_ADCS X9 X9 X11 *)
  0x9bcd7c2d;       (* arm_UMULH X13 X1 X13 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xf940b3ee;       (* arm_LDR X14 SP (Immediate_Offset (word 352)) *)
  0x9b0e7c2b;       (* arm_MUL X11 X1 X14 *)
  0x9a0d016b;       (* arm_ADC X11 X11 X13 *)
  0xd2800121;       (* arm_MOV X1 (rvalue (word 9)) *)
  0xa956d7f4;       (* arm_LDP X20 X21 SP (Immediate_Offset (iword (&360))) *)
  0xaa3403f4;       (* arm_MVN X20 X20 *)
  0x9b147c20;       (* arm_MUL X0 X1 X20 *)
  0x9bd47c34;       (* arm_UMULH X20 X1 X20 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xaa3503f5;       (* arm_MVN X21 X21 *)
  0x9b157c20;       (* arm_MUL X0 X1 X21 *)
  0x9bd57c35;       (* arm_UMULH X21 X1 X21 *)
  0xba000084;       (* arm_ADCS X4 X4 X0 *)
  0xa957dff6;       (* arm_LDP X22 X23 SP (Immediate_Offset (iword (&376))) *)
  0xaa3603f6;       (* arm_MVN X22 X22 *)
  0x9b167c20;       (* arm_MUL X0 X1 X22 *)
  0x9bd67c36;       (* arm_UMULH X22 X1 X22 *)
  0xba0000a5;       (* arm_ADCS X5 X5 X0 *)
  0xaa3703f7;       (* arm_MVN X23 X23 *)
  0x9b177c20;       (* arm_MUL X0 X1 X23 *)
  0x9bd77c37;       (* arm_UMULH X23 X1 X23 *)
  0xba0000c6;       (* arm_ADCS X6 X6 X0 *)
  0xa958cff1;       (* arm_LDP X17 X19 SP (Immediate_Offset (iword (&392))) *)
  0xaa3103f1;       (* arm_MVN X17 X17 *)
  0x9b117c20;       (* arm_MUL X0 X1 X17 *)
  0x9bd17c31;       (* arm_UMULH X17 X1 X17 *)
  0xba0000e7;       (* arm_ADCS X7 X7 X0 *)
  0xaa3303f3;       (* arm_MVN X19 X19 *)
  0x9b137c20;       (* arm_MUL X0 X1 X19 *)
  0x9bd37c33;       (* arm_UMULH X19 X1 X19 *)
  0xba000108;       (* arm_ADCS X8 X8 X0 *)
  0xa959c3e2;       (* arm_LDP X2 X16 SP (Immediate_Offset (iword (&408))) *)
  0xaa2203e2;       (* arm_MVN X2 X2 *)
  0x9b027c20;       (* arm_MUL X0 X1 X2 *)
  0x9bc27c22;       (* arm_UMULH X2 X1 X2 *)
  0xba000129;       (* arm_ADCS X9 X9 X0 *)
  0xaa3003f0;       (* arm_MVN X16 X16 *)
  0x9b107c20;       (* arm_MUL X0 X1 X16 *)
  0x9bd07c30;       (* arm_UMULH X16 X1 X16 *)
  0xba00014a;       (* arm_ADCS X10 X10 X0 *)
  0xf940d7e0;       (* arm_LDR X0 SP (Immediate_Offset (word 424)) *)
  0xd2402000;       (* arm_EOR X0 X0 (rvalue (word 511)) *)
  0x9b007c20;       (* arm_MUL X0 X1 X0 *)
  0x9a00016b;       (* arm_ADC X11 X11 X0 *)
  0xab140084;       (* arm_ADDS X4 X4 X20 *)
  0xba1500a5;       (* arm_ADCS X5 X5 X21 *)
  0x8a05008f;       (* arm_AND X15 X4 X5 *)
  0xba1600c6;       (* arm_ADCS X6 X6 X22 *)
  0x8a0601ef;       (* arm_AND X15 X15 X6 *)
  0xba1700e7;       (* arm_ADCS X7 X7 X23 *)
  0x8a0701ef;       (* arm_AND X15 X15 X7 *)
  0xba110108;       (* arm_ADCS X8 X8 X17 *)
  0x8a0801ef;       (* arm_AND X15 X15 X8 *)
  0xba130129;       (* arm_ADCS X9 X9 X19 *)
  0x8a0901ef;       (* arm_AND X15 X15 X9 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0x9a10016b;       (* arm_ADC X11 X11 X16 *)
  0xd349fd6c;       (* arm_LSR X12 X11 9 *)
  0xb277d96b;       (* arm_ORR X11 X11 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba0c007f;       (* arm_ADCS XZR X3 X12 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xba0c0063;       (* arm_ADCS X3 X3 X12 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0x9240216b;       (* arm_AND X11 X11 (rvalue (word 511)) *)
  0xa91693e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&360))) *)
  0xa9179be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&376))) *)
  0xa918a3e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&392))) *)
  0xa919abe9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&408))) *)
  0xf900d7eb;       (* arm_STR X11 SP (Immediate_Offset (word 424)) *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa94b2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xa94c33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf9406bed;       (* arm_LDR X13 SP (Immediate_Offset (word 208)) *)
  0xf94023e4;       (* arm_LDR X4 SP (Immediate_Offset (word 64)) *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa9091be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa90a23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xf9006bed;       (* arm_STR X13 SP (Immediate_Offset (word 208)) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x9400035d;       (* arm_BL (word 3444) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x910363e2;       (* arm_ADD X2 SP (rvalue (word 216)) *)
  0x940000b6;       (* arm_BL (word 728) *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa9448fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&72))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa9458fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&88))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa94b2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xa9468fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&104))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xa94c33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xa9478fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&120))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf9406bed;       (* arm_LDR X13 SP (Immediate_Offset (word 208)) *)
  0xf94047e4;       (* arm_LDR X4 SP (Immediate_Offset (word 136)) *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa9091b45;       (* arm_STP X5 X6 X26 (Immediate_Offset (iword (&144))) *)
  0xa90a2347;       (* arm_STP X7 X8 X26 (Immediate_Offset (iword (&160))) *)
  0xa90b2b49;       (* arm_STP X9 X10 X26 (Immediate_Offset (iword (&176))) *)
  0xa90c334b;       (* arm_STP X11 X12 X26 (Immediate_Offset (iword (&192))) *)
  0xf9006b4d;       (* arm_STR X13 X26 (Immediate_Offset (word 208)) *)
  0xa9521fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&288))) *)
  0xd37ef4c3;       (* arm_LSL X3 X6 2 *)
  0x93c6f8e4;       (* arm_EXTR X4 X7 X6 62 *)
  0xa95327e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&304))) *)
  0x93c7f905;       (* arm_EXTR X5 X8 X7 62 *)
  0x93c8f926;       (* arm_EXTR X6 X9 X8 62 *)
  0xa9542fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&320))) *)
  0x93c9f947;       (* arm_EXTR X7 X10 X9 62 *)
  0x93caf968;       (* arm_EXTR X8 X11 X10 62 *)
  0xa95537ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&336))) *)
  0x93cbf989;       (* arm_EXTR X9 X12 X11 62 *)
  0x93ccf9aa;       (* arm_EXTR X10 X13 X12 62 *)
  0xf940b3ee;       (* arm_LDR X14 SP (Immediate_Offset (word 352)) *)
  0x93cdf9cb;       (* arm_EXTR X11 X14 X13 62 *)
  0xa95687e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&360))) *)
  0xaa2003e0;       (* arm_MVN X0 X0 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xfa010084;       (* arm_SBCS X4 X4 X1 *)
  0xa95787e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&376))) *)
  0xfa0000a5;       (* arm_SBCS X5 X5 X0 *)
  0x8a05008f;       (* arm_AND X15 X4 X5 *)
  0xfa0100c6;       (* arm_SBCS X6 X6 X1 *)
  0x8a0601ef;       (* arm_AND X15 X15 X6 *)
  0xa95887e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&392))) *)
  0xfa0000e7;       (* arm_SBCS X7 X7 X0 *)
  0x8a0701ef;       (* arm_AND X15 X15 X7 *)
  0xfa010108;       (* arm_SBCS X8 X8 X1 *)
  0x8a0801ef;       (* arm_AND X15 X15 X8 *)
  0xa95987e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&408))) *)
  0xfa000129;       (* arm_SBCS X9 X9 X0 *)
  0x8a0901ef;       (* arm_AND X15 X15 X9 *)
  0xfa01014a;       (* arm_SBCS X10 X10 X1 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xf940d7e0;       (* arm_LDR X0 SP (Immediate_Offset (word 424)) *)
  0xd2402000;       (* arm_EOR X0 X0 (rvalue (word 511)) *)
  0x9a00016b;       (* arm_ADC X11 X11 X0 *)
  0xd349fd6c;       (* arm_LSR X12 X11 9 *)
  0xb277d96b;       (* arm_ORR X11 X11 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba0c007f;       (* arm_ADCS XZR X3 X12 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xba0c0063;       (* arm_ADCS X3 X3 X12 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0x9240216b;       (* arm_AND X11 X11 (rvalue (word 511)) *)
  0xa9001343;       (* arm_STP X3 X4 X26 (Immediate_Offset (iword (&0))) *)
  0xa9011b45;       (* arm_STP X5 X6 X26 (Immediate_Offset (iword (&16))) *)
  0xa9022347;       (* arm_STP X7 X8 X26 (Immediate_Offset (iword (&32))) *)
  0xa9032b49;       (* arm_STP X9 X10 X26 (Immediate_Offset (iword (&48))) *)
  0xf900234b;       (* arm_STR X11 X26 (Immediate_Offset (word 64)) *)
  0xa94d9fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&216))) *)
  0xd37ff8c3;       (* arm_LSL X3 X6 1 *)
  0xab060063;       (* arm_ADDS X3 X3 X6 *)
  0x93c6fce4;       (* arm_EXTR X4 X7 X6 63 *)
  0xba070084;       (* arm_ADCS X4 X4 X7 *)
  0xa94ea7e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&232))) *)
  0x93c7fd05;       (* arm_EXTR X5 X8 X7 63 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x93c8fd26;       (* arm_EXTR X6 X9 X8 63 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0xa94fafea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&248))) *)
  0x93c9fd47;       (* arm_EXTR X7 X10 X9 63 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0x93cafd68;       (* arm_EXTR X8 X11 X10 63 *)
  0xba0b0108;       (* arm_ADCS X8 X8 X11 *)
  0xa950b7ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&264))) *)
  0x93cbfd89;       (* arm_EXTR X9 X12 X11 63 *)
  0xba0c0129;       (* arm_ADCS X9 X9 X12 *)
  0x93ccfdaa;       (* arm_EXTR X10 X13 X12 63 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xf9408fee;       (* arm_LDR X14 SP (Immediate_Offset (word 280)) *)
  0x93cdfdcb;       (* arm_EXTR X11 X14 X13 63 *)
  0x9a0e016b;       (* arm_ADC X11 X11 X14 *)
  0xa94057f4;       (* arm_LDP X20 X21 SP (Immediate_Offset (iword (&0))) *)
  0xaa3403f4;       (* arm_MVN X20 X20 *)
  0xd37df280;       (* arm_LSL X0 X20 3 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xaa3503f5;       (* arm_MVN X21 X21 *)
  0x93d4f6a0;       (* arm_EXTR X0 X21 X20 61 *)
  0xba000084;       (* arm_ADCS X4 X4 X0 *)
  0xa9415ff6;       (* arm_LDP X22 X23 SP (Immediate_Offset (iword (&16))) *)
  0xaa3603f6;       (* arm_MVN X22 X22 *)
  0x93d5f6c0;       (* arm_EXTR X0 X22 X21 61 *)
  0xba0000a5;       (* arm_ADCS X5 X5 X0 *)
  0x8a05008f;       (* arm_AND X15 X4 X5 *)
  0xaa3703f7;       (* arm_MVN X23 X23 *)
  0x93d6f6e0;       (* arm_EXTR X0 X23 X22 61 *)
  0xba0000c6;       (* arm_ADCS X6 X6 X0 *)
  0x8a0601ef;       (* arm_AND X15 X15 X6 *)
  0xa94257f4;       (* arm_LDP X20 X21 SP (Immediate_Offset (iword (&32))) *)
  0xaa3403f4;       (* arm_MVN X20 X20 *)
  0x93d7f680;       (* arm_EXTR X0 X20 X23 61 *)
  0xba0000e7;       (* arm_ADCS X7 X7 X0 *)
  0x8a0701ef;       (* arm_AND X15 X15 X7 *)
  0xaa3503f5;       (* arm_MVN X21 X21 *)
  0x93d4f6a0;       (* arm_EXTR X0 X21 X20 61 *)
  0xba000108;       (* arm_ADCS X8 X8 X0 *)
  0x8a0801ef;       (* arm_AND X15 X15 X8 *)
  0xa9435ff6;       (* arm_LDP X22 X23 SP (Immediate_Offset (iword (&48))) *)
  0xaa3603f6;       (* arm_MVN X22 X22 *)
  0x93d5f6c0;       (* arm_EXTR X0 X22 X21 61 *)
  0xba000129;       (* arm_ADCS X9 X9 X0 *)
  0x8a0901ef;       (* arm_AND X15 X15 X9 *)
  0xaa3703f7;       (* arm_MVN X23 X23 *)
  0x93d6f6e0;       (* arm_EXTR X0 X23 X22 61 *)
  0xba00014a;       (* arm_ADCS X10 X10 X0 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xf94023e0;       (* arm_LDR X0 SP (Immediate_Offset (word 64)) *)
  0xd2402000;       (* arm_EOR X0 X0 (rvalue (word 511)) *)
  0x93d7f400;       (* arm_EXTR X0 X0 X23 61 *)
  0x9a00016b;       (* arm_ADC X11 X11 X0 *)
  0xd349fd6c;       (* arm_LSR X12 X11 9 *)
  0xb277d96b;       (* arm_ORR X11 X11 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba0c007f;       (* arm_ADCS XZR X3 X12 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xba0c0063;       (* arm_ADCS X3 X3 X12 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0x9240216b;       (* arm_AND X11 X11 (rvalue (word 511)) *)
  0xa9049343;       (* arm_STP X3 X4 X26 (Immediate_Offset (iword (&72))) *)
  0xa9059b45;       (* arm_STP X5 X6 X26 (Immediate_Offset (iword (&88))) *)
  0xa906a347;       (* arm_STP X7 X8 X26 (Immediate_Offset (iword (&104))) *)
  0xa907ab49;       (* arm_STP X9 X10 X26 (Immediate_Offset (iword (&120))) *)
  0xf900474b;       (* arm_STR X11 X26 (Immediate_Offset (word 136)) *)
  0x910803ff;       (* arm_ADD SP SP (rvalue (word 512)) *)
  0xa8c17bfd;       (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10143ff;       (* arm_SUB SP SP (rvalue (word 80)) *)
  0x3dc00046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 0)) *)
  0xa941442a;       (* arm_LDP X10 X17 X1 (Immediate_Offset (iword (&16))) *)
  0x3dc00024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 0)) *)
  0x3dc00850;       (* arm_LDR Q16 X2 (Immediate_Offset (word 32)) *)
  0xa9415045;       (* arm_LDP X5 X20 X2 (Immediate_Offset (iword (&16))) *)
  0x3dc00822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 32)) *)
  0x6f00e5ff;       (* arm_MOVI Q31 (word 4294967295) *)
  0x4e8658d1;       (* arm_UZP2 Q17 Q6 Q6 32 *)
  0x4ea008c7;       (* arm_REV64_VEC Q7 Q6 32 *)
  0xa940542f;       (* arm_LDP X15 X21 X1 (Immediate_Offset (iword (&0))) *)
  0x0ea128d9;       (* arm_XTN Q25 Q6 32 *)
  0x0ea12896;       (* arm_XTN Q22 Q4 32 *)
  0xeb11014e;       (* arm_SUBS X14 X10 X17 *)
  0x4ea49ce7;       (* arm_MUL_VEC Q7 Q7 Q4 32 128 *)
  0xda9f23e8;       (* arm_CSETM X8 Condition_CC *)
  0x4ea00a03;       (* arm_REV64_VEC Q3 Q16 32 *)
  0x0ea12a01;       (* arm_XTN Q1 Q16 32 *)
  0xa940404d;       (* arm_LDP X13 X16 X2 (Immediate_Offset (iword (&0))) *)
  0x9b057d5a;       (* arm_MUL X26 X10 X5 *)
  0x4e905a10;       (* arm_UZP2 Q16 Q16 Q16 32 *)
  0x6ea028fa;       (* arm_UADDLP Q26 Q7 32 *)
  0xda8e25c4;       (* arm_CNEG X4 X14 Condition_CC *)
  0xeb1501f8;       (* arm_SUBS X24 X15 X21 *)
  0x0ea12845;       (* arm_XTN Q5 Q2 32 *)
  0x4ea29c7c;       (* arm_MUL_VEC Q28 Q3 Q2 32 128 *)
  0x4f60575a;       (* arm_SHL_VEC Q26 Q26 32 64 128 *)
  0x9b147e36;       (* arm_MUL X22 X17 X20 *)
  0x2eb9c2d4;       (* arm_UMULL_VEC Q20 Q22 Q25 32 *)
  0x4e845886;       (* arm_UZP2 Q6 Q4 Q4 32 *)
  0x2eb1c2d2;       (* arm_UMULL_VEC Q18 Q22 Q17 32 *)
  0x4e825844;       (* arm_UZP2 Q4 Q2 Q2 32 *)
  0xda98270e;       (* arm_CNEG X14 X24 Condition_CC *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0x9bd47e2b;       (* arm_UMULH X11 X17 X20 *)
  0x6f601692;       (* arm_USRA_VEC Q18 Q20 32 64 128 *)
  0x6ea02b87;       (* arm_UADDLP Q7 Q28 32 *)
  0xeb0d0213;       (* arm_SUBS X19 X16 X13 *)
  0x2eb982da;       (* arm_UMLAL_VEC Q26 Q22 Q25 32 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0x4f6054fc;       (* arm_SHL_VEC Q28 Q7 32 64 128 *)
  0x2ea1c0a7;       (* arm_UMULL_VEC Q7 Q5 Q1 32 *)
  0x2eb0c0be;       (* arm_UMULL_VEC Q30 Q5 Q16 32 *)
  0xda8720e6;       (* arm_CINV X6 X7 Condition_CC *)
  0x9b137dd9;       (* arm_MUL X25 X14 X19 *)
  0x2ea180bc;       (* arm_UMLAL_VEC Q28 Q5 Q1 32 *)
  0x2eb1c0d5;       (* arm_UMULL_VEC Q21 Q6 Q17 32 *)
  0x9bd37dce;       (* arm_UMULH X14 X14 X19 *)
  0x6f6014fe;       (* arm_USRA_VEC Q30 Q7 32 64 128 *)
  0xeb050289;       (* arm_SUBS X9 X20 X5 *)
  0x4e3f1e5d;       (* arm_AND_VEC Q29 Q18 Q31 128 *)
  0xda882117;       (* arm_CINV X23 X8 Condition_CC *)
  0x4e183f48;       (* arm_UMOV X8 Q26 1 8 *)
  0xda89252c;       (* arm_CNEG X12 X9 Condition_CC *)
  0x6f601655;       (* arm_USRA_VEC Q21 Q18 32 64 128 *)
  0x2eb980dd;       (* arm_UMLAL_VEC Q29 Q6 Q25 32 *)
  0x9b0c7c98;       (* arm_MUL X24 X4 X12 *)
  0x2eb0c092;       (* arm_UMULL_VEC Q18 Q4 Q16 32 *)
  0x6f00e5f9;       (* arm_MOVI Q25 (word 4294967295) *)
  0xca0601c9;       (* arm_EOR X9 X14 X6 *)
  0x4e391fc7;       (* arm_AND_VEC Q7 Q30 Q25 128 *)
  0x6f6017b5;       (* arm_USRA_VEC Q21 Q29 32 64 128 *)
  0x9bc57d47;       (* arm_UMULH X7 X10 X5 *)
  0x6f6017d2;       (* arm_USRA_VEC Q18 Q30 32 64 128 *)
  0x2ea18087;       (* arm_UMLAL_VEC Q7 Q4 Q1 32 *)
  0x4e083eb3;       (* arm_UMOV X19 Q21 0 8 *)
  0x9bcc7c83;       (* arm_UMULH X3 X4 X12 *)
  0x4e183eae;       (* arm_UMOV X14 Q21 1 8 *)
  0x6f6014f2;       (* arm_USRA_VEC Q18 Q7 32 64 128 *)
  0xab130104;       (* arm_ADDS X4 X8 X19 *)
  0x4e083f48;       (* arm_UMOV X8 Q26 0 8 *)
  0xba0e0353;       (* arm_ADCS X19 X26 X14 *)
  0xba0702ce;       (* arm_ADCS X14 X22 X7 *)
  0x9a1f016c;       (* arm_ADC X12 X11 XZR *)
  0xab08008b;       (* arm_ADDS X11 X4 X8 *)
  0xba04027a;       (* arm_ADCS X26 X19 X4 *)
  0xba1301d6;       (* arm_ADCS X22 X14 X19 *)
  0xca170304;       (* arm_EOR X4 X24 X23 *)
  0xba0e018e;       (* arm_ADCS X14 X12 X14 *)
  0xca060327;       (* arm_EOR X7 X25 X6 *)
  0x9a0c03f9;       (* arm_ADC X25 XZR X12 *)
  0xca170073;       (* arm_EOR X19 X3 X23 *)
  0xab080343;       (* arm_ADDS X3 X26 X8 *)
  0xba0b02d8;       (* arm_ADCS X24 X22 X11 *)
  0xba1a01cc;       (* arm_ADCS X12 X14 X26 *)
  0xba160336;       (* arm_ADCS X22 X25 X22 *)
  0xba0e03fa;       (* arm_ADCS X26 XZR X14 *)
  0x9a1903ee;       (* arm_ADC X14 XZR X25 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba0402d6;       (* arm_ADCS X22 X22 X4 *)
  0xba130353;       (* arm_ADCS X19 X26 X19 *)
  0x9a1701d9;       (* arm_ADC X25 X14 X23 *)
  0xeb1102ae;       (* arm_SUBS X14 X21 X17 *)
  0xda8e25d7;       (* arm_CNEG X23 X14 Condition_CC *)
  0xda9f23fa;       (* arm_CSETM X26 Condition_CC *)
  0xeb100284;       (* arm_SUBS X4 X20 X16 *)
  0xda84248e;       (* arm_CNEG X14 X4 Condition_CC *)
  0xda9a2344;       (* arm_CINV X4 X26 Condition_CC *)
  0xb10004df;       (* arm_CMN X6 (rvalue (word 1)) *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b0e7ee7;       (* arm_MUL X7 X23 X14 *)
  0xba090069;       (* arm_ADCS X9 X3 X9 *)
  0xba06031a;       (* arm_ADCS X26 X24 X6 *)
  0x9bce7ee3;       (* arm_UMULH X3 X23 X14 *)
  0xba06018e;       (* arm_ADCS X14 X12 X6 *)
  0xba0602d6;       (* arm_ADCS X22 X22 X6 *)
  0xba06026c;       (* arm_ADCS X12 X19 X6 *)
  0x93c8dd78;       (* arm_EXTR X24 X11 X8 55 *)
  0x9a060326;       (* arm_ADC X6 X25 X6 *)
  0xeb1101f3;       (* arm_SUBS X19 X15 X17 *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xda932677;       (* arm_CNEG X23 X19 Condition_CC *)
  0xeb0d0293;       (* arm_SUBS X19 X20 X13 *)
  0xd377d919;       (* arm_LSL X25 X8 9 *)
  0xca0400e8;       (* arm_EOR X8 X7 X4 *)
  0xda932674;       (* arm_CNEG X20 X19 Condition_CC *)
  0x9bd47ee7;       (* arm_UMULH X7 X23 X20 *)
  0xda912233;       (* arm_CINV X19 X17 Condition_CC *)
  0xeb0a01f1;       (* arm_SUBS X17 X15 X10 *)
  0xda9f23ef;       (* arm_CSETM X15 Condition_CC *)
  0xa90263f9;       (* arm_STP X25 X24 SP (Immediate_Offset (iword (&32))) *)
  0xda912638;       (* arm_CNEG X24 X17 Condition_CC *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xeb0d00b9;       (* arm_SUBS X25 X5 X13 *)
  0xda99272d;       (* arm_CNEG X13 X25 Condition_CC *)
  0xda8f21ef;       (* arm_CINV X15 X15 Condition_CC *)
  0x9b0d7f19;       (* arm_MUL X25 X24 X13 *)
  0xeb0a02b5;       (* arm_SUBS X21 X21 X10 *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xda9526b1;       (* arm_CNEG X17 X21 Condition_CC *)
  0xeb1000b5;       (* arm_SUBS X21 X5 X16 *)
  0x9bcd7f0d;       (* arm_UMULH X13 X24 X13 *)
  0xda9722ea;       (* arm_CINV X10 X23 Condition_CC *)
  0xda9526b7;       (* arm_CNEG X23 X21 Condition_CC *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0xca040075;       (* arm_EOR X21 X3 X4 *)
  0xba1502d5;       (* arm_ADCS X21 X22 X21 *)
  0xca130285;       (* arm_EOR X5 X20 X19 *)
  0xba040198;       (* arm_ADCS X24 X12 X4 *)
  0x9b177e2c;       (* arm_MUL X12 X17 X23 *)
  0xca0f0328;       (* arm_EOR X8 X25 X15 *)
  0x9a0400d9;       (* arm_ADC X25 X6 X4 *)
  0xb10005ff;       (* arm_CMN X15 (rvalue (word 1)) *)
  0xba080126;       (* arm_ADCS X6 X9 X8 *)
  0xa9432054;       (* arm_LDP X20 X8 X2 (Immediate_Offset (iword (&48))) *)
  0xca0f01a9;       (* arm_EOR X9 X13 X15 *)
  0xba090344;       (* arm_ADCS X4 X26 X9 *)
  0x9bd77e3a;       (* arm_UMULH X26 X17 X23 *)
  0xa9433431;       (* arm_LDP X17 X13 X1 (Immediate_Offset (iword (&48))) *)
  0xba0f01c9;       (* arm_ADCS X9 X14 X15 *)
  0xba0f02b0;       (* arm_ADCS X16 X21 X15 *)
  0xba0f030e;       (* arm_ADCS X14 X24 X15 *)
  0xca1300f5;       (* arm_EOR X21 X7 X19 *)
  0x9b147e37;       (* arm_MUL X23 X17 X20 *)
  0x9a0f0338;       (* arm_ADC X24 X25 X15 *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xba050087;       (* arm_ADCS X7 X4 X5 *)
  0xba150129;       (* arm_ADCS X9 X9 X21 *)
  0x9bc87da3;       (* arm_UMULH X3 X13 X8 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0xba1301d6;       (* arm_ADCS X22 X14 X19 *)
  0xca0a0185;       (* arm_EOR X5 X12 X10 *)
  0x9a13030c;       (* arm_ADC X12 X24 X19 *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xba0500f3;       (* arm_ADCS X19 X7 X5 *)
  0xca0a034e;       (* arm_EOR X14 X26 X10 *)
  0x4e183f87;       (* arm_UMOV X7 Q28 1 8 *)
  0xba0e0138;       (* arm_ADCS X24 X9 X14 *)
  0x93c6de64;       (* arm_EXTR X4 X19 X6 55 *)
  0x9bd47e2f;       (* arm_UMULH X15 X17 X20 *)
  0x4e183e4e;       (* arm_UMOV X14 Q18 1 8 *)
  0xd377fe69;       (* arm_LSR X9 X19 55 *)
  0xba0a0205;       (* arm_ADCS X5 X16 X10 *)
  0x4e083e50;       (* arm_UMOV X16 Q18 0 8 *)
  0xba0a02d3;       (* arm_ADCS X19 X22 X10 *)
  0xf90023e9;       (* arm_STR X9 SP (Immediate_Offset (word 64)) *)
  0x93cbdcd9;       (* arm_EXTR X25 X6 X11 55 *)
  0x9a0a0195;       (* arm_ADC X21 X12 X10 *)
  0xeb0d023a;       (* arm_SUBS X26 X17 X13 *)
  0xa90313f9;       (* arm_STP X25 X4 SP (Immediate_Offset (iword (&48))) *)
  0xa90157f3;       (* arm_STP X19 X21 SP (Immediate_Offset (iword (&16))) *)
  0xda9f23e6;       (* arm_CSETM X6 Condition_CC *)
  0xda9a2744;       (* arm_CNEG X4 X26 Condition_CC *)
  0x9b087db3;       (* arm_MUL X19 X13 X8 *)
  0xeb14010b;       (* arm_SUBS X11 X8 X20 *)
  0xa90017f8;       (* arm_STP X24 X5 SP (Immediate_Offset (iword (&0))) *)
  0xa9422835;       (* arm_LDP X21 X10 X1 (Immediate_Offset (iword (&32))) *)
  0xda8620cc;       (* arm_CINV X12 X6 Condition_CC *)
  0xda8b2566;       (* arm_CNEG X6 X11 Condition_CC *)
  0x4e083f89;       (* arm_UMOV X9 Q28 0 8 *)
  0x9bc67c99;       (* arm_UMULH X25 X4 X6 *)
  0xab1000f6;       (* arm_ADDS X22 X7 X16 *)
  0xa9421450;       (* arm_LDP X16 X5 X2 (Immediate_Offset (iword (&32))) *)
  0xba0e02ee;       (* arm_ADCS X14 X23 X14 *)
  0xba0f026b;       (* arm_ADCS X11 X19 X15 *)
  0x9a1f0078;       (* arm_ADC X24 X3 XZR *)
  0xab0902c3;       (* arm_ADDS X3 X22 X9 *)
  0xba1601cf;       (* arm_ADCS X15 X14 X22 *)
  0x9b067c96;       (* arm_MUL X22 X4 X6 *)
  0xba0e0166;       (* arm_ADCS X6 X11 X14 *)
  0xba0b0304;       (* arm_ADCS X4 X24 X11 *)
  0xca0c032e;       (* arm_EOR X14 X25 X12 *)
  0x9a1803fa;       (* arm_ADC X26 XZR X24 *)
  0xeb0a02a7;       (* arm_SUBS X7 X21 X10 *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xda8724f3;       (* arm_CNEG X19 X7 Condition_CC *)
  0xeb1000b8;       (* arm_SUBS X24 X5 X16 *)
  0xda98270b;       (* arm_CNEG X11 X24 Condition_CC *)
  0xda9722e7;       (* arm_CINV X7 X23 Condition_CC *)
  0xab0901f9;       (* arm_ADDS X25 X15 X9 *)
  0xca0c02d7;       (* arm_EOR X23 X22 X12 *)
  0xba0300d6;       (* arm_ADCS X22 X6 X3 *)
  0x9b0b7e78;       (* arm_MUL X24 X19 X11 *)
  0xba0f008f;       (* arm_ADCS X15 X4 X15 *)
  0xba060346;       (* arm_ADCS X6 X26 X6 *)
  0x9bcb7e73;       (* arm_UMULH X19 X19 X11 *)
  0xba0403eb;       (* arm_ADCS X11 XZR X4 *)
  0x9a1a03fa;       (* arm_ADC X26 XZR X26 *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xba1700c4;       (* arm_ADCS X4 X6 X23 *)
  0xca070306;       (* arm_EOR X6 X24 X7 *)
  0xba0e016e;       (* arm_ADCS X14 X11 X14 *)
  0x9a0c035a;       (* arm_ADC X26 X26 X12 *)
  0xeb0d014b;       (* arm_SUBS X11 X10 X13 *)
  0xda8b256c;       (* arm_CNEG X12 X11 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xca070273;       (* arm_EOR X19 X19 X7 *)
  0xeb050118;       (* arm_SUBS X24 X8 X5 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0x9b187d97;       (* arm_MUL X23 X12 X24 *)
  0xba130339;       (* arm_ADCS X25 X25 X19 *)
  0xba0702c6;       (* arm_ADCS X6 X22 X7 *)
  0x9bd87d93;       (* arm_UMULH X19 X12 X24 *)
  0xba0701f6;       (* arm_ADCS X22 X15 X7 *)
  0xba07008c;       (* arm_ADCS X12 X4 X7 *)
  0xca0b02f8;       (* arm_EOR X24 X23 X11 *)
  0xba0701c4;       (* arm_ADCS X4 X14 X7 *)
  0x9a07035a;       (* arm_ADC X26 X26 X7 *)
  0xca0b0273;       (* arm_EOR X19 X19 X11 *)
  0xeb1102ae;       (* arm_SUBS X14 X21 X17 *)
  0xda8e25c7;       (* arm_CNEG X7 X14 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb100297;       (* arm_SUBS X23 X20 X16 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xda9726f7;       (* arm_CNEG X23 X23 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba1802d6;       (* arm_ADCS X22 X22 X24 *)
  0x9b177cf8;       (* arm_MUL X24 X7 X23 *)
  0xba13018f;       (* arm_ADCS X15 X12 X19 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a0b0353;       (* arm_ADC X19 X26 X11 *)
  0x9bd77cfa;       (* arm_UMULH X26 X7 X23 *)
  0xeb0d02a7;       (* arm_SUBS X7 X21 X13 *)
  0xca0e030b;       (* arm_EOR X11 X24 X14 *)
  0xda8724f7;       (* arm_CNEG X23 X7 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb100107;       (* arm_SUBS X7 X8 X16 *)
  0xda8724e7;       (* arm_CNEG X7 X7 Condition_CC *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xca0e035a;       (* arm_EOR X26 X26 X14 *)
  0xba0b032b;       (* arm_ADCS X11 X25 X11 *)
  0x9b077ef9;       (* arm_MUL X25 X23 X7 *)
  0xba1a00da;       (* arm_ADCS X26 X6 X26 *)
  0xba0e02c6;       (* arm_ADCS X6 X22 X14 *)
  0xba0e01f8;       (* arm_ADCS X24 X15 X14 *)
  0x9bc77ef7;       (* arm_UMULH X23 X23 X7 *)
  0xba0e0084;       (* arm_ADCS X4 X4 X14 *)
  0x9a0e0276;       (* arm_ADC X22 X19 X14 *)
  0xca0c032e;       (* arm_EOR X14 X25 X12 *)
  0xca0c02e7;       (* arm_EOR X7 X23 X12 *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xba0e034e;       (* arm_ADCS X14 X26 X14 *)
  0xa9406453;       (* arm_LDP X19 X25 X2 (Immediate_Offset (iword (&0))) *)
  0xa9415c4f;       (* arm_LDP X15 X23 X2 (Immediate_Offset (iword (&16))) *)
  0xba0700da;       (* arm_ADCS X26 X6 X7 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0xba0c0087;       (* arm_ADCS X7 X4 X12 *)
  0x9a0c02c4;       (* arm_ADC X4 X22 X12 *)
  0xeb100273;       (* arm_SUBS X19 X19 X16 *)
  0xa9405830;       (* arm_LDP X16 X22 X1 (Immediate_Offset (iword (&0))) *)
  0xfa050326;       (* arm_SBCS X6 X25 X5 *)
  0xa941642c;       (* arm_LDP X12 X25 X1 (Immediate_Offset (iword (&16))) *)
  0xfa1401ef;       (* arm_SBCS X15 X15 X20 *)
  0xfa0802e8;       (* arm_SBCS X8 X23 X8 *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb1002b5;       (* arm_SUBS X21 X21 X16 *)
  0xca170270;       (* arm_EOR X16 X19 X23 *)
  0xfa160153;       (* arm_SBCS X19 X10 X22 *)
  0xca1700d6;       (* arm_EOR X22 X6 X23 *)
  0xca170108;       (* arm_EOR X8 X8 X23 *)
  0xfa0c0226;       (* arm_SBCS X6 X17 X12 *)
  0xfa1901ad;       (* arm_SBCS X13 X13 X25 *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb11014a;       (* arm_SUBS X10 X10 X17 *)
  0xda8a2551;       (* arm_CNEG X17 X10 Condition_CC *)
  0xda9f23f9;       (* arm_CSETM X25 Condition_CC *)
  0xeb050285;       (* arm_SUBS X5 X20 X5 *)
  0xca0c026a;       (* arm_EOR X10 X19 X12 *)
  0xda8524b3;       (* arm_CNEG X19 X5 Condition_CC *)
  0xca1701f4;       (* arm_EOR X20 X15 X23 *)
  0xca0c02b5;       (* arm_EOR X21 X21 X12 *)
  0xda99232f;       (* arm_CINV X15 X25 Condition_CC *)
  0x9b137e39;       (* arm_MUL X25 X17 X19 *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa1702c5;       (* arm_SBCS X5 X22 X23 *)
  0xca0c00c6;       (* arm_EOR X6 X6 X12 *)
  0xfa170294;       (* arm_SBCS X20 X20 X23 *)
  0xca0c01b6;       (* arm_EOR X22 X13 X12 *)
  0xda170108;       (* arm_SBC X8 X8 X23 *)
  0xeb0c02b5;       (* arm_SUBS X21 X21 X12 *)
  0x9bd37e33;       (* arm_UMULH X19 X17 X19 *)
  0xfa0c014a;       (* arm_SBCS X10 X10 X12 *)
  0xfa0c00d1;       (* arm_SBCS X17 X6 X12 *)
  0xca0f0266;       (* arm_EOR X6 X19 X15 *)
  0xca0f0333;       (* arm_EOR X19 X25 X15 *)
  0x9bd47e39;       (* arm_UMULH X25 X17 X20 *)
  0xda0c02cd;       (* arm_SBC X13 X22 X12 *)
  0xb10005ff;       (* arm_CMN X15 (rvalue (word 1)) *)
  0xba1301d6;       (* arm_ADCS X22 X14 X19 *)
  0xba060353;       (* arm_ADCS X19 X26 X6 *)
  0xa9406be6;       (* arm_LDP X6 X26 SP (Immediate_Offset (iword (&0))) *)
  0xba0f030e;       (* arm_ADCS X14 X24 X15 *)
  0x9bd07eb8;       (* arm_UMULH X24 X21 X16 *)
  0xba0f00e7;       (* arm_ADCS X7 X7 X15 *)
  0x9a0f008f;       (* arm_ADC X15 X4 X15 *)
  0xab060124;       (* arm_ADDS X4 X9 X6 *)
  0xca0c02e9;       (* arm_EOR X9 X23 X12 *)
  0xba1a006c;       (* arm_ADCS X12 X3 X26 *)
  0xa90033e4;       (* arm_STP X4 X12 SP (Immediate_Offset (iword (&0))) *)
  0xa9416be4;       (* arm_LDP X4 X26 SP (Immediate_Offset (iword (&16))) *)
  0x9bc57d4c;       (* arm_UMULH X12 X10 X5 *)
  0xa9425fe6;       (* arm_LDP X6 X23 SP (Immediate_Offset (iword (&32))) *)
  0xba040163;       (* arm_ADCS X3 X11 X4 *)
  0x9b087da4;       (* arm_MUL X4 X13 X8 *)
  0xba1a02da;       (* arm_ADCS X26 X22 X26 *)
  0xa9432ff6;       (* arm_LDP X22 X11 SP (Immediate_Offset (iword (&48))) *)
  0xba060266;       (* arm_ADCS X6 X19 X6 *)
  0xa9016be3;       (* arm_STP X3 X26 SP (Immediate_Offset (iword (&16))) *)
  0x9b057d5a;       (* arm_MUL X26 X10 X5 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xa9023be6;       (* arm_STP X6 X14 SP (Immediate_Offset (iword (&32))) *)
  0xf94023e6;       (* arm_LDR X6 SP (Immediate_Offset (word 64)) *)
  0xba1600f6;       (* arm_ADCS X22 X7 X22 *)
  0xba0b01ee;       (* arm_ADCS X14 X15 X11 *)
  0x9b147e2b;       (* arm_MUL X11 X17 X20 *)
  0x9a1f00d3;       (* arm_ADC X19 X6 XZR *)
  0xa9033bf6;       (* arm_STP X22 X14 SP (Immediate_Offset (iword (&48))) *)
  0xab18034e;       (* arm_ADDS X14 X26 X24 *)
  0xf90023f3;       (* arm_STR X19 SP (Immediate_Offset (word 64)) *)
  0x9bc87db3;       (* arm_UMULH X19 X13 X8 *)
  0xba0c0167;       (* arm_ADCS X7 X11 X12 *)
  0xba190096;       (* arm_ADCS X22 X4 X25 *)
  0x9b107ea6;       (* arm_MUL X6 X21 X16 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xeb0d022b;       (* arm_SUBS X11 X17 X13 *)
  0xda8b256c;       (* arm_CNEG X12 X11 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb140118;       (* arm_SUBS X24 X8 X20 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xab0601c4;       (* arm_ADDS X4 X14 X6 *)
  0xba0e00ee;       (* arm_ADCS X14 X7 X14 *)
  0x9b187d83;       (* arm_MUL X3 X12 X24 *)
  0xba0702c7;       (* arm_ADCS X7 X22 X7 *)
  0xba160276;       (* arm_ADCS X22 X19 X22 *)
  0x9bd87d8c;       (* arm_UMULH X12 X12 X24 *)
  0x9a1303f8;       (* arm_ADC X24 XZR X19 *)
  0xab0601d3;       (* arm_ADDS X19 X14 X6 *)
  0xca0b0063;       (* arm_EOR X3 X3 X11 *)
  0xba0400fa;       (* arm_ADCS X26 X7 X4 *)
  0xba0e02ce;       (* arm_ADCS X14 X22 X14 *)
  0xba070319;       (* arm_ADCS X25 X24 X7 *)
  0xba1603f7;       (* arm_ADCS X23 XZR X22 *)
  0xca0b0187;       (* arm_EOR X7 X12 X11 *)
  0x9a1803ec;       (* arm_ADC X12 XZR X24 *)
  0xeb0a02b6;       (* arm_SUBS X22 X21 X10 *)
  0xda9626d8;       (* arm_CNEG X24 X22 Condition_CC *)
  0xda9f23f6;       (* arm_CSETM X22 Condition_CC *)
  0xeb1000af;       (* arm_SUBS X15 X5 X16 *)
  0xda9622d6;       (* arm_CINV X22 X22 Condition_CC *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba030323;       (* arm_ADCS X3 X25 X3 *)
  0x9b0f7f19;       (* arm_MUL X25 X24 X15 *)
  0xba0702f7;       (* arm_ADCS X23 X23 X7 *)
  0x9a0b018b;       (* arm_ADC X11 X12 X11 *)
  0xeb0d0147;       (* arm_SUBS X7 X10 X13 *)
  0x9bcf7f0f;       (* arm_UMULH X15 X24 X15 *)
  0xda8724ec;       (* arm_CNEG X12 X7 Condition_CC *)
  0xda9f23e7;       (* arm_CSETM X7 Condition_CC *)
  0xca160338;       (* arm_EOR X24 X25 X22 *)
  0xca1601f9;       (* arm_EOR X25 X15 X22 *)
  0xb10006df;       (* arm_CMN X22 (rvalue (word 1)) *)
  0xba180098;       (* arm_ADCS X24 X4 X24 *)
  0xba190273;       (* arm_ADCS X19 X19 X25 *)
  0xba16034f;       (* arm_ADCS X15 X26 X22 *)
  0xba1601c4;       (* arm_ADCS X4 X14 X22 *)
  0xba16007a;       (* arm_ADCS X26 X3 X22 *)
  0xba1602f9;       (* arm_ADCS X25 X23 X22 *)
  0x9a160177;       (* arm_ADC X23 X11 X22 *)
  0xeb1102ae;       (* arm_SUBS X14 X21 X17 *)
  0xda8e25c3;       (* arm_CNEG X3 X14 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb05010e;       (* arm_SUBS X14 X8 X5 *)
  0xda8e25ce;       (* arm_CNEG X14 X14 Condition_CC *)
  0xda8720e7;       (* arm_CINV X7 X7 Condition_CC *)
  0xeb0d02ad;       (* arm_SUBS X13 X21 X13 *)
  0xda8d25b5;       (* arm_CNEG X21 X13 Condition_CC *)
  0xda9f23ed;       (* arm_CSETM X13 Condition_CC *)
  0x9b0e7d96;       (* arm_MUL X22 X12 X14 *)
  0xeb100108;       (* arm_SUBS X8 X8 X16 *)
  0xda8d21ad;       (* arm_CINV X13 X13 Condition_CC *)
  0x9bce7d8e;       (* arm_UMULH X14 X12 X14 *)
  0xda88250c;       (* arm_CNEG X12 X8 Condition_CC *)
  0xeb100288;       (* arm_SUBS X8 X20 X16 *)
  0xda882508;       (* arm_CNEG X8 X8 Condition_CC *)
  0xda8b2170;       (* arm_CINV X16 X11 Condition_CC *)
  0xca0702d6;       (* arm_EOR X22 X22 X7 *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0xca0701ce;       (* arm_EOR X14 X14 X7 *)
  0xba160084;       (* arm_ADCS X4 X4 X22 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0e0356;       (* arm_ADCS X22 X26 X14 *)
  0xba07032e;       (* arm_ADCS X14 X25 X7 *)
  0xca090319;       (* arm_EOR X25 X24 X9 *)
  0x9a0702fa;       (* arm_ADC X26 X23 X7 *)
  0x9bc87c67;       (* arm_UMULH X7 X3 X8 *)
  0xeb110151;       (* arm_SUBS X17 X10 X17 *)
  0xda912638;       (* arm_CNEG X24 X17 Condition_CC *)
  0xca100163;       (* arm_EOR X3 X11 X16 *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb050294;       (* arm_SUBS X20 X20 X5 *)
  0xda942685;       (* arm_CNEG X5 X20 Condition_CC *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0x9b0c7eb1;       (* arm_MUL X17 X21 X12 *)
  0xca1000e8;       (* arm_EOR X8 X7 X16 *)
  0xba03026a;       (* arm_ADCS X10 X19 X3 *)
  0x92402133;       (* arm_AND X19 X9 (rvalue (word 511)) *)
  0xba0801f4;       (* arm_ADCS X20 X15 X8 *)
  0x9bcc7eaf;       (* arm_UMULH X15 X21 X12 *)
  0xca09014c;       (* arm_EOR X12 X10 X9 *)
  0xca0900c8;       (* arm_EOR X8 X6 X9 *)
  0xba100086;       (* arm_ADCS X6 X4 X16 *)
  0xba1002c4;       (* arm_ADCS X4 X22 X16 *)
  0xba1001d5;       (* arm_ADCS X21 X14 X16 *)
  0x9a100347;       (* arm_ADC X7 X26 X16 *)
  0x9b057f0a;       (* arm_MUL X10 X24 X5 *)
  0xb10005bf;       (* arm_CMN X13 (rvalue (word 1)) *)
  0xa9403823;       (* arm_LDP X3 X14 X1 (Immediate_Offset (iword (&0))) *)
  0xca0d0231;       (* arm_EOR X17 X17 X13 *)
  0x9bc57f05;       (* arm_UMULH X5 X24 X5 *)
  0xba110294;       (* arm_ADCS X20 X20 X17 *)
  0xca0d01f1;       (* arm_EOR X17 X15 X13 *)
  0xba1100d0;       (* arm_ADCS X16 X6 X17 *)
  0xca0b0156;       (* arm_EOR X22 X10 X11 *)
  0xba0d0097;       (* arm_ADCS X23 X4 X13 *)
  0x93c3d1ca;       (* arm_EXTR X10 X14 X3 52 *)
  0x9240cc7a;       (* arm_AND X26 X3 (rvalue (word 4503599627370495)) *)
  0xba0d02b8;       (* arm_ADCS X24 X21 X13 *)
  0x9240cd4f;       (* arm_AND X15 X10 (rvalue (word 4503599627370495)) *)
  0x9a0d00e6;       (* arm_ADC X6 X7 X13 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba160291;       (* arm_ADCS X17 X20 X22 *)
  0xca0b00a4;       (* arm_EOR X4 X5 X11 *)
  0xa9402bf5;       (* arm_LDP X21 X10 SP (Immediate_Offset (iword (&0))) *)
  0xba040207;       (* arm_ADCS X7 X16 X4 *)
  0xca090230;       (* arm_EOR X16 X17 X9 *)
  0xca0900ed;       (* arm_EOR X13 X7 X9 *)
  0xa94147e3;       (* arm_LDP X3 X17 SP (Immediate_Offset (iword (&16))) *)
  0xba0b02e7;       (* arm_ADCS X7 X23 X11 *)
  0xca0900f7;       (* arm_EOR X23 X7 X9 *)
  0xa9425be5;       (* arm_LDP X5 X22 SP (Immediate_Offset (iword (&32))) *)
  0xba0b0307;       (* arm_ADCS X7 X24 X11 *)
  0x9a0b00d8;       (* arm_ADC X24 X6 X11 *)
  0xf9402046;       (* arm_LDR X6 X2 (Immediate_Offset (word 64)) *)
  0xab150114;       (* arm_ADDS X20 X8 X21 *)
  0xd377da8b;       (* arm_LSL X11 X20 9 *)
  0xca0900e4;       (* arm_EOR X4 X7 X9 *)
  0xaa130167;       (* arm_ORR X7 X11 X19 *)
  0xca090308;       (* arm_EOR X8 X24 X9 *)
  0xba0a032b;       (* arm_ADCS X11 X25 X10 *)
  0x9b1a7cda;       (* arm_MUL X26 X6 X26 *)
  0xa94363f3;       (* arm_LDP X19 X24 SP (Immediate_Offset (iword (&48))) *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0xba0501a9;       (* arm_ADCS X9 X13 X5 *)
  0xf94023f9;       (* arm_LDR X25 SP (Immediate_Offset (word 64)) *)
  0x93d4dd74;       (* arm_EXTR X20 X11 X20 55 *)
  0xba1602ed;       (* arm_ADCS X13 X23 X22 *)
  0xba130084;       (* arm_ADCS X4 X4 X19 *)
  0x93cbdd97;       (* arm_EXTR X23 X12 X11 55 *)
  0xba180108;       (* arm_ADCS X8 X8 X24 *)
  0x9a1f032b;       (* arm_ADC X11 X25 XZR *)
  0xab150135;       (* arm_ADDS X21 X9 X21 *)
  0x93ccde09;       (* arm_EXTR X9 X16 X12 55 *)
  0xd377fe0c;       (* arm_LSR X12 X16 55 *)
  0xba0a01aa;       (* arm_ADCS X10 X13 X10 *)
  0x9b0f7ccf;       (* arm_MUL X15 X6 X15 *)
  0xba03008d;       (* arm_ADCS X13 X4 X3 *)
  0xa9401050;       (* arm_LDP X16 X4 X2 (Immediate_Offset (iword (&0))) *)
  0xf9402023;       (* arm_LDR X3 X1 (Immediate_Offset (word 64)) *)
  0xba110111;       (* arm_ADCS X17 X8 X17 *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba1402d4;       (* arm_ADCS X20 X22 X20 *)
  0xba170268;       (* arm_ADCS X8 X19 X23 *)
  0x9240ce16;       (* arm_AND X22 X16 (rvalue (word 4503599627370495)) *)
  0xa9411c33;       (* arm_LDP X19 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xba090309;       (* arm_ADCS X9 X24 X9 *)
  0x93d0d098;       (* arm_EXTR X24 X4 X16 52 *)
  0x9a190190;       (* arm_ADC X16 X12 X25 *)
  0x9b167c76;       (* arm_MUL X22 X3 X22 *)
  0x9240cf19;       (* arm_AND X25 X24 (rvalue (word 4503599627370495)) *)
  0x93cea26e;       (* arm_EXTR X14 X19 X14 40 *)
  0x9240cdcc;       (* arm_AND X12 X14 (rvalue (word 4503599627370495)) *)
  0x93d370f7;       (* arm_EXTR X23 X7 X19 28 *)
  0xa9416053;       (* arm_LDP X19 X24 X2 (Immediate_Offset (iword (&16))) *)
  0x9b197c6e;       (* arm_MUL X14 X3 X25 *)
  0x9240cef7;       (* arm_AND X23 X23 (rvalue (word 4503599627370495)) *)
  0x8b160356;       (* arm_ADD X22 X26 X22 *)
  0xd3503d6b;       (* arm_LSL X11 X11 48 *)
  0xd374feda;       (* arm_LSR X26 X22 52 *)
  0xd374ced9;       (* arm_LSL X25 X22 12 *)
  0x9b0c7cd6;       (* arm_MUL X22 X6 X12 *)
  0x93c4a26c;       (* arm_EXTR X12 X19 X4 40 *)
  0x8b0e01e4;       (* arm_ADD X4 X15 X14 *)
  0x9b177ccf;       (* arm_MUL X15 X6 X23 *)
  0x8b1a0084;       (* arm_ADD X4 X4 X26 *)
  0x93d37317;       (* arm_EXTR X23 X24 X19 28 *)
  0xa9424c2e;       (* arm_LDP X14 X19 X1 (Immediate_Offset (iword (&32))) *)
  0x9240cd9a;       (* arm_AND X26 X12 (rvalue (word 4503599627370495)) *)
  0x93d9308c;       (* arm_EXTR X12 X4 X25 12 *)
  0x9240cef9;       (* arm_AND X25 X23 (rvalue (word 4503599627370495)) *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0x9b1a7c6c;       (* arm_MUL X12 X3 X26 *)
  0x93c741d7;       (* arm_EXTR X23 X14 X7 16 *)
  0x9240cef7;       (* arm_AND X23 X23 (rvalue (word 4503599627370495)) *)
  0x9b197c67;       (* arm_MUL X7 X3 X25 *)
  0xa9426859;       (* arm_LDP X25 X26 X2 (Immediate_Offset (iword (&32))) *)
  0x8b0c02cc;       (* arm_ADD X12 X22 X12 *)
  0x93cee276;       (* arm_EXTR X22 X19 X14 56 *)
  0x9b177cd7;       (* arm_MUL X23 X6 X23 *)
  0xd344fdce;       (* arm_LSR X14 X14 4 *)
  0x93d84338;       (* arm_EXTR X24 X25 X24 16 *)
  0x8b0701e7;       (* arm_ADD X7 X15 X7 *)
  0x9240cf0f;       (* arm_AND X15 X24 (rvalue (word 4503599627370495)) *)
  0x9240ced6;       (* arm_AND X22 X22 (rvalue (word 4503599627370495)) *)
  0xd374fc98;       (* arm_LSR X24 X4 52 *)
  0x9b0f7c6f;       (* arm_MUL X15 X3 X15 *)
  0x9240cdce;       (* arm_AND X14 X14 (rvalue (word 4503599627370495)) *)
  0x8b18018c;       (* arm_ADD X12 X12 X24 *)
  0xd374cc98;       (* arm_LSL X24 X4 12 *)
  0xd374fd84;       (* arm_LSR X4 X12 52 *)
  0x93d86198;       (* arm_EXTR X24 X12 X24 24 *)
  0xba18014a;       (* arm_ADCS X10 X10 X24 *)
  0xd374cd98;       (* arm_LSL X24 X12 12 *)
  0x8b0400ec;       (* arm_ADD X12 X7 X4 *)
  0x9b167cd6;       (* arm_MUL X22 X6 X22 *)
  0x8b0f02e4;       (* arm_ADD X4 X23 X15 *)
  0x93d89187;       (* arm_EXTR X7 X12 X24 36 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0xd374cd8f;       (* arm_LSL X15 X12 12 *)
  0x8b0b0087;       (* arm_ADD X7 X4 X11 *)
  0xd374fd98;       (* arm_LSR X24 X12 52 *)
  0xa9432c57;       (* arm_LDP X23 X11 X2 (Immediate_Offset (iword (&48))) *)
  0x8b1800e4;       (* arm_ADD X4 X7 X24 *)
  0x9b0e7ccc;       (* arm_MUL X12 X6 X14 *)
  0x93d9e347;       (* arm_EXTR X7 X26 X25 56 *)
  0x93cfc08e;       (* arm_EXTR X14 X4 X15 48 *)
  0x9240cce2;       (* arm_AND X2 X7 (rvalue (word 4503599627370495)) *)
  0x93d78178;       (* arm_EXTR X24 X11 X23 32 *)
  0xa9431c2f;       (* arm_LDP X15 X7 X1 (Immediate_Offset (iword (&48))) *)
  0x9240cf01;       (* arm_AND X1 X24 (rvalue (word 4503599627370495)) *)
  0xd374fc98;       (* arm_LSR X24 X4 52 *)
  0x9b027c62;       (* arm_MUL X2 X3 X2 *)
  0x93dab2fa;       (* arm_EXTR X26 X23 X26 44 *)
  0xd344ff37;       (* arm_LSR X23 X25 4 *)
  0x9240cef7;       (* arm_AND X23 X23 (rvalue (word 4503599627370495)) *)
  0x9240cf59;       (* arm_AND X25 X26 (rvalue (word 4503599627370495)) *)
  0x93cf80fa;       (* arm_EXTR X26 X7 X15 32 *)
  0x93d3b1f3;       (* arm_EXTR X19 X15 X19 44 *)
  0x9b177c77;       (* arm_MUL X23 X3 X23 *)
  0x9240cf4f;       (* arm_AND X15 X26 (rvalue (word 4503599627370495)) *)
  0xd374cc9a;       (* arm_LSL X26 X4 12 *)
  0x9240ce64;       (* arm_AND X4 X19 (rvalue (word 4503599627370495)) *)
  0xd354fd6b;       (* arm_LSR X11 X11 20 *)
  0x9b047cd3;       (* arm_MUL X19 X6 X4 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x8b0202ce;       (* arm_ADD X14 X22 X2 *)
  0x8b170196;       (* arm_ADD X22 X12 X23 *)
  0xd354fce7;       (* arm_LSR X7 X7 20 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0x93daf2c2;       (* arm_EXTR X2 X22 X26 60 *)
  0x9b197c78;       (* arm_MUL X24 X3 X25 *)
  0xd374fed6;       (* arm_LSR X22 X22 52 *)
  0x8b1601ce;       (* arm_ADD X14 X14 X22 *)
  0xd378dc56;       (* arm_LSL X22 X2 8 *)
  0x93d621d6;       (* arm_EXTR X22 X14 X22 8 *)
  0xd374cdc2;       (* arm_LSL X2 X14 12 *)
  0x9b017c61;       (* arm_MUL X1 X3 X1 *)
  0xba1600ac;       (* arm_ADCS X12 X5 X22 *)
  0x9b0f7cc5;       (* arm_MUL X5 X6 X15 *)
  0x8a0d015a;       (* arm_AND X26 X10 X13 *)
  0x8a110344;       (* arm_AND X4 X26 X17 *)
  0x8b180277;       (* arm_ADD X23 X19 X24 *)
  0xd374fdce;       (* arm_LSR X14 X14 52 *)
  0x9b0b7c76;       (* arm_MUL X22 X3 X11 *)
  0x8b0e02eb;       (* arm_ADD X11 X23 X14 *)
  0x93c25179;       (* arm_EXTR X25 X11 X2 20 *)
  0xd374cd73;       (* arm_LSL X19 X11 12 *)
  0xba190299;       (* arm_ADCS X25 X20 X25 *)
  0x8a0c008e;       (* arm_AND X14 X4 X12 *)
  0x8b0100a1;       (* arm_ADD X1 X5 X1 *)
  0x8a1901ce;       (* arm_AND X14 X14 X25 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x8b1601fa;       (* arm_ADD X26 X15 X22 *)
  0x9b037cc6;       (* arm_MUL X6 X6 X3 *)
  0xd374fd76;       (* arm_LSR X22 X11 52 *)
  0x8b160024;       (* arm_ADD X4 X1 X22 *)
  0xd374fc81;       (* arm_LSR X1 X4 52 *)
  0x93d38083;       (* arm_EXTR X3 X4 X19 32 *)
  0xd374cc8f;       (* arm_LSL X15 X4 12 *)
  0x8b010347;       (* arm_ADD X7 X26 X1 *)
  0xba030117;       (* arm_ADCS X23 X8 X3 *)
  0x93cfb0f4;       (* arm_EXTR X20 X7 X15 44 *)
  0x8a1701c3;       (* arm_AND X3 X14 X23 *)
  0xd36cfcf3;       (* arm_LSR X19 X7 44 *)
  0xba140127;       (* arm_ADCS X7 X9 X20 *)
  0x8b1300cb;       (* arm_ADD X11 X6 X19 *)
  0x9a0b0204;       (* arm_ADC X4 X16 X11 *)
  0xd349fc8e;       (* arm_LSR X14 X4 9 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x8a07006f;       (* arm_AND X15 X3 X7 *)
  0xb277d883;       (* arm_ORR X3 X4 (rvalue (word 18446744073709551104)) *)
  0xba0e02bf;       (* arm_ADCS XZR X21 X14 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xba0e02ab;       (* arm_ADCS X11 X21 X14 *)
  0x9240216e;       (* arm_AND X14 X11 (rvalue (word 511)) *)
  0xba1f0141;       (* arm_ADCS X1 X10 XZR *)
  0x93cb242a;       (* arm_EXTR X10 X1 X11 9 *)
  0xf900200e;       (* arm_STR X14 X0 (Immediate_Offset (word 64)) *)
  0xba1f01ae;       (* arm_ADCS X14 X13 XZR *)
  0x93c125cb;       (* arm_EXTR X11 X14 X1 9 *)
  0xba1f0221;       (* arm_ADCS X1 X17 XZR *)
  0x93ce2424;       (* arm_EXTR X4 X1 X14 9 *)
  0xa9002c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xba1f018b;       (* arm_ADCS X11 X12 XZR *)
  0x93c1256e;       (* arm_EXTR X14 X11 X1 9 *)
  0xba1f032a;       (* arm_ADCS X10 X25 XZR *)
  0x93cb254b;       (* arm_EXTR X11 X10 X11 9 *)
  0xa9013804;       (* arm_STP X4 X14 X0 (Immediate_Offset (iword (&16))) *)
  0xba1f02ee;       (* arm_ADCS X14 X23 XZR *)
  0x93ca25ca;       (* arm_EXTR X10 X14 X10 9 *)
  0xba1f00e1;       (* arm_ADCS X1 X7 XZR *)
  0xa902280b;       (* arm_STP X11 X10 X0 (Immediate_Offset (iword (&32))) *)
  0x93ce242e;       (* arm_EXTR X14 X1 X14 9 *)
  0x9a1f006a;       (* arm_ADC X10 X3 XZR *)
  0x93c1255a;       (* arm_EXTR X26 X10 X1 9 *)
  0xa903680e;       (* arm_STP X14 X26 X0 (Immediate_Offset (iword (&48))) *)
  0x910143ff;       (* arm_ADD SP SP (rvalue (word 80)) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0x3dc00837;       (* arm_LDR Q23 X1 (Immediate_Offset (word 32)) *)
  0xa9420829;       (* arm_LDP X9 X2 X1 (Immediate_Offset (iword (&32))) *)
  0x3dc00830;       (* arm_LDR Q16 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c34;       (* arm_LDR Q20 X1 (Immediate_Offset (word 48)) *)
  0xa9433426;       (* arm_LDP X6 X13 X1 (Immediate_Offset (iword (&48))) *)
  0x4ea00ae2;       (* arm_REV64_VEC Q2 Q23 32 *)
  0x9b027d2e;       (* arm_MUL X14 X9 X2 *)
  0x3dc00c3f;       (* arm_LDR Q31 X1 (Immediate_Offset (word 48)) *)
  0xeb020136;       (* arm_SUBS X22 X9 X2 *)
  0x4e975afa;       (* arm_UZP2 Q26 Q23 Q23 32 *)
  0x4eb09c5e;       (* arm_MUL_VEC Q30 Q2 Q16 32 128 *)
  0x0ea12a80;       (* arm_XTN Q0 Q20 32 *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0x0ea12a15;       (* arm_XTN Q21 Q16 32 *)
  0x0ea12af7;       (* arm_XTN Q23 Q23 32 *)
  0x9bc67d2a;       (* arm_UMULH X10 X9 X6 *)
  0x4ea00bfb;       (* arm_REV64_VEC Q27 Q31 32 *)
  0x2ebac2a2;       (* arm_UMULL_VEC Q2 Q21 Q26 32 *)
  0xda9626d7;       (* arm_CNEG X23 X22 Condition_CC *)
  0x6ea02bd9;       (* arm_UADDLP Q25 Q30 32 *)
  0x2eb7c2b2;       (* arm_UMULL_VEC Q18 Q21 Q23 32 *)
  0x9b067d36;       (* arm_MUL X22 X9 X6 *)
  0x4eb49f66;       (* arm_MUL_VEC Q6 Q27 Q20 32 128 *)
  0x4e945a91;       (* arm_UZP2 Q17 Q20 Q20 32 *)
  0x4f605734;       (* arm_SHL_VEC Q20 Q25 32 64 128 *)
  0x4e9f5bfb;       (* arm_UZP2 Q27 Q31 Q31 32 *)
  0x9b0d7c50;       (* arm_MUL X16 X2 X13 *)
  0x2eb782b4;       (* arm_UMLAL_VEC Q20 Q21 Q23 32 *)
  0x6f601642;       (* arm_USRA_VEC Q2 Q18 32 64 128 *)
  0xab0a02c8;       (* arm_ADDS X8 X22 X10 *)
  0x2ebbc239;       (* arm_UMULL_VEC Q25 Q17 Q27 32 *)
  0x0ea12bff;       (* arm_XTN Q31 Q31 32 *)
  0x6f00e5e1;       (* arm_MOVI Q1 (word 4294967295) *)
  0x9a1f0143;       (* arm_ADC X3 X10 XZR *)
  0x9bcd7c55;       (* arm_UMULH X21 X2 X13 *)
  0x4e905a15;       (* arm_UZP2 Q21 Q16 Q16 32 *)
  0x2ebbc012;       (* arm_UMULL_VEC Q18 Q0 Q27 32 *)
  0xeb0601b3;       (* arm_SUBS X19 X13 X6 *)
  0x4e211c47;       (* arm_AND_VEC Q7 Q2 Q1 128 *)
  0x2ebfc01b;       (* arm_UMULL_VEC Q27 Q0 Q31 32 *)
  0xda932674;       (* arm_CNEG X20 X19 Condition_CC *)
  0x6f00e5fe;       (* arm_MOVI Q30 (word 4294967295) *)
  0x2ebac2b0;       (* arm_UMULL_VEC Q16 Q21 Q26 32 *)
  0x2eb782a7;       (* arm_UMLAL_VEC Q7 Q21 Q23 32 *)
  0x9b147ef3;       (* arm_MUL X19 X23 X20 *)
  0xda8c2187;       (* arm_CINV X7 X12 Condition_CC *)
  0x6ea028c6;       (* arm_UADDLP Q6 Q6 32 *)
  0xca07026c;       (* arm_EOR X12 X19 X7 *)
  0xab10010b;       (* arm_ADDS X11 X8 X16 *)
  0x9bd47eea;       (* arm_UMULH X10 X23 X20 *)
  0x3dc00021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 0)) *)
  0x6f601450;       (* arm_USRA_VEC Q16 Q2 32 64 128 *)
  0xba150073;       (* arm_ADCS X19 X3 X21 *)
  0x4f6054c2;       (* arm_SHL_VEC Q2 Q6 32 64 128 *)
  0x9a1f02b4;       (* arm_ADC X20 X21 XZR *)
  0xab100271;       (* arm_ADDS X17 X19 X16 *)
  0x6f601772;       (* arm_USRA_VEC Q18 Q27 32 64 128 *)
  0x9a1f0293;       (* arm_ADC X19 X20 XZR *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0x2ebf8002;       (* arm_UMLAL_VEC Q2 Q0 Q31 32 *)
  0x9bc27d30;       (* arm_UMULH X16 X9 X2 *)
  0xba0c0168;       (* arm_ADCS X8 X11 X12 *)
  0x6f6014f0;       (* arm_USRA_VEC Q16 Q7 32 64 128 *)
  0xf940202c;       (* arm_LDR X12 X1 (Immediate_Offset (word 64)) *)
  0xca070154;       (* arm_EOR X20 X10 X7 *)
  0x9bcd7cca;       (* arm_UMULH X10 X6 X13 *)
  0x4e083c57;       (* arm_UMOV X23 Q2 0 8 *)
  0x4e183c43;       (* arm_UMOV X3 Q2 1 8 *)
  0xba140235;       (* arm_ADCS X21 X17 X20 *)
  0x6f601659;       (* arm_USRA_VEC Q25 Q18 32 64 128 *)
  0x4e3e1e57;       (* arm_AND_VEC Q23 Q18 Q30 128 *)
  0x9a070267;       (* arm_ADC X7 X19 X7 *)
  0xab1602d6;       (* arm_ADDS X22 X22 X22 *)
  0x3dc00427;       (* arm_LDR Q7 X1 (Immediate_Offset (word 16)) *)
  0xba080111;       (* arm_ADCS X17 X8 X8 *)
  0x2ebf8237;       (* arm_UMLAL_VEC Q23 Q17 Q31 32 *)
  0x4e083e13;       (* arm_UMOV X19 Q16 0 8 *)
  0x9b0c7d8b;       (* arm_MUL X11 X12 X12 *)
  0x3dc00024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 0)) *)
  0x6f6016f9;       (* arm_USRA_VEC Q25 Q23 32 64 128 *)
  0x8b0c0185;       (* arm_ADD X5 X12 X12 *)
  0xba1502af;       (* arm_ADCS X15 X21 X21 *)
  0x3dc0003c;       (* arm_LDR Q28 X1 (Immediate_Offset (word 0)) *)
  0x4e183e8c;       (* arm_UMOV X12 Q20 1 8 *)
  0xba0700f8;       (* arm_ADCS X24 X7 X7 *)
  0x4e183e15;       (* arm_UMOV X21 Q16 1 8 *)
  0x9a1f03e4;       (* arm_ADC X4 XZR XZR *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x3dc00432;       (* arm_LDR Q18 X1 (Immediate_Offset (word 16)) *)
  0x0ea1283a;       (* arm_XTN Q26 Q1 32 *)
  0xba100188;       (* arm_ADCS X8 X12 X16 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0267;       (* arm_ADDS X7 X19 X14 *)
  0x0ea128f7;       (* arm_XTN Q23 Q7 32 *)
  0x4ea00b95;       (* arm_REV64_VEC Q21 Q28 32 *)
  0xba10010c;       (* arm_ADCS X12 X8 X16 *)
  0xa9404c34;       (* arm_LDP X20 X19 X1 (Immediate_Offset (iword (&0))) *)
  0x4e183f30;       (* arm_UMOV X16 Q25 1 8 *)
  0x0ea12b96;       (* arm_XTN Q22 Q28 32 *)
  0x9a1f02ae;       (* arm_ADC X14 X21 XZR *)
  0xab0c02c8;       (* arm_ADDS X8 X22 X12 *)
  0x4e9c5b98;       (* arm_UZP2 Q24 Q28 Q28 32 *)
  0x4ea00a5c;       (* arm_REV64_VEC Q28 Q18 32 *)
  0x9b0d7ccc;       (* arm_MUL X12 X6 X13 *)
  0x4ea19eb0;       (* arm_MUL_VEC Q16 Q21 Q1 32 128 *)
  0x0f2084ff;       (* arm_SHRN Q31 Q7 32 32 *)
  0xba0e0236;       (* arm_ADCS X22 X17 X14 *)
  0x4e083f2e;       (* arm_UMOV X14 Q25 0 8 *)
  0x9240ce95;       (* arm_AND X21 X20 (rvalue (word 4503599627370495)) *)
  0x2eb8c351;       (* arm_UMULL_VEC Q17 Q26 Q24 32 *)
  0x3dc00822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 32)) *)
  0xba1f01f1;       (* arm_ADCS X17 X15 XZR *)
  0x3dc00c3e;       (* arm_LDR Q30 X1 (Immediate_Offset (word 48)) *)
  0x2eb6c347;       (* arm_UMULL_VEC Q7 Q26 Q22 32 *)
  0xba1f030f;       (* arm_ADCS X15 X24 XZR *)
  0x3dc00420;       (* arm_LDR Q0 X1 (Immediate_Offset (word 16)) *)
  0x6f00e5e6;       (* arm_MOVI Q6 (word 4294967295) *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0xab0c01ce;       (* arm_ADDS X14 X14 X12 *)
  0x4e841a5b;       (* arm_UZP1 Q27 Q18 Q4 32 *)
  0x4e815833;       (* arm_UZP2 Q19 Q1 Q1 32 *)
  0xba0a0078;       (* arm_ADCS X24 X3 X10 *)
  0x9b157ca3;       (* arm_MUL X3 X5 X21 *)
  0x2ebfc2fd;       (* arm_UMULL_VEC Q29 Q23 Q31 32 *)
  0x3dc00025;       (* arm_LDR Q5 X1 (Immediate_Offset (word 0)) *)
  0x9a1f0215;       (* arm_ADC X21 X16 XZR *)
  0xab0c01d0;       (* arm_ADDS X16 X14 X12 *)
  0x93d4d26c;       (* arm_EXTR X12 X19 X20 52 *)
  0x2eb8c272;       (* arm_UMULL_VEC Q18 Q19 Q24 32 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9240cd8a;       (* arm_AND X10 X12 (rvalue (word 4503599627370495)) *)
  0xa941302e;       (* arm_LDP X14 X12 X1 (Immediate_Offset (iword (&16))) *)
  0x6f6014f1;       (* arm_USRA_VEC Q17 Q7 32 64 128 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab1102f7;       (* arm_ADDS X23 X23 X17 *)
  0x9b0a7cb1;       (* arm_MUL X17 X5 X10 *)
  0x4f6157b5;       (* arm_SHL_VEC Q21 Q29 33 64 128 *)
  0xd374cc6a;       (* arm_LSL X10 X3 12 *)
  0xd374fc61;       (* arm_LSR X1 X3 52 *)
  0x4ea0085d;       (* arm_REV64_VEC Q29 Q2 32 *)
  0x6ea02a19;       (* arm_UADDLP Q25 Q16 32 *)
  0x8b010231;       (* arm_ADD X17 X17 X1 *)
  0xba0f0210;       (* arm_ADCS X16 X16 X15 *)
  0x93d3a1c3;       (* arm_EXTR X3 X14 X19 40 *)
  0x4e083e8f;       (* arm_UMOV X15 Q20 0 8 *)
  0x93ca322a;       (* arm_EXTR X10 X17 X10 12 *)
  0x9240cc63;       (* arm_AND X3 X3 (rvalue (word 4503599627370495)) *)
  0x4f605723;       (* arm_SHL_VEC Q3 Q25 32 64 128 *)
  0x4e261e26;       (* arm_AND_VEC Q6 Q17 Q6 128 *)
  0x9b037ca1;       (* arm_MUL X1 X5 X3 *)
  0x6f601632;       (* arm_USRA_VEC Q18 Q17 32 64 128 *)
  0xba040303;       (* arm_ADCS X3 X24 X4 *)
  0x93ce7184;       (* arm_EXTR X4 X12 X14 28 *)
  0x2eb68266;       (* arm_UMLAL_VEC Q6 Q19 Q22 32 *)
  0x0ea12854;       (* arm_XTN Q20 Q2 32 *)
  0x2eb68343;       (* arm_UMLAL_VEC Q3 Q26 Q22 32 *)
  0x6f00e5fa;       (* arm_MOVI Q26 (word 4294967295) *)
  0xd374fe38;       (* arm_LSR X24 X17 52 *)
  0x9240cc84;       (* arm_AND X4 X4 (rvalue (word 4503599627370495)) *)
  0x4e825853;       (* arm_UZP2 Q19 Q2 Q2 32 *)
  0x8b180021;       (* arm_ADD X1 X1 X24 *)
  0x9b047cb8;       (* arm_MUL X24 X5 X4 *)
  0xd374ce24;       (* arm_LSL X4 X17 12 *)
  0x0ea128b8;       (* arm_XTN Q24 Q5 32 *)
  0x93c46031;       (* arm_EXTR X17 X1 X4 24 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x2eb782f5;       (* arm_UMLAL_VEC Q21 Q23 Q23 32 *)
  0xab0a01e4;       (* arm_ADDS X4 X15 X10 *)
  0xd374cc2a;       (* arm_LSL X10 X1 12 *)
  0xba1100ef;       (* arm_ADCS X15 X7 X17 *)
  0x4ea49f97;       (* arm_MUL_VEC Q23 Q28 Q4 32 128 *)
  0x92402087;       (* arm_AND X7 X4 (rvalue (word 511)) *)
  0xd374fc31;       (* arm_LSR X17 X1 52 *)
  0x9bcc7e61;       (* arm_UMULH X1 X19 X12 *)
  0x4e8558b1;       (* arm_UZP2 Q17 Q5 Q5 32 *)
  0x93c425e4;       (* arm_EXTR X4 X15 X4 9 *)
  0x8b110318;       (* arm_ADD X24 X24 X17 *)
  0x4ea59fbd;       (* arm_MUL_VEC Q29 Q29 Q5 32 128 *)
  0x93ca9311;       (* arm_EXTR X17 X24 X10 36 *)
  0x93cc412a;       (* arm_EXTR X10 X9 X12 16 *)
  0x4e84189c;       (* arm_UZP1 Q28 Q4 Q4 32 *)
  0xba110111;       (* arm_ADCS X17 X8 X17 *)
  0x9240cd48;       (* arm_AND X8 X10 (rvalue (word 4503599627370495)) *)
  0x2eb4c310;       (* arm_UMULL_VEC Q16 Q24 Q20 32 *)
  0x93cf262a;       (* arm_EXTR X10 X17 X15 9 *)
  0x9b087caf;       (* arm_MUL X15 X5 X8 *)
  0xa9002804;       (* arm_STP X4 X10 X0 (Immediate_Offset (iword (&0))) *)
  0xd374cf04;       (* arm_LSL X4 X24 12 *)
  0xd344fd28;       (* arm_LSR X8 X9 4 *)
  0x6ea02ae4;       (* arm_UADDLP Q4 Q23 32 *)
  0x9240cd08;       (* arm_AND X8 X8 (rvalue (word 4503599627370495)) *)
  0x2eb3c317;       (* arm_UMULL_VEC Q23 Q24 Q19 32 *)
  0x9b087ca8;       (* arm_MUL X8 X5 X8 *)
  0x93c9e04a;       (* arm_EXTR X10 X2 X9 56 *)
  0xd374ff18;       (* arm_LSR X24 X24 52 *)
  0x9240cd4a;       (* arm_AND X10 X10 (rvalue (word 4503599627370495)) *)
  0x8b1801ef;       (* arm_ADD X15 X15 X24 *)
  0x93c4c1e4;       (* arm_EXTR X4 X15 X4 48 *)
  0x9b0a7cb8;       (* arm_MUL X24 X5 X10 *)
  0xd374fdea;       (* arm_LSR X10 X15 52 *)
  0x6f601617;       (* arm_USRA_VEC Q23 Q16 32 64 128 *)
  0x8b0a010a;       (* arm_ADD X10 X8 X10 *)
  0x4f605484;       (* arm_SHL_VEC Q4 Q4 32 64 128 *)
  0xba0402d6;       (* arm_ADCS X22 X22 X4 *)
  0x93c2b0c4;       (* arm_EXTR X4 X6 X2 44 *)
  0xd374cdef;       (* arm_LSL X15 X15 12 *)
  0xd374fd48;       (* arm_LSR X8 X10 52 *)
  0x93cff14f;       (* arm_EXTR X15 X10 X15 60 *)
  0x9240cc8a;       (* arm_AND X10 X4 (rvalue (word 4503599627370495)) *)
  0x2ebb8384;       (* arm_UMLAL_VEC Q4 Q28 Q27 32 *)
  0x8b080308;       (* arm_ADD X8 X24 X8 *)
  0x93c681a4;       (* arm_EXTR X4 X13 X6 32 *)
  0x9b0a7cb8;       (* arm_MUL X24 X5 X10 *)
  0x4e9e5bd0;       (* arm_UZP2 Q16 Q30 Q30 32 *)
  0xd378ddea;       (* arm_LSL X10 X15 8 *)
  0x4ea00bdc;       (* arm_REV64_VEC Q28 Q30 32 *)
  0x9240cc8f;       (* arm_AND X15 X4 (rvalue (word 4503599627370495)) *)
  0x93ca2104;       (* arm_EXTR X4 X8 X10 8 *)
  0x9b0f7caa;       (* arm_MUL X10 X5 X15 *)
  0xd374cd0f;       (* arm_LSL X15 X8 12 *)
  0xba0402f7;       (* arm_ADCS X23 X23 X4 *)
  0xd374fd04;       (* arm_LSR X4 X8 52 *)
  0xd354fda8;       (* arm_LSR X8 X13 20 *)
  0x8b040304;       (* arm_ADD X4 X24 X4 *)
  0x9b087ca8;       (* arm_MUL X8 X5 X8 *)
  0xd374fc98;       (* arm_LSR X24 X4 52 *)
  0x93cf508f;       (* arm_EXTR X15 X4 X15 20 *)
  0xd374cc84;       (* arm_LSL X4 X4 12 *)
  0x8b18014a;       (* arm_ADD X10 X10 X24 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0x93c48144;       (* arm_EXTR X4 X10 X4 32 *)
  0x9bce7e85;       (* arm_UMULH X5 X20 X14 *)
  0xba040063;       (* arm_ADCS X3 X3 X4 *)
  0x6f6014d2;       (* arm_USRA_VEC Q18 Q6 32 64 128 *)
  0xd374cd50;       (* arm_LSL X16 X10 12 *)
  0x93d725f8;       (* arm_EXTR X24 X15 X23 9 *)
  0xd374fd4a;       (* arm_LSR X10 X10 52 *)
  0x4e80581b;       (* arm_UZP2 Q27 Q0 Q0 32 *)
  0x8b0a0108;       (* arm_ADD X8 X8 X10 *)
  0x93cf246a;       (* arm_EXTR X10 X3 X15 9 *)
  0x93d126c4;       (* arm_EXTR X4 X22 X17 9 *)
  0x4e3a1ef9;       (* arm_AND_VEC Q25 Q23 Q26 128 *)
  0xd36cfd11;       (* arm_LSR X17 X8 44 *)
  0x93d0b10f;       (* arm_EXTR X15 X8 X16 44 *)
  0x93d626f0;       (* arm_EXTR X16 X23 X22 9 *)
  0x0ea12bc7;       (* arm_XTN Q7 Q30 32 *)
  0x4e083c88;       (* arm_UMOV X8 Q4 0 8 *)
  0xa9022818;       (* arm_STP X24 X10 X0 (Immediate_Offset (iword (&32))) *)
  0x6ea02bbe;       (* arm_UADDLP Q30 Q29 32 *)
  0xa9014004;       (* arm_STP X4 X16 X0 (Immediate_Offset (iword (&16))) *)
  0x9bd37e98;       (* arm_UMULH X24 X20 X19 *)
  0xba0f02af;       (* arm_ADCS X15 X21 X15 *)
  0x9a110170;       (* arm_ADC X16 X11 X17 *)
  0xeb13028b;       (* arm_SUBS X11 X20 X19 *)
  0x0ea12805;       (* arm_XTN Q5 Q0 32 *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0x93c325e3;       (* arm_EXTR X3 X15 X3 9 *)
  0x4e183c96;       (* arm_UMOV X22 Q4 1 8 *)
  0xda8b2575;       (* arm_CNEG X21 X11 Condition_CC *)
  0xeb0e018a;       (* arm_SUBS X10 X12 X14 *)
  0x4ea09f9f;       (* arm_MUL_VEC Q31 Q28 Q0 32 128 *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0xda91222b;       (* arm_CINV X11 X17 Condition_CC *)
  0x4f6057c4;       (* arm_SHL_VEC Q4 Q30 32 64 128 *)
  0x2eb0c0bc;       (* arm_UMULL_VEC Q28 Q5 Q16 32 *)
  0x93cf2617;       (* arm_EXTR X23 X16 X15 9 *)
  0xab050104;       (* arm_ADDS X4 X8 X5 *)
  0x9b0a7eb1;       (* arm_MUL X17 X21 X10 *)
  0x2ea7c0b6;       (* arm_UMULL_VEC Q22 Q5 Q7 32 *)
  0x9a1f00af;       (* arm_ADC X15 X5 XZR *)
  0xab160084;       (* arm_ADDS X4 X4 X22 *)
  0x6ea02be2;       (* arm_UADDLP Q2 Q31 32 *)
  0xd349fe05;       (* arm_LSR X5 X16 9 *)
  0xba0101f0;       (* arm_ADCS X16 X15 X1 *)
  0x4e083e4f;       (* arm_UMOV X15 Q18 0 8 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0x9bca7eaa;       (* arm_UMULH X10 X21 X10 *)
  0xab160216;       (* arm_ADDS X22 X16 X22 *)
  0x2eb48304;       (* arm_UMLAL_VEC Q4 Q24 Q20 32 *)
  0x2eb0c37e;       (* arm_UMULL_VEC Q30 Q27 Q16 32 *)
  0xa9035c03;       (* arm_STP X3 X23 X0 (Immediate_Offset (iword (&48))) *)
  0x8b0500e3;       (* arm_ADD X3 X7 X5 *)
  0x9a1f0030;       (* arm_ADC X16 X1 XZR *)
  0x6f6016dc;       (* arm_USRA_VEC Q28 Q22 32 64 128 *)
  0x9b137e97;       (* arm_MUL X23 X20 X19 *)
  0xca0b0221;       (* arm_EOR X1 X17 X11 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0x4e183e51;       (* arm_UMOV X17 Q18 1 8 *)
  0x2eb3c232;       (* arm_UMULL_VEC Q18 Q17 Q19 32 *)
  0xba010087;       (* arm_ADCS X7 X4 X1 *)
  0xca0b0141;       (* arm_EOR X1 X10 X11 *)
  0x2eb48239;       (* arm_UMLAL_VEC Q25 Q17 Q20 32 *)
  0x6f00e5f0;       (* arm_MOVI Q16 (word 4294967295) *)
  0xba0102d6;       (* arm_ADCS X22 X22 X1 *)
  0x6f6016f2;       (* arm_USRA_VEC Q18 Q23 32 64 128 *)
  0x9bce7dc4;       (* arm_UMULH X4 X14 X14 *)
  0x9a0b0201;       (* arm_ADC X1 X16 X11 *)
  0xab08010a;       (* arm_ADDS X10 X8 X8 *)
  0x4f605457;       (* arm_SHL_VEC Q23 Q2 32 64 128 *)
  0xf9002003;       (* arm_STR X3 X0 (Immediate_Offset (word 64)) *)
  0xba0700e5;       (* arm_ADCS X5 X7 X7 *)
  0x4e301f90;       (* arm_AND_VEC Q16 Q28 Q16 128 *)
  0x6f60179e;       (* arm_USRA_VEC Q30 Q28 32 64 128 *)
  0xba1602c7;       (* arm_ADCS X7 X22 X22 *)
  0x4e183c75;       (* arm_UMOV X21 Q3 1 8 *)
  0xba01002b;       (* arm_ADCS X11 X1 X1 *)
  0x2ea78370;       (* arm_UMLAL_VEC Q16 Q27 Q7 32 *)
  0x9a1f03f6;       (* arm_ADC X22 XZR XZR *)
  0xab1701f0;       (* arm_ADDS X16 X15 X23 *)
  0x9b0c7dc8;       (* arm_MUL X8 X14 X12 *)
  0x2ea780b7;       (* arm_UMLAL_VEC Q23 Q5 Q7 32 *)
  0x6f601732;       (* arm_USRA_VEC Q18 Q25 32 64 128 *)
  0x9bcc7dcf;       (* arm_UMULH X15 X14 X12 *)
  0xba1802b5;       (* arm_ADCS X21 X21 X24 *)
  0x6f60161e;       (* arm_USRA_VEC Q30 Q16 32 64 128 *)
  0x9a1f0221;       (* arm_ADC X1 X17 XZR *)
  0xab170203;       (* arm_ADDS X3 X16 X23 *)
  0xba1802b5;       (* arm_ADCS X21 X21 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab150158;       (* arm_ADDS X24 X10 X21 *)
  0x9bcc7d95;       (* arm_UMULH X21 X12 X12 *)
  0xba0100b0;       (* arm_ADCS X16 X5 X1 *)
  0xba1f00ea;       (* arm_ADCS X10 X7 XZR *)
  0x4e183eb1;       (* arm_UMOV X17 Q21 1 8 *)
  0xba1f0177;       (* arm_ADCS X23 X11 XZR *)
  0x9a1f02c5;       (* arm_ADC X5 X22 XZR *)
  0xab080081;       (* arm_ADDS X1 X4 X8 *)
  0xba0f0236;       (* arm_ADCS X22 X17 X15 *)
  0xa9401011;       (* arm_LDP X17 X4 X0 (Immediate_Offset (iword (&0))) *)
  0x4e083eab;       (* arm_UMOV X11 Q21 0 8 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab080021;       (* arm_ADDS X1 X1 X8 *)
  0xba0f02cf;       (* arm_ADCS X15 X22 X15 *)
  0x9a1f02a8;       (* arm_ADC X8 X21 XZR *)
  0xab0a0176;       (* arm_ADDS X22 X11 X10 *)
  0x4e083c75;       (* arm_UMOV X21 Q3 0 8 *)
  0xba17002b;       (* arm_ADCS X11 X1 X23 *)
  0xa9412801;       (* arm_LDP X1 X10 X0 (Immediate_Offset (iword (&16))) *)
  0xba0501ef;       (* arm_ADCS X15 X15 X5 *)
  0x9a1f0107;       (* arm_ADC X7 X8 XZR *)
  0xab150228;       (* arm_ADDS X8 X17 X21 *)
  0x4e183c97;       (* arm_UMOV X23 Q4 1 8 *)
  0xa9425405;       (* arm_LDP X5 X21 X0 (Immediate_Offset (iword (&32))) *)
  0xba030091;       (* arm_ADCS X17 X4 X3 *)
  0xf9402004;       (* arm_LDR X4 X0 (Immediate_Offset (word 64)) *)
  0x4e083e43;       (* arm_UMOV X3 Q18 0 8 *)
  0xba180038;       (* arm_ADCS X24 X1 X24 *)
  0xa9004408;       (* arm_STP X8 X17 X0 (Immediate_Offset (iword (&0))) *)
  0xba100151;       (* arm_ADCS X17 X10 X16 *)
  0xa9434001;       (* arm_LDP X1 X16 X0 (Immediate_Offset (iword (&48))) *)
  0xba1600a5;       (* arm_ADCS X5 X5 X22 *)
  0xba0b02a8;       (* arm_ADCS X8 X21 X11 *)
  0xa9022005;       (* arm_STP X5 X8 X0 (Immediate_Offset (iword (&32))) *)
  0xba0f0021;       (* arm_ADCS X1 X1 X15 *)
  0x4e183eef;       (* arm_UMOV X15 Q23 1 8 *)
  0xba070215;       (* arm_ADCS X21 X16 X7 *)
  0xa9035401;       (* arm_STP X1 X21 X0 (Immediate_Offset (iword (&48))) *)
  0x9a1f008a;       (* arm_ADC X10 X4 XZR *)
  0xeb0c01c7;       (* arm_SUBS X7 X14 X12 *)
  0x4e183e50;       (* arm_UMOV X16 Q18 1 8 *)
  0xda8724e5;       (* arm_CNEG X5 X7 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb0601ab;       (* arm_SUBS X11 X13 X6 *)
  0x4e083ee8;       (* arm_UMOV X8 Q23 0 8 *)
  0xda8b2567;       (* arm_CNEG X7 X11 Condition_CC *)
  0xda842095;       (* arm_CINV X21 X4 Condition_CC *)
  0x4e083fcb;       (* arm_UMOV X11 Q30 0 8 *)
  0xab0302e4;       (* arm_ADDS X4 X23 X3 *)
  0x9b077cb6;       (* arm_MUL X22 X5 X7 *)
  0x4e183fd7;       (* arm_UMOV X23 Q30 1 8 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba0b01f0;       (* arm_ADCS X16 X15 X11 *)
  0x9a1f02eb;       (* arm_ADC X11 X23 XZR *)
  0x9bc77ca3;       (* arm_UMULH X3 X5 X7 *)
  0xa9014418;       (* arm_STP X24 X17 X0 (Immediate_Offset (iword (&16))) *)
  0x4e083c85;       (* arm_UMOV X5 Q4 0 8 *)
  0xeb13028f;       (* arm_SUBS X15 X20 X19 *)
  0xda8f25e7;       (* arm_CNEG X7 X15 Condition_CC *)
  0xf900200a;       (* arm_STR X10 X0 (Immediate_Offset (word 64)) *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xeb090058;       (* arm_SUBS X24 X2 X9 *)
  0xda982711;       (* arm_CNEG X17 X24 Condition_CC *)
  0xda81202f;       (* arm_CINV X15 X1 Condition_CC *)
  0xab050097;       (* arm_ADDS X23 X4 X5 *)
  0x9bd17ce1;       (* arm_UMULH X1 X7 X17 *)
  0xba040118;       (* arm_ADCS X24 X8 X4 *)
  0xba08020a;       (* arm_ADCS X10 X16 X8 *)
  0xca1502c8;       (* arm_EOR X8 X22 X21 *)
  0xba100170;       (* arm_ADCS X16 X11 X16 *)
  0x9b117cf6;       (* arm_MUL X22 X7 X17 *)
  0xca0f0031;       (* arm_EOR X17 X1 X15 *)
  0x9a0b03e1;       (* arm_ADC X1 XZR X11 *)
  0xab05030b;       (* arm_ADDS X11 X24 X5 *)
  0xca150067;       (* arm_EOR X7 X3 X21 *)
  0xba170143;       (* arm_ADCS X3 X10 X23 *)
  0xba180218;       (* arm_ADCS X24 X16 X24 *)
  0xba0a0024;       (* arm_ADCS X4 X1 X10 *)
  0xca0f02ca;       (* arm_EOR X10 X22 X15 *)
  0xba1003f0;       (* arm_ADCS X16 XZR X16 *)
  0x9a0103e1;       (* arm_ADC X1 XZR X1 *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xba080088;       (* arm_ADCS X8 X4 X8 *)
  0xba070216;       (* arm_ADCS X22 X16 X7 *)
  0x9a150027;       (* arm_ADC X7 X1 X21 *)
  0xeb0c0275;       (* arm_SUBS X21 X19 X12 *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xda9526a1;       (* arm_CNEG X1 X21 Condition_CC *)
  0xeb0201b5;       (* arm_SUBS X21 X13 X2 *)
  0xda842090;       (* arm_CINV X16 X4 Condition_CC *)
  0xda9526a4;       (* arm_CNEG X4 X21 Condition_CC *)
  0xb10005ff;       (* arm_CMN X15 (rvalue (word 1)) *)
  0xba0a02f5;       (* arm_ADCS X21 X23 X10 *)
  0x9b047c37;       (* arm_MUL X23 X1 X4 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xba0f0063;       (* arm_ADCS X3 X3 X15 *)
  0x9bc47c21;       (* arm_UMULH X1 X1 X4 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba0f02d6;       (* arm_ADCS X22 X22 X15 *)
  0xca1002f1;       (* arm_EOR X17 X23 X16 *)
  0x9a0f00ef;       (* arm_ADC X15 X7 X15 *)
  0xeb0e0287;       (* arm_SUBS X7 X20 X14 *)
  0xda8724e7;       (* arm_CNEG X7 X7 Condition_CC *)
  0xda9f23e4;       (* arm_CSETM X4 Condition_CC *)
  0xeb0c028a;       (* arm_SUBS X10 X20 X12 *)
  0xda8a2557;       (* arm_CNEG X23 X10 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xeb0900cc;       (* arm_SUBS X12 X6 X9 *)
  0xda842094;       (* arm_CINV X20 X4 Condition_CC *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba110311;       (* arm_ADCS X17 X24 X17 *)
  0x9b0c7ce4;       (* arm_MUL X4 X7 X12 *)
  0xba010108;       (* arm_ADCS X8 X8 X1 *)
  0x9bcc7ce1;       (* arm_UMULH X1 X7 X12 *)
  0xba1002d8;       (* arm_ADCS X24 X22 X16 *)
  0x9a1001e7;       (* arm_ADC X7 X15 X16 *)
  0xeb0901ac;       (* arm_SUBS X12 X13 X9 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0xda8a214d;       (* arm_CINV X13 X10 Condition_CC *)
  0xeb0e0273;       (* arm_SUBS X19 X19 X14 *)
  0x9b0c7ee9;       (* arm_MUL X9 X23 X12 *)
  0xda932673;       (* arm_CNEG X19 X19 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xca140030;       (* arm_EOR X16 X1 X20 *)
  0xeb0200d6;       (* arm_SUBS X22 X6 X2 *)
  0x9bcc7eec;       (* arm_UMULH X12 X23 X12 *)
  0xca140081;       (* arm_EOR X1 X4 X20 *)
  0xda8a2144;       (* arm_CINV X4 X10 Condition_CC *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xba01016f;       (* arm_ADCS X15 X11 X1 *)
  0xca0d0186;       (* arm_EOR X6 X12 X13 *)
  0xba10006a;       (* arm_ADCS X10 X3 X16 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0xca0d0137;       (* arm_EOR X23 X9 X13 *)
  0xba140102;       (* arm_ADCS X2 X8 X20 *)
  0x9b167e6b;       (* arm_MUL X11 X19 X22 *)
  0xba140318;       (* arm_ADCS X24 X24 X20 *)
  0x9a1400e7;       (* arm_ADC X7 X7 X20 *)
  0xb10005bf;       (* arm_CMN X13 (rvalue (word 1)) *)
  0xba170143;       (* arm_ADCS X3 X10 X23 *)
  0x9bd67e76;       (* arm_UMULH X22 X19 X22 *)
  0xba060231;       (* arm_ADCS X17 X17 X6 *)
  0xca0402cc;       (* arm_EOR X12 X22 X4 *)
  0x93d5fdf6;       (* arm_EXTR X22 X15 X21 63 *)
  0xba0d0048;       (* arm_ADCS X8 X2 X13 *)
  0x93c5feb5;       (* arm_EXTR X21 X21 X5 63 *)
  0xa9405c10;       (* arm_LDP X16 X23 X0 (Immediate_Offset (iword (&0))) *)
  0xba0d0314;       (* arm_ADCS X20 X24 X13 *)
  0xca040161;       (* arm_EOR X1 X11 X4 *)
  0x9a0d00e6;       (* arm_ADC X6 X7 X13 *)
  0xb100049f;       (* arm_CMN X4 (rvalue (word 1)) *)
  0xa9411c02;       (* arm_LDP X2 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xba010061;       (* arm_ADCS X1 X3 X1 *)
  0x93cffc33;       (* arm_EXTR X19 X1 X15 63 *)
  0xba0c022e;       (* arm_ADCS X14 X17 X12 *)
  0x93c1fdc1;       (* arm_EXTR X1 X14 X1 63 *)
  0xd37ff8b1;       (* arm_LSL X17 X5 1 *)
  0xba040108;       (* arm_ADCS X8 X8 X4 *)
  0x93ce210c;       (* arm_EXTR X12 X8 X14 8 *)
  0xa9422c0f;       (* arm_LDP X15 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xba040289;       (* arm_ADCS X9 X20 X4 *)
  0x9a0400c3;       (* arm_ADC X3 X6 X4 *)
  0xab100190;       (* arm_ADDS X16 X12 X16 *)
  0x93c82126;       (* arm_EXTR X6 X9 X8 8 *)
  0xa943300e;       (* arm_LDP X14 X12 X0 (Immediate_Offset (iword (&48))) *)
  0x93c92068;       (* arm_EXTR X8 X3 X9 8 *)
  0xba1700d4;       (* arm_ADCS X20 X6 X23 *)
  0xf9402018;       (* arm_LDR X24 X0 (Immediate_Offset (word 64)) *)
  0xd348fc66;       (* arm_LSR X6 X3 8 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x92402022;       (* arm_AND X2 X1 (rvalue (word 511)) *)
  0x8a080281;       (* arm_AND X1 X20 X8 *)
  0xba0700c4;       (* arm_ADCS X4 X6 X7 *)
  0xba0f0223;       (* arm_ADCS X3 X17 X15 *)
  0x8a040021;       (* arm_AND X1 X1 X4 *)
  0xba0b02a9;       (* arm_ADCS X9 X21 X11 *)
  0x8a030021;       (* arm_AND X1 X1 X3 *)
  0xba0e02c6;       (* arm_ADCS X6 X22 X14 *)
  0x8a090021;       (* arm_AND X1 X1 X9 *)
  0x8a060035;       (* arm_AND X21 X1 X6 *)
  0xba0c026e;       (* arm_ADCS X14 X19 X12 *)
  0x9a020301;       (* arm_ADC X1 X24 X2 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xb277d82c;       (* arm_ORR X12 X1 (rvalue (word 18446744073709551104)) *)
  0xd349fc21;       (* arm_LSR X1 X1 9 *)
  0xba01021f;       (* arm_ADCS XZR X16 X1 *)
  0x8a0e02b5;       (* arm_AND X21 X21 X14 *)
  0xba1f02bf;       (* arm_ADCS XZR X21 XZR *)
  0xba1f019f;       (* arm_ADCS XZR X12 XZR *)
  0xba010215;       (* arm_ADCS X21 X16 X1 *)
  0xba1f0281;       (* arm_ADCS X1 X20 XZR *)
  0xba1f0113;       (* arm_ADCS X19 X8 XZR *)
  0xa9000415;       (* arm_STP X21 X1 X0 (Immediate_Offset (iword (&0))) *)
  0xba1f0081;       (* arm_ADCS X1 X4 XZR *)
  0xba1f0075;       (* arm_ADCS X21 X3 XZR *)
  0xa9010413;       (* arm_STP X19 X1 X0 (Immediate_Offset (iword (&16))) *)
  0xba1f0121;       (* arm_ADCS X1 X9 XZR *)
  0xa9020415;       (* arm_STP X21 X1 X0 (Immediate_Offset (iword (&32))) *)
  0xba1f00d5;       (* arm_ADCS X21 X6 XZR *)
  0xba1f01c1;       (* arm_ADCS X1 X14 XZR *)
  0xa9030415;       (* arm_STP X21 X1 X0 (Immediate_Offset (iword (&48))) *)
  0x9a1f0181;       (* arm_ADC X1 X12 XZR *)
  0x92402021;       (* arm_AND X1 X1 (rvalue (word 511)) *)
  0xf9002001;       (* arm_STR X1 X0 (Immediate_Offset (word 64)) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
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
  0xa943302b;       (* arm_LDP X11 X12 X1 (Immediate_Offset (iword (&48))) *)
  0xa9430c44;       (* arm_LDP X4 X3 X2 (Immediate_Offset (iword (&48))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf940202d;       (* arm_LDR X13 X1 (Immediate_Offset (word 64)) *)
  0xf9402044;       (* arm_LDR X4 X2 (Immediate_Offset (word 64)) *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0xa903300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200d;       (* arm_STR X13 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P521_JSCALARMUL_EXEC = ARM_MK_EXEC_RULE p521_jscalarmul_mc;;

(* ------------------------------------------------------------------------- *)
(* Level 1: the embedded field squaring and multiplication                   *)
(* ------------------------------------------------------------------------- *)

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

let P_521_AS_WORDLIST = prove
 (`p_521 =
   bignum_of_wordlist
    [word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word(0x1FF)]`,
  REWRITE_TAC[p_521; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_EQ_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] = p_521 <=>
   (!i. i < 64
        ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
            bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
   (!i. i < 9 ==> bit i n8) /\ (!i. i < 64 ==> 9 <= i ==> ~bit i n8)`,
  REWRITE_TAC[P_521_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let BIGNUM_FROM_MEMORY_LE_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] <= p_521 <=>
   !i. i < 64 ==> 9 <= i ==> ~bit i n8`,
  SIMP_TAC[P_521; ARITH_RULE `p_521 = 2 EXP 521 - 1 ==>
    (n <= p_521 <=> n DIV 2 EXP (8 * 64) < 2 EXP 9)`] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `8`; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV; EXP; DIV_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; GSYM UPPER_BITS_ZERO] THEN
  MP_TAC(ISPEC `n8:int64` BIT_TRIVIAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MESON_TAC[NOT_LE]);;

let BIGNUM_FROM_MEMORY_LT_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] < p_521 <=>
   (!i. i < 64 ==> 9 <= i ==> ~bit i n8) /\
   ~((!i. i < 64
          ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
              bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
     (!i. i < 9 ==> bit i n8))`,
  GEN_REWRITE_TAC LAND_CONV [LT_LE] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_P521; BIGNUM_FROM_MEMORY_LE_P521] THEN
  MESON_TAC[]);;

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

let LOCAL_SQR_P521_SUBR_CORRECT =
  let lemma = prove(`!z x n pc.
        nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x2984) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word(pc + 0x2984 + LENGTH bignum_sqr_p521_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (n EXP 2) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                         X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9)])`,
    SUBGOAL_THEN
      `bignum_sqr_p521_core_mc =
        SUB_LIST (0x2984, LENGTH bignum_sqr_p521_core_mc) p521_jscalarmul_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_SQR_P521_CORE_EXEC;
                  bignum_sqr_p521_core_mc; p521_jscalarmul_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
      ARM_SUB_LIST_OF_MC_TAC BIGNUM_SQR_P521_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_SQR_P521_CORE_EXEC] th)
        [fst BIGNUM_SQR_P521_CORE_EXEC;fst P521_JSCALARMUL_EXEC])) in
  prove(`!z x n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH p521_jscalarmul_mc); (x,8 * 9); (z,8 * 9)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x2978) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (n EXP 2) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                         X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                         memory :> bytes(word_sub stackpointer (word 48),48)])`,
    ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
      (let th = REWRITE_RULE [fst BIGNUM_SQR_P521_CORE_EXEC] lemma in
        CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
      `[X19;X20;X21;X22;X23;X24]` 48);;

let LOCAL_MUL_P521_SUBR_CORRECT =
  let lemma = prove(`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH p521_jscalarmul_mc); (z,8 * 9); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH p521_jscalarmul_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x1f00) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word(pc + 0x1f00 + LENGTH bignum_mul_p521_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                         X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9); memory :> bytes(stackpointer,80)])`,
    SUBGOAL_THEN
      `bignum_mul_p521_core_mc =
        SUB_LIST (0x1f00, LENGTH bignum_mul_p521_core_mc) p521_jscalarmul_mc` MP_TAC THENL [
      REWRITE_TAC[fst BIGNUM_MUL_P521_CORE_EXEC;
                  bignum_mul_p521_core_mc; p521_jscalarmul_mc] THEN
      CONV_TAC (RAND_CONV SUB_LIST_CONV) THEN REFL_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th ->
      ARM_SUB_LIST_OF_MC_TAC BIGNUM_MUL_P521_CORE_CORRECT
        (REWRITE_RULE [fst BIGNUM_MUL_P521_CORE_EXEC] th)
        [fst BIGNUM_MUL_P521_CORE_EXEC;fst P521_JSCALARMUL_EXEC])) in
  prove(`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [(word pc,LENGTH p521_jscalarmul_mc); (x,8 * 9); (y,8 * 9); (z,8 * 9)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x1eec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = returnaddress /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                         X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                         memory :> bytes(word_sub stackpointer (word 144),144)])`,
    ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
      (let th = REWRITE_RULE [fst BIGNUM_MUL_P521_CORE_EXEC] lemma in
        CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
      `[X19;X20;X21;X22;X23;X24;X25;X26]` 144);;

let LOCAL_SUB_P521_SUBR_CORRECT = prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x31d0) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_521 /\ n < p_521
                  ==> &(bignum_from_memory (z,9) s) = (&m - &n) rem &p_521))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst P521_JSCALARMUL_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 9)) s0` THEN

  (*** Initial subtraction x - y, comparison result ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC [3;4;7;8;11;12;15;16;19] (1--19) THEN

  SUBGOAL_THEN `carry_s19 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (20--28) (20--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Map things into the reals, doing case analysis over comparison ***)

  TRANS_TAC EQ_TRANS `if m < n then &m - &n + &p_521:int else &m - &n` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
   REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th];
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
   EXISTS_TAC `if m:num < n then --(&1):int else &0` THEN
   MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_521] THEN INT_ARITH_TAC] THEN

  (*** Hence show that we get the right result in 521 bits ***)

  CONV_TAC SYM_CONV THEN
  CONV_TAC(RAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`521`; `&0:real`] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Level 2: the embedded point operations.                                   *)
(* ------------------------------------------------------------------------- *)

let lvs =
 ["x_1",[`X27`;`0`];
  "y_1",[`X27`;`72`];
  "z_1",[`X27`;`144`];
  "x_3",[`X26`;`0`];
  "y_3",[`X26`;`72`];
  "z_3",[`X26`;`144`];
  "z2",[`SP`;`0`];
  "y4",[`SP`;`0`];
  "y2",[`SP`;`72`];
  "t1",[`SP`;`144`];
  "t2",[`SP`;`216`];
  "x2p",[`SP`;`216`];
  "dx2",[`SP`;`216`];
  "xy2",[`SP`;`288`];
  "x4p",[`SP`;`360`];
  "d",[`SP`;`360`];
  "tmp",[`SP`;`432`]];;

let PROLOGUE_SUBROUTINE_SIM_TAC corth inargs outarg m inouts =
  let main_tac =
     ARM_SUBROUTINE_SIM_ABBREV_TAC
      (p521_jscalarmul_mc,P521_JSCALARMUL_EXEC,0,p521_jscalarmul_mc,corth)
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
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC ((n+1)--(n+m+k)) THEN
    main_tac (name_of dvar') (n+m+k+1));;

let LOCAL_MUL_P521_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_MUL_P521_SUBR_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 9)) s`;
    `read (memory :> bytes(read X2 s,8 * 9)) s`;
    `pc:num`; `read SP s`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 9)) s'`;;

let LOCAL_SQR_P521_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_SQR_P521_SUBR_CORRECT
   [`read X0 s`; `read X1 s`;
    `read (memory :> bytes(read X1 s,8 * 9)) s`;
    `pc:num`; `read SP s`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 9)) s'`;;

let LOCAL_ADD_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_mc 37 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (word_add (read p3 t) (word n3),72)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read PC s = pcout /\
              (m < p_521 /\ n < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 9)) s = (m + n) MOD p_521))
         (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the m < p_521 /\ n < p_521 assumption ***)

  ASM_CASES_TAC `m < p_521 /\ n < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JSCALARMUL_EXEC (1--37)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial non-overflowing addition s = x + y + 1 ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC [4;5;8;9;12;13;16;17;20] (1--20) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s4;sum_s5;sum_s8;sum_s9;sum_s12;sum_s13;sum_s16;sum_s17;sum_s20] =
    m + n + 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[p_521] THEN REAL_ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The net comparison s >= 2^521 <=> x + y >= p_521 ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (21--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LT]) THEN
  SUBGOAL_THEN `512 <= val(sum_s20:int64) <=> p_521 <= m + n`
  SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS `512 <= (m + n + 1) DIV 2 EXP 512` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (23::(25--32)) (23--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 9`;
    `if p_521 <= m + n then &(m + n + 1) - &2 pow 521
     else &(m + n + 1) - &1:real`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `s = m + n + 1` THEN POP_ASSUM(K ALL_TAC) THEN EXPAND_TAC "s" THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_SUB_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_mc 34 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (word_add (read p3 t) (word n3),72)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read PC s = pcout /\
              (m < p_521 /\ n < p_521
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 9)) s) = (&m - &n) rem &p_521))
         (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
          MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial subtraction x - y, comparison result ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC [3;4;7;8;11;12;15;16;19] (1--19) THEN

  SUBGOAL_THEN `carry_s19 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (20--28) (20--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Map things into the reals, doing case analysis over comparison ***)

  TRANS_TAC EQ_TRANS `if m < n then &m - &n + &p_521:int else &m - &n` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
   REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th];
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
   EXISTS_TAC `if m:num < n then --(&1):int else &0` THEN
   MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_521] THEN INT_ARITH_TAC] THEN

  (*** Hence show that we get the right result in 521 bits ***)

  CONV_TAC SYM_CONV THEN
  CONV_TAC(RAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`521`; `&0:real`] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_CMSUBC9_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_mc 107 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < 2 * p_521 /\ n <= p_521
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 9)) s) = (&12 * &m - &9 * &n) rem &p_521))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17;
                        X19; X20; X21; X22; X23] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JSCALARMUL_EXEC (1--107)] THEN

  (*** Digitize and introduce the sign-flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
    [word_not n_0; word_not n_1; word_not n_2; word_not n_3; word_not n_4;
     word_not n_5; word_not n_6; word_not n_7; word_xor n_8 (word 0x1FF)]` THEN

  SUBGOAL_THEN `p_521 - n = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n + m:num = p ==> p - n = m`) THEN
    MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    SUBGOAL_THEN
     `&(val(word_xor (n_8:int64) (word 511))):real = &2 pow 9 - &1 - &(val n_8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_VAL_WORD_XOR];
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
      REAL_ARITH_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH
     `n':real = n ==> (n + c) - &2 * n' = c - n`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n <= p_521` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `n <= p ==> n DIV 2 EXP 512 <= p DIV 2 EXP 512`)) THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_521 =
    (&12 * &m + &9 * (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca = 12 * m + 9 * n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "n'"] THEN UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (1--86) (1--86) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s37; sum_s73; sum_s74; sum_s76;
      sum_s78; sum_s80; sum_s82; sum_s84; sum_s86] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "ca" THEN CONJ_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN EXPAND_TAC "n'" THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    UNDISCH_THEN `p_521 - n = n'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (87--89) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s86 9`;
    `d:int64 = word_or sum_s86 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s73 (word_and sum_s74 (word_and sum_s76
      (word_and sum_s78 (word_and sum_s80 (word_and sum_s82 sum_s84)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (90--92) (90--92) THEN
  SUBGOAL_THEN
   `carry_s92 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s37:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (93--101) (93--107) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s107" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s86:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s86:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s37; sum_s73; sum_s74; sum_s76; sum_s78; sum_s80; sum_s82; sum_s84] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s92`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s92" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s73; sum_s74; sum_s76; sum_s78; sum_s80; sum_s82; sum_s84] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s37:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s86:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s86:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s37:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_CMSUB41_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_mc 57 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < 2 * p_521 /\ n <= p_521
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 9)) s) = (&4 * &m - &n) rem &p_521))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JSCALARMUL_EXEC (1--57)] THEN

  (*** Digitize and introduce the sign-flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
    [word_not n_0; word_not n_1; word_not n_2; word_not n_3; word_not n_4;
     word_not n_5; word_not n_6; word_not n_7; word_xor n_8 (word 0x1FF)]` THEN

  SUBGOAL_THEN `p_521 - n = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n + m:num = p ==> p - n = m`) THEN
    MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    SUBGOAL_THEN
     `&(val(word_xor (n_8:int64) (word 511))):real = &2 pow 9 - &1 - &(val n_8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_VAL_WORD_XOR];
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
      REAL_ARITH_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH
     `n':real = n ==> (n + c) - &2 * n' = c - n`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n <= p_521` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `n <= p ==> n DIV 2 EXP 512 <= p DIV 2 EXP 512`)) THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Now introduce the shifted version of m ***)

  ABBREV_TAC
   `m' = bignum_of_wordlist
     [word_shl m_0 2;
      word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
      word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
      word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
      word_subword ((word_join:int64->int64->int128) m_4 m_3) (62,64);
      word_subword ((word_join:int64->int64->int128) m_5 m_4) (62,64);
      word_subword ((word_join:int64->int64->int128) m_6 m_5) (62,64);
      word_subword ((word_join:int64->int64->int128) m_7 m_6) (62,64);
      word_subword ((word_join:int64->int64->int128) m_8 m_7) (62,64)]` THEN
  SUBGOAL_THEN `4 * m = m'` ASSUME_TAC THENL
   [SUBGOAL_THEN `m DIV 2 EXP 512 < 2 EXP 62` MP_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "m'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `62` th) THEN MP_TAC(SPEC `63` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN DISCH_TAC THEN
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
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&4 * &m - &n) rem &p_521 =
    (&4 * &m + (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca:num = m' + n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "m'"; "n'"] THEN
    UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC [17;18;20;22;25;27;30;32;36] (1--36) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s17; sum_s18; sum_s20; sum_s22;
      sum_s25; sum_s27; sum_s30; sum_s32; sum_s36] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED] THEN EXPAND_TAC "ca"] THEN
    UNDISCH_THEN `p_521 - n = n'` (K ALL_TAC) THEN
    UNDISCH_THEN `4 * m = m'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m'"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (37--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s36 9`;
    `d:int64 = word_or sum_s36 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s18 (word_and sum_s20 (word_and sum_s22
      (word_and sum_s25 (word_and sum_s27 (word_and sum_s30 sum_s32)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (40--42) (40--42) THEN
  SUBGOAL_THEN
   `carry_s42 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s17:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (43--51) (43--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s57" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s36:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s36:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s17; sum_s18; sum_s20; sum_s22; sum_s25; sum_s27; sum_s30; sum_s32] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s42`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s42" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s18; sum_s20; sum_s22; sum_s25; sum_s27; sum_s30; sum_s32] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s17:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s36:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s36:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s17:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_CMSUB38_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_mc 82 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,LENGTH p521_jscalarmul_mc) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < 2 * p_521 /\ n <= p_521
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 9)) s) = (&3 * &m - &8 *  &n) rem &p_521))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17;
                        X19; X20; X21; X22; X23] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JSCALARMUL_EXEC (1--82)] THEN

  (*** Digitize and introduce the shifted and flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
     [word_shl (word_not n_0) 3;
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_1) (word_not n_0)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_2) (word_not n_1)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_3) (word_not n_2)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_4) (word_not n_3)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_5) (word_not n_4)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_6) (word_not n_5)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_7) (word_not n_6)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_xor n_8 (word 0x1FF)) (word_not n_7)) (61,64)]` THEN
  SUBGOAL_THEN `8 * (p_521 - n) = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `8 * n + m = 8 * p ==> 8 * (p - n) = m`) THEN
    SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
     [UNDISCH_TAC `n <= p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "n'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
     `(!i. P i) ==> (!i. i < 64 ==> P i)`)) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_SHL;
                BIT_WORD_NOT; BIT_WORD_XOR; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_521] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN

  (*** Now introduce the shifted version of m for 3 * m = 2 * m + m ***)

  ABBREV_TAC
   `m' = bignum_of_wordlist
     [word_shl m_0 1;
      word_subword ((word_join:int64->int64->int128) m_1 m_0) (63,64);
      word_subword ((word_join:int64->int64->int128) m_2 m_1) (63,64);
      word_subword ((word_join:int64->int64->int128) m_3 m_2) (63,64);
      word_subword ((word_join:int64->int64->int128) m_4 m_3) (63,64);
      word_subword ((word_join:int64->int64->int128) m_5 m_4) (63,64);
      word_subword ((word_join:int64->int64->int128) m_6 m_5) (63,64);
      word_subword ((word_join:int64->int64->int128) m_7 m_6) (63,64);
      word_subword ((word_join:int64->int64->int128) m_8 m_7) (63,64)]` THEN
  SUBGOAL_THEN `2 * m = m'` ASSUME_TAC THENL
   [SUBGOAL_THEN `m DIV 2 EXP 512 < 2 EXP 63` MP_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "m'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `63`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
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
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 *  &n) rem &p_521 =
    (&2 * &m + &m + &8 *  (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca = m' + m + n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "m'"; "n'"] THEN
    UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [3;5;8;10;13;15;18;20;23;27;30;34;38;43;47;52;56;61] (1--61) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s27; sum_s30; sum_s34; sum_s38;
      sum_s43; sum_s47; sum_s52; sum_s56; sum_s61] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED] THEN EXPAND_TAC "ca"] THEN
    UNDISCH_THEN `8 * (p_521 - n) = n'` (K ALL_TAC) THEN
    UNDISCH_THEN `2 * m = m'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m"; "m'"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (62--64) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s61 9`;
    `d:int64 = word_or sum_s61 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s30 (word_and sum_s34 (word_and sum_s38
      (word_and sum_s43 (word_and sum_s47 (word_and sum_s52 sum_s56)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (65--67) (65--67) THEN
  SUBGOAL_THEN
   `carry_s67 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s27:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (68--76) (68--82) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s82" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s61:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s61:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s27; sum_s30; sum_s34; sum_s38; sum_s43; sum_s47; sum_s52; sum_s56] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s67`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s67" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s30; sum_s34; sum_s38; sum_s43; sum_s47; sum_s52; sum_s56] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s27:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s61:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s61:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s27:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let unilemma0 = prove
 (`x = a MOD p_521 ==> x < p_521 /\ &x = &a rem &p_521`,
  REWRITE_TAC[INT_OF_NUM_REM; p_521] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_521 ==> x < p_521 /\ &x = a rem &p_521`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_521] THEN INT_ARITH_TAC);;

let weierstrass_of_jacobian_p521_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp521
         (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) =
        (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521)
       ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                  (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521) =
                group_mul p521_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp521; P521_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_521; b_521] THEN CONV_TAC INT_REDUCE_CONV);;

let weierstrass_of_jacobian_p521_add = prove
 (`!P1 P2 x1 y1 z1 x2 y2 z2 x3 y3 z3.
        ~(weierstrass_of_jacobian (integer_mod_ring p_521)
           (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) =
          weierstrass_of_jacobian (integer_mod_ring p_521)
           (x2 rem &p_521,y2 rem &p_521,z2 rem &p_521)) /\
        jacobian_add_unexceptional nistp521
         (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521)
         (x2 rem &p_521,y2 rem &p_521,z2 rem &p_521) =
        (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521)
        ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) = P1 /\
            weierstrass_of_jacobian (integer_mod_ring p_521)
                (x2 rem &p_521,y2 rem &p_521,z2 rem &p_521) = P2
            ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                  (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521) =
                group_mul p521_group P1 P2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[nistp521; P521_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(MP_TAC o PART_MATCH (rand o rand) WEIERSTRASS_OF_JACOBIAN_EQ o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_521; b_521] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p521 = new_definition
 `represents_p521 P (x,y,z) <=>
        x < p_521 /\ y < p_521 /\ z < p_521 /\
        weierstrass_of_jacobian (integer_mod_ring p_521)
         (tripled (modular_decode (576,p_521)) (x,y,z)) = P`;;

let LOCAL_JDOUBLE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,656))
            [(word pc,LENGTH p521_jscalarmul_mc); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,LENGTH p521_jscalarmul_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x17c0) /\
                  // 144 is used by bignum_mul_p521
                  read SP s = word_add stackpointer (word 144) /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read PC s = word (pc + 0x1ecc) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,656)])`,
  REWRITE_TAC[FORALL_PAIR_THM; fst P521_JSCALARMUL_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x:num`; `y:num`; `z:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SQR_P521_TAC 2 ["z2";"z_1"] THEN
  LOCAL_SQR_P521_TAC 0 ["y2";"y_1"] THEN
  LOCAL_SUB_P521_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_ADD_P521_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_MUL_P521_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P521_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_MUL_P521_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_SQR_P521_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_SQR_P521_TAC 0 ["t2";"t1"] THEN
  LOCAL_CMSUBC9_P521_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P521_TAC 0 ["t1";"t1";"z2"] THEN
  LOCAL_SQR_P521_TAC 0 ["y4";"y2"] THEN
  LOCAL_MUL_P521_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_SUB_P521_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_CMSUB41_P521_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P521_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s45" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p521; tripled] THEN
  REWRITE_TAC[modular_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_521] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_521]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_MUL_REM]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p521_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp521;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_JDOUBLE_SUBR_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 752),752))
            [(word pc,LENGTH p521_jscalarmul_mc); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,LENGTH p521_jscalarmul_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x17a4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read PC s = returnaddress /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 752),752)])`,
  ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
   LOCAL_JDOUBLE_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]`
   752);;

let LOCAL_SUB_P521_TAC =
  PROLOGUE_SUBROUTINE_SIM_TAC LOCAL_SUB_P521_SUBR_CORRECT
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X1 s,8 * 9)) s`;
    `read (memory :> bytes(read X2 s,8 * 9)) s`;
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 9)) s'`;;

let LOCAL_JADD_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,720))
            [(word pc,LENGTH p521_jscalarmul_mc); (p1,216); (p2,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,LENGTH p521_jscalarmul_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x13d4) /\
                  // 144 is used by bignum_mul_p521
                  read SP s = word_add stackpointer (word 144) /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,9) s = t1 /\
                  bignum_triple_from_memory (p2,9) s = t2)
             (\s. read PC s = word (pc + 0x1784) /\
                  !P1 P2. represents_p521 P1 t1 /\
                          represents_p521 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p521(group_mul p521_group P1 P2)
                               (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,720)])`,
  REWRITE_TAC[FORALL_PAIR_THM; fst P521_JSCALARMUL_EXEC] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`; `p2:int64`;
    `x2:num`; `y2:num`; `z2:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SQR_P521_TAC 3 ["z1sq";"z_1"] THEN
  LOCAL_SQR_P521_TAC 0 ["z2sq";"z_2"] THEN
  LOCAL_MUL_P521_TAC 0 ["y1a";"z_2";"y_1"] THEN
  LOCAL_MUL_P521_TAC 0 ["y2a";"z_1";"y_2"] THEN
  LOCAL_MUL_P521_TAC 0 ["x2a";"z1sq";"x_2"] THEN
  LOCAL_MUL_P521_TAC 0 ["x1a";"z2sq";"x_1"] THEN
  LOCAL_MUL_P521_TAC 0 ["y2a";"z1sq";"y2a"] THEN
  LOCAL_MUL_P521_TAC 0 ["y1a";"z2sq";"y1a"] THEN
  LOCAL_SUB_P521_TAC 0 ["xd";"x2a";"x1a"] THEN
  LOCAL_SUB_P521_TAC 0 ["yd";"y2a";"y1a"] THEN
  LOCAL_SQR_P521_TAC 0 ["zz";"xd"] THEN
  LOCAL_SQR_P521_TAC 0 ["ww";"yd"] THEN
  LOCAL_MUL_P521_TAC 0 ["zzx1";"zz";"x1a"] THEN
  LOCAL_MUL_P521_TAC 0 ["zzx2";"zz";"x2a"] THEN
  LOCAL_SUB_P521_TAC 0 ["resx";"ww";"zzx1"] THEN
  LOCAL_SUB_P521_TAC 0 ["t1";"zzx2";"zzx1"] THEN
  LOCAL_MUL_P521_TAC 0 ["xd";"xd";"z_1"] THEN
  LOCAL_SUB_P521_TAC 0 ["resx";"resx";"zzx2"] THEN
  LOCAL_SUB_P521_TAC 0 ["t2";"zzx1";"resx"] THEN
  LOCAL_MUL_P521_TAC 0 ["t1";"t1";"y1a"] THEN
  LOCAL_MUL_P521_TAC 0 ["resz";"xd";"z_2"] THEN
  LOCAL_MUL_P521_TAC 0 ["t2";"yd";"t2"] THEN
  LOCAL_SUB_P521_TAC 0 ["resy";"t2";"t1"] THEN

  BIGNUM_LDIGITIZE_TAC "x1_"
   `read (memory :> bytes (p1,8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "y1_"
   `read (memory :> bytes (word_add p1 (word 72),8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "z1_"
   `read (memory :> bytes (word_add p1 (word 144),8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "x2_"
   `read (memory :> bytes (p2,8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "y2_"
   `read (memory :> bytes (word_add p2 (word 72),8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "z2_"
   `read (memory :> bytes (word_add p2 (word 144),8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resx_"
   `read (memory :> bytes (word_add stackpointer (word 144),8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resy_"
   `read (memory :> bytes (word_add stackpointer (word 432),8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resz_"
   `read (memory :> bytes (word_add stackpointer (word 504),8 * 9)) s114` THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (115--259) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s259" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
  REWRITE_TAC[WORD_BITWISE_RULE
   `word_or (word_or (word_or (word_or x0 x1) (word_or x2 x3)) x8)
            (word_or (word_or x4 x5) (word_or x6 x7)) =
    word_or x0 (word_or x1 (word_or x2 (word_or x3
       (word_or x4 (word_or x5 (word_or x6 (word_or x7 x8)))))))`] THEN

  MAP_EVERY X_GEN_TAC [`P1:(int#int)option`; `P2:(int#int)option`] THEN
  REWRITE_TAC[represents_p521; tripled; paired] THEN
  REWRITE_TAC[modular_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_521] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_521]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN

  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; INT_OF_NUM_EQ; WORD_OR_EQ_0] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MP_TAC(GEN_ALL(SPEC `[x0:int64;x1;x2;x3;x4;x5;x6;x7;x8]`
    BIGNUM_OF_WORDLIST_EQ_0)) THEN
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
    REWRITE_TAC[P521_GROUP; weierstrass_add] THEN
    REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P1" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P521_GROUP; weierstrass_add];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P2" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[P521_GROUP; weierstrass_add];
    ALL_TAC] THEN

  SUBGOAL_THEN `~(&z1 rem &p_521 = &0) /\ ~(&z2 rem &p_521 = &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_REM; MOD_LT]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN ANTS_TAC THENL
   [EXPAND_TAC "P2" THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; OPTION_DISTINCT;
                    GSYM INT_OF_NUM_REM];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REM_DOWN_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_ADD_REM; GSYM INT_SUB_REM]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl))) THEN
  REWRITE_TAC[IMP_IMP] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p521_add THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_add_unexceptional; nistp521;
                  INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_521] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_JADD_SUBR_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 816),816))
            [(word pc,LENGTH p521_jscalarmul_mc); (p1,216); (p2,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,LENGTH p521_jscalarmul_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x13b8) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,9) s = t1 /\
                  bignum_triple_from_memory (p2,9) s = t2)
             (\s. read PC s = returnaddress /\
                  !P1 P2. represents_p521 P1 t1 /\
                          represents_p521 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_p521(group_mul p521_group P1 P2)
                               (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 816),816)])`,
  ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
   LOCAL_JADD_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]`
   816);;

(* ------------------------------------------------------------------------- *)
(* Level 3: the top-level proof.                                             *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MOD_N521_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_mc,P521_JSCALARMUL_EXEC,
    0x12a0,bignum_mod_n521_9_mc,BIGNUM_MOD_N521_9_SUBROUTINE_CORRECT)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 9)) s`;
   `pc + 0x12a0`; `read X30 s`];;

let LOCAL_MOD_P521_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_mc,P521_JSCALARMUL_EXEC,
    0x121c,bignum_mod_p521_9_mc,BIGNUM_MOD_P521_9_SUBROUTINE_CORRECT)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 9)) s`;
   `pc + 0x121c`; `read X30 s`];;

let LOCAL_JADD_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
       LOCAL_JADD_SUBR_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_mc,P521_JSCALARMUL_EXEC,
    0x0,p521_jscalarmul_mc,th)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 9)) s,
    read(memory :> bytes(word_add (read X1 s) (word 72),8 * 9)) s,
    read(memory :> bytes(word_add (read X1 s) (word 144),8 * 9)) s`;
   `read X2 s`;
   `read(memory :> bytes(read X2 s,8 * 9)) s,
    read(memory :> bytes(word_add (read X2 s) (word 72),8 * 9)) s,
    read(memory :> bytes(word_add (read X2 s) (word 144),8 * 9)) s`;
   `pc:num`; `read SP s`; `read X30 s`];;

let LOCAL_JDOUBLE_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
       LOCAL_JDOUBLE_SUBR_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_mc,P521_JSCALARMUL_EXEC,
    0x0,p521_jscalarmul_mc,th)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 9)) s,
    read(memory :> bytes(word_add (read X1 s) (word 72),8 * 9)) s,
    read(memory :> bytes(word_add (read X1 s) (word 144),8 * 9)) s`;
   `pc:num`; `read SP s`; `read X30 s`];;

let REPRESENTS_P521_REDUCTION = prove
 (`!P x y z.
        represents_p521 P (x,y,z)
        ==> represents_p521 P (x MOD p_521,y MOD p_521,z MOD p_521)`,
  REWRITE_TAC[represents_p521; modular_decode; tripled; MOD_LT_EQ] THEN
  SIMP_TAC[INT_OF_NUM_REM; MOD_MOD_REFL] THEN REWRITE_TAC[p_521; ARITH_EQ]);;

let REPRESENTS_P521_NEGATION_ALT = prove
 (`!P x y z.
        represents_p521 P (x,y,z)
        ==> P IN group_carrier p521_group
            ==> represents_p521 (group_inv p521_group P)
                   (x,(if y = 0 then 0 else p_521 - y),z)`,
  REWRITE_TAC[represents_p521] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_521`; `ring_neg (integer_mod_ring p_521) (&3)`;
    `&b_521:int`;
    `tripled (modular_decode (576,p_521)) (x,y,z)`]
   WEIERSTRASS_OF_JACOBIAN_NEG) THEN
  ASM_REWRITE_TAC[jacobian_point; GSYM nistp521; P521_GROUP; tripled] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
    REWRITE_TAC[b_521; IN_INTEGER_MOD_RING_CARRIER; p_521;
                INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_521] THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THEN
    MATCH_MP_TAC MODULAR_DECODE THEN
    REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[jacobian_neg; INTEGER_MOD_RING_CLAUSES; nistp521] THEN
    REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[modular_decode] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_LNEG] THEN
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; MOD_LT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_ABS_NUM; MOD_0] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; LT_IMP_LE; INT_OF_NUM_EQ] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let P521_JSCALARMUL_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,4784))
            [(word pc,LENGTH p521_jscalarmul_mc); (res,216); (scalar,72); (point,216)] /\
        nonoverlapping (res,216) (word pc,LENGTH p521_jscalarmul_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0xc) /\
                  read SP s = word_add stackpointer (word 816) /\
                  C_ARGUMENTS [res;scalar;point] s /\
                  bignum_from_memory (scalar,9) s = n /\
                  bignum_triple_from_memory (point,9) s = xyz)
             (\s. read PC s = word (pc + 0x120c) /\
                  !P. P IN group_carrier p521_group /\
                      represents_p521 P xyz
                      ==> represents_p521
                            (group_pow p521_group P n)
                            (bignum_triple_from_memory(res,9) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X19; X20; X21; X30] ,,
           MAYCHANGE [memory :> bytes(res,216);
                      memory :> bytes(stackpointer,4784)])`,
  REWRITE_TAC[FORALL_PAIR_THM; fst P521_JSCALARMUL_EXEC] THEN
  REWRITE_TAC[GSYM SEQ_ASSOC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `point:int64`;
    `n_input:num`; `x_input:num`; `y_input:num`; `z_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN

  (*** Modified input arguments, mathematically first ***)

  MAP_EVERY ABBREV_TAC
   [`x = x_input MOD p_521`;
    `y = y_input MOD p_521`;
    `z = z_input MOD p_521`] THEN
  SUBGOAL_THEN `x < p_521 /\ y < p_521 /\ z < p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"; "z"] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `n_red = n_input MOD n_521` THEN
  SUBGOAL_THEN `n_red < n_521` ASSUME_TAC THENL
   [EXPAND_TAC "n_red" THEN REWRITE_TAC[n_521] THEN ARITH_TAC; ALL_TAC] THEN

  ABBREV_TAC `sgn <=> 2 EXP 520 <= n_red` THEN
  ABBREV_TAC `n_neg = if sgn then n_521 - n_red else n_red` THEN
  SUBGOAL_THEN `n_neg < 2 EXP 520` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n_neg"; "sgn"] THEN
    UNDISCH_TAC `n_red < n_521` THEN REWRITE_TAC[n_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `recoder = nsum(0..103) (\i. 2 EXP (5 * i) * 16)` THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(LAND_CONV EXPAND_NSUM_CONV)) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN DISCH_TAC THEN
  ABBREV_TAC `n = n_neg + recoder` THEN
  SUBGOAL_THEN `n < 2 EXP 521` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n"; "recoder"] THEN
    UNDISCH_TAC `n_neg < 2 EXP 520` THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `y' = if sgn /\ ~(y = 0) then p_521 - y else y` THEN

  (*** Main loop invariant setup. ***)

  ENSURES_WHILE_DOWN_TAC `104` `pc + 0x3e8` `pc + 0x1198`
   `\i s.
      read SP s = word_add stackpointer (word 816) /\
      read X20 s = res /\
      read X19 s = word (5 * i) /\
      bignum_from_memory(word_add stackpointer (word 816),9) s =
      2 EXP (576 - 5 * i) * n MOD (2 EXP (5 * i)) /\
      !P. P IN group_carrier p521_group /\ represents_p521 P (x,y',z)
          ==> represents_p521
                (group_zpow p521_group P
                    (&(n DIV 2 EXP (5 * i)) - &(recoder DIV 2 EXP (5 * i))))
                (bignum_triple_from_memory
                     (word_add stackpointer (word 888),9) s) /\
              !i. i < 16
                  ==> represents_p521 (group_pow p521_group P (i + 1))
                       (bignum_triple_from_memory
                       (word_add stackpointer (word (216 * i + 1320)),9) s)`
  THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of invariant ***)
    (*** First, the input reduced modulo the group order ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (1--4) THEN
    LOCAL_MOD_N521_TAC 5 THEN

    (*** Reduction of input point coordinates, actually supererogatory ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (6--9) THEN
    LOCAL_MOD_P521_TAC 10 THEN
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (11--13) THEN
    LOCAL_MOD_P521_TAC 14 THEN
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (15--17) THEN
    LOCAL_MOD_P521_TAC 18 THEN

    (*** Conditional negation of scalar ***)

    BIGNUM_LDIGITIZE_TAC "nn_"
     `read (memory :> bytes (word_add stackpointer (word 816),8 * 9)) s18` THEN
    ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
     [24;29;35;40;43;45;48;50;53] (19--69) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0]) THEN
    SUBGOAL_THEN
     `word_and nn_8 (word 256):int64 = word 0 <=> ~sgn`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "sgn" THEN REWRITE_TAC[NOT_LE] THEN
      SUBGOAL_THEN `n_red < 2 EXP 520 <=>
                    (n_red DIV 2 EXP 512) MOD 2 EXP 9 < 2 EXP 8`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[DIV_MOD; ARITH_ADD; ARITH_SUC; GSYM EXP_ADD] THEN
        REWRITE_TAC[ARITH_RULE
         `n DIV 2 EXP 512 < 2 EXP 8 <=> n < 2 EXP 520`] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `n_red < n_521` THEN
        REWRITE_TAC[n_521] THEN ARITH_TAC;
        EXPAND_TAC "n_red" THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)] THEN
      REWRITE_TAC[BITBLAST_RULE
       `word_and nn_8 (word 256) = word 0 <=> ~bit 8 (nn_8:int64)`] THEN
      CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
      ASM_CASES_TAC `bit 8 (nn_8:int64)` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; NOT_LT] THEN BOUNDER_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP])] THEN

    SUBGOAL_THEN
     `read (memory :> bytes (word_add stackpointer (word 816),8 * 9)) s69 =
      n_neg`
    ASSUME_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "n_neg" THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [UNDISCH_TAC `n_red < n_521` THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; n_521] THEN ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
      EXPAND_TAC "n_red" THEN
      REWRITE_TAC[bignum_of_wordlist; n_521; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; n_521] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Corresponding negation of the point (y coordinate) ***)

    BIGNUM_LDIGITIZE_TAC "y_"
    `read (memory :> bytes (word_add stackpointer (word 1392),8 * 9)) s69` THEN
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (70--100) THEN

    SUBGOAL_THEN
     `read (memory :> bytes (word_add stackpointer (word 1392),8 * 9)) s100 =
      y'`
    ASSUME_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; COND_SWAP; WORD_BITVAL_EQ_0] THEN
      REWRITE_TAC[WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
      MP_TAC(SPEC `[y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7;y_8]:int64 list`
        BIGNUM_OF_WORDLIST_EQ_0) THEN
      ASM_REWRITE_TAC[ALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[MESON[]
       `(if p then x else if q then y else x) =
        (if q /\ ~p then y else x)`] THEN
      EXPAND_TAC "y'" THEN REWRITE_TAC[COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONV_TAC WORD_REDUCE_CONV;
        SUBGOAL_THEN `y < 2 EXP 521` MP_TAC THENL
         [UNDISCH_TAC `y < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
          EXPAND_TAC "y" THEN
          REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST]] THEN
      MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 521` THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `word_xor y_8 (word 511):int64 =
          word_and (word 511) (word_xor y_8 (word 511))`
         (fun th -> SUBST1_TAC th THEN BOUNDER_TAC[]) THEN
        SUBGOAL_THEN `y < 2 EXP 521` MP_TAC THENL
         [UNDISCH_TAC `y < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
          EXPAND_TAC "y"] THEN
        REWRITE_TAC[ARITH_RULE
         `n < 2 EXP 521 <=> n DIV 2 EXP 512 < 2 EXP 9`] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        CONV_TAC WORD_BLAST;
        ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_EQ_0] THEN
      REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN EXPAND_TAC "y" THEN
      REWRITE_TAC[bignum_of_wordlist; p_521; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_BITVAL_NOT] THEN
      REAL_INTEGER_TAC;
      ALL_TAC] THEN

    (*** Computation of 2 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (101--103) THEN
    LOCAL_JDOUBLE_TAC 104 THEN
    MAP_EVERY ABBREV_TAC
     [`x2 = read(memory :> bytes(word_add stackpointer (word 1536),8 * 9)) s104`;
      `y2 = read(memory :> bytes(word_add stackpointer (word 1608),8 * 9)) s104`;
      `z2 = read(memory :> bytes(word_add stackpointer (word 1680),8 * 9)) s104`
     ] THEN

    (*** Computation of 3 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (105--108) THEN
    LOCAL_JADD_TAC 109 THEN
    MAP_EVERY ABBREV_TAC
     [`x3 = read(memory :> bytes(word_add stackpointer (word 1752),8 * 9)) s109`;
      `y3 = read(memory :> bytes(word_add stackpointer (word 1824),8 * 9)) s109`;
      `z3 = read(memory :> bytes(word_add stackpointer (word 1896),8 * 9)) s109`
     ] THEN

    (*** Computation of 4 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (110--112) THEN
    LOCAL_JDOUBLE_TAC 113 THEN
    MAP_EVERY ABBREV_TAC
     [`x4 = read(memory :> bytes(word_add stackpointer (word 1968),8 * 9)) s113`;
      `y4 = read(memory :> bytes(word_add stackpointer (word 2040),8 * 9)) s113`;
      `z4 = read(memory :> bytes(word_add stackpointer (word 2112),8 * 9)) s113`
     ] THEN

    (*** Computation of 5 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (114--117) THEN
    LOCAL_JADD_TAC 118 THEN
    MAP_EVERY ABBREV_TAC
     [`x5 = read(memory :> bytes(word_add stackpointer (word 2184),8 * 9)) s118`;
      `y5 = read(memory :> bytes(word_add stackpointer (word 2256),8 * 9)) s118`;
      `z5 = read(memory :> bytes(word_add stackpointer (word 2328),8 * 9)) s118`
     ] THEN

    (*** Computation of 6 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (119--121) THEN
    LOCAL_JDOUBLE_TAC 122 THEN
    MAP_EVERY ABBREV_TAC
     [`x6 = read(memory :> bytes(word_add stackpointer (word 2400),8 * 9)) s122`;
      `y6 = read(memory :> bytes(word_add stackpointer (word 2472),8 * 9)) s122`;
      `z6 = read(memory :> bytes(word_add stackpointer (word 2544),8 * 9)) s122`
     ] THEN

    (*** Computation of 7 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (123--126) THEN
    LOCAL_JADD_TAC 127 THEN
    MAP_EVERY ABBREV_TAC
     [`x7 = read(memory :> bytes(word_add stackpointer (word 2616),8 * 9)) s127`;
      `y7 = read(memory :> bytes(word_add stackpointer (word 2688),8 * 9)) s127`;
      `z7 = read(memory :> bytes(word_add stackpointer (word 2760),8 * 9)) s127`
     ] THEN

    (*** Computation of 8 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (128--130) THEN
    LOCAL_JDOUBLE_TAC 131 THEN
    MAP_EVERY ABBREV_TAC
     [`x8 = read(memory :> bytes(word_add stackpointer (word 2832),8 * 9)) s131`;
      `y8 = read(memory :> bytes(word_add stackpointer (word 2904),8 * 9)) s131`;
      `z8 = read(memory :> bytes(word_add stackpointer (word 2976),8 * 9)) s131`
     ] THEN

    (*** Computation of 9 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (132--135) THEN
    LOCAL_JADD_TAC 136 THEN
    MAP_EVERY ABBREV_TAC
     [`x9 = read(memory :> bytes(word_add stackpointer (word 3048),8 * 9)) s136`;
      `y9 = read(memory :> bytes(word_add stackpointer (word 3120),8 * 9)) s136`;
      `z9 = read(memory :> bytes(word_add stackpointer (word 3192),8 * 9)) s136`
     ] THEN

    (*** Computation of 10 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (137--139) THEN
    LOCAL_JDOUBLE_TAC 140 THEN
    MAP_EVERY ABBREV_TAC
     [`xa = read(memory :> bytes(word_add stackpointer (word 3264),8 * 9)) s140`;
      `ya = read(memory :> bytes(word_add stackpointer (word 3336),8 * 9)) s140`;
      `za = read(memory :> bytes(word_add stackpointer (word 3408),8 * 9)) s140`
     ] THEN

    (*** Computation of 11 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (141--144) THEN
    LOCAL_JADD_TAC 145 THEN
    MAP_EVERY ABBREV_TAC
     [`xb = read(memory :> bytes(word_add stackpointer (word 3480),8 * 9)) s145`;
      `yb = read(memory :> bytes(word_add stackpointer (word 3552),8 * 9)) s145`;
      `zb = read(memory :> bytes(word_add stackpointer (word 3624),8 * 9)) s145`
     ] THEN

    (*** Computation of 12 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (146--148) THEN
    LOCAL_JDOUBLE_TAC 149 THEN
    MAP_EVERY ABBREV_TAC
     [`xc = read(memory :> bytes(word_add stackpointer (word 3696),8 * 9)) s149`;
      `yc = read(memory :> bytes(word_add stackpointer (word 3768),8 * 9)) s149`;
      `zc = read(memory :> bytes(word_add stackpointer (word 3840),8 * 9)) s149`
     ] THEN

    (*** Computation of 13 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (150--153) THEN
    LOCAL_JADD_TAC 154 THEN
    MAP_EVERY ABBREV_TAC
     [`xd = read(memory :> bytes(word_add stackpointer (word 3912),8 * 9)) s154`;
      `yd = read(memory :> bytes(word_add stackpointer (word 3984),8 * 9)) s154`;
      `zd = read(memory :> bytes(word_add stackpointer (word 4056),8 * 9)) s154`
     ] THEN

    (*** Computation of 14 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (155--157) THEN
    LOCAL_JDOUBLE_TAC 158 THEN
    MAP_EVERY ABBREV_TAC
     [`xe = read(memory :> bytes(word_add stackpointer (word 4128),8 * 9)) s158`;
      `ye = read(memory :> bytes(word_add stackpointer (word 4200),8 * 9)) s158`;
      `ze = read(memory :> bytes(word_add stackpointer (word 4272),8 * 9)) s158`
     ] THEN

    (*** Computation of 15 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (159--162) THEN
    LOCAL_JADD_TAC 163 THEN
    MAP_EVERY ABBREV_TAC
     [`xf = read(memory :> bytes(word_add stackpointer (word 4344),8 * 9)) s163`;
      `yf = read(memory :> bytes(word_add stackpointer (word 4416),8 * 9)) s163`;
      `zf = read(memory :> bytes(word_add stackpointer (word 4488),8 * 9)) s163`
     ] THEN

    (*** Computation of 16 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (164--166) THEN
    LOCAL_JDOUBLE_TAC 167 THEN
    MAP_EVERY ABBREV_TAC
     [`xg = read(memory :> bytes(word_add stackpointer (word 4560),8 * 9)) s167`;
      `yg = read(memory :> bytes(word_add stackpointer (word 4632),8 * 9)) s167`;
      `zg = read(memory :> bytes(word_add stackpointer (word 4704),8 * 9)) s167`
     ] THEN

    (*** Add the recoding constant ***)

    DISCARD_MATCHING_ASSUMPTIONS [`read c s = if p then x else y`] THEN
    BIGNUM_LDIGITIZE_TAC "nr_"
     `read(memory :> bytes (word_add stackpointer (word 816),8 * 9)) s167` THEN
    ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
      [177;178;180;182;184;186;188;190;193] (168--208) THEN
    SUBGOAL_THEN
     `bignum_of_wordlist
        [sum_s177; sum_s178; sum_s180; sum_s182; sum_s184;
         sum_s186; sum_s188; sum_s190; sum_s193] = n`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 576` THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      MAP_EVERY EXPAND_TAC ["n"; "recoder"; "n_neg"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL])] THEN

    (*** Selection of the top window by conditional selection ***)

    DISCARD_MATCHING_ASSUMPTIONS [`read c s = word_xor a b`] THEN
    BIGNUM_LDIGITIZE_TAC "xx_"
     `read(memory :> bytes (word_add stackpointer (word 1320),8 * 9)) s208` THEN
    BIGNUM_LDIGITIZE_TAC "yy_"
     `read(memory :> bytes (word_add stackpointer (word 1392),8 * 9)) s208` THEN
    BIGNUM_LDIGITIZE_TAC "zz_"
     `read(memory :> bytes (word_add stackpointer (word 1464),8 * 9)) s208` THEN
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (209--266) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
    REWRITE_TAC[bignum_triple_from_memory] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[ARITH_RULE
       `x = 2 EXP (576 - 520) * y MOD 2 EXP 520 <=>
        2 EXP 576 * y DIV 2 EXP 520 + x = 2 EXP 56 * y`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      REWRITE_TAC[WORD_SUB_0]] THEN
    X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word_ushr sum_s193 8:int64) = n DIV 2 EXP 520`
    SUBST1_TAC THENL
     [EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    SUBGOAL_THEN `n DIV 2 EXP 520 < 2` MP_TAC THENL
     [UNDISCH_TAC `n < 2 EXP 521` THEN ARITH_TAC;
      SPEC_TAC(`n DIV 2 EXP 520`,`b:num`)] THEN
    REWRITE_TAC[MESON[ARITH_RULE `0 < 2`]
      `(!b. b < 2 ==> P b /\ Q) <=> (Q ==> !b. b < 2 ==> P b) /\ Q`] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "recoder" THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[INT_SUB_RZERO; GROUP_NPOW] THEN
      CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[WORD_SUB_0; VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[group_pow; P521_GROUP; represents_p521; tripled;
                  weierstrass_of_jacobian; modular_decode; p_521;
                  bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC INVERSE_MOD_CONV));
      ALL_TAC] THEN

    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_forall o concl))) THEN
    DISCH_THEN(MP_TAC o SPEC `P:(int#int)option`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[GROUP_RULE `group_mul G x x = group_pow G x 2`] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 2`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE `group_pow G x 2 = x <=> x = group_id G`] THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 2) x = group_pow G x 3`] THEN
    ANTS_TAC THENL [REWRITE_TAC[P521_GROUP]; DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 2`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 4`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 4) x = group_pow G x 5`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 4 = x <=> group_pow G x 3 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 3`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 6`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 6) x = group_pow G x 7`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 6 = x <=> group_pow G x 5 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 4`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 8`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 8) x = group_pow G x 9`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 8 = x <=> group_pow G x 7 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 5`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 10`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 10) x = group_pow G x 11`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 10 = x <=> group_pow G x 9 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 6`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 12`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 12) x = group_pow G x 13`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 12 = x <=> group_pow G x 11 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC
     `group_pow p521_group P 7`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPECL
     [`group_pow p521_group P 14`; `P:(int#int)option`]) THEN
    ASM_SIMP_TAC[GROUP_RULE
     `group_mul G (group_pow G x 14) x = group_pow G x 15`] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_POW_EQ_ID; P521_GROUP_ELEMENT_ORDER; GROUP_RULE
        `group_pow G x 14 = x <=> group_pow G x 13 = group_id G`] THEN
      REWRITE_TAC[P521_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[n_521] THEN CONV_TAC(RAND_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      DISCH_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `group_pow p521_group P 8`) THEN
    ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN ASM_SIMP_TAC[GROUP_POW_1];

    (*** Defer the main invariant preservation proof till below ***)

    ALL_TAC;

    (*** Trivial loop-back goal ***)

    REPEAT STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ARM_SIM_TAC P521_JSCALARMUL_EXEC [1] THEN
    VAL_INT64_TAC `5 * i` THEN
    ASM_REWRITE_TAC[ARITH_RULE `5 * i = 0 <=> ~(0 < i)`];

    (*** Final copying to the output and specializing invariant ***)

    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_"
     `read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y_"
     `read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "z_"
     `read (memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s0` THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (MESON[]
      `(!x. P x ==> Q x /\ R x) ==> (!x. P x ==> Q x)`)) THEN
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (1--29) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s29" THEN X_GEN_TAC `P:(int#int)option` THEN
    STRIP_TAC THEN
    ABBREV_TAC `Q = if sgn then group_inv p521_group P else P` THEN
    SUBGOAL_THEN `Q IN group_carrier p521_group` ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_INV];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:(int#int)option`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `group_zpow p521_group Q (&n - &recoder) = group_pow p521_group P n_input`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Q"; "n"; "n_neg"; "n_red"] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[INT_ARITH `(x + y) - y:int = x`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM GROUP_NPOW] THEN
      ASM_SIMP_TAC[GSYM GROUP_INV_ZPOW; GSYM GROUP_ZPOW_NEG; GROUP_ZPOW_EQ] THEN
      ASM_SIMP_TAC[P521_GROUP_ELEMENT_ORDER; INT_CONG_LREM; INT_CONG_REFL] THEN
      EXPAND_TAC "n_red" THEN COND_CASES_TAC THEN
      REWRITE_TAC[INT_CONG_MOD_1] THEN
      (SUBGOAL_THEN `n_input MOD n_521 <= n_521`
       (fun th -> SIMP_TAC[GSYM INT_OF_NUM_SUB; th])
       THENL [REWRITE_TAC[n_521] THEN ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[INTEGER_RULE
      `(--(n - x):int == y) (mod n) <=> (x == y) (mod n)`] THEN
      REWRITE_TAC[INT_CONG_LREM; INT_CONG_REFL; GSYM INT_OF_NUM_REM];
      DISCH_THEN MATCH_MP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P521_REDUCTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["y'"; "Q"] THEN
    BOOL_CASES_TAC `sgn:bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P521_NEGATION_ALT) THEN
    ASM_SIMP_TAC[COND_SWAP]] THEN

  (**** Now the preservation of the loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [bignum_triple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN

  GHOST_INTRO_TAC `Xa:num`
   `bignum_from_memory (word_add stackpointer (word 888),9)` THEN
  GHOST_INTRO_TAC `Ya:num`
   `bignum_from_memory (word_add stackpointer (word 960),9)` THEN
  GHOST_INTRO_TAC `Za:num`
   `bignum_from_memory (word_add stackpointer (word 1032),9)` THEN

  (*** Computation of 2 * (Xa,Ya,Za) ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (5 * (i + 1))) (word 5) = word(5 * i)`]) THEN
  LOCAL_JDOUBLE_TAC 5 THEN
  MAP_EVERY ABBREV_TAC
   [`X2a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s5`;
    `Y2a = read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s5`;
    `Z2a = read (memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s5`
   ] THEN

  (*** Computation of 4 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (6--8) THEN
  LOCAL_JDOUBLE_TAC 9 THEN
  MAP_EVERY ABBREV_TAC
   [`X4a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s9`;
    `Y4a = read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s9`;
    `Z4a = read (memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s9`
   ] THEN

  (*** Computation of 8 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (10--12) THEN
  LOCAL_JDOUBLE_TAC 13 THEN
  MAP_EVERY ABBREV_TAC
   [`X8a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s13`;
    `Y8a = read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s13`;
    `Z8a = read (memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s13`
   ] THEN

  (*** Computation of 16 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (14--16) THEN
  LOCAL_JDOUBLE_TAC 17 THEN
  MAP_EVERY ABBREV_TAC
   [`Xha = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s17`;
    `Yha = read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s17`;
    `Zha = read (memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s17`
   ] THEN

  (*** Computation of 32 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (18--20) THEN
  LOCAL_JDOUBLE_TAC 21 THEN
  MAP_EVERY ABBREV_TAC
   [`Xta = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s21`;
    `Yta = read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s21`;
    `Zta = read (memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s21`
   ] THEN

  (*** Selection of bitfield ***)

  BIGNUM_LDIGITIZE_TAC "n_"
    `read (memory :> bytes (word_add stackpointer (word 816),8 * 9)) s21` THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (22--44) THEN
  ABBREV_TAC `bf = (n DIV (2 EXP (5 * i))) MOD 32` THEN
  SUBGOAL_THEN
   `word_ushr (n_8:int64) 59 = word bf /\
    read (memory :> bytes (word_add stackpointer (word 816),8 * 9)) s44 =
    2 EXP (576 - 5 * i) * n MOD 2 EXP (5 * i)`
  MP_TAC THENL
   [EXPAND_TAC "bf" THEN
    SUBGOAL_THEN
     `(n DIV 2 EXP (5 * i)) MOD 32 =
      (2 EXP 5 *
       bignum_of_wordlist [n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7; n_8]) DIV
      2 EXP 576 /\
      2 EXP (576 - 5 * i) * n MOD 2 EXP (5 * i) =
      (2 EXP 5 *
       bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7; n_8]) MOD
      2 EXP 576`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONV_TAC(BINOP_CONV SYM_CONV) THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "bf" THEN REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 5`)] THEN
        REWRITE_TAC[EXP_ADD; MOD_MULT_MOD; ARITH_RULE
         `5 * (i + 1) = 5 * i + 5`] THEN
        ASM_REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `i < 104 ==> 5 + 576 - (5 * i + 5) = 576 - 5 * i`] THEN
        REWRITE_TAC[ARITH_RULE`e * (a + b):num = x + e * b <=> e * a = x`] THEN
        ASM_SIMP_TAC[MULT_ASSOC; GSYM EXP_ADD; ARITH_RULE
         `i < 104 ==> 576 - 5 * i + 5 * i = 576`] THEN
        ARITH_TAC;
        SUBGOAL_THEN `2 EXP 576 = 2 EXP (576 - 5 * i) * 2 EXP (5 * i)`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
          UNDISCH_TAC `i < 104` THEN ARITH_TAC;
          REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; MOD_LT_EQ]]];
      REWRITE_TAC[bignum_of_wordlist] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN MATCH_MP_TAC(MESON[]
       `q = a /\ r = b ==> word a = word q /\ b = r`) THEN
      MATCH_MP_TAC DIVMOD_UNIQ THEN
      CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)] THEN

  (*** Sign-magnitude recoding of bitfield ***)

  SUBGOAL_THEN `val(word bf:int64) = bf` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "bf" THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ix = if bf < 16 then 16 - bf else bf - 16` THEN

  FIRST_X_ASSUM(MP_TAC o SPEC `word ix:int64` o MATCH_MP (MESON[]
   `read X16 s = x ==> !x'. x = x' ==> read X16 s = x'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "ix" THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
    REWRITE_TAC[WORD_NEG_SUB] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN

  (*** Constant-time selection from the table ***)

  BIGNUM_LDIGITIZE_TAC "tab_"
   `read(memory :> bytes(word_add stackpointer (word 1320),8 * 432)) s44` THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (45--852) THEN

  MAP_EVERY ABBREV_TAC
   [`Xt = read (memory :> bytes(word_add stackpointer (word 1104),8 * 9)) s852`;
    `Zt = read (memory :> bytes(word_add stackpointer (word 1248),8 * 9)) s852`
   ] THEN
  MAP_EVERY REABBREV_TAC
   [`tab0 = read X0 s852`;
    `tab1 = read X1 s852`;
    `tab2 = read X2 s852`;
    `tab3 = read X3 s852`;
    `tab4 = read X4 s852`;
    `tab5 = read X5 s852`;
    `tab6 = read X6 s852`;
    `tab7 = read X7 s852`;
    `tab8 = read X8 s852`] THEN

  SUBGOAL_THEN
   `!P. P IN group_carrier p521_group /\ represents_p521 P (x,y',z)
        ==> represents_p521 (group_pow p521_group P ix)
               (Xt,
                bignum_of_wordlist
                 [tab0;tab1;tab2;tab3;tab4;tab5;tab6;tab7;tab8],
                Zt)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    MAP_EVERY EXPAND_TAC ["Xt"; "Zt"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC
     (map (fun n -> "tab"^string_of_int n) (0--8)) THEN
    SUBGOAL_THEN `ix < 17` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ix"; "bf"] THEN ARITH_TAC;
      SPEC_TAC(`ix:num`,`ix:num`)] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
    REWRITE_TAC[group_pow; P521_GROUP; represents_p521; tripled;
                weierstrass_of_jacobian; modular_decode; p_521;
                bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC INVERSE_MOD_CONV));
    ALL_TAC] THEN

  (*** Optional negation of the table entry ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (853--877) THEN
  ABBREV_TAC
   `Yt =
    read(memory :> bytes(word_add stackpointer (word 1176),8 * 9)) s877` THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier p521_group /\ represents_p521 P (x,y',z)
        ==> represents_p521 (group_zpow p521_group P (&bf - &16)) (Xt,Yt,Zt)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `P:(int#int)option`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXPAND_TAC "Yt" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&bf - &16:int = if bf < 16 then --(&ix) else &ix`
    SUBST1_TAC THENL
     [EXPAND_TAC "ix" THEN
      SUBGOAL_THEN `bf < 32` MP_TAC THENL
       [EXPAND_TAC "bf" THEN ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM NOT_LT] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; COND_SWAP; WORD_BITVAL_EQ_0] THEN
    REWRITE_TAC[WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
    MP_TAC(SPEC `[tab0;tab1;tab2;tab3;tab4;tab5;tab6;tab7;tab8]:int64 list`
      BIGNUM_OF_WORDLIST_EQ_0) THEN
    ASM_REWRITE_TAC[ALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN REWRITE_TAC[MESON[]
     `(if p then x else if q then y else x) =
      (if q /\ ~p then y else x)`] THEN
    ASM_CASES_TAC `bf < 16` THEN
    ASM_REWRITE_TAC[GROUP_NPOW; WORD_XOR_0; WORD_AND_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[COND_SWAP] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P521_NEGATION_ALT) THEN
    ASM_SIMP_TAC[GROUP_POW; GROUP_ZPOW_NEG; GROUP_NPOW] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0; WORD_AND_0] THEN
    REWRITE_TAC[WORD_BLAST
     `word_xor (x:int64) (word 18446744073709551615) = word_not x`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 521` THEN CONJ_TAC THENL
     [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `word_xor tab8 (word 511):int64 =
        word_and (word 511) (word_xor tab8 (word 511))`
       (fun th -> SUBST1_TAC th THEN BOUNDER_TAC[]) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p521]) THEN
      DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `m < n ==> m DIV 2 EXP 512 <= n DIV 2 EXP 512`)) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p521]) THEN
    SIMP_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ;
             GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist;
                REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
    CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_BITVAL_NOT] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Final addition of the table entry ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (878--881) THEN
  LOCAL_JADD_TAC 882 THEN
  MAP_EVERY ABBREV_TAC
   [`X' = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s882`;
    `Y' = read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s882`;
    `Z' = read (memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s882`
   ] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The final mathematics ***)

  X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
  CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[bignum_triple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])) THEN
  ABBREV_TAC
   `Q = group_zpow p521_group P
      (&(n DIV 2 EXP (5 * (i + 1))) -
       &(recoder DIV 2 EXP (5 * (i + 1))))` THEN
  SUBGOAL_THEN `Q IN group_carrier p521_group` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC GROUP_ZPOW THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN
   `!P. represents_p521 P (Xa,Ya,Za)
        ==> represents_p521 (group_mul p521_group P P) (X2a,Y2a,Z2a)`
   (MP_TAC o SPEC `Q:(int#int)option`) THEN
  ASM_SIMP_TAC[GROUP_RULE `group_mul G x x = group_pow G x 2`] THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (X2a,Y2a,Z2a)
        ==> represents_p521 (group_mul p521_group P P) (X4a,Y4a,Z4a)`
   (MP_TAC o SPEC `group_pow p521_group Q 2`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (X4a,Y4a,Z4a)
        ==> represents_p521 (group_mul p521_group P P) (X8a,Y8a,Z8a)`
   (MP_TAC o SPEC `group_pow p521_group Q 4`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (X8a,Y8a,Z8a)
        ==> represents_p521 (group_mul p521_group P P) (Xha,Yha,Zha)`
   (MP_TAC o SPEC `group_pow p521_group Q 8`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN UNDISCH_THEN
   `!P. represents_p521 P (Xha,Yha,Zha)
        ==> represents_p521 (group_mul p521_group P P) (Xta,Yta,Zta)`
   (MP_TAC o SPEC `group_pow p521_group Q 16`) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`group_pow p521_group Q 32`;
    `group_zpow p521_group P (&bf - &16)`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM GROUP_NPOW] THEN EXPAND_TAC "Q" THEN
  ASM_SIMP_TAC[GSYM GROUP_ZPOW_MUL; GSYM GROUP_ZPOW_ADD] THEN
  ANTS_TAC THENL
   [SUBST1_TAC(SYM(el 1 (CONJUNCTS P521_GROUP))) THEN
    ASM_SIMP_TAC[GROUP_ZPOW_EQ; GROUP_ZPOW_EQ_ID;
                 P521_GROUP_ELEMENT_ORDER] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_DIVIDES_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        INT_CONG_IMP_EQ)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `&32 * max (&x) (&y) + abs(bf) + &16:int < n
        ==> abs((&x - &y) * &32 - (bf - &16)) < n`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_ABS_NUM] THEN
      REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`; EXP_ADD] THEN
      REWRITE_TAC[GSYM DIV_DIV] THEN MATCH_MP_TAC(ARITH_RULE
        `a + c + d < n /\ b + c + d < n
         ==> 32 * MAX (a DIV 2 EXP 5) (b DIV 2 EXP 5) + c + d < n`) THEN
      CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
       `n DIV m <= n /\ n + x < y ==> n DIV m + x < y`) THEN
      REWRITE_TAC[DIV_LE] THEN
      EXPAND_TAC "n" THEN UNDISCH_TAC `n_neg < 2 EXP 520` THEN
      MAP_EVERY EXPAND_TAC ["recoder"; "bf"] THEN
      REWRITE_TAC[n_521] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `&bf - &16:int = &0` THEN ASM_REWRITE_TAC[INT_DIVIDES_0] THEN
    UNDISCH_TAC `~(&bf - &16:int = &0)` THEN
    MATCH_MP_TAC(TAUT `(p ==> ~q) ==> p ==> q ==> r`) THEN
    MATCH_MP_TAC(INT_ARITH
     `abs(y:int) < &32 /\ (~(x = &0) ==> &1 <= abs(x))
      ==> ~(y = &0) ==> ~(x * &32 = y)`) THEN
    CONJ_TAC THENL [EXPAND_TAC "bf"; CONV_TAC INT_ARITH] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC INT_ARITH;
    MATCH_MP_TAC EQ_IMP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!n. n DIV 2 EXP (5 * i) =
        32 * (n DIV 2 EXP (5 * (i + 1))) + (n DIV 2 EXP (5 * i)) MOD 32`
  MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`; EXP_ADD] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN ARITH_TAC;
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(recoder DIV 2 EXP (5 * i)) MOD 32 = 16` SUBST1_TAC THENL
   [UNDISCH_TAC `i < 104` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    EXPAND_TAC "recoder" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_ARITH);;

let P521_JSCALARMUL_SUBROUTINE_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 4816),4816))
            [(word pc,LENGTH p521_jscalarmul_mc); (res,216); (scalar,72); (point,216)] /\
        nonoverlapping (res,216) (word pc,LENGTH p521_jscalarmul_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [res;scalar;point] s /\
                  bignum_from_memory (scalar,9) s = n /\
                  bignum_triple_from_memory (point,9) s = xyz)
             (\s. read PC s = returnaddress /\
                  !P. P IN group_carrier p521_group /\
                      represents_p521 P xyz
                      ==> represents_p521
                            (group_pow p521_group P n)
                            (bignum_triple_from_memory(res,9) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE[memory :> bytes(res,216);
                  memory :> bytes(word_sub stackpointer (word 4816),4816)])`,
   ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
   P521_JSCALARMUL_CORRECT
    `[X19; X20; X21; X30]` 4816);;
