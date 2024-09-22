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
  0x94000530;       (* arm_BL (word 5312) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x91024381;       (* arm_ADD X1 X28 (rvalue (word 144)) *)
  0x9400052d;       (* arm_BL (word 5300) *)
  0x9107e3e0;       (* arm_ADD X0 SP (rvalue (word 504)) *)
  0x91024381;       (* arm_ADD X1 X28 (rvalue (word 144)) *)
  0x91012362;       (* arm_ADD X2 X27 (rvalue (word 72)) *)
  0x940002b8;       (* arm_BL (word 2784) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x91024361;       (* arm_ADD X1 X27 (rvalue (word 144)) *)
  0x91012382;       (* arm_ADD X2 X28 (rvalue (word 72)) *)
  0x940002b4;       (* arm_BL (word 2768) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x91000382;       (* arm_ADD X2 X28 (rvalue (word 0)) *)
  0x940002b0;       (* arm_BL (word 2752) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91000362;       (* arm_ADD X2 X27 (rvalue (word 0)) *)
  0x940002ac;       (* arm_BL (word 2736) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910123e2;       (* arm_ADD X2 SP (rvalue (word 72)) *)
  0x940002a8;       (* arm_BL (word 2720) *)
  0x9107e3e0;       (* arm_ADD X0 SP (rvalue (word 504)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x940002a4;       (* arm_BL (word 2704) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x940006ae;       (* arm_BL (word 6840) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x940006aa;       (* arm_BL (word 6824) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x9400050a;       (* arm_BL (word 5160) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x94000507;       (* arm_BL (word 5148) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000292;       (* arm_BL (word 2632) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x910243e2;       (* arm_ADD X2 SP (rvalue (word 144)) *)
  0x9400028e;       (* arm_BL (word 2616) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000698;       (* arm_BL (word 6752) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000694;       (* arm_BL (word 6736) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91024362;       (* arm_ADD X2 X27 (rvalue (word 144)) *)
  0x94000282;       (* arm_BL (word 2568) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910243e2;       (* arm_ADD X2 SP (rvalue (word 144)) *)
  0x9400068c;       (* arm_BL (word 6704) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910483e1;       (* arm_ADD X1 SP (rvalue (word 288)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x94000688;       (* arm_BL (word 6688) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000276;       (* arm_BL (word 2520) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91024382;       (* arm_ADD X2 X28 (rvalue (word 144)) *)
  0x94000272;       (* arm_BL (word 2504) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x9400026e;       (* arm_BL (word 2488) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910483e1;       (* arm_ADD X1 SP (rvalue (word 288)) *)
  0x910363e2;       (* arm_ADD X2 SP (rvalue (word 216)) *)
  0x94000678;       (* arm_BL (word 6624) *)
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
  0xa9bf7bfb;       (* arm_STP X27 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10803ff;       (* arm_SUB SP SP (rvalue (word 512)) *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xaa0103fb;       (* arm_MOV X27 X1 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x91024361;       (* arm_ADD X1 X27 (rvalue (word 144)) *)
  0x94000437;       (* arm_BL (word 4316) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x91012361;       (* arm_ADD X1 X27 (rvalue (word 72)) *)
  0x94000434;       (* arm_BL (word 4304) *)
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
  0x94000178;       (* arm_BL (word 1504) *)
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
  0x9400014f;       (* arm_BL (word 1340) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x940003bd;       (* arm_BL (word 3828) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x940003ba;       (* arm_BL (word 3816) *)
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
  0x9400032a;       (* arm_BL (word 3240) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x910363e2;       (* arm_ADD X2 SP (rvalue (word 216)) *)
  0x940000b5;       (* arm_BL (word 724) *)
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
  0xa8c17bfb;       (* arm_LDP X27 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8f;       (* arm_MUL X15 X4 X8 *)
  0x9b097cb0;       (* arm_MUL X16 X5 X9 *)
  0x9b0a7cd1;       (* arm_MUL X17 X6 X10 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xab1301ef;       (* arm_ADDS X15 X15 X19 *)
  0x9bc87c93;       (* arm_UMULH X19 X4 X8 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9bc97cb3;       (* arm_UMULH X19 X5 X9 *)
  0xba130231;       (* arm_ADCS X17 X17 X19 *)
  0x9bca7cd3;       (* arm_UMULH X19 X6 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab0b01ec;       (* arm_ADDS X12 X15 X11 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0xba110271;       (* arm_ADCS X17 X19 X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xab0b01ed;       (* arm_ADDS X13 X15 X11 *)
  0xba0c020e;       (* arm_ADCS X14 X16 X12 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba100270;       (* arm_ADCS X16 X19 X16 *)
  0xba1103f1;       (* arm_ADCS X17 XZR X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xeb0600b8;       (* arm_SUBS X24 X5 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba170210;       (* arm_ADCS X16 X16 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070116;       (* arm_SUBS X22 X8 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba17018c;       (* arm_ADCS X12 X12 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080156;       (* arm_SUBS X22 X10 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070136;       (* arm_SUBS X22 X9 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070156;       (* arm_SUBS X22 X10 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080136;       (* arm_SUBS X22 X9 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xd377d975;       (* arm_LSL X21 X11 9 *)
  0x93cbdd8b;       (* arm_EXTR X11 X12 X11 55 *)
  0x93ccddac;       (* arm_EXTR X12 X13 X12 55 *)
  0x93cdddcd;       (* arm_EXTR X13 X14 X13 55 *)
  0xd377fdce;       (* arm_LSR X14 X14 55 *)
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0xa9431825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&48))) *)
  0xa9422047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&32))) *)
  0xa9432849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&48))) *)
  0xa91b43ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&432))) *)
  0xa91c4ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&448))) *)
  0xa91d2ff5;       (* arm_STP X21 X11 SP (Immediate_Offset (iword (&464))) *)
  0xa91e37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&480))) *)
  0xf900fbee;       (* arm_STR X14 SP (Immediate_Offset (word 496)) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8f;       (* arm_MUL X15 X4 X8 *)
  0x9b097cb0;       (* arm_MUL X16 X5 X9 *)
  0x9b0a7cd1;       (* arm_MUL X17 X6 X10 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xab1301ef;       (* arm_ADDS X15 X15 X19 *)
  0x9bc87c93;       (* arm_UMULH X19 X4 X8 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9bc97cb3;       (* arm_UMULH X19 X5 X9 *)
  0xba130231;       (* arm_ADCS X17 X17 X19 *)
  0x9bca7cd3;       (* arm_UMULH X19 X6 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab0b01ec;       (* arm_ADDS X12 X15 X11 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0xba110271;       (* arm_ADCS X17 X19 X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xab0b01ed;       (* arm_ADDS X13 X15 X11 *)
  0xba0c020e;       (* arm_ADCS X14 X16 X12 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba100270;       (* arm_ADCS X16 X19 X16 *)
  0xba1103f1;       (* arm_ADCS X17 XZR X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xeb0600b8;       (* arm_SUBS X24 X5 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba170210;       (* arm_ADCS X16 X16 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070116;       (* arm_SUBS X22 X8 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba17018c;       (* arm_ADCS X12 X12 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080156;       (* arm_SUBS X22 X10 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070136;       (* arm_SUBS X22 X9 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070156;       (* arm_SUBS X22 X10 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080136;       (* arm_SUBS X22 X9 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xa95b5bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&432))) *)
  0xab17016b;       (* arm_ADDS X11 X11 X23 *)
  0xba16018c;       (* arm_ADCS X12 X12 X22 *)
  0xa91b33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&432))) *)
  0xa95c5bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&448))) *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xa91c3bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&448))) *)
  0xa95d5bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&464))) *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xa91d43ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&464))) *)
  0xa95e5bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&480))) *)
  0xba170231;       (* arm_ADCS X17 X17 X23 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xa91e4ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&480))) *)
  0xf940fbf5;       (* arm_LDR X21 SP (Immediate_Offset (word 496)) *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xf900fbf5;       (* arm_STR X21 SP (Immediate_Offset (word 496)) *)
  0xa9405837;       (* arm_LDP X23 X22 X1 (Immediate_Offset (iword (&0))) *)
  0xeb170063;       (* arm_SUBS X3 X3 X23 *)
  0xfa160084;       (* arm_SBCS X4 X4 X22 *)
  0xa9415837;       (* arm_LDP X23 X22 X1 (Immediate_Offset (iword (&16))) *)
  0xfa1700a5;       (* arm_SBCS X5 X5 X23 *)
  0xfa1600c6;       (* arm_SBCS X6 X6 X22 *)
  0xda9f23f8;       (* arm_CSETM X24 Condition_CC *)
  0xa9405857;       (* arm_LDP X23 X22 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0702e7;       (* arm_SUBS X7 X23 X7 *)
  0xfa0802c8;       (* arm_SBCS X8 X22 X8 *)
  0xa9415857;       (* arm_LDP X23 X22 X2 (Immediate_Offset (iword (&16))) *)
  0xfa0902e9;       (* arm_SBCS X9 X23 X9 *)
  0xfa0a02ca;       (* arm_SBCS X10 X22 X10 *)
  0xda9f23f9;       (* arm_CSETM X25 Condition_CC *)
  0xca180063;       (* arm_EOR X3 X3 X24 *)
  0xeb180063;       (* arm_SUBS X3 X3 X24 *)
  0xca180084;       (* arm_EOR X4 X4 X24 *)
  0xfa180084;       (* arm_SBCS X4 X4 X24 *)
  0xca1800a5;       (* arm_EOR X5 X5 X24 *)
  0xfa1800a5;       (* arm_SBCS X5 X5 X24 *)
  0xca1800c6;       (* arm_EOR X6 X6 X24 *)
  0xda1800c6;       (* arm_SBC X6 X6 X24 *)
  0xca1900e7;       (* arm_EOR X7 X7 X25 *)
  0xeb1900e7;       (* arm_SUBS X7 X7 X25 *)
  0xca190108;       (* arm_EOR X8 X8 X25 *)
  0xfa190108;       (* arm_SBCS X8 X8 X25 *)
  0xca190129;       (* arm_EOR X9 X9 X25 *)
  0xfa190129;       (* arm_SBCS X9 X9 X25 *)
  0xca19014a;       (* arm_EOR X10 X10 X25 *)
  0xda19014a;       (* arm_SBC X10 X10 X25 *)
  0xca180339;       (* arm_EOR X25 X25 X24 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8f;       (* arm_MUL X15 X4 X8 *)
  0x9b097cb0;       (* arm_MUL X16 X5 X9 *)
  0x9b0a7cd1;       (* arm_MUL X17 X6 X10 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xab1301ef;       (* arm_ADDS X15 X15 X19 *)
  0x9bc87c93;       (* arm_UMULH X19 X4 X8 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9bc97cb3;       (* arm_UMULH X19 X5 X9 *)
  0xba130231;       (* arm_ADCS X17 X17 X19 *)
  0x9bca7cd3;       (* arm_UMULH X19 X6 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab0b01ec;       (* arm_ADDS X12 X15 X11 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0xba110271;       (* arm_ADCS X17 X19 X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xab0b01ed;       (* arm_ADDS X13 X15 X11 *)
  0xba0c020e;       (* arm_ADCS X14 X16 X12 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba100270;       (* arm_ADCS X16 X19 X16 *)
  0xba1103f1;       (* arm_ADCS X17 XZR X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xeb0600b8;       (* arm_SUBS X24 X5 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba170210;       (* arm_ADCS X16 X16 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070116;       (* arm_SUBS X22 X8 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba17018c;       (* arm_ADCS X12 X12 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080156;       (* arm_SUBS X22 X10 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070136;       (* arm_SUBS X22 X9 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070156;       (* arm_SUBS X22 X10 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080136;       (* arm_SUBS X22 X9 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xa95b13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&432))) *)
  0xa95c1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&448))) *)
  0xca19016b;       (* arm_EOR X11 X11 X25 *)
  0xab03016b;       (* arm_ADDS X11 X11 X3 *)
  0xca19018c;       (* arm_EOR X12 X12 X25 *)
  0xba04018c;       (* arm_ADCS X12 X12 X4 *)
  0xca1901ad;       (* arm_EOR X13 X13 X25 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca1901ce;       (* arm_EOR X14 X14 X25 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0xca1901ef;       (* arm_EOR X15 X15 X25 *)
  0xa95d23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&464))) *)
  0xa95e2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&480))) *)
  0xf940fbf4;       (* arm_LDR X20 SP (Immediate_Offset (word 496)) *)
  0xba0701ef;       (* arm_ADCS X15 X15 X7 *)
  0xca190210;       (* arm_EOR X16 X16 X25 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0xca190231;       (* arm_EOR X17 X17 X25 *)
  0xba090231;       (* arm_ADCS X17 X17 X9 *)
  0xca190273;       (* arm_EOR X19 X19 X25 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a1f0295;       (* arm_ADC X21 X20 XZR *)
  0xab0301ef;       (* arm_ADDS X15 X15 X3 *)
  0xba040210;       (* arm_ADCS X16 X16 X4 *)
  0xba050231;       (* arm_ADCS X17 X17 X5 *)
  0xba060273;       (* arm_ADCS X19 X19 X6 *)
  0x92402339;       (* arm_AND X25 X25 (rvalue (word 511)) *)
  0xd377d978;       (* arm_LSL X24 X11 9 *)
  0xaa190318;       (* arm_ORR X24 X24 X25 *)
  0xba1800e7;       (* arm_ADCS X7 X7 X24 *)
  0x93cbdd98;       (* arm_EXTR X24 X12 X11 55 *)
  0xba180108;       (* arm_ADCS X8 X8 X24 *)
  0x93ccddb8;       (* arm_EXTR X24 X13 X12 55 *)
  0xba180129;       (* arm_ADCS X9 X9 X24 *)
  0x93cdddd8;       (* arm_EXTR X24 X14 X13 55 *)
  0xba18014a;       (* arm_ADCS X10 X10 X24 *)
  0xd377fdd8;       (* arm_LSR X24 X14 55 *)
  0x9a140314;       (* arm_ADC X20 X24 X20 *)
  0xf9402046;       (* arm_LDR X6 X2 (Immediate_Offset (word 64)) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0x9240cc77;       (* arm_AND X23 X3 (rvalue (word 4503599627370495)) *)
  0x9b177cd7;       (* arm_MUL X23 X6 X23 *)
  0xf940202e;       (* arm_LDR X14 X1 (Immediate_Offset (word 64)) *)
  0xa940304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&0))) *)
  0x9240cd78;       (* arm_AND X24 X11 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0x93c3d098;       (* arm_EXTR X24 X4 X3 52 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0x93cbd198;       (* arm_EXTR X24 X12 X11 52 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d732d8;       (* arm_EXTR X24 X22 X23 12 *)
  0xab1801ef;       (* arm_ADDS X15 X15 X24 *)
  0xa9410c25;       (* arm_LDP X5 X3 X1 (Immediate_Offset (iword (&16))) *)
  0xa9412c4d;       (* arm_LDP X13 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x93c4a0b8;       (* arm_EXTR X24 X5 X4 40 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cca1b8;       (* arm_EXTR X24 X13 X12 40 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374ced6;       (* arm_LSL X22 X22 12 *)
  0x93d662f8;       (* arm_EXTR X24 X23 X22 24 *)
  0xba180210;       (* arm_ADCS X16 X16 X24 *)
  0x93c57078;       (* arm_EXTR X24 X3 X5 28 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0x93cd7178;       (* arm_EXTR X24 X11 X13 28 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d792d8;       (* arm_EXTR X24 X22 X23 36 *)
  0xba180231;       (* arm_ADCS X17 X17 X24 *)
  0x8a110219;       (* arm_AND X25 X16 X17 *)
  0xa9421424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&32))) *)
  0xa942344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&32))) *)
  0x93c34098;       (* arm_EXTR X24 X4 X3 16 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cb4198;       (* arm_EXTR X24 X12 X11 16 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd3503eb5;       (* arm_LSL X21 X21 48 *)
  0x8b1502f7;       (* arm_ADD X23 X23 X21 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374ced6;       (* arm_LSL X22 X22 12 *)
  0x93d6c2f8;       (* arm_EXTR X24 X23 X22 48 *)
  0xba180273;       (* arm_ADCS X19 X19 X24 *)
  0x8a130339;       (* arm_AND X25 X25 X19 *)
  0xd344fc98;       (* arm_LSR X24 X4 4 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0xd344fd98;       (* arm_LSR X24 X12 4 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d7f2d5;       (* arm_EXTR X21 X22 X23 60 *)
  0x93c4e0b8;       (* arm_EXTR X24 X5 X4 56 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cce1b8;       (* arm_EXTR X24 X13 X12 56 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd378deb5;       (* arm_LSL X21 X21 8 *)
  0x93d522f8;       (* arm_EXTR X24 X23 X21 8 *)
  0xba1800e7;       (* arm_ADCS X7 X7 X24 *)
  0x8a070339;       (* arm_AND X25 X25 X7 *)
  0xa9431023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&48))) *)
  0xa943304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&48))) *)
  0x93c5b078;       (* arm_EXTR X24 X3 X5 44 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0x93cdb178;       (* arm_EXTR X24 X11 X13 44 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d752d8;       (* arm_EXTR X24 X22 X23 20 *)
  0xba180108;       (* arm_ADCS X8 X8 X24 *)
  0x8a080339;       (* arm_AND X25 X25 X8 *)
  0x93c38098;       (* arm_EXTR X24 X4 X3 32 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cb8198;       (* arm_EXTR X24 X12 X11 32 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374ced6;       (* arm_LSL X22 X22 12 *)
  0x93d682f8;       (* arm_EXTR X24 X23 X22 32 *)
  0xba180129;       (* arm_ADCS X9 X9 X24 *)
  0x8a090339;       (* arm_AND X25 X25 X9 *)
  0xd354fc98;       (* arm_LSR X24 X4 20 *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0xd354fd98;       (* arm_LSR X24 X12 20 *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d7b2d8;       (* arm_EXTR X24 X22 X23 44 *)
  0xba18014a;       (* arm_ADCS X10 X10 X24 *)
  0x8a0a0339;       (* arm_AND X25 X25 X10 *)
  0x9b0e7cd8;       (* arm_MUL X24 X6 X14 *)
  0xd36cfed6;       (* arm_LSR X22 X22 44 *)
  0x8b160318;       (* arm_ADD X24 X24 X22 *)
  0x9a180294;       (* arm_ADC X20 X20 X24 *)
  0xd349fe96;       (* arm_LSR X22 X20 9 *)
  0xb277da94;       (* arm_ORR X20 X20 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba1601ff;       (* arm_ADCS XZR X15 X22 *)
  0xba1f033f;       (* arm_ADCS XZR X25 XZR *)
  0xba1f029f;       (* arm_ADCS XZR X20 XZR *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0273;       (* arm_ADCS X19 X19 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x924021f6;       (* arm_AND X22 X15 (rvalue (word 511)) *)
  0x93cf260f;       (* arm_EXTR X15 X16 X15 9 *)
  0x93d02630;       (* arm_EXTR X16 X17 X16 9 *)
  0xa900400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&0))) *)
  0x93d12671;       (* arm_EXTR X17 X19 X17 9 *)
  0x93d324f3;       (* arm_EXTR X19 X7 X19 9 *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
  0x93c72507;       (* arm_EXTR X7 X8 X7 9 *)
  0x93c82528;       (* arm_EXTR X8 X9 X8 9 *)
  0xa9022007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&32))) *)
  0x93c92549;       (* arm_EXTR X9 X10 X9 9 *)
  0x93ca268a;       (* arm_EXTR X10 X20 X10 9 *)
  0xa9032809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&48))) *)
  0xf9002016;       (* arm_STR X22 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9b097cf1;       (* arm_MUL X17 X7 X9 *)
  0x9bc87cd6;       (* arm_UMULH X22 X6 X8 *)
  0xeb0700d7;       (* arm_SUBS X23 X6 X7 *)
  0xda9726f7;       (* arm_CNEG X23 X23 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb08012a;       (* arm_SUBS X10 X9 X8 *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0x9b0a7ef0;       (* arm_MUL X16 X23 X10 *)
  0x9bca7eea;       (* arm_UMULH X10 X23 X10 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b0210;       (* arm_EOR X16 X16 X11 *)
  0xca0b014a;       (* arm_EOR X10 X10 X11 *)
  0xab16018d;       (* arm_ADDS X13 X12 X22 *)
  0x9a1f02d6;       (* arm_ADC X22 X22 XZR *)
  0x9bc97cf7;       (* arm_UMULH X23 X7 X9 *)
  0xab1101ad;       (* arm_ADDS X13 X13 X17 *)
  0xba1702d6;       (* arm_ADCS X22 X22 X23 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9a0b02f7;       (* arm_ADC X23 X23 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0x9b077cf0;       (* arm_MUL X16 X7 X7 *)
  0x9b077cd5;       (* arm_MUL X21 X6 X7 *)
  0x9bc67ccb;       (* arm_UMULH X11 X6 X6 *)
  0x9bc77cf1;       (* arm_UMULH X17 X7 X7 *)
  0x9bc77cd4;       (* arm_UMULH X20 X6 X7 *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1f02d6;       (* arm_ADCS X22 X22 XZR *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b087d0e;       (* arm_MUL X14 X8 X8 *)
  0x9b097d30;       (* arm_MUL X16 X9 X9 *)
  0x9b097d15;       (* arm_MUL X21 X8 X9 *)
  0x9bc87d0f;       (* arm_UMULH X15 X8 X8 *)
  0x9bc97d31;       (* arm_UMULH X17 X9 X9 *)
  0x9bc97d14;       (* arm_UMULH X20 X8 X9 *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1601ce;       (* arm_ADDS X14 X14 X22 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xf9402033;       (* arm_LDR X19 X1 (Immediate_Offset (word 64)) *)
  0x8b130277;       (* arm_ADD X23 X19 X19 *)
  0x9b137e73;       (* arm_MUL X19 X19 X19 *)
  0x9240cc55;       (* arm_AND X21 X2 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0x93c2d074;       (* arm_EXTR X20 X3 X2 52 *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 52 *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 12 *)
  0x93d53296;       (* arm_EXTR X22 X20 X21 12 *)
  0xab16014a;       (* arm_ADDS X10 X10 X22 *)
  0x93c3a095;       (* arm_EXTR X21 X4 X3 40 *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 52 *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd374ce94;       (* arm_LSL X20 X20 12 *)
  0x93d462b6;       (* arm_EXTR X22 X21 X20 24 *)
  0xba16016b;       (* arm_ADCS X11 X11 X22 *)
  0x93c470b4;       (* arm_EXTR X20 X5 X4 28 *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 52 *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 12 *)
  0x93d59296;       (* arm_EXTR X22 X20 X21 36 *)
  0xba16018c;       (* arm_ADCS X12 X12 X22 *)
  0x93c540d5;       (* arm_EXTR X21 X6 X5 16 *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 52 *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd374ce94;       (* arm_LSL X20 X20 12 *)
  0x93d4c2b6;       (* arm_EXTR X22 X21 X20 48 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xd344fcd4;       (* arm_LSR X20 X6 4 *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 52 *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 12 *)
  0x93d5f298;       (* arm_EXTR X24 X20 X21 60 *)
  0x93c6e0f5;       (* arm_EXTR X21 X7 X6 56 *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 52 *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd378df18;       (* arm_LSL X24 X24 8 *)
  0x93d822b6;       (* arm_EXTR X22 X21 X24 8 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0x93c7b114;       (* arm_EXTR X20 X8 X7 44 *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 52 *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 12 *)
  0x93d55296;       (* arm_EXTR X22 X20 X21 20 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0x93c88135;       (* arm_EXTR X21 X9 X8 32 *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 52 *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd374ce94;       (* arm_LSL X20 X20 12 *)
  0x93d482b6;       (* arm_EXTR X22 X21 X20 32 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xd354fd34;       (* arm_LSR X20 X9 20 *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 52 *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 12 *)
  0x93d5b296;       (* arm_EXTR X22 X20 X21 44 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xd36cfe94;       (* arm_LSR X20 X20 44 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0x93ca2575;       (* arm_EXTR X21 X11 X10 9 *)
  0x93cb2594;       (* arm_EXTR X20 X12 X11 9 *)
  0xa9005015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0x93cc25b5;       (* arm_EXTR X21 X13 X12 9 *)
  0x93cd25d4;       (* arm_EXTR X20 X14 X13 9 *)
  0xa9015015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0x93ce25f5;       (* arm_EXTR X21 X15 X14 9 *)
  0x93cf2614;       (* arm_EXTR X20 X16 X15 9 *)
  0xa9025015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0x93d02635;       (* arm_EXTR X21 X17 X16 9 *)
  0x93d12674;       (* arm_EXTR X20 X19 X17 9 *)
  0xa9035015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0x92402156;       (* arm_AND X22 X10 (rvalue (word 511)) *)
  0xd349fe73;       (* arm_LSR X19 X19 9 *)
  0x8b1302d6;       (* arm_ADD X22 X22 X19 *)
  0xf9002016;       (* arm_STR X22 X0 (Immediate_Offset (word 64)) *)
  0x9b047c4c;       (* arm_MUL X12 X2 X4 *)
  0x9b057c71;       (* arm_MUL X17 X3 X5 *)
  0x9bc47c56;       (* arm_UMULH X22 X2 X4 *)
  0xeb030057;       (* arm_SUBS X23 X2 X3 *)
  0xda9726f7;       (* arm_CNEG X23 X23 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb0400aa;       (* arm_SUBS X10 X5 X4 *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0x9b0a7ef0;       (* arm_MUL X16 X23 X10 *)
  0x9bca7eea;       (* arm_UMULH X10 X23 X10 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b0210;       (* arm_EOR X16 X16 X11 *)
  0xca0b014a;       (* arm_EOR X10 X10 X11 *)
  0xab16018d;       (* arm_ADDS X13 X12 X22 *)
  0x9a1f02d6;       (* arm_ADC X22 X22 XZR *)
  0x9bc57c77;       (* arm_UMULH X23 X3 X5 *)
  0xab1101ad;       (* arm_ADDS X13 X13 X17 *)
  0xba1702d6;       (* arm_ADCS X22 X22 X23 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9a0b02f7;       (* arm_ADC X23 X23 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0x9b027c4a;       (* arm_MUL X10 X2 X2 *)
  0x9b037c70;       (* arm_MUL X16 X3 X3 *)
  0x9b037c55;       (* arm_MUL X21 X2 X3 *)
  0x9bc27c4b;       (* arm_UMULH X11 X2 X2 *)
  0x9bc37c71;       (* arm_UMULH X17 X3 X3 *)
  0x9bc37c54;       (* arm_UMULH X20 X2 X3 *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1f02d6;       (* arm_ADCS X22 X22 XZR *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c8e;       (* arm_MUL X14 X4 X4 *)
  0x9b057cb0;       (* arm_MUL X16 X5 X5 *)
  0x9b057c95;       (* arm_MUL X21 X4 X5 *)
  0x9bc47c8f;       (* arm_UMULH X15 X4 X4 *)
  0x9bc57cb1;       (* arm_UMULH X17 X5 X5 *)
  0x9bc57c94;       (* arm_UMULH X20 X4 X5 *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1601ce;       (* arm_ADDS X14 X14 X22 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xa9405015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0xab0a02b5;       (* arm_ADDS X21 X21 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0xa9005015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0xa9415015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xa9015015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0xa9425015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xba0f0294;       (* arm_ADCS X20 X20 X15 *)
  0xa9025015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0xa9435015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0xba1002b5;       (* arm_ADCS X21 X21 X16 *)
  0xba110294;       (* arm_ADCS X20 X20 X17 *)
  0xa9035015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0xf9402016;       (* arm_LDR X22 X0 (Immediate_Offset (word 64)) *)
  0x9a1f02d6;       (* arm_ADC X22 X22 XZR *)
  0xf9002016;       (* arm_STR X22 X0 (Immediate_Offset (word 64)) *)
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
  0xa9405015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0x93ce21e2;       (* arm_EXTR X2 X15 X14 8 *)
  0xab150042;       (* arm_ADDS X2 X2 X21 *)
  0x93cf2203;       (* arm_EXTR X3 X16 X15 8 *)
  0xba140063;       (* arm_ADCS X3 X3 X20 *)
  0xa9415015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0x93d02224;       (* arm_EXTR X4 X17 X16 8 *)
  0xba150084;       (* arm_ADCS X4 X4 X21 *)
  0x8a040076;       (* arm_AND X22 X3 X4 *)
  0xd348fe25;       (* arm_LSR X5 X17 8 *)
  0xba1400a5;       (* arm_ADCS X5 X5 X20 *)
  0x8a0502d6;       (* arm_AND X22 X22 X5 *)
  0xa9425015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0xd37ff946;       (* arm_LSL X6 X10 1 *)
  0xba1500c6;       (* arm_ADCS X6 X6 X21 *)
  0x8a0602d6;       (* arm_AND X22 X22 X6 *)
  0x93cafd67;       (* arm_EXTR X7 X11 X10 63 *)
  0xba1400e7;       (* arm_ADCS X7 X7 X20 *)
  0x8a0702d6;       (* arm_AND X22 X22 X7 *)
  0xa9435015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0x93cbfd88;       (* arm_EXTR X8 X12 X11 63 *)
  0xba150108;       (* arm_ADCS X8 X8 X21 *)
  0x8a0802d6;       (* arm_AND X22 X22 X8 *)
  0x93ccfda9;       (* arm_EXTR X9 X13 X12 63 *)
  0xba140129;       (* arm_ADCS X9 X9 X20 *)
  0x8a0902d6;       (* arm_AND X22 X22 X9 *)
  0xf9402015;       (* arm_LDR X21 X0 (Immediate_Offset (word 64)) *)
  0x93cdfdca;       (* arm_EXTR X10 X14 X13 63 *)
  0x9240214a;       (* arm_AND X10 X10 (rvalue (word 511)) *)
  0x9a0a02aa;       (* arm_ADC X10 X21 X10 *)
  0xd349fd54;       (* arm_LSR X20 X10 9 *)
  0xb277d94a;       (* arm_ORR X10 X10 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba14005f;       (* arm_ADCS XZR X2 X20 *)
  0xba1f02df;       (* arm_ADCS XZR X22 XZR *)
  0xba1f015f;       (* arm_ADCS XZR X10 XZR *)
  0xba140042;       (* arm_ADCS X2 X2 X20 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9240214a;       (* arm_AND X10 X10 (rvalue (word 511)) *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200a;       (* arm_STR X10 X0 (Immediate_Offset (word 64)) *)
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

let LOCAL_SQR_P521_SUBR_CORRECT = prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x2fa8) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x28a8) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (n EXP 2) MOD p_521))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                         X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P521_JSCALARMUL_EXEC (1--413)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** The 4x4 squaring of the top "half" ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [5; 6; 13; 18; 19; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31;
    32; 33; 34; 35; 36; 37; 41; 42; 43; 44; 45; 46; 47; 48; 49;
    50; 51; 52; 53; 54; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67]
   (1--67) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_4; n_5; n_6; n_7] EXP 2 =
    bignum_of_wordlist
      [mullo_s35; sum_s44; sum_s47; sum_s48; sum_s64; sum_s65; sum_s66;
       sum_s67]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN FIRST_ASSUM
     (MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
      DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The complicated augmentation with the little word contribution ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [70; 80; 88; 96; 104; 119; 127; 135; 142; 144]
   (68--144) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_4; n_5; n_6; n_7; n_8] EXP 2 +
    2 * val n_8 * bignum_of_wordlist[n_0; n_1; n_2; n_3] =
    bignum_of_wordlist[sum_s80; sum_s88; sum_s96; sum_s104;
                       sum_s119; sum_s127; sum_s135; sum_s142; sum_s144]`
  ASSUME_TAC THENL
   [REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; ARITH_RULE
     `(l + 2 EXP 256 * h) EXP 2 =
      2 EXP 512 * h EXP 2 + 2 EXP 256 * (2 * h) * l + l EXP 2`] THEN
    REWRITE_TAC[ARITH_RULE
     `(x + 2 EXP 256 * (2 * c) * h + y) + 2 * c * l =
      x + y + 2 * c * (l + 2 EXP 256 * h)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      MATCH_MP_TAC(ARITH_RULE
       `c2 < 2 EXP 9 EXP 2 /\ x < 2 EXP 512 /\ c * y <= 2 EXP 9 * 2 EXP 512
        ==> 2 EXP 512 * c2 + x + 2 * c * y < 2 EXP 576`) THEN
      ASM_REWRITE_TAC[EXP_MONO_LT; ARITH_EQ] THEN CONJ_TAC THENL
       [ALL_TAC; MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE]] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `(x + 2 EXP 256 * (2 * c) * h + y) + 2 * c * l =
      x + y + 2 * c * (l + 2 EXP 256 * h)`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(4,4))] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 52 - 1`)) THEN
    REWRITE_TAC[WORD_RULE
     `word(val(word_add (x:int64) x) * val(y:int64)):int64 =
      word(2 * val x * val y)`] THEN
    MAP_EVERY ABBREV_TAC
     [`d0:int64 = word_and n_0 (word (2 EXP 52 - 1))`;
      `d1:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_1 n_0) (52,64))
                           (word (2 EXP 52 - 1))`;
      `d2:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_2 n_1) (40,64))
                           (word (2 EXP 52 - 1))`;
      `d3:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_3 n_2) (28,64))
                           (word (2 EXP 52 - 1))`;
      `d4:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_4 n_3) (16,64))
                           (word (2 EXP 52 - 1))`;
      `d5:int64 = word_and (word_ushr n_4 4) (word (2 EXP 52 - 1))`;
      `d6:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_5 n_4) (56,64))
                           (word (2 EXP 52 - 1))`;
      `d7:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_6 n_5) (44,64))
                           (word (2 EXP 52 - 1))`;
      `d8:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_7 n_6) (32,64))
                           (word (2 EXP 52 - 1))`;
      `d9:int64 = word_ushr n_7 20`;
      `e0:int64 = word(2 * val(n_8:int64) * val(d0:int64))`;
      `e1:int64 =
       word_add(word(2 * val(n_8:int64) * val(d1:int64))) (word_ushr e0 52)`;
      `e2:int64 =
       word_add(word(2 * val(n_8:int64) * val(d2:int64))) (word_ushr e1 52)`;
      `e3:int64 =
       word_add(word(2 * val(n_8:int64) * val(d3:int64))) (word_ushr e2 52)`;
      `e4:int64 =
       word_add(word(2 * val(n_8:int64) * val(d4:int64))) (word_ushr e3 52)`;
      `e5:int64 =
       word_add(word(2 * val(n_8:int64) * val(d5:int64))) (word_ushr e4 52)`;
      `e6:int64 =
       word_add(word(2 * val(n_8:int64) * val(d6:int64))) (word_ushr e5 52)`;
      `e7:int64 =
       word_add(word(2 * val(n_8:int64) * val(d7:int64))) (word_ushr e6 52)`;
      `e8:int64 =
       word_add(word(2 * val(n_8:int64) * val(d8:int64))) (word_ushr e7 52)`;
      `e9:int64 =
       word_add(word(2 * val(n_8:int64) * val(d9:int64))) (word_ushr e8 52)`;
      `f0:int64 = word_subword
       ((word_join:int64->int64->int128) e1 (word_shl e0 12)) (12,64)`;
      `f1:int64 = word_subword
       ((word_join:int64->int64->int128) e2 (word_shl e1 12)) (24,64)`;
      `f2:int64 = word_subword
       ((word_join:int64->int64->int128) e3 (word_shl e2 12)) (36,64)`;
      `f3:int64 = word_subword
       ((word_join:int64->int64->int128) e4 (word_shl e3 12)) (48,64)`;
      `f4:int64 = word_subword
        ((word_join:int64->int64->int128) e6
        (word_shl (word_subword ((word_join:int64->int64->int128) e5
              (word_shl e4 12)) (60,64)) 8)) (8,64)`;
      `f5:int64 = word_subword
       ((word_join:int64->int64->int128) e7 (word_shl e6 12)) (20,64)`;
      `f6:int64 = word_subword
        ((word_join:int64->int64->int128) e8 (word_shl e7 12)) (32,64)`;
      `f7:int64 = word_subword
        ((word_join:int64->int64->int128) e9 (word_shl e8 12)) (44,64)`;
      `f8:int64 = word_ushr e9 44`] THEN
    SUBGOAL_THEN
     `2 * val(n_8:int64) *
      bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7] =
      bignum_of_wordlist[f0;f1;f2;f3;f4;f5;f6;f7;f8]`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7] =
        ITLIST (\(h:int64) t. val h + 2 EXP 52 * t)
               [d0;d1;d2;d3;d4;d5;d6;d7;d8;d9] 0 /\
        bignum_of_wordlist[f0; f1; f2; f3; f4; f5; f6; f7; f8] =
        2 EXP 520 * val(e9:int64) DIV 2 EXP 52 +
        ITLIST (\(h:int64) t. val h MOD 2 EXP 52 + 2 EXP 52 * t)
               [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9] 0`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[ITLIST; ADD_CLAUSES; MULT_CLAUSES; bignum_of_wordlist] THEN
        REWRITE_TAC[GSYM VAL_WORD_USHR; GSYM VAL_WORD_AND_MASK_WORD] THEN
        CONJ_TAC THENL
         [MAP_EVERY EXPAND_TAC
           ["d0"; "d1"; "d2"; "d3"; "d4"; "d5"; "d6"; "d7"; "d8"; "d9"];
          MAP_EVERY EXPAND_TAC
           ["f0"; "f1"; "f2"; "f3"; "f4"; "f5"; "f6"; "f7"; "f8"]] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
        REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
        REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
        REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                    BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
        ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC NUM_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `2 * val(n_8:int64) * val(d0:int64) = val (e0:int64) /\
        2 * val n_8 * val(d1:int64) + val e0 DIV 2 EXP 52 = val(e1:int64) /\
        2 * val n_8 * val(d2:int64) + val e1 DIV 2 EXP 52 = val(e2:int64) /\
        2 * val n_8 * val(d3:int64) + val e2 DIV 2 EXP 52 = val(e3:int64) /\
        2 * val n_8 * val(d4:int64) + val e3 DIV 2 EXP 52 = val(e4:int64) /\
        2 * val n_8 * val(d5:int64) + val e4 DIV 2 EXP 52 = val(e5:int64) /\
        2 * val n_8 * val(d6:int64) + val e5 DIV 2 EXP 52 = val(e6:int64) /\
        2 * val n_8 * val(d7:int64) + val e6 DIV 2 EXP 52 = val(e7:int64) /\
        2 * val n_8 * val(d8:int64) + val e7 DIV 2 EXP 52 = val(e8:int64) /\
        2 * val n_8 * val(d9:int64) + val e8 DIV 2 EXP 52 = val(e9:int64)`
      MP_TAC THENL [ALL_TAC; REWRITE_TAC[ITLIST] THEN ARITH_TAC] THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; VAL_WORD_USHR; DIMINDEX_64] THEN
      CONV_TAC SYM_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
      MATCH_MP_TAC MOD_LT THEN
      (MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 /\ e < 2 EXP 64
         ==> 2 * n * d + e DIV 2 EXP 52 < 2 EXP 64`) ORELSE
       MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 ==> 2 * n * d < 2 EXP 64`)) THEN
      REWRITE_TAC[VAL_BOUND_64] THEN MATCH_MP_TAC LE_MULT2 THEN
      CONJ_TAC THEN MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC
       ["d0"; "d1"; "d2"; "d3"; "d4"; "d5"; "d6"; "d7"; "d8"; "d9"] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN TRY ARITH_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR] THEN MATCH_MP_TAC
       (ARITH_RULE `n < 2 EXP 64 ==> n DIV 2 EXP 20 < 2 EXP 52`) THEN
      MATCH_ACCEPT_TAC VAL_BOUND_64;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE' o rev o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Rotation of the high portion ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (145--160) THEN
  ABBREV_TAC
   `htop:int64 =
    word_add (word_and sum_s80 (word 511)) (word_ushr sum_s144 9)` THEN
  SUBGOAL_THEN `val(htop:int64) < 2 EXP 56` ASSUME_TAC THENL
   [EXPAND_TAC "htop" THEN REWRITE_TAC[VAL_WORD_ADD] THEN
    W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
    REWRITE_TAC[DIMINDEX_64; SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD] THEN
    MP_TAC(ISPEC `sum_s144:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `h = bignum_of_wordlist
    [word_subword ((word_join:int64->int64->int128) sum_s88 sum_s80) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s96 sum_s88) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s104 sum_s96) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s119 sum_s104) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s127 sum_s119) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s135 sum_s127) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s142 sum_s135) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s144 sum_s142) (9,64);
     htop]` THEN
  SUBGOAL_THEN
   `n EXP 2 MOD p_521 =
    (2 EXP 257 * bignum_of_wordlist[n_0;n_1;n_2;n_3] *
                 bignum_of_wordlist[n_4;n_5;n_6;n_7] +
     bignum_of_wordlist[n_0;n_1;n_2;n_3] EXP 2 + h) MOD p_521`
  SUBST1_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,5)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[ARITH_RULE
     `(l + 2 EXP 256 * (h + 2 EXP 256 * c)) EXP 2 =
      2 EXP 257 * l * h + l EXP 2 +
      2 EXP 512 * ((h + 2 EXP 256 * c) EXP 2 + 2 * c * l)`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1))] THEN
    REWRITE_TAC[GSYM CONG; CONG_ADD_LCANCEL_EQ] THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    SUBGOAL_THEN
    `val(htop:int64) =
     val(word_and sum_s80 (word 511):int64) + val(word_ushr sum_s144 9:int64)`
    SUBST1_TAC THENL
     [EXPAND_TAC "htop" THEN
      REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD] THEN
      MP_TAC(ISPEC `sum_s144:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Squaring of the lower "half" ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [161; 162; 169; 174; 175; 177; 178; 179; 180; 181; 183; 184; 185; 186; 187;
    188; 189; 190; 191; 192; 193; 197; 198; 199; 200; 201; 202; 203; 204; 205;
    206; 207; 208; 209; 210; 214; 215; 216; 217; 218; 219; 220; 221; 222; 223]
   (161--223) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_0; n_1; n_2; n_3] EXP 2 =
    bignum_of_wordlist
     [mullo_s191; sum_s200; sum_s203; sum_s204;
      sum_s220; sum_s221; sum_s222; sum_s223]`
  SUBST1_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN FIRST_ASSUM
     (MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
      DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Addition of low and rotated high parts ***)

  SUBGOAL_THEN `h < 2 EXP 568` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP (64 * 8) /\ h < 2 EXP 56
      ==> l + 2 EXP 512 * h < 2 EXP 568`) THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `hl = bignum_of_wordlist
         [mullo_s191; sum_s200; sum_s203; sum_s204; sum_s220; sum_s221;
          sum_s222; sum_s223] + h` THEN
  SUBGOAL_THEN `hl < 2 EXP 569` ASSUME_TAC THENL
   [EXPAND_TAC "hl" THEN MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP (64 * 8) /\ h < 2 EXP 568 ==> l + h < 2 EXP 569`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [225; 226; 229; 230; 233; 234; 237; 238; 241] (224--242) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s225;sum_s226;sum_s229;sum_s230;
      sum_s233;sum_s234;sum_s237;sum_s238;sum_s241] = hl`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; INTEGER_CLOSED; LE_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `hl < 2 EXP 569 ==> hl < 2 EXP 576`] THEN
    MAP_EVERY EXPAND_TAC ["hl"; "h"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    FIRST_X_ASSUM(K ALL_TAC o check ((=) `hl:num` o rand o concl)) THEN
    DISCH_TAC] THEN

  (*** The cross-multiplication ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [243; 244; 245; 246; 248; 250; 252; 254; 255; 256; 257; 258;
    259; 260; 261; 262; 263; 264; 265; 271; 276; 278; 279; 285;
    290; 292; 293; 294; 295; 296; 297; 303; 308; 310; 311; 312;
    318; 323; 325; 326; 327; 328; 329; 335; 340; 342; 343; 344;
    345; 351; 356; 358; 359; 360; 361]
   (243--361) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist[n_0;n_1;n_2;n_3] *
    bignum_of_wordlist[n_4;n_5;n_6;n_7] =
    bignum_of_wordlist
     [mullo_s243; sum_s290; sum_s323; sum_s356;
      sum_s358; sum_s359; sum_s360; sum_s361]`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN FIRST_ASSUM
     (MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
      DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Addition of the rotated cross-product to the running total ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [364; 366; 369; 372; 376; 379; 383; 386; 391] (362--391) THEN
  MAP_EVERY ABBREV_TAC
  [`m0:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s359 sum_s358) (8,64)`;
  `m1:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s360 sum_s359) (8,64)`;
  `m2:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s361 sum_s360) (8,64)`;
  `m3:int64 = word_ushr sum_s361 8`;
  `m4:int64 = word_shl mullo_s243 1`;
  `m5:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s290 mullo_s243) (63,64)`;
  `m6:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s323 sum_s290) (63,64)`;
  `m7:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s356 sum_s323) (63,64)`;
  `m8:int64 = word_and
     (word_subword ((word_join:int64->int64->int128) sum_s358 sum_s356)
     (63,64)) (word 511)`] THEN

  SUBGOAL_THEN
   `(2 EXP 257 * bignum_of_wordlist
         [mullo_s243; sum_s290; sum_s323; sum_s356;
          sum_s358; sum_s359; sum_s360; sum_s361] + hl) MOD p_521 =
    (bignum_of_wordlist[m0;m1;m2;m3;m4;m5;m6;m7;m8] + hl) MOD p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CONG; CONG_ADD_RCANCEL_EQ] THEN
    MAP_EVERY EXPAND_TAC
     ["m0"; "m1"; "m2"; "m3"; "m4"; "m5"; "m6"; "m7"; "m8"] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `m = bignum_of_wordlist
         [sum_s364; sum_s366; sum_s369; sum_s372; sum_s376;
          sum_s379; sum_s383; sum_s386; sum_s391]` THEN
  SUBGOAL_THEN `m < 2 EXP 576` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [m0; m1; m2; m3; m4; m5; m6; m7; m8] + hl = m`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      MATCH_MP_TAC(ARITH_RULE
       `l < 2 EXP (64 * 8) /\ hl < 2 EXP 569 /\ h < 2 EXP 56
        ==> (l + 2 EXP 512 * h) + hl < 2 EXP 576`) THEN
      ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        EXPAND_TAC "m8" THEN
        REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
        REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED; LE_0; REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["hl"; "m"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `m MOD p_521 = (m DIV 2 EXP 521 + m MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `m = 2 EXP 521 * m DIV 2 EXP 521 + m MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m DIV 2 EXP 521 < 2 EXP 64 /\ m MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `m < 2 EXP 576` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (392--394) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `h:num` o concl))) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s391 9`;
    `d:int64 = word_or sum_s391 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s366 (word_and sum_s369 (word_and sum_s372
      (word_and sum_s376 (word_and sum_s379
         (word_and sum_s383 sum_s386)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (395--397) (395--397) THEN
  SUBGOAL_THEN
   `carry_s397 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s364:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (398--406) (398--413) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s413" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s391:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s391:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s364; sum_s366; sum_s369; sum_s372; sum_s376;
      sum_s379; sum_s383; sum_s386] =
    m MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= m MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s397`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s397" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s366; sum_s369; sum_s372; sum_s376; sum_s379; sum_s383; sum_s386] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s364:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < m ==> (a < m - 1 <=> ~(a = m - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s391:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s391:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s364:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = m DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    MATCH_MP_TAC(ARITH_RULE
     `m DIV 2 EXP 512 = x ==> x DIV 2 EXP 9 = m DIV 2 EXP 521`) THEN
    EXPAND_TAC "m" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= m MOD 2 EXP 521 + m DIV 2 EXP 521 + 1 <=>
    p_521 <= m DIV 2 EXP 521 + m MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if m DIV 2 EXP 521 + m MOD 2 EXP 521 < p_521
     then &(m DIV 2 EXP 521 + m MOD 2 EXP 521)
     else &(m DIV 2 EXP 521 + m MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `m < 2 EXP 576` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
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

let LOCAL_MUL_P521_SUBR_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,0x2fa8) (z,8 * 9) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9)
                       (word pc,0x2fa8) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9) (x,8 * 9) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9) (y,8 * 9) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x1ee4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = returnaddress /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,9);
                     memory :> bignum(word_add stackpointer (word 432),9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JSCALARMUL_EXEC (1--625)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    STRIP_TAC] THEN

  (*** 4x4 multiplication of the low portions and its rebasing ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [5; 6; 7; 8; 10; 12; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25;
    26; 27; 33; 38; 40; 41; 47; 52; 54; 55; 56; 57; 58; 59; 65; 70;
    72; 73; 74; 80; 85; 87; 88; 89; 90; 91; 97; 102; 104; 105; 106;
    107; 113; 118; 120; 121; 122; 123]
   (1--133) THEN
  ABBREV_TAC
   `l = bignum_of_wordlist
         [sum_s120; sum_s121; sum_s122; sum_s123; word_shl mullo_s5 9;
          word_subword
           ((word_join:int64->int64->int128) sum_s52 mullo_s5) (55,64);
          word_subword
           ((word_join:int64->int64->int128) sum_s85 sum_s52) (55,64);
          word_subword
           ((word_join:int64->int64->int128) sum_s118 sum_s85) (55,64);
          word_ushr sum_s118 55]` THEN
  SUBGOAL_THEN
   `l < 2 EXP 521 /\
    (2 EXP 256 * l ==
     bignum_of_wordlist[x_0;x_1;x_2;x_3] *
     bignum_of_wordlist[y_0;y_1;y_2;y_3]) (mod p_521)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; VAL_WORD_USHR] THEN
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) /\ y < 2 EXP 9
        ==> x + 2 EXP 512 * y < 2 EXP 521`) THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 55 * 2 EXP 9 = 2 EXP 64`] THEN
      REWRITE_TAC[VAL_BOUND_64] THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `bignum_of_wordlist[x_0;x_1;x_2;x_3] *
      bignum_of_wordlist[y_0;y_1;y_2;y_3] =
      bignum_of_wordlist[mullo_s5;sum_s52;sum_s85;sum_s118;
                         sum_s120;sum_s121;sum_s122;sum_s123]`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ADK_48_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** 4x4 multiplication of the high portions ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [138; 139; 140; 141; 143; 145; 147; 149; 150; 151; 152; 153;
    154; 155; 156; 157; 158; 159; 160; 166; 171; 173; 174; 180;
    185; 187; 188; 189; 190; 191; 192; 198; 203; 205; 206; 207;
    213; 218; 220; 221; 222; 223; 224; 230; 235; 237; 238; 239;
    240; 246; 251; 253; 254; 255; 256]
   (134--256) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [mullo_s138; sum_s185; sum_s218; sum_s251;
      sum_s253; sum_s254; sum_s255; sum_s256] =
    bignum_of_wordlist[x_4;x_5;x_6;x_7] *
    bignum_of_wordlist[y_4;y_5;y_6;y_7]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Addition combining high and low parts into hl ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [258; 259; 262; 263; 266; 267; 270; 271; 274]
   (257--275) THEN
  ABBREV_TAC
   `hl = bignum_of_wordlist
          [sum_s258; sum_s259; sum_s262; sum_s263;
           sum_s266; sum_s267; sum_s270; sum_s271; sum_s274]` THEN
  SUBGOAL_THEN
   `hl < 2 EXP 522 /\
    (2 EXP 256 * hl ==
     2 EXP 256 * bignum_of_wordlist[x_4;x_5;x_6;x_7] *
                 bignum_of_wordlist[y_4;y_5;y_6;y_7] +
     bignum_of_wordlist[x_0;x_1;x_2;x_3] *
     bignum_of_wordlist[y_0;y_1;y_2;y_3]) (mod p_521)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `!y:num. y < e /\ P y /\ (y < e ==> y = x)
              ==> x < e /\ P x`) THEN
    EXISTS_TAC
     `bignum_of_wordlist
       [mullo_s138; sum_s185; sum_s218; sum_s251; sum_s253; sum_s254;
        sum_s255; sum_s256] + l` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) /\ y < 2 EXP 521
        ==> x + y < 2 EXP 522`) THEN
      CONJ_TAC THENL [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; CONG_ADD_LCANCEL_EQ];
      DISCH_THEN(fun th ->
        MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 9)` THEN
        CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; ALL_TAC]) THEN
      MAP_EVERY EXPAND_TAC ["hl"; "l"] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
     ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
     REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `l:num` o concl)))] THEN

  (*** The sign-magnitude difference computation ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [277; 278; 280; 281; 284; 285; 287; 288;
    291; 293; 295; 297; 299; 301; 303; 305]
   (276--306) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; WORD_XOR_MASKS]) THEN
  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s288 <=> carry_s281)`;
   `xd = bignum_of_wordlist[sum_s291; sum_s293; sum_s295; sum_s297]`;
   `yd = bignum_of_wordlist[sum_s299; sum_s301; sum_s303; sum_s305]`] THEN
  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_4;x_5;x_6;x_7]) -
     &(bignum_of_wordlist[x_0;x_1;x_2;x_3])) *
    (&(bignum_of_wordlist[y_0;y_1;y_2;y_3]) -
     &(bignum_of_wordlist[y_4;y_5;y_6;y_7])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s281 * &xd) *
      (--(&1) pow bitval carry_s288 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s281 <=>
       bignum_of_wordlist[x_4;x_5;x_6;x_7] <
       bignum_of_wordlist[x_0;x_1;x_2;x_3]) /\
      (carry_s288 <=>
       bignum_of_wordlist[y_0;y_1;y_2;y_3] <
       bignum_of_wordlist[y_4;y_5;y_6;y_7])`
     (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    BINOP_TAC THEN REWRITE_TAC[bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = --(&1) pow 1 * z <=> y - x = z`] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** One more 4x4 multiplication of the cross-terms ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [307; 308; 309; 310; 312; 314; 316; 318; 319; 320; 321; 322;
    323; 324; 325; 326; 327; 328; 329; 335; 340; 342; 343; 349;
    354; 356; 357; 358; 359; 360; 361; 367; 372; 374; 375; 376;
    382; 387; 389; 390; 391; 392; 393; 399; 404; 406; 407; 408;
    409; 415; 420; 422; 423; 424; 425]
   (307--425) THEN
  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist
      [mullo_s307; sum_s354; sum_s387; sum_s420; sum_s422; sum_s423; sum_s424;
       sum_s425])`
  SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN
  MP_TAC(ASSUME `hl < 2 EXP 522`) THEN
  REWRITE_TAC[ARITH_RULE
   `n < 2 EXP 522 <=> n DIV 2 EXP 512 < 2 EXP 10`] THEN
  EXPAND_TAC "hl" THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
  DISCH_TAC THEN
  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [429; 431; 433; 435; 440; 442; 444; 446]
   (426--447) THEN
  ABBREV_TAC
   `hlm = bignum_of_wordlist
     [sum_s429; sum_s431; sum_s433; sum_s435;
      sum_s440; sum_s442; sum_s444; sum_s446;
      word_and (word_neg(word(bitval sgn))) (word 511)]` THEN
  SUBGOAL_THEN
   `(&hl +
     --(&1) pow bitval sgn *
     &(bignum_of_wordlist
       [mullo_s307; sum_s354; sum_s387; sum_s420; sum_s422; sum_s423;
        sum_s424; sum_s425]):int ==
     &2 pow 512 * &(val(sum_s274:int64) + bitval carry_s446) + &hlm)
    (mod &p_521)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hl"; "hlm"] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; p_521; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_add_th; int_sub_th; int_mul_th; int_pow_th;
                int_neg_th; int_of_num_th; bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN
    BOOL_CASES_TAC `sgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ABBREV_TAC `topcar:int64 = word_add sum_s274 (word(bitval carry_s446))` THEN
  SUBGOAL_THEN
   `val(sum_s274:int64) + bitval carry_s446 = val(topcar:int64) /\
    val(topcar:int64) <= 2 EXP 10`
  (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [MATCH_MP_TAC(ARITH_RULE
     `c <= 1 /\ s < 2 EXP 10 /\
      (s + c < 2 EXP 64 ==> y = s + c)
      ==> s + c = y /\ y <= 2 EXP 10`) THEN
    ASM_REWRITE_TAC[BITVAL_BOUND] THEN EXPAND_TAC "topcar" THEN
    SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64; VAL_WORD_BITVAL; MOD_LT];
    ALL_TAC] THEN
  ABBREV_TAC
   `hlm' = bignum_of_wordlist
     [sum_s440; sum_s442; sum_s444; sum_s446;
      word_or (word_shl sum_s429 9)
              (word_and (word_neg (word (bitval sgn))) (word 511));
      word_subword ((word_join:int64->int64->int128) sum_s431 sum_s429) (55,64);
      word_subword ((word_join:int64->int64->int128) sum_s433 sum_s431) (55,64);
      word_subword ((word_join:int64->int64->int128) sum_s435 sum_s433) (55,64);
      word_ushr sum_s435 55]` THEN
  SUBGOAL_THEN `(2 EXP 256 * hlm' == hlm) (mod p_521)` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hlm"; "hlm'"] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
     REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR; BIT_WORD_MASK;
      BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    FIRST_X_ASSUM(MP_TAC o
     check(can (term_match [] `(x:int == y) (mod n)` o concl))) THEN
    REWRITE_TAC[num_congruent; IMP_IMP] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (INTEGER_RULE
     `(x:int == a + y) (mod n) /\ (y' == y) (mod n)
      ==> (x == a + y') (mod n)`))] THEN
  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [448; 449; 450; 451; 455; 457; 459; 461]
   (448--463) THEN
  ABBREV_TAC
   `newtop:int64 =
    word_add (word_add (word_ushr sum_s435 55) sum_s274)
             (word (bitval carry_s461))` THEN
  SUBGOAL_THEN
   `val(word_ushr (sum_s435:int64) 55) +
    val(sum_s274:int64) + bitval carry_s461 =
    val(newtop:int64) /\
    val(newtop:int64) <= 2 EXP 11`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `u < 2 EXP 9 /\ c <= 1 /\ s < 2 EXP 10 /\
      (u + s + c < 2 EXP 64 ==> y = u + s + c)
      ==> u + s + c = y /\ y <= 2 EXP 11`) THEN
    ASM_REWRITE_TAC[BITVAL_BOUND] THEN CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD_USHR] THEN
      MP_TAC(SPEC `sum_s435:int64` VAL_BOUND_64) THEN ARITH_TAC;
      EXPAND_TAC "newtop" THEN
      REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; VAL_WORD_BITVAL] THEN
      CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[ADD_ASSOC; MOD_LT]];
    ALL_TAC] THEN
  ABBREV_TAC
   `topsum = bignum_of_wordlist
     [sum_s448; sum_s449; sum_s450; sum_s451;
      sum_s455; sum_s457; sum_s459; sum_s461; newtop]` THEN
  SUBGOAL_THEN
   `(2 EXP 512 * (2 EXP 256 * val(topcar:int64) + topsum) ==
     bignum_of_wordlist [x_0; x_1; x_2; x_3; x_4; x_5; x_6; x_7] *
     bignum_of_wordlist [y_0; y_1; y_2; y_3; y_4; y_5; y_6; y_7])
    (mod p_521)`
  MP_TAC THENL
   [REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,4)] THEN
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_ARITH
     `(l + &2 pow 256 * h) * (l' + &2 pow 256 * h'):int =
      (&1 + &2 pow 256) * (&2 pow 256 * h * h' + l * l') +
      &2 pow 256 * (h - l) * (l' - h')`] THEN
    FIRST_X_ASSUM(MP_TAC o
     check(can (term_match [] `x:real = a pow n * y`) o concl)) THEN
    REWRITE_TAC[GSYM int_of_num_th; GSYM int_pow_th; GSYM int_mul_th;
                GSYM int_sub_th; GSYM int_add_th; GSYM int_neg_th] THEN
    REWRITE_TAC[GSYM int_eq] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC(INTEGER_RULE
     `(a:int == b * x' + c) (mod n)
      ==> (x' == x) (mod n)
          ==> (a == b * x + c) (mod n)`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(hl + m:int == tc + e * hlm) (mod n)
      ==> (x == e * e * hl + e * tc + e * e * hlm) (mod n)
          ==> (x == (&1 + e) * e * hl + e * m) (mod n)`)) THEN
    REWRITE_TAC[INT_ARITH `(&2:int) pow 512 = &2 pow 256 * &2 pow 256`] THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC; GSYM INT_ADD_LDISTRIB] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `hl + hlm:int = s
      ==> (e * e * (tc + s) == e * e * (hl + tc + hlm)) (mod n)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN EXPAND_TAC "topsum" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
    MAP_EVERY EXPAND_TAC ["hl"; "hlm'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`(a:int == b) (mod n)`; `(a:num == b) (mod n)`; `x:real = y`;
      `a:num = b * c`; `word_add a b = c`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `hl:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `hlm':num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `sgn:bool` o concl))) THEN
    DISCH_TAC] THEN

  (*** The intricate augmentation of the product with top words ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC
   [484; 498; 510; 527; 551; 566; 579; 590; 595]
   (464--595) THEN
  SUBGOAL_THEN
   `(a * b) MOD p_521 =
    (2 EXP 512 *
     (2 EXP 512 * val(x_8:int64) * val(y_8:int64) +
      val x_8 * bignum_of_wordlist[y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7] +
      val y_8 * bignum_of_wordlist[x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] +
      2 EXP 256 * val(topcar:int64) + topsum)) MOD p_521`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE
     `e * (e * h + x + y + z):num = e * (e * h + x + y) + e * z`] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [CONG]) THEN
    CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [CONG])] THEN
  SUBGOAL_THEN
   `2 EXP 512 * val(x_8:int64) * val(y_8:int64) +
    val x_8 * bignum_of_wordlist[y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7] +
    val y_8 * bignum_of_wordlist[x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] +
    2 EXP 256 * val(topcar:int64) + topsum =
    bignum_of_wordlist
     [sum_s484; sum_s498; sum_s510; sum_s527;
      sum_s551; sum_s566; sum_s579; sum_s590; sum_s595]`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      MATCH_MP_TAC(ARITH_RULE
       `c2 <= 2 EXP 9 * 2 EXP 9 /\
        x <= 2 EXP 9 * 2 EXP 512 /\ y <= 2 EXP 9 * 2 EXP 512 /\
        c <= 2 EXP 256 * 2 EXP 64 /\
        s < 2 EXP 512 * 2 EXP 11 + 2 EXP 512
        ==> 2 EXP 512 * c2 + x + y + c + s < 2 EXP 576`) THEN
      REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC LE_MULT2 THEN
          ASM_SIMP_TAC[LT_IMP_LE; LE_REFL; VAL_BOUND_64] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
          BOUNDER_TAC[]) THEN
      EXPAND_TAC "topsum" THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      MATCH_MP_TAC(ARITH_RULE
       `c <= 2 EXP 11 /\ s < 2 EXP 512
        ==> s + 2 EXP 512 * c < 2 EXP 512 * 2 EXP 11 + 2 EXP 512`) THEN
      ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 52 - 1`)) THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word(val(x:int64) * val(d:int64)))
               (word(val(y:int64) * val(e:int64))):int64 =
      word(val x * val d + val y * val e)`] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word x) (word_shl c 48):int64 =
      word(2 EXP 48 * val c + x)`] THEN
    MAP_EVERY ABBREV_TAC
     [`dx0:int64 = word_and x_0 (word (2 EXP 52 - 1))`;
      `dx1:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_1 x_0) (52,64))
                           (word (2 EXP 52 - 1))`;
      `dx2:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_2 x_1) (40,64))
                           (word (2 EXP 52 - 1))`;
      `dx3:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_3 x_2) (28,64))
                           (word (2 EXP 52 - 1))`;
      `dx4:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_4 x_3) (16,64))
                           (word (2 EXP 52 - 1))`;
      `dx5:int64 = word_and (word_ushr x_4 4) (word (2 EXP 52 - 1))`;
      `dx6:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_5 x_4) (56,64))
                           (word (2 EXP 52 - 1))`;
      `dx7:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_6 x_5) (44,64))
                           (word (2 EXP 52 - 1))`;
      `dx8:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_7 x_6) (32,64))
                           (word (2 EXP 52 - 1))`;
      `dx9:int64 = word_ushr x_7 20`;
      `dy0:int64 = word_and y_0 (word (2 EXP 52 - 1))`;
      `dy1:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_1 y_0) (52,64))
                           (word (2 EXP 52 - 1))`;
      `dy2:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_2 y_1) (40,64))
                           (word (2 EXP 52 - 1))`;
      `dy3:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_3 y_2) (28,64))
                           (word (2 EXP 52 - 1))`;
      `dy4:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_4 y_3) (16,64))
                           (word (2 EXP 52 - 1))`;
      `dy5:int64 = word_and (word_ushr y_4 4) (word (2 EXP 52 - 1))`;
      `dy6:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_5 y_4) (56,64))
                           (word (2 EXP 52 - 1))`;
      `dy7:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_6 y_5) (44,64))
                           (word (2 EXP 52 - 1))`;
      `dy8:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_7 y_6) (32,64))
                           (word (2 EXP 52 - 1))`;
      `dy9:int64 = word_ushr y_7 20`;
      `e0:int64 = word(val(y_8:int64) * val(dx0:int64) +
                       val(x_8:int64) * val(dy0:int64))`;
      `e1:int64 =
       word_add (word(val(y_8:int64) * val(dx1:int64) +
                      val(x_8:int64) * val(dy1:int64)))
                (word_ushr e0 52)`;
      `e2:int64 =
       word_add (word(val(y_8:int64) * val(dx2:int64) +
                      val(x_8:int64) * val(dy2:int64)))
                (word_ushr e1 52)`;
      `e3:int64 =
       word_add (word(val(y_8:int64) * val(dx3:int64) +
                      val(x_8:int64) * val(dy3:int64)))
                (word_ushr e2 52)`;
      `e4:int64 =
       word_add (word(2 EXP 48 * val(topcar:int64) +
                      val(y_8:int64) * val(dx4:int64) +
                      val(x_8:int64) * val(dy4:int64)))
                (word_ushr e3 52)`;
      `e5:int64 =
       word_add (word(val(y_8:int64) * val(dx5:int64) +
                      val(x_8:int64) * val(dy5:int64)))
                (word_ushr e4 52)`;
      `e6:int64 =
       word_add (word(val(y_8:int64) * val(dx6:int64) +
                      val(x_8:int64) * val(dy6:int64)))
                (word_ushr e5 52)`;
      `e7:int64 =
       word_add (word(val(y_8:int64) * val(dx7:int64) +
                      val(x_8:int64) * val(dy7:int64)))
                (word_ushr e6 52)`;
      `e8:int64 =
       word_add (word(val(y_8:int64) * val(dx8:int64) +
                      val(x_8:int64) * val(dy8:int64)))
                (word_ushr e7 52)`;
      `e9:int64 =
       word_add (word(val(y_8:int64) * val(dx9:int64) +
                      val(x_8:int64) * val(dy9:int64)))
                (word_ushr e8 52)`;
      `f0:int64 = word_subword
       ((word_join:int64->int64->int128) e1 (word_shl e0 12)) (12,64)`;
      `f1:int64 = word_subword
       ((word_join:int64->int64->int128) e2 (word_shl e1 12)) (24,64)`;
      `f2:int64 = word_subword
       ((word_join:int64->int64->int128) e3 (word_shl e2 12)) (36,64)`;
      `f3:int64 = word_subword
       ((word_join:int64->int64->int128) e4 (word_shl e3 12)) (48,64)`;
      `f4:int64 = word_subword
        ((word_join:int64->int64->int128) e6
        (word_shl (word_subword ((word_join:int64->int64->int128) e5
              (word_shl e4 12)) (60,64)) 8)) (8,64)`;
      `f5:int64 = word_subword
       ((word_join:int64->int64->int128) e7 (word_shl e6 12)) (20,64)`;
      `f6:int64 = word_subword
        ((word_join:int64->int64->int128) e8 (word_shl e7 12)) (32,64)`;
      `f7:int64 = word_subword
        ((word_join:int64->int64->int128) e9 (word_shl e8 12)) (44,64)`;
      `f8:int64 = word_ushr e9 44`] THEN
    SUBGOAL_THEN
     `val(x_8:int64) * bignum_of_wordlist [y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7] +
      val(y_8:int64) * bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] +
      2 EXP 256 * val(topcar:int64) + topsum =
      bignum_of_wordlist[f0;f1;f2;f3;f4;f5;f6;f7;f8] + topsum`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `bignum_of_wordlist[x_0; x_1; x_2; x_3; x_4; x_5; x_6; x_7] =
        ITLIST (\(h:int64) t. val h + 2 EXP 52 * t)
               [dx0;dx1;dx2;dx3;dx4;dx5;dx6;dx7;dx8;dx9] 0 /\
        bignum_of_wordlist[y_0; y_1; y_2; y_3; y_4; y_5; y_6; y_7] =
        ITLIST (\(h:int64) t. val h + 2 EXP 52 * t)
               [dy0;dy1;dy2;dy3;dy4;dy5;dy6;dy7;dy8;dy9] 0 /\
        bignum_of_wordlist[f0; f1; f2; f3; f4; f5; f6; f7; f8] =
        2 EXP 520 * val(e9:int64) DIV 2 EXP 52 +
        ITLIST (\(h:int64) t. val h MOD 2 EXP 52 + 2 EXP 52 * t)
               [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9] 0`
      (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[ITLIST; ADD_CLAUSES; MULT_CLAUSES; bignum_of_wordlist] THEN
        REWRITE_TAC[GSYM VAL_WORD_USHR; GSYM VAL_WORD_AND_MASK_WORD] THEN
        REPEAT CONJ_TAC THENL
         [MAP_EVERY EXPAND_TAC
           ["dx0";"dx1";"dx2";"dx3";"dx4";"dx5";"dx6";"dx7";"dx8";"dx9"];
          MAP_EVERY EXPAND_TAC
           ["dy0";"dy1";"dy2";"dy3";"dy4";"dy5";"dy6";"dy7";"dy8";"dy9"];
          MAP_EVERY EXPAND_TAC
           ["f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8"]] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
        REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
        REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
        REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                    BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
        ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC NUM_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `val(y_8:int64) * val(dx0:int64) + val(x_8:int64) * val(dy0:int64) =
        val (e0:int64) /\
        val(y_8:int64) * val(dx1:int64) + val(x_8:int64) * val(dy1:int64) +
        val e0 DIV 2 EXP 52 = val(e1:int64) /\
        val(y_8:int64) * val(dx2:int64) + val(x_8:int64) * val(dy2:int64) +
        val e1 DIV 2 EXP 52 = val(e2:int64) /\
        val(y_8:int64) * val(dx3:int64) + val(x_8:int64) * val(dy3:int64) +
        val e2 DIV 2 EXP 52 = val(e3:int64) /\
        2 EXP 48 * val(topcar:int64) +
        val(y_8:int64) * val(dx4:int64) + val(x_8:int64) * val(dy4:int64) +
        val e3 DIV 2 EXP 52 = val(e4:int64) /\
        val(y_8:int64) * val(dx5:int64) + val(x_8:int64) * val(dy5:int64) +
        val e4 DIV 2 EXP 52 = val(e5:int64) /\
        val(y_8:int64) * val(dx6:int64) + val(x_8:int64) * val(dy6:int64) +
        val e5 DIV 2 EXP 52 = val(e6:int64) /\
        val(y_8:int64) * val(dx7:int64) + val(x_8:int64) * val(dy7:int64) +
        val e6 DIV 2 EXP 52 = val(e7:int64) /\
        val(y_8:int64) * val(dx8:int64) + val(x_8:int64) * val(dy8:int64) +
        val e7 DIV 2 EXP 52 = val(e8:int64) /\
        val(y_8:int64) * val(dx9:int64) + val(x_8:int64) * val(dy9:int64) +
        val e8 DIV 2 EXP 52 = val(e9:int64)`
      MP_TAC THENL [ALL_TAC; REWRITE_TAC[ITLIST] THEN ARITH_TAC] THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; VAL_WORD_USHR; DIMINDEX_64] THEN
      CONV_TAC SYM_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN MATCH_MP_TAC MOD_LT THEN
      (MATCH_MP_TAC(ARITH_RULE
        `c <= 2 EXP 10 /\ x < 2 EXP 63 ==> 2 EXP 48 * c + x < 2 EXP 64`) ORELSE
       MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 63 ==> x < 2 EXP 64`)) THEN
      ASM_REWRITE_TAC[] THEN
      (MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 /\
         m * e <= 2 EXP 9 * 2 EXP 52 /\
         f < 2 EXP 64
         ==> n * d + m * e + f DIV 2 EXP 52 < 2 EXP 63`) ORELSE
       MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 /\
         m * e <= 2 EXP 9 * 2 EXP 52
         ==> n * d + m * e < 2 EXP 63`)) THEN
      REWRITE_TAC[VAL_BOUND_64] THEN CONJ_TAC THEN
      MATCH_MP_TAC LE_MULT2 THEN
      CONJ_TAC THEN MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC
       ["dx0";"dx1";"dx2";"dx3";"dx4";"dx5";"dx6";"dx7";"dx8";"dx9";
        "dy0";"dy1";"dy2";"dy3";"dy4";"dy5";"dy6";"dy7";"dy8";"dy9"] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN TRY ARITH_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR] THEN MATCH_MP_TAC
       (ARITH_RULE `n < 2 EXP 64 ==> n DIV 2 EXP 20 < 2 EXP 52`) THEN
      MATCH_ACCEPT_TAC VAL_BOUND_64;
      ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    EXPAND_TAC "topsum" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE' o rev o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final modular reduction ***)

  ABBREV_TAC
   `n = bignum_of_wordlist
         [sum_s484; sum_s498; sum_s510; sum_s527; sum_s551; sum_s566;
          sum_s579; sum_s590; sum_s595]` THEN

  SUBGOAL_THEN `n < 2 EXP 576` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  SUBGOAL_THEN `n MOD p_521 = (n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `n = 2 EXP 521 * n DIV 2 EXP 521 + n MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n DIV 2 EXP 521 < 2 EXP 64 /\ n MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `n < 2 EXP 576` THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (596--598) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s595 9`;
    `d:int64 = word_or sum_s595 (word 18446744073709551104)`;
    `dd:int64 =
      word_and sum_s498 (word_and sum_s510 (word_and sum_s527
       (word_and sum_s551 (word_and sum_s566
         (word_and sum_s579 sum_s590)))))`] THEN
  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (599--601) (599--601) THEN
  SUBGOAL_THEN
   `carry_s601 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s484:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_ACCSTEPS_TAC P521_JSCALARMUL_EXEC (602--610) (602--610) THEN
  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s595:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s595:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s484; sum_s498; sum_s510; sum_s527;
      sum_s551; sum_s566; sum_s579; sum_s590] =
    n MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s601`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s601" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s498; sum_s510; sum_s527; sum_s551; sum_s566; sum_s579; sum_s590] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s484:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN SUBST1_TAC(SYM(ASSUME
     `word_and sum_s498 (word_and sum_s510 (word_and sum_s527
      (word_and sum_s551 (word_and sum_s566 (word_and sum_s579 sum_s590))))) =
      (dd:int64)`)) THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s595:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s595:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s484:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN
  SUBGOAL_THEN `val(h:int64) = n DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_ushr sum_s595 9 = (h:int64)`)) THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    MATCH_MP_TAC(ARITH_RULE
     `m DIV 2 EXP 512 = x ==> x DIV 2 EXP 9 = m DIV 2 EXP 521`) THEN
    EXPAND_TAC "n" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + n DIV 2 EXP 521 + 1 <=>
    p_521 <= n DIV 2 EXP 521 + n MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521 < p_521`
  MP_TAC THENL [REWRITE_TAC[MOD_LT_EQ; p_521] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521 =
    bignum_of_wordlist
     [sum_s602; sum_s603; sum_s604; sum_s605; sum_s606;
      sum_s607; sum_s608; sum_s609; word_and sum_s610 (word(2 EXP 9 - 1))]`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`521`;
      `if n DIV 2 EXP 521 + n MOD 2 EXP 521 < p_521
       then &(n DIV 2 EXP 521 + n MOD 2 EXP 521)
       else &(n DIV 2 EXP 521 + n MOD 2 EXP 521) - &p_521`] THEN
    REPEAT CONJ_TAC THENL
     [BOUNDER_TAC[];
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      ALL_TAC;
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `n < 2 EXP 576` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
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
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** The rotation to shift from the 512 position ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (611--625) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC MOD_DOWN_CONV THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[MOD_UNIQUE] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
   UNDISCH_TAC
   `bignum_of_wordlist
     [sum_s602; sum_s603; sum_s604; sum_s605; sum_s606;
      sum_s607; sum_s608; sum_s609; word_and sum_s610 (word(2 EXP 9 - 1))]
    < p_521` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_LT_P521; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[DIMINDEX_64; BIT_WORD_AND; BIT_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN (LABEL_TAC "*" o CONV_RULE(RAND_CONV CONJ_CANON_CONV)) THEN
  REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
  REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_AND; BIT_WORD;
              BIT_WORD_USHR; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV CONJ_CANON_CONV))) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REAL_INTEGER_TAC);;

let LOCAL_SUB_P521_SUBR_CORRECT = prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x2fa8) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x2f1c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read PC s = returnaddress /\
                  (m < p_521 /\ n < p_521
                  ==> &(bignum_from_memory (z,9) s) = (&m - &n) rem &p_521))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
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
    `pc:num`; `read X30 s`]
   `read (memory :> bytes(read X0 s,8 * 9)) s'`;;

let LOCAL_ADD_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_mc 37 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2fa8) (word_add (read p3 t) (word n3),72)
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
          MAYCHANGE SOME_FLAGS)`
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
    nonoverlapping (word pc,0x2fa8) (word_add (read p3 t) (word n3),72)
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
          MAYCHANGE SOME_FLAGS)`
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
    nonoverlapping (word pc,0x2fa8) (word_add (read p3 t) (word n3),72) /\
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
             MAYCHANGE SOME_FLAGS)`
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
    nonoverlapping (word pc,0x2fa8) (word_add (read p3 t) (word n3),72) /\
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
             MAYCHANGE SOME_FLAGS)`
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
    nonoverlapping (word pc,0x2fa8) (word_add (read p3 t) (word n3),72) /\
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
             MAYCHANGE SOME_FLAGS)`
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
        ALL (nonoverlapping (stackpointer,512))
            [(word pc,0x2fa8); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x2fa8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x17bc) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read PC s = word (pc + 0x1ec8) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X27; X30] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,512)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
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
        ALL (nonoverlapping (word_sub stackpointer (word 592),592))
            [(word pc,0x2fa8); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x2fa8)
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
                      memory :> bytes(word_sub stackpointer (word 592),592)])`,
  ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
   LOCAL_JDOUBLE_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X30]`
   592);;

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
        ALL (nonoverlapping (stackpointer,576))
            [(word pc,0x2fa8); (p1,216); (p2,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x2fa8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0x13d4) /\
                  read SP s = stackpointer /\
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
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,576)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
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
   `read (memory :> bytes (stackpointer,8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resy_"
   `read (memory :> bytes (word_add stackpointer (word 288),8 * 9)) s114` THEN
  BIGNUM_LDIGITIZE_TAC "resz_"
   `read (memory :> bytes (word_add stackpointer (word 360),8 * 9)) s114` THEN
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
        ALL (nonoverlapping (word_sub stackpointer (word 672),672))
            [(word pc,0x2fa8); (p1,216); (p2,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x2fa8)
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
                      memory :> bytes(word_sub stackpointer (word 672),672)])`,
  ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
   LOCAL_JADD_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]`
   672);;

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
        ALL (nonoverlapping (stackpointer,4640))
            [(word pc,0x2fa8); (res,216); (scalar,72); (point,216)] /\
        nonoverlapping (res,216) (word pc,0x2fa8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_mc /\
                  read PC s = word(pc + 0xc) /\
                  read SP s = word_add stackpointer (word 672) /\
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
                      memory :> bytes(stackpointer,4640)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
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
      read SP s = word_add stackpointer (word 672) /\
      read X20 s = res /\
      read X19 s = word (5 * i) /\
      bignum_from_memory(word_add stackpointer (word 672),9) s =
      2 EXP (576 - 5 * i) * n MOD (2 EXP (5 * i)) /\
      !P. P IN group_carrier p521_group /\ represents_p521 P (x,y',z)
          ==> represents_p521
                (group_zpow p521_group P
                    (&(n DIV 2 EXP (5 * i)) - &(recoder DIV 2 EXP (5 * i))))
                (bignum_triple_from_memory
                     (word_add stackpointer (word 744),9) s) /\
              !i. i < 16
                  ==> represents_p521 (group_pow p521_group P (i + 1))
                       (bignum_triple_from_memory
                       (word_add stackpointer (word (216 * i + 1176)),9) s)`
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
     `read (memory :> bytes (word_add stackpointer (word 672),8 * 9)) s18` THEN
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
     `read (memory :> bytes (word_add stackpointer (word 672),8 * 9)) s69 =
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
    `read (memory :> bytes (word_add stackpointer (word 1248),8 * 9)) s69` THEN
    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (70--100) THEN

    SUBGOAL_THEN
     `read (memory :> bytes (word_add stackpointer (word 1248),8 * 9)) s100 =
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
     [`x2 = read(memory :> bytes(word_add stackpointer (word 1392),8 * 9)) s104`;
      `y2 = read(memory :> bytes(word_add stackpointer (word 1464),8 * 9)) s104`;
      `z2 = read(memory :> bytes(word_add stackpointer (word 1536),8 * 9)) s104`
     ] THEN

    (*** Computation of 3 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (105--108) THEN
    LOCAL_JADD_TAC 109 THEN
    MAP_EVERY ABBREV_TAC
     [`x3 = read(memory :> bytes(word_add stackpointer (word 1608),8 * 9)) s109`;
      `y3 = read(memory :> bytes(word_add stackpointer (word 1680),8 * 9)) s109`;
      `z3 = read(memory :> bytes(word_add stackpointer (word 1752),8 * 9)) s109`
     ] THEN

    (*** Computation of 4 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (110--112) THEN
    LOCAL_JDOUBLE_TAC 113 THEN
    MAP_EVERY ABBREV_TAC
     [`x4 = read(memory :> bytes(word_add stackpointer (word 1824),8 * 9)) s113`;
      `y4 = read(memory :> bytes(word_add stackpointer (word 1896),8 * 9)) s113`;
      `z4 = read(memory :> bytes(word_add stackpointer (word 1968),8 * 9)) s113`
     ] THEN

    (*** Computation of 5 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (114--117) THEN
    LOCAL_JADD_TAC 118 THEN
    MAP_EVERY ABBREV_TAC
     [`x5 = read(memory :> bytes(word_add stackpointer (word 2040),8 * 9)) s118`;
      `y5 = read(memory :> bytes(word_add stackpointer (word 2112),8 * 9)) s118`;
      `z5 = read(memory :> bytes(word_add stackpointer (word 2184),8 * 9)) s118`
     ] THEN

    (*** Computation of 6 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (119--121) THEN
    LOCAL_JDOUBLE_TAC 122 THEN
    MAP_EVERY ABBREV_TAC
     [`x6 = read(memory :> bytes(word_add stackpointer (word 2256),8 * 9)) s122`;
      `y6 = read(memory :> bytes(word_add stackpointer (word 2328),8 * 9)) s122`;
      `z6 = read(memory :> bytes(word_add stackpointer (word 2400),8 * 9)) s122`
     ] THEN

    (*** Computation of 7 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (123--126) THEN
    LOCAL_JADD_TAC 127 THEN
    MAP_EVERY ABBREV_TAC
     [`x7 = read(memory :> bytes(word_add stackpointer (word 2472),8 * 9)) s127`;
      `y7 = read(memory :> bytes(word_add stackpointer (word 2544),8 * 9)) s127`;
      `z7 = read(memory :> bytes(word_add stackpointer (word 2616),8 * 9)) s127`
     ] THEN

    (*** Computation of 8 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (128--130) THEN
    LOCAL_JDOUBLE_TAC 131 THEN
    MAP_EVERY ABBREV_TAC
     [`x8 = read(memory :> bytes(word_add stackpointer (word 2688),8 * 9)) s131`;
      `y8 = read(memory :> bytes(word_add stackpointer (word 2760),8 * 9)) s131`;
      `z8 = read(memory :> bytes(word_add stackpointer (word 2832),8 * 9)) s131`
     ] THEN

    (*** Computation of 9 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (132--135) THEN
    LOCAL_JADD_TAC 136 THEN
    MAP_EVERY ABBREV_TAC
     [`x9 = read(memory :> bytes(word_add stackpointer (word 2904),8 * 9)) s136`;
      `y9 = read(memory :> bytes(word_add stackpointer (word 2976),8 * 9)) s136`;
      `z9 = read(memory :> bytes(word_add stackpointer (word 3048),8 * 9)) s136`
     ] THEN

    (*** Computation of 10 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (137--139) THEN
    LOCAL_JDOUBLE_TAC 140 THEN
    MAP_EVERY ABBREV_TAC
     [`xa = read(memory :> bytes(word_add stackpointer (word 3120),8 * 9)) s140`;
      `ya = read(memory :> bytes(word_add stackpointer (word 3192),8 * 9)) s140`;
      `za = read(memory :> bytes(word_add stackpointer (word 3264),8 * 9)) s140`
     ] THEN

    (*** Computation of 11 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (141--144) THEN
    LOCAL_JADD_TAC 145 THEN
    MAP_EVERY ABBREV_TAC
     [`xb = read(memory :> bytes(word_add stackpointer (word 3336),8 * 9)) s145`;
      `yb = read(memory :> bytes(word_add stackpointer (word 3408),8 * 9)) s145`;
      `zb = read(memory :> bytes(word_add stackpointer (word 3480),8 * 9)) s145`
     ] THEN

    (*** Computation of 12 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (146--148) THEN
    LOCAL_JDOUBLE_TAC 149 THEN
    MAP_EVERY ABBREV_TAC
     [`xc = read(memory :> bytes(word_add stackpointer (word 3552),8 * 9)) s149`;
      `yc = read(memory :> bytes(word_add stackpointer (word 3624),8 * 9)) s149`;
      `zc = read(memory :> bytes(word_add stackpointer (word 3696),8 * 9)) s149`
     ] THEN

    (*** Computation of 13 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (150--153) THEN
    LOCAL_JADD_TAC 154 THEN
    MAP_EVERY ABBREV_TAC
     [`xd = read(memory :> bytes(word_add stackpointer (word 3768),8 * 9)) s154`;
      `yd = read(memory :> bytes(word_add stackpointer (word 3840),8 * 9)) s154`;
      `zd = read(memory :> bytes(word_add stackpointer (word 3912),8 * 9)) s154`
     ] THEN

    (*** Computation of 14 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (155--157) THEN
    LOCAL_JDOUBLE_TAC 158 THEN
    MAP_EVERY ABBREV_TAC
     [`xe = read(memory :> bytes(word_add stackpointer (word 3984),8 * 9)) s158`;
      `ye = read(memory :> bytes(word_add stackpointer (word 4056),8 * 9)) s158`;
      `ze = read(memory :> bytes(word_add stackpointer (word 4128),8 * 9)) s158`
     ] THEN

    (*** Computation of 15 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (159--162) THEN
    LOCAL_JADD_TAC 163 THEN
    MAP_EVERY ABBREV_TAC
     [`xf = read(memory :> bytes(word_add stackpointer (word 4200),8 * 9)) s163`;
      `yf = read(memory :> bytes(word_add stackpointer (word 4272),8 * 9)) s163`;
      `zf = read(memory :> bytes(word_add stackpointer (word 4344),8 * 9)) s163`
     ] THEN

    (*** Computation of 16 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_EXEC (164--166) THEN
    LOCAL_JDOUBLE_TAC 167 THEN
    MAP_EVERY ABBREV_TAC
     [`xg = read(memory :> bytes(word_add stackpointer (word 4416),8 * 9)) s167`;
      `yg = read(memory :> bytes(word_add stackpointer (word 4488),8 * 9)) s167`;
      `zg = read(memory :> bytes(word_add stackpointer (word 4560),8 * 9)) s167`
     ] THEN

    (*** Add the recoding constant ***)

    DISCARD_MATCHING_ASSUMPTIONS [`read c s = if p then x else y`] THEN
    BIGNUM_LDIGITIZE_TAC "nr_"
     `read(memory :> bytes (word_add stackpointer (word 672),8 * 9)) s167` THEN
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
     `read(memory :> bytes (word_add stackpointer (word 1176),8 * 9)) s208` THEN
    BIGNUM_LDIGITIZE_TAC "yy_"
     `read(memory :> bytes (word_add stackpointer (word 1248),8 * 9)) s208` THEN
    BIGNUM_LDIGITIZE_TAC "zz_"
     `read(memory :> bytes (word_add stackpointer (word 1320),8 * 9)) s208` THEN
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
     `read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y_"
     `read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "z_"
     `read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s0` THEN
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
   `bignum_from_memory (word_add stackpointer (word 744),9)` THEN
  GHOST_INTRO_TAC `Ya:num`
   `bignum_from_memory (word_add stackpointer (word 816),9)` THEN
  GHOST_INTRO_TAC `Za:num`
   `bignum_from_memory (word_add stackpointer (word 888),9)` THEN

  (*** Computation of 2 * (Xa,Ya,Za) ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (5 * (i + 1))) (word 5) = word(5 * i)`]) THEN
  LOCAL_JDOUBLE_TAC 5 THEN
  MAP_EVERY ABBREV_TAC
   [`X2a = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s5`;
    `Y2a = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s5`;
    `Z2a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s5`
   ] THEN

  (*** Computation of 4 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (6--8) THEN
  LOCAL_JDOUBLE_TAC 9 THEN
  MAP_EVERY ABBREV_TAC
   [`X4a = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s9`;
    `Y4a = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s9`;
    `Z4a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s9`
   ] THEN

  (*** Computation of 8 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (10--12) THEN
  LOCAL_JDOUBLE_TAC 13 THEN
  MAP_EVERY ABBREV_TAC
   [`X8a = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s13`;
    `Y8a = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s13`;
    `Z8a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s13`
   ] THEN

  (*** Computation of 16 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (14--16) THEN
  LOCAL_JDOUBLE_TAC 17 THEN
  MAP_EVERY ABBREV_TAC
   [`Xha = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s17`;
    `Yha = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s17`;
    `Zha = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s17`
   ] THEN

  (*** Computation of 32 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (18--20) THEN
  LOCAL_JDOUBLE_TAC 21 THEN
  MAP_EVERY ABBREV_TAC
   [`Xta = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s21`;
    `Yta = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s21`;
    `Zta = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s21`
   ] THEN

  (*** Selection of bitfield ***)

  BIGNUM_LDIGITIZE_TAC "n_"
    `read (memory :> bytes (word_add stackpointer (word 672),8 * 9)) s21` THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (22--44) THEN
  ABBREV_TAC `bf = (n DIV (2 EXP (5 * i))) MOD 32` THEN
  SUBGOAL_THEN
   `word_ushr (n_8:int64) 59 = word bf /\
    read (memory :> bytes (word_add stackpointer (word 672),8 * 9)) s44 =
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
   `read(memory :> bytes(word_add stackpointer (word 1176),8 * 432)) s44` THEN
  ARM_STEPS_TAC P521_JSCALARMUL_EXEC (45--852) THEN

  MAP_EVERY ABBREV_TAC
   [`Xt = read (memory :> bytes(word_add stackpointer (word 960),8 * 9)) s852`;
    `Zt = read (memory :> bytes(word_add stackpointer (word 1104),8 * 9)) s852`
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
    read(memory :> bytes(word_add stackpointer (word 1032),8 * 9)) s877` THEN
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
   [`X' = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s882`;
    `Y' = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s882`;
    `Z' = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s882`
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
        ALL (nonoverlapping (word_sub stackpointer (word 4672),4672))
            [(word pc,0x2fa8); (res,216); (scalar,72); (point,216)] /\
        nonoverlapping (res,216) (word pc,0x2fa8)
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
                  memory :> bytes(word_sub stackpointer (word 4672),4672)])`,
   ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_EXEC
   P521_JSCALARMUL_CORRECT
    `[X19; X20; X21; X30]` 4672);;
