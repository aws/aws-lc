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

(**** print_literal_from_elf "arm/p521/p521_jscalarmul_alt.o";;
 ****)

let p521_jscalarmul_alt_mc = define_assert_from_elf
  "p521_jscalarmul_alt_mc" "arm/p521/p521_jscalarmul_alt.o"
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
  0xaa0003fb;       (* arm_MOV X27 X0 *)
  0xaa0103fc;       (* arm_MOV X28 X1 *)
  0xaa0203fd;       (* arm_MOV X29 X2 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x91024381;       (* arm_ADD X1 X28 (rvalue (word 144)) *)
  0x94000437;       (* arm_BL (word 4316) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x910243a1;       (* arm_ADD X1 X29 (rvalue (word 144)) *)
  0x94000434;       (* arm_BL (word 4304) *)
  0x9107e3e0;       (* arm_ADD X0 SP (rvalue (word 504)) *)
  0x910243a1;       (* arm_ADD X1 X29 (rvalue (word 144)) *)
  0x91012382;       (* arm_ADD X2 X28 (rvalue (word 72)) *)
  0x940002ba;       (* arm_BL (word 2792) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x91024381;       (* arm_ADD X1 X28 (rvalue (word 144)) *)
  0x910123a2;       (* arm_ADD X2 X29 (rvalue (word 72)) *)
  0x940002b6;       (* arm_BL (word 2776) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910003a2;       (* arm_ADD X2 X29 (rvalue (word 0)) *)
  0x940002b2;       (* arm_BL (word 2760) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91000382;       (* arm_ADD X2 X28 (rvalue (word 0)) *)
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
  0x940004ff;       (* arm_BL (word 5116) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x940004fb;       (* arm_BL (word 5100) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x94000411;       (* arm_BL (word 4164) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x9400040e;       (* arm_BL (word 4152) *)
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
  0x940004e9;       (* arm_BL (word 5028) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x940004e5;       (* arm_BL (word 5012) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x91024382;       (* arm_ADD X2 X28 (rvalue (word 144)) *)
  0x94000284;       (* arm_BL (word 2576) *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x910003e1;       (* arm_ADD X1 SP (rvalue (word 0)) *)
  0x910243e2;       (* arm_ADD X2 SP (rvalue (word 144)) *)
  0x940004dd;       (* arm_BL (word 4980) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910483e1;       (* arm_ADD X1 SP (rvalue (word 288)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x940004d9;       (* arm_BL (word 4964) *)
  0x910363e0;       (* arm_ADD X0 SP (rvalue (word 216)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x9107e3e2;       (* arm_ADD X2 SP (rvalue (word 504)) *)
  0x94000278;       (* arm_BL (word 2528) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x9105a3e1;       (* arm_ADD X1 SP (rvalue (word 360)) *)
  0x910243a2;       (* arm_ADD X2 X29 (rvalue (word 144)) *)
  0x94000274;       (* arm_BL (word 2512) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910123e1;       (* arm_ADD X1 SP (rvalue (word 72)) *)
  0x910483e2;       (* arm_ADD X2 SP (rvalue (word 288)) *)
  0x94000270;       (* arm_BL (word 2496) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910483e1;       (* arm_ADD X1 SP (rvalue (word 288)) *)
  0x910363e2;       (* arm_ADD X2 SP (rvalue (word 216)) *)
  0x940004c9;       (* arm_BL (word 4900) *)
  0xa9490780;       (* arm_LDP X0 X1 X28 (Immediate_Offset (iword (&144))) *)
  0xa94a0f82;       (* arm_LDP X2 X3 X28 (Immediate_Offset (iword (&160))) *)
  0xa94b1784;       (* arm_LDP X4 X5 X28 (Immediate_Offset (iword (&176))) *)
  0xa94c1f86;       (* arm_LDP X6 X7 X28 (Immediate_Offset (iword (&192))) *)
  0xf9406b88;       (* arm_LDR X8 X28 (Immediate_Offset (word 208)) *)
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
  0xa9492faa;       (* arm_LDP X10 X11 X29 (Immediate_Offset (iword (&144))) *)
  0xa94a37ac;       (* arm_LDP X12 X13 X29 (Immediate_Offset (iword (&160))) *)
  0xa94b3fae;       (* arm_LDP X14 X15 X29 (Immediate_Offset (iword (&176))) *)
  0xa94c47b0;       (* arm_LDP X16 X17 X29 (Immediate_Offset (iword (&192))) *)
  0xf9406bb3;       (* arm_LDR X19 X29 (Immediate_Offset (word 208)) *)
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
  0xa9405794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&0))) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0x9a803280;       (* arm_CSEL X0 X20 X0 Condition_CC *)
  0x9a8132a1;       (* arm_CSEL X1 X21 X1 Condition_CC *)
  0xa94057b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&0))) *)
  0x9a808280;       (* arm_CSEL X0 X20 X0 Condition_HI *)
  0x9a8182a1;       (* arm_CSEL X1 X21 X1 Condition_HI *)
  0xa9415794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&16))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0x9a823282;       (* arm_CSEL X2 X20 X2 Condition_CC *)
  0x9a8332a3;       (* arm_CSEL X3 X21 X3 Condition_CC *)
  0xa94157b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&16))) *)
  0x9a828282;       (* arm_CSEL X2 X20 X2 Condition_HI *)
  0x9a8382a3;       (* arm_CSEL X3 X21 X3 Condition_HI *)
  0xa9425794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&32))) *)
  0xa94217e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&32))) *)
  0x9a843284;       (* arm_CSEL X4 X20 X4 Condition_CC *)
  0x9a8532a5;       (* arm_CSEL X5 X21 X5 Condition_CC *)
  0xa94257b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&32))) *)
  0x9a848284;       (* arm_CSEL X4 X20 X4 Condition_HI *)
  0x9a8582a5;       (* arm_CSEL X5 X21 X5 Condition_HI *)
  0xa9435794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&48))) *)
  0xa9431fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&48))) *)
  0x9a863286;       (* arm_CSEL X6 X20 X6 Condition_CC *)
  0x9a8732a7;       (* arm_CSEL X7 X21 X7 Condition_CC *)
  0xa94357b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&48))) *)
  0x9a868286;       (* arm_CSEL X6 X20 X6 Condition_HI *)
  0x9a8782a7;       (* arm_CSEL X7 X21 X7 Condition_HI *)
  0xf9402394;       (* arm_LDR X20 X28 (Immediate_Offset (word 64)) *)
  0xf94023e8;       (* arm_LDR X8 SP (Immediate_Offset (word 64)) *)
  0x9a883288;       (* arm_CSEL X8 X20 X8 Condition_CC *)
  0xf94023b5;       (* arm_LDR X21 X29 (Immediate_Offset (word 64)) *)
  0x9a8882a8;       (* arm_CSEL X8 X21 X8 Condition_HI *)
  0xa944d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&72))) *)
  0xa9522fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&288))) *)
  0x9a8a328a;       (* arm_CSEL X10 X20 X10 Condition_CC *)
  0x9a8b32ab;       (* arm_CSEL X11 X21 X11 Condition_CC *)
  0xa944d7b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&72))) *)
  0x9a8a828a;       (* arm_CSEL X10 X20 X10 Condition_HI *)
  0x9a8b82ab;       (* arm_CSEL X11 X21 X11 Condition_HI *)
  0xa945d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&88))) *)
  0xa95337ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&304))) *)
  0x9a8c328c;       (* arm_CSEL X12 X20 X12 Condition_CC *)
  0x9a8d32ad;       (* arm_CSEL X13 X21 X13 Condition_CC *)
  0xa945d7b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&88))) *)
  0x9a8c828c;       (* arm_CSEL X12 X20 X12 Condition_HI *)
  0x9a8d82ad;       (* arm_CSEL X13 X21 X13 Condition_HI *)
  0xa946d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&104))) *)
  0xa9543fee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&320))) *)
  0x9a8e328e;       (* arm_CSEL X14 X20 X14 Condition_CC *)
  0x9a8f32af;       (* arm_CSEL X15 X21 X15 Condition_CC *)
  0xa946d7b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&104))) *)
  0x9a8e828e;       (* arm_CSEL X14 X20 X14 Condition_HI *)
  0x9a8f82af;       (* arm_CSEL X15 X21 X15 Condition_HI *)
  0xa947d794;       (* arm_LDP X20 X21 X28 (Immediate_Offset (iword (&120))) *)
  0xa95547f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&336))) *)
  0x9a903290;       (* arm_CSEL X16 X20 X16 Condition_CC *)
  0x9a9132b1;       (* arm_CSEL X17 X21 X17 Condition_CC *)
  0xa947d7b4;       (* arm_LDP X20 X21 X29 (Immediate_Offset (iword (&120))) *)
  0x9a908290;       (* arm_CSEL X16 X20 X16 Condition_HI *)
  0x9a9182b1;       (* arm_CSEL X17 X21 X17 Condition_HI *)
  0xf9404794;       (* arm_LDR X20 X28 (Immediate_Offset (word 136)) *)
  0xf940b3f3;       (* arm_LDR X19 SP (Immediate_Offset (word 352)) *)
  0x9a933293;       (* arm_CSEL X19 X20 X19 Condition_CC *)
  0xf94047b5;       (* arm_LDR X21 X29 (Immediate_Offset (word 136)) *)
  0x9a9382b3;       (* arm_CSEL X19 X21 X19 Condition_HI *)
  0xa9000760;       (* arm_STP X0 X1 X27 (Immediate_Offset (iword (&0))) *)
  0xa9010f62;       (* arm_STP X2 X3 X27 (Immediate_Offset (iword (&16))) *)
  0xa9021764;       (* arm_STP X4 X5 X27 (Immediate_Offset (iword (&32))) *)
  0xa9031f66;       (* arm_STP X6 X7 X27 (Immediate_Offset (iword (&48))) *)
  0xf9002368;       (* arm_STR X8 X27 (Immediate_Offset (word 64)) *)
  0xa95687e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&360))) *)
  0xa9578fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&376))) *)
  0xa95897e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&392))) *)
  0xa9599fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&408))) *)
  0xf940d7e8;       (* arm_LDR X8 SP (Immediate_Offset (word 424)) *)
  0xa904af6a;       (* arm_STP X10 X11 X27 (Immediate_Offset (iword (&72))) *)
  0xa905b76c;       (* arm_STP X12 X13 X27 (Immediate_Offset (iword (&88))) *)
  0xa906bf6e;       (* arm_STP X14 X15 X27 (Immediate_Offset (iword (&104))) *)
  0xa907c770;       (* arm_STP X16 X17 X27 (Immediate_Offset (iword (&120))) *)
  0xf9004773;       (* arm_STR X19 X27 (Immediate_Offset (word 136)) *)
  0xa9090760;       (* arm_STP X0 X1 X27 (Immediate_Offset (iword (&144))) *)
  0xa90a0f62;       (* arm_STP X2 X3 X27 (Immediate_Offset (iword (&160))) *)
  0xa90b1764;       (* arm_STP X4 X5 X27 (Immediate_Offset (iword (&176))) *)
  0xa90c1f66;       (* arm_STP X6 X7 X27 (Immediate_Offset (iword (&192))) *)
  0xf9006b68;       (* arm_STR X8 X27 (Immediate_Offset (word 208)) *)
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
  0xaa0003fb;       (* arm_MOV X27 X0 *)
  0xaa0103fc;       (* arm_MOV X28 X1 *)
  0x910003e0;       (* arm_ADD X0 SP (rvalue (word 0)) *)
  0x91024381;       (* arm_ADD X1 X28 (rvalue (word 144)) *)
  0x9400033d;       (* arm_BL (word 3316) *)
  0x910123e0;       (* arm_ADD X0 SP (rvalue (word 72)) *)
  0x91012381;       (* arm_ADD X1 X28 (rvalue (word 72)) *)
  0x9400033a;       (* arm_BL (word 3304) *)
  0xa9401b85;       (* arm_LDP X5 X6 X28 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412387;       (* arm_LDP X7 X8 X28 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9422b89;       (* arm_LDP X9 X10 X28 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xa943338b;       (* arm_LDP X11 X12 X28 (Immediate_Offset (iword (&48))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf940238d;       (* arm_LDR X13 X28 (Immediate_Offset (word 64)) *)
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
  0xa9401b85;       (* arm_LDP X5 X6 X28 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xba0400a5;       (* arm_ADCS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412387;       (* arm_LDP X7 X8 X28 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422b89;       (* arm_LDP X9 X10 X28 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xa943338b;       (* arm_LDP X11 X12 X28 (Immediate_Offset (iword (&48))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xba04016b;       (* arm_ADCS X11 X11 X4 *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf940238d;       (* arm_LDR X13 X28 (Immediate_Offset (word 64)) *)
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
  0xa9449b85;       (* arm_LDP X5 X6 X28 (Immediate_Offset (iword (&72))) *)
  0xa9490f84;       (* arm_LDP X4 X3 X28 (Immediate_Offset (iword (&144))) *)
  0xba0400a5;       (* arm_ADCS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa945a387;       (* arm_LDP X7 X8 X28 (Immediate_Offset (iword (&88))) *)
  0xa94a0f84;       (* arm_LDP X4 X3 X28 (Immediate_Offset (iword (&160))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa946ab89;       (* arm_LDP X9 X10 X28 (Immediate_Offset (iword (&104))) *)
  0xa94b0f84;       (* arm_LDP X4 X3 X28 (Immediate_Offset (iword (&176))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xa947b38b;       (* arm_LDP X11 X12 X28 (Immediate_Offset (iword (&120))) *)
  0xa94c0f84;       (* arm_LDP X4 X3 X28 (Immediate_Offset (iword (&192))) *)
  0xba04016b;       (* arm_ADCS X11 X11 X4 *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf940478d;       (* arm_LDR X13 X28 (Immediate_Offset (word 136)) *)
  0xf9406b84;       (* arm_LDR X4 X28 (Immediate_Offset (word 208)) *)
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
  0x91000381;       (* arm_ADD X1 X28 (rvalue (word 0)) *)
  0x910123e2;       (* arm_ADD X2 SP (rvalue (word 72)) *)
  0x94000150;       (* arm_BL (word 1344) *)
  0x9105a3e0;       (* arm_ADD X0 SP (rvalue (word 360)) *)
  0x910363e1;       (* arm_ADD X1 SP (rvalue (word 216)) *)
  0x940002c3;       (* arm_BL (word 2828) *)
  0x910243e0;       (* arm_ADD X0 SP (rvalue (word 144)) *)
  0x910243e1;       (* arm_ADD X1 SP (rvalue (word 144)) *)
  0x940002c0;       (* arm_BL (word 2816) *)
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
  0x94000230;       (* arm_BL (word 2240) *)
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
  0xa9091b65;       (* arm_STP X5 X6 X27 (Immediate_Offset (iword (&144))) *)
  0xa90a2367;       (* arm_STP X7 X8 X27 (Immediate_Offset (iword (&160))) *)
  0xa90b2b69;       (* arm_STP X9 X10 X27 (Immediate_Offset (iword (&176))) *)
  0xa90c336b;       (* arm_STP X11 X12 X27 (Immediate_Offset (iword (&192))) *)
  0xf9006b6d;       (* arm_STR X13 X27 (Immediate_Offset (word 208)) *)
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
  0xa9001363;       (* arm_STP X3 X4 X27 (Immediate_Offset (iword (&0))) *)
  0xa9011b65;       (* arm_STP X5 X6 X27 (Immediate_Offset (iword (&16))) *)
  0xa9022367;       (* arm_STP X7 X8 X27 (Immediate_Offset (iword (&32))) *)
  0xa9032b69;       (* arm_STP X9 X10 X27 (Immediate_Offset (iword (&48))) *)
  0xf900236b;       (* arm_STR X11 X27 (Immediate_Offset (word 64)) *)
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
  0xa9049363;       (* arm_STP X3 X4 X27 (Immediate_Offset (iword (&72))) *)
  0xa9059b65;       (* arm_STP X5 X6 X27 (Immediate_Offset (iword (&88))) *)
  0xa906a367;       (* arm_STP X7 X8 X27 (Immediate_Offset (iword (&104))) *)
  0xa907ab69;       (* arm_STP X9 X10 X27 (Immediate_Offset (iword (&120))) *)
  0xf900476b;       (* arm_STR X11 X27 (Immediate_Offset (word 136)) *)
  0x910803ff;       (* arm_ADD SP SP (rvalue (word 512)) *)
  0xa8c17bfd;       (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&0))) *)
  0x9b057c6f;       (* arm_MUL X15 X3 X5 *)
  0x9bc57c70;       (* arm_UMULH X16 X3 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xa9412047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0x9bc87c74;       (* arm_UMULH X20 X3 X8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xa9422849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&32))) *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0x9bc97c75;       (* arm_UMULH X21 X3 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0x9bca7c76;       (* arm_UMULH X22 X3 X10 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xa943304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&48))) *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0x9bcb7c77;       (* arm_UMULH X23 X3 X11 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xf940204d;       (* arm_LDR X13 X2 (Immediate_Offset (word 64)) *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0x9bcc7c78;       (* arm_UMULH X24 X3 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0x9bcd7c79;       (* arm_UMULH X25 X3 X13 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9a9f37fa;       (* arm_CSET X26 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e0231;       (* arm_ADDS X17 X17 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e035a;       (* arm_ADC X26 X26 X14 *)
  0xa91b43ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&432))) *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0231;       (* arm_ADDS X17 X17 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9a9f37ef;       (* arm_CSET X15 Condition_CS *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bcd7c6e;       (* arm_UMULH X14 X3 X13 *)
  0x9a0e01ef;       (* arm_ADC X15 X15 X14 *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0210;       (* arm_ADC X16 X16 X14 *)
  0xa91c4ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&448))) *)
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9a9f37f1;       (* arm_CSET X17 Condition_CS *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e02b5;       (* arm_ADDS X21 X21 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcd7c6e;       (* arm_UMULH X14 X3 X13 *)
  0x9a0e0231;       (* arm_ADC X17 X17 X14 *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e02b5;       (* arm_ADDS X21 X21 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9a9f37f3;       (* arm_CSET X19 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e02d6;       (* arm_ADDS X22 X22 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0273;       (* arm_ADC X19 X19 X14 *)
  0xa91d57f4;       (* arm_STP X20 X21 SP (Immediate_Offset (iword (&464))) *)
  0xa9431023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&48))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e02d6;       (* arm_ADDS X22 X22 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e02f7;       (* arm_ADDS X23 X23 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bcd7c6e;       (* arm_UMULH X14 X3 X13 *)
  0x9a0e0294;       (* arm_ADC X20 X20 X14 *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e02f7;       (* arm_ADDS X23 X23 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9a9f37f5;       (* arm_CSET X21 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e0318;       (* arm_ADDS X24 X24 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e02b5;       (* arm_ADC X21 X21 X14 *)
  0xa91e5ff6;       (* arm_STP X22 X23 SP (Immediate_Offset (iword (&480))) *)
  0xf9402023;       (* arm_LDR X3 X1 (Immediate_Offset (word 64)) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0318;       (* arm_ADDS X24 X24 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0x9a0e02b5;       (* arm_ADC X21 X21 X14 *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e0339;       (* arm_ADDS X25 X25 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0x9a0e02b5;       (* arm_ADC X21 X21 X14 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa95b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&432))) *)
  0x93d8272e;       (* arm_EXTR X14 X25 X24 9 *)
  0xba0e00a5;       (* arm_ADCS X5 X5 X14 *)
  0x93d9274e;       (* arm_EXTR X14 X26 X25 9 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0xa95c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&448))) *)
  0x93da25ee;       (* arm_EXTR X14 X15 X26 9 *)
  0xba0e00e7;       (* arm_ADCS X7 X7 X14 *)
  0x93cf260e;       (* arm_EXTR X14 X16 X15 9 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0xa95d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&464))) *)
  0x93d0262e;       (* arm_EXTR X14 X17 X16 9 *)
  0xba0e0129;       (* arm_ADCS X9 X9 X14 *)
  0x93d1266e;       (* arm_EXTR X14 X19 X17 9 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xa95e33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&480))) *)
  0x93d3268e;       (* arm_EXTR X14 X20 X19 9 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x93d426ae;       (* arm_EXTR X14 X21 X20 9 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0xb277db0d;       (* arm_ORR X13 X24 (rvalue (word 18446744073709551104)) *)
  0xd349feae;       (* arm_LSR X14 X21 9 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0xa903300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200d;       (* arm_STR X13 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4d;       (* arm_UMULH X13 X2 X4 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4e;       (* arm_UMULH X14 X2 X5 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c4f;       (* arm_UMULH X15 X2 X6 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c50;       (* arm_UMULH X16 X2 X7 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c51;       (* arm_UMULH X17 X2 X8 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c53;       (* arm_UMULH X19 X2 X9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a0294;       (* arm_ADC X20 X20 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd5;       (* arm_UMULH X21 X6 X7 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02d6;       (* arm_ADC X22 X22 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf7;       (* arm_UMULH X23 X7 X8 *)
  0xab0a02d6;       (* arm_ADDS X22 X22 X10 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0318;       (* arm_ADC X24 X24 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d19;       (* arm_UMULH X25 X8 X9 *)
  0xab0a0318;       (* arm_ADDS X24 X24 X10 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0x9a9f37fa;       (* arm_CSET X26 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0xab0a016b;       (* arm_ADDS X11 X11 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a035a;       (* arm_ADC X26 X26 X10 *)
  0xf9402021;       (* arm_LDR X1 X1 (Immediate_Offset (word 64)) *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x9b027c2a;       (* arm_MUL X10 X1 X2 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc27c2a;       (* arm_UMULH X10 X1 X2 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b047c2a;       (* arm_MUL X10 X1 X4 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc47c2a;       (* arm_UMULH X10 X1 X4 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b067c2a;       (* arm_MUL X10 X1 X6 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc67c2a;       (* arm_UMULH X10 X1 X6 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b087c2a;       (* arm_MUL X10 X1 X8 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc87c2a;       (* arm_UMULH X10 X1 X8 *)
  0xba0a035a;       (* arm_ADCS X26 X26 X10 *)
  0xd341fc24;       (* arm_LSR X4 X1 1 *)
  0x9b047c84;       (* arm_MUL X4 X4 X4 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b037c2a;       (* arm_MUL X10 X1 X3 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9bc37c2a;       (* arm_UMULH X10 X1 X3 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b057c2a;       (* arm_MUL X10 X1 X5 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc57c2a;       (* arm_UMULH X10 X1 X5 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b077c2a;       (* arm_MUL X10 X1 X7 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc77c2a;       (* arm_UMULH X10 X1 X7 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b097c2a;       (* arm_MUL X10 X1 X9 *)
  0xba0a035a;       (* arm_ADCS X26 X26 X10 *)
  0x9bc97c2a;       (* arm_UMULH X10 X1 X9 *)
  0x9a0a0084;       (* arm_ADC X4 X4 X10 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93d3268a;       (* arm_EXTR X10 X20 X19 9 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0x93d426aa;       (* arm_EXTR X10 X21 X20 9 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x93d526ca;       (* arm_EXTR X10 X22 X21 9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x93d626ea;       (* arm_EXTR X10 X23 X22 9 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x93d7270a;       (* arm_EXTR X10 X24 X23 9 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x93d8272a;       (* arm_EXTR X10 X25 X24 9 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x93d9274a;       (* arm_EXTR X10 X26 X25 9 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x93da248a;       (* arm_EXTR X10 X4 X26 9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xb277da73;       (* arm_ORR X19 X19 (rvalue (word 18446744073709551104)) *)
  0xd349fc8a;       (* arm_LSR X10 X4 9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f0273;       (* arm_SBC X19 X19 XZR *)
  0x92402273;       (* arm_AND X19 X19 (rvalue (word 511)) *)
  0xa9002c02;       (* arm_STP X2 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xa901340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&16))) *)
  0xa9023c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&32))) *)
  0xa9034410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&48))) *)
  0xf9002013;       (* arm_STR X19 X0 (Immediate_Offset (word 64)) *)
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

let P521_JSCALARMUL_ALT_EXEC = ARM_MK_EXEC_RULE p521_jscalarmul_alt_mc;;

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Level 1: the embedded field squaring and multiplication                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P521_SUBR_CORRECT = prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x28ec) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
                  read PC s = word(pc + 0x24c4) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (n EXP 2) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--231)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** Simulate the initial squaring ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--195) (1--195) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`l0 = read X2 s195`;
    `l1 = read X11 s195`;
    `l2 = read X12 s195`;
    `l3 = read X13 s195`;
    `l4 = read X14 s195`;
    `l5 = read X15 s195`;
    `l6 = read X16 s195`;
    `l7 = read X17 s195`;
    `h0 = read X19 s195`;
    `h1 = read X20 s195`;
    `h2 = read X21 s195`;
    `h3 = read X22 s195`;
    `h4 = read X23 s195`;
    `h5 = read X24 s195`;
    `h6 = read X25 s195`;
    `h7 = read X26 s195`;
    `h8 = read X4 s195`]  THEN

  (*** Handle the two anomalous operations ***)

  UNDISCH_THEN
   `&2 pow 64 * &(bitval carry_s159) + &(val(sum_s159:int64)):real =
    &(val(n_8:int64)) + &(val n_8)`
  (MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
   MATCH_MP_TAC(ARITH_RULE `a < b ==> ~(b + s:num = a)`) THEN
   ASM BOUNDER_TAC[];
   REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
   DISCH_THEN SUBST_ALL_TAC] THEN

  UNDISCH_THEN
   `&2 pow 64 * &(val(mulhi_s176:int64)) + &(val(mullo_s176:int64)):real =
    &2 pow 63 * (&(val(n_8:int64)) + &(val n_8))`
    (MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 63 * (n + n) = 2 EXP 64 * n`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `e * h + l = e * x ==> e divides l /\ e * h + l = e * x`)) THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REWRITE_TAC[REWRITE_RULE[GSYM NOT_LE] VAL_BOUND_64] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 * x + 0 = 2 EXP 64 * y <=> x = y`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN

  (*** Show that the core squaring operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_of_wordlist[l0;l1;l2;l3;l4;l5;l6;l7] =
    n EXP 2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[EXP_2; ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      MATCH_MP_TAC LT_MULT2 THEN UNDISCH_TAC `n < p_521` THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the shift-and-add of high and lower parts ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [198;200;202;204;206;208;210;212;215] (196--215) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (n EXP 2) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (n EXP 2) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n EXP 2) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`n EXP 2:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(n EXP 2) DIV 2 EXP 521 =
    bignum_of_wordlist
     [word_subword (word_join (h1:int64) h0:int128) (9,64);
      word_subword (word_join (h2:int64) h1:int128) (9,64);
      word_subword (word_join (h3:int64) h2:int128) (9,64);
      word_subword (word_join (h4:int64) h3:int128) (9,64);
      word_subword (word_join (h5:int64) h4:int128) (9,64);
      word_subword (word_join (h6:int64) h5:int128) (9,64);
      word_subword (word_join (h7:int64) h6:int128) (9,64);
      word_subword (word_join (h8:int64) h7:int128) (9,64);
      word_ushr h8 9] /\
    (n EXP 2) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist [l0; l1; l2; l3; l4; l5; l6; l7]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_USHR] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
      ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) ==> 2 EXP 512 * h MOD 2 EXP 9 + x < 2 EXP 521`) THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH]];
    ALL_TAC] THEN

  (*** The net comparison h + l >= p_521 ***)

  SUBGOAL_THEN
   `&(val (word_or h0 (word 18446744073709551104))):real =
    (&2 pow 64 - &2 pow 9) + &(val(word_and h0 (word 511):int64))`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s215 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (216--224) (216--231) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ABBREV_TAC `bb <=> h + l < p_521` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_SIMP_TAC[MOD_CASES; ARITH_RULE
     `h < p /\ l <= p ==> h + l < 2 * p`] THEN
    SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; COND_SWAP; GSYM NOT_LE] THEN
    MESON_TAC[]]);;

let LOCAL_MUL_P521_SUBR_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word pc,0x28ec) (z,8 * 9) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9)
                       (word pc,0x28ec) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9) (x,8 * 9) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9) (y,8 * 9) /\
        nonoverlapping (word_add stackpointer (word 432),8 * 9) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
                  read PC s = word(pc + 0x1eec) /\
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
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
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
    ARM_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--374)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `bignum_from_memory (y,9) s0` THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--334) (1--334) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`h0 = read X24 s334`;
    `h1 = read X25 s334`;
    `h2 = read X26 s334`;
    `h3 = read X15 s334`;
    `h4 = read X16 s334`;
    `h5 = read X17 s334`;
    `h6 = read X19 s334`;
    `h7 = read X20 s334`;
    `h8 = read X21 s334`] THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(word_add stackpointer (word 432),8) s334 =
    a * b`
  ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[EXP_2; ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      MATCH_MP_TAC LT_MULT2 THEN
      MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the shift-and-add of high and lower parts ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [338;340;343;345;348;350;353;355;358] (335--358) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (a * b) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (a * b) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a * b) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`a * b:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a * b) DIV 2 EXP 521 =
    bignum_of_wordlist
     [word_subword (word_join (h1:int64) h0:int128) (9,64);
      word_subword (word_join (h2:int64) h1:int128) (9,64);
      word_subword (word_join (h3:int64) h2:int128) (9,64);
      word_subword (word_join (h4:int64) h3:int128) (9,64);
      word_subword (word_join (h5:int64) h4:int128) (9,64);
      word_subword (word_join (h6:int64) h5:int128) (9,64);
      word_subword (word_join (h7:int64) h6:int128) (9,64);
      word_subword (word_join (h8:int64) h7:int128) (9,64);
      word_ushr h8 9] /\
    (a * b) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist
     [mullo_s3; sum_s35; sum_s74; sum_s111;
      sum_s150; sum_s187; sum_s226;  sum_s263]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_USHR] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
      ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) ==> 2 EXP 512 * h MOD 2 EXP 9 + x < 2 EXP 521`) THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH]];
    ALL_TAC] THEN

  (*** The net comparison h + l >= p_521 ***)

  SUBGOAL_THEN
   `&(val (word_or h0 (word 18446744073709551104))):real =
    (&2 pow 64 - &2 pow 9) + &(val(word_and h0 (word 511):int64))`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s358 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (359--367) (359--374) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ABBREV_TAC `bb <=> h + l < p_521` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_SIMP_TAC[MOD_CASES; ARITH_RULE
     `h < p /\ l <= p ==> h + l < 2 * p`] THEN
    SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; COND_SWAP; GSYM NOT_LE] THEN
    MESON_TAC[]]);;

let LOCAL_SUB_P521_SUBR_CORRECT = prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x28ec) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
                  read PC s = word(pc + 0x2860) /\
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
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 9)) s0` THEN

  (*** Initial subtraction x - y, comparison result ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
   [3;4;7;8;11;12;15;16;19] (1--19) THEN

  SUBGOAL_THEN `carry_s19 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (20--28) (20--35) THEN
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
 ["x_1",[`X28`;`0`];
  "y_1",[`X28`;`72`];
  "z_1",[`X28`;`144`];
  "x_3",[`X27`;`0`];
  "y_3",[`X27`;`72`];
  "z_3",[`X27`;`144`];
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
      (p521_jscalarmul_alt_mc,P521_JSCALARMUL_ALT_EXEC,0,p521_jscalarmul_alt_mc,corth)
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
    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC ((n+1)--(n+m+k)) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_mc 37 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x28ec) (word_add (read p3 t) (word n3),72)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X27 s = read X27 t /\
              read X28 s = read X28 t /\
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
    ARM_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--37)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial non-overflowing addition s = x + y + 1 ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [4;5;8;9;12;13;16;17;20] (1--20) THEN
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

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (21--22) THEN
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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (23::(25--32)) (23--37) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_mc 34 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x28ec) (word_add (read p3 t) (word n3),72)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X27 s = read X27 t /\
              read X28 s = read X28 t /\
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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [3;4;7;8;11;12;15;16;19] (1--19) THEN

  SUBGOAL_THEN `carry_s19 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (20--28) (20--34) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_mc 107 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x28ec) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X27 t,216) (stackpointer,512) /\
    nonoverlapping (read X28 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X27 s = read X27 t /\
              read X28 s = read X28 t /\
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
    ARM_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--107)] THEN

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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--86) (1--86) THEN
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

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (87--89) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s86 9`;
    `d:int64 = word_or sum_s86 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s73 (word_and sum_s74 (word_and sum_s76
      (word_and sum_s78 (word_and sum_s80 (word_and sum_s82 sum_s84)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (90--92) (90--92) THEN
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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (93--101) (93--107) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_mc 57 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x28ec) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X27 t,216) (stackpointer,512) /\
    nonoverlapping (read X28 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X27 s = read X27 t /\
              read X28 s = read X28 t /\
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
    ARM_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--57)] THEN

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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC [17;18;20;22;25;27;30;32;36] (1--36) THEN
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

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (37--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s36 9`;
    `d:int64 = word_or sum_s36 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s18 (word_and sum_s20 (word_and sum_s22
      (word_and sum_s25 (word_and sum_s27 (word_and sum_s30 sum_s32)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (40--42) (40--42) THEN
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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (43--51) (43--57) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC p521_jscalarmul_alt_mc 82 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x28ec) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X27 t,216) (stackpointer,512) /\
    nonoverlapping (read X28 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X27 s = read X27 t /\
              read X28 s = read X28 t /\
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
    ARM_SIM_TAC P521_JSCALARMUL_ALT_EXEC (1--82)] THEN

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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
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

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (62--64) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s61 9`;
    `d:int64 = word_or sum_s61 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s30 (word_and sum_s34 (word_and sum_s38
      (word_and sum_s43 (word_and sum_s47 (word_and sum_s52 sum_s56)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (65--67) (65--67) THEN
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

  ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC (68--76) (68--82) THEN
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
            [(word pc,0x28ec); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x28ec)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
                  read PC s = word(pc + 0x17c0) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read PC s = word (pc + 0x1ecc) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X27; X28; X30] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
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
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
            [(word pc,0x28ec); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x28ec)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
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
                      memory :> bytes(word_sub stackpointer (word 608),608)])`,
  ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC
   LOCAL_JDOUBLE_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]`
   608);;

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
            [(word pc,0x28ec); (p1,216); (p2,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x28ec)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
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
                      X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
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
  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (115--259) THEN
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
            [(word pc,0x28ec); (p1,216); (p2,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x28ec)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
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
  ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC
   LOCAL_JADD_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]`
   672);;

(* ------------------------------------------------------------------------- *)
(* Level 3: the top-level proof.                                             *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MOD_N521_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_alt_mc,P521_JSCALARMUL_ALT_EXEC,
    0x12a0,bignum_mod_n521_9_mc,BIGNUM_MOD_N521_9_SUBROUTINE_CORRECT)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 9)) s`;
   `pc + 0x12a0`; `read X30 s`];;

let LOCAL_MOD_P521_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p521_jscalarmul_alt_mc,P521_JSCALARMUL_ALT_EXEC,
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
   (p521_jscalarmul_alt_mc,P521_JSCALARMUL_ALT_EXEC,
    0x0,p521_jscalarmul_alt_mc,th)
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
   (p521_jscalarmul_alt_mc,P521_JSCALARMUL_ALT_EXEC,
    0x0,p521_jscalarmul_alt_mc,th)
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

let P521_JSCALARMUL_ALT_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,4640))
            [(word pc,0x28ec); (res,216); (scalar,72); (point,216)] /\
        nonoverlapping (res,216) (word pc,0x28ec)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
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
    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--4) THEN
    LOCAL_MOD_N521_TAC 5 THEN

    (*** Reduction of input point coordinates, actually supererogatory ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (6--9) THEN
    LOCAL_MOD_P521_TAC 10 THEN
    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (11--13) THEN
    LOCAL_MOD_P521_TAC 14 THEN
    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (15--17) THEN
    LOCAL_MOD_P521_TAC 18 THEN

    (*** Conditional negation of scalar ***)

    BIGNUM_LDIGITIZE_TAC "nn_"
     `read (memory :> bytes (word_add stackpointer (word 672),8 * 9)) s18` THEN
    ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
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
    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (70--100) THEN

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

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (101--103) THEN
    LOCAL_JDOUBLE_TAC 104 THEN
    MAP_EVERY ABBREV_TAC
     [`x2 = read(memory :> bytes(word_add stackpointer (word 1392),8 * 9)) s104`;
      `y2 = read(memory :> bytes(word_add stackpointer (word 1464),8 * 9)) s104`;
      `z2 = read(memory :> bytes(word_add stackpointer (word 1536),8 * 9)) s104`
     ] THEN

    (*** Computation of 3 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (105--108) THEN
    LOCAL_JADD_TAC 109 THEN
    MAP_EVERY ABBREV_TAC
     [`x3 = read(memory :> bytes(word_add stackpointer (word 1608),8 * 9)) s109`;
      `y3 = read(memory :> bytes(word_add stackpointer (word 1680),8 * 9)) s109`;
      `z3 = read(memory :> bytes(word_add stackpointer (word 1752),8 * 9)) s109`
     ] THEN

    (*** Computation of 4 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (110--112) THEN
    LOCAL_JDOUBLE_TAC 113 THEN
    MAP_EVERY ABBREV_TAC
     [`x4 = read(memory :> bytes(word_add stackpointer (word 1824),8 * 9)) s113`;
      `y4 = read(memory :> bytes(word_add stackpointer (word 1896),8 * 9)) s113`;
      `z4 = read(memory :> bytes(word_add stackpointer (word 1968),8 * 9)) s113`
     ] THEN

    (*** Computation of 5 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (114--117) THEN
    LOCAL_JADD_TAC 118 THEN
    MAP_EVERY ABBREV_TAC
     [`x5 = read(memory :> bytes(word_add stackpointer (word 2040),8 * 9)) s118`;
      `y5 = read(memory :> bytes(word_add stackpointer (word 2112),8 * 9)) s118`;
      `z5 = read(memory :> bytes(word_add stackpointer (word 2184),8 * 9)) s118`
     ] THEN

    (*** Computation of 6 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (119--121) THEN
    LOCAL_JDOUBLE_TAC 122 THEN
    MAP_EVERY ABBREV_TAC
     [`x6 = read(memory :> bytes(word_add stackpointer (word 2256),8 * 9)) s122`;
      `y6 = read(memory :> bytes(word_add stackpointer (word 2328),8 * 9)) s122`;
      `z6 = read(memory :> bytes(word_add stackpointer (word 2400),8 * 9)) s122`
     ] THEN

    (*** Computation of 7 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (123--126) THEN
    LOCAL_JADD_TAC 127 THEN
    MAP_EVERY ABBREV_TAC
     [`x7 = read(memory :> bytes(word_add stackpointer (word 2472),8 * 9)) s127`;
      `y7 = read(memory :> bytes(word_add stackpointer (word 2544),8 * 9)) s127`;
      `z7 = read(memory :> bytes(word_add stackpointer (word 2616),8 * 9)) s127`
     ] THEN

    (*** Computation of 8 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (128--130) THEN
    LOCAL_JDOUBLE_TAC 131 THEN
    MAP_EVERY ABBREV_TAC
     [`x8 = read(memory :> bytes(word_add stackpointer (word 2688),8 * 9)) s131`;
      `y8 = read(memory :> bytes(word_add stackpointer (word 2760),8 * 9)) s131`;
      `z8 = read(memory :> bytes(word_add stackpointer (word 2832),8 * 9)) s131`
     ] THEN

    (*** Computation of 9 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (132--135) THEN
    LOCAL_JADD_TAC 136 THEN
    MAP_EVERY ABBREV_TAC
     [`x9 = read(memory :> bytes(word_add stackpointer (word 2904),8 * 9)) s136`;
      `y9 = read(memory :> bytes(word_add stackpointer (word 2976),8 * 9)) s136`;
      `z9 = read(memory :> bytes(word_add stackpointer (word 3048),8 * 9)) s136`
     ] THEN

    (*** Computation of 10 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (137--139) THEN
    LOCAL_JDOUBLE_TAC 140 THEN
    MAP_EVERY ABBREV_TAC
     [`xa = read(memory :> bytes(word_add stackpointer (word 3120),8 * 9)) s140`;
      `ya = read(memory :> bytes(word_add stackpointer (word 3192),8 * 9)) s140`;
      `za = read(memory :> bytes(word_add stackpointer (word 3264),8 * 9)) s140`
     ] THEN

    (*** Computation of 11 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (141--144) THEN
    LOCAL_JADD_TAC 145 THEN
    MAP_EVERY ABBREV_TAC
     [`xb = read(memory :> bytes(word_add stackpointer (word 3336),8 * 9)) s145`;
      `yb = read(memory :> bytes(word_add stackpointer (word 3408),8 * 9)) s145`;
      `zb = read(memory :> bytes(word_add stackpointer (word 3480),8 * 9)) s145`
     ] THEN

    (*** Computation of 12 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (146--148) THEN
    LOCAL_JDOUBLE_TAC 149 THEN
    MAP_EVERY ABBREV_TAC
     [`xc = read(memory :> bytes(word_add stackpointer (word 3552),8 * 9)) s149`;
      `yc = read(memory :> bytes(word_add stackpointer (word 3624),8 * 9)) s149`;
      `zc = read(memory :> bytes(word_add stackpointer (word 3696),8 * 9)) s149`
     ] THEN

    (*** Computation of 13 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (150--153) THEN
    LOCAL_JADD_TAC 154 THEN
    MAP_EVERY ABBREV_TAC
     [`xd = read(memory :> bytes(word_add stackpointer (word 3768),8 * 9)) s154`;
      `yd = read(memory :> bytes(word_add stackpointer (word 3840),8 * 9)) s154`;
      `zd = read(memory :> bytes(word_add stackpointer (word 3912),8 * 9)) s154`
     ] THEN

    (*** Computation of 14 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (155--157) THEN
    LOCAL_JDOUBLE_TAC 158 THEN
    MAP_EVERY ABBREV_TAC
     [`xe = read(memory :> bytes(word_add stackpointer (word 3984),8 * 9)) s158`;
      `ye = read(memory :> bytes(word_add stackpointer (word 4056),8 * 9)) s158`;
      `ze = read(memory :> bytes(word_add stackpointer (word 4128),8 * 9)) s158`
     ] THEN

    (*** Computation of 15 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (159--162) THEN
    LOCAL_JADD_TAC 163 THEN
    MAP_EVERY ABBREV_TAC
     [`xf = read(memory :> bytes(word_add stackpointer (word 4200),8 * 9)) s163`;
      `yf = read(memory :> bytes(word_add stackpointer (word 4272),8 * 9)) s163`;
      `zf = read(memory :> bytes(word_add stackpointer (word 4344),8 * 9)) s163`
     ] THEN

    (*** Computation of 16 * P ***)

    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (164--166) THEN
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
    ARM_ACCSTEPS_TAC P521_JSCALARMUL_ALT_EXEC
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
    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (209--266) THEN
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
    ARM_SIM_TAC P521_JSCALARMUL_ALT_EXEC [1] THEN
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
    ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--29) THEN
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
  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (5 * (i + 1))) (word 5) = word(5 * i)`]) THEN
  LOCAL_JDOUBLE_TAC 5 THEN
  MAP_EVERY ABBREV_TAC
   [`X2a = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s5`;
    `Y2a = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s5`;
    `Z2a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s5`
   ] THEN

  (*** Computation of 4 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (6--8) THEN
  LOCAL_JDOUBLE_TAC 9 THEN
  MAP_EVERY ABBREV_TAC
   [`X4a = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s9`;
    `Y4a = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s9`;
    `Z4a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s9`
   ] THEN

  (*** Computation of 8 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (10--12) THEN
  LOCAL_JDOUBLE_TAC 13 THEN
  MAP_EVERY ABBREV_TAC
   [`X8a = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s13`;
    `Y8a = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s13`;
    `Z8a = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s13`
   ] THEN

  (*** Computation of 16 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (14--16) THEN
  LOCAL_JDOUBLE_TAC 17 THEN
  MAP_EVERY ABBREV_TAC
   [`Xha = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s17`;
    `Yha = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s17`;
    `Zha = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s17`
   ] THEN

  (*** Computation of 32 * (Xa,Ya,Za) ***)

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (18--20) THEN
  LOCAL_JDOUBLE_TAC 21 THEN
  MAP_EVERY ABBREV_TAC
   [`Xta = read (memory :> bytes(word_add stackpointer (word 744),8 * 9)) s21`;
    `Yta = read (memory :> bytes(word_add stackpointer (word 816),8 * 9)) s21`;
    `Zta = read (memory :> bytes(word_add stackpointer (word 888),8 * 9)) s21`
   ] THEN

  (*** Selection of bitfield ***)

  BIGNUM_LDIGITIZE_TAC "n_"
    `read (memory :> bytes (word_add stackpointer (word 672),8 * 9)) s21` THEN
  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (22--44) THEN
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
  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (45--852) THEN

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

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (853--877) THEN
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

  ARM_STEPS_TAC P521_JSCALARMUL_ALT_EXEC (878--881) THEN
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

let P521_JSCALARMUL_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar point n xyz pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 4672),4672))
            [(word pc,0x28ec); (res,216); (scalar,72); (point,216)] /\
        nonoverlapping (res,216) (word pc,0x28ec)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jscalarmul_alt_mc /\
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
   ARM_ADD_RETURN_STACK_TAC P521_JSCALARMUL_ALT_EXEC
   P521_JSCALARMUL_ALT_CORRECT
    `[X19; X20; X21; X30]` 4672);;
