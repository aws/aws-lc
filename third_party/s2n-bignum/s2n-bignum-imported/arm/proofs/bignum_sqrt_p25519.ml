(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Square roots modulo p_25519, the field characteristic for curve25519.     *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "arm/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/curve25519/bignum_sqrt_p25519.o";;
 ****)

let bignum_sqrt_p25519_mc = define_assert_from_elf "bignum_sqrt_p25519_mc" "arm/curve25519/bignum_sqrt_p25519.o"
[
  0xa9bf7bf3;       (* arm_STP X19 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10203ff;       (* arm_SUB SP SP (rvalue (word 128)) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0xd37ffca6;       (* arm_LSR X6 X5 63 *)
  0x9b061ce6;       (* arm_MADD X6 X7 X6 X7 *)
  0xab060042;       (* arm_ADDS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xb24100a5;       (* arm_ORR X5 X5 (rvalue (word 9223372036854775808)) *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a9f30e6;       (* arm_CSEL X6 X7 XZR Condition_CC *)
  0xeb060042;       (* arm_SUBS X2 X2 X6 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xa9000fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0xa90117e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&16))) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x94000164;       (* arm_BL (word 1424) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x940000ab;       (* arm_BL (word 684) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800041;       (* arm_MOV X1 (rvalue (word 2)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x9400015c;       (* arm_BL (word 1392) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x940000a3;       (* arm_BL (word 652) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x94000154;       (* arm_BL (word 1360) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x9400009b;       (* arm_BL (word 620) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x9400014c;       (* arm_BL (word 1328) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000093;       (* arm_BL (word 588) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800141;       (* arm_MOV X1 (rvalue (word 10)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x94000144;       (* arm_BL (word 1296) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x9400008b;       (* arm_BL (word 556) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x9400013c;       (* arm_BL (word 1264) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000083;       (* arm_BL (word 524) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000134;       (* arm_BL (word 1232) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x9400007b;       (* arm_BL (word 492) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800641;       (* arm_MOV X1 (rvalue (word 50)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x9400012c;       (* arm_BL (word 1200) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x94000073;       (* arm_BL (word 460) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x94000124;       (* arm_BL (word 1168) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x9400006b;       (* arm_BL (word 428) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800fa1;       (* arm_MOV X1 (rvalue (word 125)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x9400011c;       (* arm_BL (word 1136) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000063;       (* arm_BL (word 396) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000114;       (* arm_BL (word 1104) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x9400005b;       (* arm_BL (word 364) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x9400010c;       (* arm_BL (word 1072) *)
  0xd2941600;       (* arm_MOV X0 (rvalue (word 41136)) *)
  0xf2a941c0;       (* arm_MOVK X0 (word 18958) 16 *)
  0xf2c364e0;       (* arm_MOVK X0 (word 6951) 32 *)
  0xf2f89dc0;       (* arm_MOVK X0 (word 50414) 48 *)
  0xd29c8f01;       (* arm_MOV X1 (rvalue (word 58488)) *)
  0xf2b5a5e1;       (* arm_MOVK X1 (word 44335) 16 *)
  0xf2c300c1;       (* arm_MOVK X1 (word 6150) 32 *)
  0xf2e5e861;       (* arm_MOVK X1 (word 12099) 48 *)
  0xd29af4e2;       (* arm_MOV X2 (rvalue (word 55207)) *)
  0xf2a7bf62;       (* arm_MOVK X2 (word 15867) 16 *)
  0xf2c01322;       (* arm_MOVK X2 (word 153) 32 *)
  0xf2e569a2;       (* arm_MOVK X2 (word 11085) 48 *)
  0xd29be163;       (* arm_MOV X3 (rvalue (word 57099)) *)
  0xf2a9f823;       (* arm_MOVK X3 (word 20417) 16 *)
  0xf2c49003;       (* arm_MOVK X3 (word 9344) 32 *)
  0xf2e57063;       (* arm_MOVK X3 (word 11139) 48 *)
  0xa90607e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xa9070fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x94000041;       (* arm_BL (word 260) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x940000f2;       (* arm_BL (word 968) *)
  0xa9402fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0xa9423fee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&32))) *)
  0xca0e014a;       (* arm_EOR X10 X10 X14 *)
  0xca0f016b;       (* arm_EOR X11 X11 X15 *)
  0xaa0b014a;       (* arm_ORR X10 X10 X11 *)
  0xa94137ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  0xa94347f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&48))) *)
  0xca10018c;       (* arm_EOR X12 X12 X16 *)
  0xca1101ad;       (* arm_EOR X13 X13 X17 *)
  0xaa0d018c;       (* arm_ORR X12 X12 X13 *)
  0xaa0c014a;       (* arm_ORR X10 X10 X12 *)
  0xeb1f015f;       (* arm_CMP X10 XZR *)
  0xa9442fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&64))) *)
  0xa9463fee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&96))) *)
  0x9a8e014a;       (* arm_CSEL X10 X10 X14 Condition_EQ *)
  0x9a8f016b;       (* arm_CSEL X11 X11 X15 Condition_EQ *)
  0xa94537ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&80))) *)
  0xa94747f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&112))) *)
  0x9a90018c;       (* arm_CSEL X12 X12 X16 Condition_EQ *)
  0x9a9101ad;       (* arm_CSEL X13 X13 X17 Condition_EQ *)
  0x9280024e;       (* arm_MOVN X14 (word 18) 0 *)
  0xeb0a01ce;       (* arm_SUBS X14 X14 X10 *)
  0x92800010;       (* arm_MOVN X16 (word 0) 0 *)
  0xfa0b020f;       (* arm_SBCS X15 X16 X11 *)
  0x92f00011;       (* arm_MOVN X17 (word 32768) 48 *)
  0xfa0c0210;       (* arm_SBCS X16 X16 X12 *)
  0xda0d0231;       (* arm_SBC X17 X17 X13 *)
  0xf240015f;       (* arm_TST X10 (rvalue (word 1)) *)
  0x9a8e014a;       (* arm_CSEL X10 X10 X14 Condition_EQ *)
  0x9a8f016b;       (* arm_CSEL X11 X11 X15 Condition_EQ *)
  0x9a90018c;       (* arm_CSEL X12 X12 X16 Condition_EQ *)
  0x9a9101ad;       (* arm_CSEL X13 X13 X17 Condition_EQ *)
  0xaa1303e2;       (* arm_MOV X2 X19 *)
  0xa9002c4a;       (* arm_STP X10 X11 X2 (Immediate_Offset (iword (&0))) *)
  0xa901344c;       (* arm_STP X12 X13 X2 (Immediate_Offset (iword (&16))) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x940000cc;       (* arm_BL (word 816) *)
  0xa9402fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0xa9423fee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&32))) *)
  0xca0e014e;       (* arm_EOR X14 X10 X14 *)
  0xca0f016f;       (* arm_EOR X15 X11 X15 *)
  0xaa0f01ce;       (* arm_ORR X14 X14 X15 *)
  0xa94137ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  0xa94347f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&48))) *)
  0xca100190;       (* arm_EOR X16 X12 X16 *)
  0xca1101b1;       (* arm_EOR X17 X13 X17 *)
  0xaa110210;       (* arm_ORR X16 X16 X17 *)
  0xaa1001ce;       (* arm_ORR X14 X14 X16 *)
  0xeb1f01df;       (* arm_CMP X14 XZR *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0xda800400;       (* arm_CNEG X0 X0 Condition_NE *)
  0xaa0b014a;       (* arm_ORR X10 X10 X11 *)
  0xaa0d018c;       (* arm_ORR X12 X12 X13 *)
  0xaa0c014a;       (* arm_ORR X10 X10 X12 *)
  0xeb1f015f;       (* arm_CMP X10 XZR *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x910203ff;       (* arm_ADD SP SP (rvalue (word 128)) *)
  0xa8c17bf3;       (* arm_LDP X19 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&0))) *)
  0x9ba57c67;       (* arm_UMULL X7 W3 W5 *)
  0xd360fc71;       (* arm_LSR X17 X3 32 *)
  0x9ba57e2f;       (* arm_UMULL X15 W17 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9bb17e08;       (* arm_UMULL X8 W16 W17 *)
  0x9bb07c70;       (* arm_UMULL X16 W3 W16 *)
  0xab0f80e7;       (* arm_ADDS X7 X7 (Shiftedreg X15 LSL 32) *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x9a0f0108;       (* arm_ADC X8 X8 X15 *)
  0xab1080e7;       (* arm_ADDS X7 X7 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a100108;       (* arm_ADC X8 X8 X16 *)
  0x9b067c89;       (* arm_MUL X9 X4 X6 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xeb0600a3;       (* arm_SUBS X3 X5 X6 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b037c8f;       (* arm_MUL X15 X4 X3 *)
  0x9bc37c83;       (* arm_UMULH X3 X4 X3 *)
  0xab0900e8;       (* arm_ADDS X8 X7 X9 *)
  0xba0a0129;       (* arm_ADCS X9 X9 X10 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0801e8;       (* arm_ADCS X8 X15 X8 *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xba090069;       (* arm_ADCS X9 X3 X9 *)
  0x9a10014a;       (* arm_ADC X10 X10 X16 *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0xa9411845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&16))) *)
  0x9ba57c6b;       (* arm_UMULL X11 W3 W5 *)
  0xd360fc71;       (* arm_LSR X17 X3 32 *)
  0x9ba57e2f;       (* arm_UMULL X15 W17 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9bb17e0c;       (* arm_UMULL X12 W16 W17 *)
  0x9bb07c70;       (* arm_UMULL X16 W3 W16 *)
  0xab0f816b;       (* arm_ADDS X11 X11 (Shiftedreg X15 LSL 32) *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x9a0f018c;       (* arm_ADC X12 X12 X15 *)
  0xab10816b;       (* arm_ADDS X11 X11 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a10018c;       (* arm_ADC X12 X12 X16 *)
  0x9b067c8d;       (* arm_MUL X13 X4 X6 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab0c01ad;       (* arm_ADDS X13 X13 X12 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xeb0600a3;       (* arm_SUBS X3 X5 X6 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b037c8f;       (* arm_MUL X15 X4 X3 *)
  0x9bc37c83;       (* arm_UMULH X3 X4 X3 *)
  0xab0d016c;       (* arm_ADDS X12 X11 X13 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0c01ec;       (* arm_ADCS X12 X15 X12 *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xba0d006d;       (* arm_ADCS X13 X3 X13 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0xa940402f;       (* arm_LDP X15 X16 X1 (Immediate_Offset (iword (&0))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa940444f;       (* arm_LDP X15 X17 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060226;       (* arm_SBCS X6 X17 X6 *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca1100a5;       (* arm_EOR X5 X5 X17 *)
  0xeb1100a5;       (* arm_SUBS X5 X5 X17 *)
  0xca1100c6;       (* arm_EOR X6 X6 X17 *)
  0xda1100c6;       (* arm_SBC X6 X6 X17 *)
  0xca100230;       (* arm_EOR X16 X17 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c71;       (* arm_UMULH X17 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0051;       (* arm_ADDS X17 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba1100b1;       (* arm_ADCS X17 X5 X17 *)
  0xca0900c6;       (* arm_EOR X6 X6 X9 *)
  0xba0f00cf;       (* arm_ADCS X15 X6 X15 *)
  0x9a090021;       (* arm_ADC X1 X1 X9 *)
  0xab070169;       (* arm_ADDS X9 X11 X7 *)
  0xba08018a;       (* arm_ADCS X10 X12 X8 *)
  0xba0b01ab;       (* arm_ADCS X11 X13 X11 *)
  0xba0c01cc;       (* arm_ADCS X12 X14 X12 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca100042;       (* arm_EOR X2 X2 X16 *)
  0xba090049;       (* arm_ADCS X9 X2 X9 *)
  0xca100231;       (* arm_EOR X17 X17 X16 *)
  0xba0a022a;       (* arm_ADCS X10 X17 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9ba37d64;       (* arm_UMULL X4 W11 W3 *)
  0x8b274084;       (* arm_ADD X4 X4 (Extendedreg W7 UXTW) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0xd360fd6b;       (* arm_LSR X11 X11 32 *)
  0x9ba31d6b;       (* arm_UMADDL X11 W11 W3 X7 *)
  0xaa0403e7;       (* arm_MOV X7 X4 *)
  0x9ba37d84;       (* arm_UMULL X4 W12 W3 *)
  0x8b284084;       (* arm_ADD X4 X4 (Extendedreg W8 UXTW) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9ba3218c;       (* arm_UMADDL X12 W12 W3 X8 *)
  0xaa0403e8;       (* arm_MOV X8 X4 *)
  0x9ba37da4;       (* arm_UMULL X4 W13 W3 *)
  0x8b294084;       (* arm_ADD X4 X4 (Extendedreg W9 UXTW) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9ba325ad;       (* arm_UMADDL X13 W13 W3 X9 *)
  0xaa0403e9;       (* arm_MOV X9 X4 *)
  0x9ba37dc4;       (* arm_UMULL X4 W14 W3 *)
  0x8b2a4084;       (* arm_ADD X4 X4 (Extendedreg W10 UXTW) *)
  0xd360fd4a;       (* arm_LSR X10 X10 32 *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9ba329ce;       (* arm_UMADDL X14 W14 W3 X10 *)
  0xaa0403ea;       (* arm_MOV X10 X4 *)
  0xd35ffdd1;       (* arm_LSR X17 X14 31 *)
  0xd2800265;       (* arm_MOV X5 (rvalue (word 19)) *)
  0x9bb114a5;       (* arm_UMADDL X5 W5 W17 X5 *)
  0x8b0500e7;       (* arm_ADD X7 X7 X5 *)
  0xab0b80e7;       (* arm_ADDS X7 X7 (Shiftedreg X11 LSL 32) *)
  0x93cb8183;       (* arm_EXTR X3 X12 X11 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x93cc81a3;       (* arm_EXTR X3 X13 X12 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x93cd81c3;       (* arm_EXTR X3 X14 X13 32 *)
  0xd3410225;       (* arm_LSL X5 X17 63 *)
  0xca05014a;       (* arm_EOR X10 X10 X5 *)
  0x9a03014a;       (* arm_ADC X10 X10 X3 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0xf241015f;       (* arm_TST X10 (rvalue (word 9223372036854775808)) *)
  0x9a9f5063;       (* arm_CSEL X3 X3 XZR Condition_PL *)
  0xeb0300e7;       (* arm_SUBS X7 X7 X3 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0x9240f94a;       (* arm_AND X10 X10 (rvalue (word 9223372036854775807)) *)
  0xa9002007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9402c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&0))) *)
  0xa941344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&16))) *)
  0x9baa7d42;       (* arm_UMULL X2 W10 W10 *)
  0xd360fd4e;       (* arm_LSR X14 X10 32 *)
  0x9bae7dc3;       (* arm_UMULL X3 W14 W14 *)
  0x9bae7d4e;       (* arm_UMULL X14 W10 W14 *)
  0xab0e8442;       (* arm_ADDS X2 X2 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e0063;       (* arm_ADC X3 X3 X14 *)
  0x9bab7d64;       (* arm_UMULL X4 W11 W11 *)
  0xd360fd6e;       (* arm_LSR X14 X11 32 *)
  0x9bae7dc5;       (* arm_UMULL X5 W14 W14 *)
  0x9bae7d6e;       (* arm_UMULL X14 W11 W14 *)
  0x9b0b7d4f;       (* arm_MUL X15 X10 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0e8484;       (* arm_ADDS X4 X4 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e00a5;       (* arm_ADC X5 X5 X14 *)
  0xab0f01ef;       (* arm_ADDS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100084;       (* arm_ADCS X4 X4 X16 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9bac7d86;       (* arm_UMULL X6 W12 W12 *)
  0xd360fd8e;       (* arm_LSR X14 X12 32 *)
  0x9bae7dc7;       (* arm_UMULL X7 W14 W14 *)
  0x9bae7d8e;       (* arm_UMULL X14 W12 W14 *)
  0xab0e84c6;       (* arm_ADDS X6 X6 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e00e7;       (* arm_ADC X7 X7 X14 *)
  0x9bad7da8;       (* arm_UMULL X8 W13 W13 *)
  0xd360fdae;       (* arm_LSR X14 X13 32 *)
  0x9bae7dc9;       (* arm_UMULL X9 W14 W14 *)
  0x9bae7dae;       (* arm_UMULL X14 W13 W14 *)
  0x9b0d7d8f;       (* arm_MUL X15 X12 X13 *)
  0x9bcd7d90;       (* arm_UMULH X16 X12 X13 *)
  0xab0e8508;       (* arm_ADDS X8 X8 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e0129;       (* arm_ADC X9 X9 X14 *)
  0xab0f01ef;       (* arm_ADDS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xeb0c014a;       (* arm_SUBS X10 X10 X12 *)
  0xfa0d016b;       (* arm_SBCS X11 X11 X13 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xca10014a;       (* arm_EOR X10 X10 X16 *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xca10016b;       (* arm_EOR X11 X11 X16 *)
  0xda10016b;       (* arm_SBC X11 X11 X16 *)
  0xab0400c6;       (* arm_ADDS X6 X6 X4 *)
  0xba0500e7;       (* arm_ADCS X7 X7 X5 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0x9baa7d4c;       (* arm_UMULL X12 W10 W10 *)
  0xd360fd45;       (* arm_LSR X5 X10 32 *)
  0x9ba57cad;       (* arm_UMULL X13 W5 W5 *)
  0x9ba57d45;       (* arm_UMULL X5 W10 W5 *)
  0xab05858c;       (* arm_ADDS X12 X12 (Shiftedreg X5 LSL 33) *)
  0xd35ffca5;       (* arm_LSR X5 X5 31 *)
  0x9a0501ad;       (* arm_ADC X13 X13 X5 *)
  0x9bab7d6f;       (* arm_UMULL X15 W11 W11 *)
  0xd360fd65;       (* arm_LSR X5 X11 32 *)
  0x9ba57cae;       (* arm_UMULL X14 W5 W5 *)
  0x9ba57d65;       (* arm_UMULL X5 W11 W5 *)
  0x9b0b7d44;       (* arm_MUL X4 X10 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0585ef;       (* arm_ADDS X15 X15 (Shiftedreg X5 LSL 33) *)
  0xd35ffca5;       (* arm_LSR X5 X5 31 *)
  0x9a0501ce;       (* arm_ADC X14 X14 X5 *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0401ad;       (* arm_ADDS X13 X13 X4 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab060044;       (* arm_ADDS X4 X2 X6 *)
  0xba070065;       (* arm_ADCS X5 X3 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xba0900e7;       (* arm_ADCS X7 X7 X9 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xeb0c0084;       (* arm_SUBS X4 X4 X12 *)
  0xfa0d00a5;       (* arm_SBCS X5 X5 X13 *)
  0xfa0f00c6;       (* arm_SBCS X6 X6 X15 *)
  0xfa0e00e7;       (* arm_SBCS X7 X7 X14 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a100129;       (* arm_ADC X9 X9 X16 *)
  0xd28004ca;       (* arm_MOV X10 (rvalue (word 38)) *)
  0x9baa7ccc;       (* arm_UMULL X12 W6 W10 *)
  0x8b22418c;       (* arm_ADD X12 X12 (Extendedreg W2 UXTW) *)
  0xd360fc42;       (* arm_LSR X2 X2 32 *)
  0xd360fcc6;       (* arm_LSR X6 X6 32 *)
  0x9baa08c6;       (* arm_UMADDL X6 W6 W10 X2 *)
  0xaa0c03e2;       (* arm_MOV X2 X12 *)
  0x9baa7cec;       (* arm_UMULL X12 W7 W10 *)
  0x8b23418c;       (* arm_ADD X12 X12 (Extendedreg W3 UXTW) *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9baa0ce7;       (* arm_UMADDL X7 W7 W10 X3 *)
  0xaa0c03e3;       (* arm_MOV X3 X12 *)
  0x9baa7d0c;       (* arm_UMULL X12 W8 W10 *)
  0x8b24418c;       (* arm_ADD X12 X12 (Extendedreg W4 UXTW) *)
  0xd360fc84;       (* arm_LSR X4 X4 32 *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0x9baa1108;       (* arm_UMADDL X8 W8 W10 X4 *)
  0xaa0c03e4;       (* arm_MOV X4 X12 *)
  0x9baa7d2c;       (* arm_UMULL X12 W9 W10 *)
  0x8b25418c;       (* arm_ADD X12 X12 (Extendedreg W5 UXTW) *)
  0xd360fca5;       (* arm_LSR X5 X5 32 *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0x9baa1529;       (* arm_UMADDL X9 W9 W10 X5 *)
  0xaa0c03e5;       (* arm_MOV X5 X12 *)
  0xd35ffd2d;       (* arm_LSR X13 X9 31 *)
  0xd280026b;       (* arm_MOV X11 (rvalue (word 19)) *)
  0x9bad7d6b;       (* arm_UMULL X11 W11 W13 *)
  0x8b0b0042;       (* arm_ADD X2 X2 X11 *)
  0xab06804a;       (* arm_ADDS X10 X2 (Shiftedreg X6 LSL 32) *)
  0x93c680ec;       (* arm_EXTR X12 X7 X6 32 *)
  0xba0c006b;       (* arm_ADCS X11 X3 X12 *)
  0x93c7810c;       (* arm_EXTR X12 X8 X7 32 *)
  0xba0c008c;       (* arm_ADCS X12 X4 X12 *)
  0x93c8812e;       (* arm_EXTR X14 X9 X8 32 *)
  0xd34101af;       (* arm_LSL X15 X13 63 *)
  0xca0f00a5;       (* arm_EOR X5 X5 X15 *)
  0x9a0e00ad;       (* arm_ADC X13 X5 X14 *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fff021;       (* arm_BNE (word 2096644) *)
  0xb1004d46;       (* arm_ADDS X6 X10 (rvalue (word 19)) *)
  0xba1f0167;       (* arm_ADCS X7 X11 XZR *)
  0xba1f0188;       (* arm_ADCS X8 X12 XZR *)
  0xba1f01a9;       (* arm_ADCS X9 X13 XZR *)
  0x9a86514a;       (* arm_CSEL X10 X10 X6 Condition_PL *)
  0x9a87516b;       (* arm_CSEL X11 X11 X7 Condition_PL *)
  0x9a88518c;       (* arm_CSEL X12 X12 X8 Condition_PL *)
  0x9a8951ad;       (* arm_CSEL X13 X13 X9 Condition_PL *)
  0x9240f9ad;       (* arm_AND X13 X13 (rvalue (word 9223372036854775807)) *)
  0xa9002c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xa901340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQRT_P25519_EXEC = ARM_MK_EXEC_RULE bignum_sqrt_p25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Local subroutine correctness.                                             *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let lemma0 = prove
 (`!x0 x1:int64.
        &(val(if val x0 <= val x1 then word_sub x1 x0
         else word_neg(word_sub x1 x0))):real = abs(&(val x1) - &(val x0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[WORD_NEG_SUB; REAL_ARITH
   `abs(x - y):real = if y <= x then x - y else y - x`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES; NOT_LE]) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; LT_IMP_LE; REAL_OF_NUM_SUB]);;

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
 (`!p x0 x1 y0 y1:real.
    (x0 + p * x1) * (y0 + p * y1) =
    x0 * y0 + p pow 2 * x1 * y1 +
    p * (x0 * y0 + x1 * y1 +
         --(&1) pow bitval(y1 <= y0 <=> x1 < x0) *
         abs(x1 - x0) * abs(y0 - y1))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`y1:real <= y0`; `x1:real < x0`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ASM_REAL_ARITH_TAC);;

let VAL_WORD_MADDL_0 = prove
 (`!x y. val(word(0 + val(x:int32) * val(y:int32)):int64) = val x * val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; VAL_WORD_EQ_EQ] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[GSYM DIMINDEX_32; VAL_BOUND]);;

let DIVMOD_32_32 = prove
 (`!n. (2 EXP 32 * n) MOD 2 EXP 64 = 2 EXP 32 * n MOD 2 EXP 32`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

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

let DIVMOD_63_64 = prove
 (`!n. (2 EXP 63 * n) MOD 2 EXP 64 = 2 EXP 63 * n MOD 2`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let p25519redlemma32 = prove
 (`!h l. h < 2 EXP 256 /\ l < 2 EXP 256
         ==> let q = (38 * h DIV 2 EXP 224 + l DIV 2 EXP 224) DIV 2 EXP 31 in
             q <= 77 /\
             q < 2 EXP 64 /\
             (q + 1) * p_25519 <= (38 * h + l) + p_25519 /\
             38 * h + l < (q + 1) * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let endp25519redlemma = prove
 (`(&z == &2 pow 255 + x) (mod (&2 pow 256)) /\
   --(&p_25519) <= x /\ x < &p_25519 /\ z < 2 EXP 256
   ==> x rem &p_25519 =
       if z < 2 EXP 255 then &z - &19  else &z - &2 pow 255`,
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&z:int < &2 pow 255 <=> x:int < &0` SUBST1_TAC THENL
   [ALL_TAC;
   COND_CASES_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
    [EXISTS_TAC `--(&1):int`; EXISTS_TAC `&0:int`]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_IMP_EQ)) THEN
  REWRITE_TAC[p_25519] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p_25519]) THEN ASM_INT_ARITH_TAC);;

let KARATSUBA12_TAC =
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[lemma2; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ACCUMULATOR_POP_ASSUM_LIST(fun thl ->
    MP_TAC(end_itlist CONJ(rev thl)) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; GSYM NOT_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC(filter(is_ratconst o rand o concl) (DECARRY_RULE thl)) THEN
    REAL_INTEGER_TAC);;

let LOCAL_MUL_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x828) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_mc /\
                  read PC s = word(pc + 0x31c) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x5ec) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_25519)
         (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                     X13; X14; X15; X16; X17] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** Retrofitted insertion for the 32-bit fiddling (1 of 2) ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC [9;11;12;14] (1--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; VAL_WORD_USHR; VAL_WORD_SHL;
    DIVMOD_32_32; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s14:int64)) + &(val(sum_s12:int64)):real =
    &(val(x_0:int64)) * &(val(y_0:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `y_0:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`sum_s12:int64`,`mullo_s3:int64`) THEN
    SPEC_TAC(`sum_s14:int64`,`mulhi_s3:int64`) THEN
    SPEC_TAC(`s14:armstate`,`s4:armstate`) THEN REPEAT STRIP_TAC] THEN

  (*** First nested block multiplying the lower halves ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
   [5;10;11;15;17;18;19;22;24;25] (5--25) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = bignum_of_wordlist[mullo_s3;sum_s22]`;
    `q1 = bignum_of_wordlist[sum_s24;sum_s25]`] THEN
  SUBGOAL_THEN
   `2 EXP 128 * q1 + q0 =
    bignum_of_wordlist [x_0;x_1] * bignum_of_wordlist[y_0;y_1]`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q0"; "q1"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Retrofitted insertion for the 32-bit fiddling (2 of 2) ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC [34;36;37;39] (26--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; VAL_WORD_USHR; VAL_WORD_SHL;
    DIVMOD_32_32; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s39:int64)) + &(val(sum_s37:int64)):real =
    &(val(x_2:int64)) * &(val(y_2:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_2:int64`; `y_2:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`sum_s37:int64`,`mullo_s28:int64`) THEN
    SPEC_TAC(`sum_s39:int64`,`mulhi_s28:int64`) THEN
    SPEC_TAC(`s39:armstate`,`s29:armstate`) THEN REPEAT STRIP_TAC] THEN

  (*** Second nested block multiplying the upper halves ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
   [30;35;36;40;42;43;44;47;49;50] (30--50) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN

  ABBREV_TAC
   `q23 = bignum_of_wordlist[mullo_s28;sum_s47; sum_s49;sum_s50]` THEN
  SUBGOAL_THEN
   `q23 = bignum_of_wordlist [x_2;x_3] * bignum_of_wordlist[y_2;y_3]`
  ASSUME_TAC THENL
   [EXPAND_TAC "q23" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The sign-magnitude difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
    [53;54; 57;58; 61;63; 65;67] (51--68) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN

  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s58 <=> carry_s54)`;
   `xd = bignum_of_wordlist[sum_s61;sum_s63]`;
   `yd = bignum_of_wordlist[sum_s65;sum_s67]`] THEN
  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_2;x_3]) -
     &(bignum_of_wordlist[x_0;x_1])) *
    (&(bignum_of_wordlist[y_0;y_1]) -
     &(bignum_of_wordlist[y_2;y_3])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s54 * &xd) *
      (--(&1) pow bitval carry_s58 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s54 <=>
       bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1]) /\
      (carry_s58 <=>
       bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])`
     (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    BINOP_TAC THEN REWRITE_TAC[bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = --(&1) pow 1 * z <=> y - x = z`] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Clean up the overall sign ***)

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_XOR_MASKS]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** The augmented H' = H + L_top ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (69--72) (69--72) THEN
  MAP_EVERY ABBREV_TAC
   [`q2 = bignum_of_wordlist[sum_s69;sum_s70]`;
    `q3 = bignum_of_wordlist[sum_s71;sum_s72]`] THEN
  SUBGOAL_THEN
   `2 EXP 128 * q3 + q2 =
    bignum_of_wordlist [x_2;x_3] * bignum_of_wordlist[y_2;y_3] + q1`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "q2"; "q3"] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    REPEAT(CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o LAND_CONV) [SYM th]) THEN
    MAP_EVERY EXPAND_TAC ["q23"] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Third nested block multiplying the absolute differences ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
   [73;75;80;81;85;87;88;89;92;94;95] (73--95) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN
  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist[mullo_s73; sum_s92; sum_s94; sum_s95])`
  SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The rest of the basic 4x4->8 multiply computation and its proof ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
   [96;97;98;99;100;101;104;106;108;110;111;112] (96--112) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s22; sum_s104; sum_s106]`;
    `h = bignum_of_wordlist[sum_s108; sum_s110; sum_s111; sum_s112]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [DISCARD_STATE_TAC "s112" THEN MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    SUBGOAL_THEN
     `&m * &n:real =
      (&1 + &2 pow 128) * (&q0 + &2 pow 128 * &q2 + &2 pow 256 * &q3) +
      &2 pow 128 *
      (&(bignum_of_wordlist [x_2; x_3]) -
       &(bignum_of_wordlist [x_0; x_1])) *
      (&(bignum_of_wordlist [y_0; y_1]) -
       &(bignum_of_wordlist [y_2; y_3]))`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`2 EXP 128 * q1 + q0 =
         bignum_of_wordlist[x_0; x_1] * bignum_of_wordlist[y_0; y_1]`;
        `2 EXP 128 * q3 + q2 =
         bignum_of_wordlist[x_2; x_3] * bignum_of_wordlist[y_2; y_3] +
         q1`] THEN
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[]] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"; "q0"; "q2"; "q3"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPECL [`h:num`; `l:num`] p25519redlemma32) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    LET_TAC THEN STRIP_TAC] THEN

  (*** The somewhat fiddly reduction with 32-bit operations etc. ***)

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (113--137) THEN

  MAP_EVERY (fun t -> REABBREV_TAC t THEN POP_ASSUM MP_TAC)
   [`u0 = read X7 s137`;
    `u1 = read X8 s137`;
    `u2 = read X9 s137`;
    `u3 = read X10 s137`;
    `u4 = read X11 s137`;
    `u5 = read X12 s137`;
    `u6 = read X13 s137`;
    `u7 = read X14 s137`] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [word_add; modular; ADD_CLAUSES; VAL_WORD; VAL_WORD_ZX_GEN;
    VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
   `n < 2 EXP 64 ==> n MOD 2 EXP 32 * 38 < 2 EXP 64`] THEN
  STRIP_TAC THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC [142;144;146;150] (138--150) THEN
  SUBGOAL_THEN `word_ushr u7 31:int64 = word q` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_USHR] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT] THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s106:int64) DIV 2 EXP 32 +
           val(sum_s112:int64) DIV 2 EXP 32 * 38):int64 = u7`)) THEN
    MAP_EVERY EXPAND_TAC ["q"; "l"; "h"] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD; ARITH_RULE `a + b * 38 = 38 * b + a`] THEN
    MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN
    REWRITE_TAC[GSYM VAL_WORD_USHR] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_add (u0:int64)
       (word(19 + 19 * val((word_zx:int64->int32)(word q)))))):real =
    &(val u0) + &19 * (&q + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; VAL_WORD; VAL_WORD_ZX_GEN;
                DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[ARITH_RULE `q <= 77 ==> q < 2 EXP MIN 64 32`; MOD_LT] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `19 + 19 * q = 19 * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s108:int64) MOD 2 EXP 32 * 38 +
           val(mullo_s3:int64) MOD 2 EXP 32):int64 = u0`)) THEN
    MATCH_MP_TAC(ARITH_RULE
     `w <= 2 EXP 63 /\ q <= 77 ==> w + 19 * (q + 1) < 2 EXP 64`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_LE; FIRST_ASSUM ACCEPT_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  REWRITE_TAC[REAL_VAL_WORD_XOR; WORD_AND_POW2_BITVAL;
              REWRITE_RULE[DIMINDEX_64; NUM_REDUCE_CONV `64 - 1`]
                (ISPEC `x:int64` WORD_SHL_LSB)] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIVMOD_63_64] THEN
  SIMP_TAC[MOD_LT; BITVAL_BOUND_ALT; GSYM REAL_OF_NUM_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM VAL_MOD_2; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `r = bignum_of_wordlist[sum_s142; sum_s144; sum_s146; sum_s150]` THEN

  SUBGOAL_THEN
   `(&r:int == &2 pow 255 + &(38 * h + l) - (&q + &1) * &p_25519)
    (mod (&2 pow 256))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `38 * h + l =
      bignum_of_wordlist[u0;u1;u2;u3] +
      2 EXP 32 * bignum_of_wordlist[u4;u5;u6;u7]`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (can (term_match [] `word x = n`) o concl))) THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD; DIMINDEX_64] THEN
      SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
        `m < 2 EXP 64 /\ n < 2 EXP 64
         ==> m DIV 2 EXP 32 + n DIV 2 EXP 32 * 38 < 2 EXP 64`;
        ARITH_RULE `m MOD 2 EXP 32 * 38 + n MOD 2 EXP 32 < 2 EXP 64`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 32 * bignum_of_wordlist [u4; u5; u6; u7] =
      bignum_of_wordlist
       [word_shl u4 32;
        word_subword ((word_join:int64->int64->int128) u5 u4) (32,64);
        word_subword ((word_join:int64->int64->int128) u6 u5) (32,64);
        word_subword ((word_join:int64->int64->int128) u7 u6) (32,64);
        word_ushr u7 32]`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
                int_mul_th; int_pow_th] THEN
    EXPAND_TAC "r" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final optional correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (154--157) (151--160) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`255`;
    `(if r < 2 EXP 255 then &r - &19 else &r - &2 pow 255):real`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s160" THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `r < 2 EXP 255 <=> r DIV 2 EXP 192 < 2 EXP 63`] THEN
    EXPAND_TAC "r" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
    ABBREV_TAC `bb <=> val(sum_s150:int64) < 2 EXP 63` THEN
    SUBGOAL_THEN
     `ival(word_and sum_s150 (word 9223372036854775808):int64) < &0 <=> ~bb`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM MSB_IVAL; BIT_WORD_AND] THEN
      REWRITE_TAC[MSB_VAL] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "bb" THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        endp25519redlemma)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_ARITH `--p:int <= x - y <=> y <= x + p`] THEN
      REWRITE_TAC[INT_ARITH `x - y:int < p <=> x < y + p`] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "r" THEN BOUNDER_TAC[];
      REWRITE_TAC[INT_ARITH `x - q * p:int = --q * p + x`] THEN
      REWRITE_TAC[INT_REM_MUL_ADD] THEN
      REWRITE_TAC[int_eq; int_of_num_th; INT_OF_NUM_REM] THEN
      DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[int_of_num_th; int_sub_th; int_pow_th]]]);;

let LOCAL_MUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (bignum_sqrt_p25519_mc,BIGNUM_SQRT_P25519_EXEC,
    0x0,bignum_sqrt_p25519_mc,LOCAL_MUL_P25519_CORRECT)
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s`;
   `pc:num`];;

let LOCAL_NSQR_P25519_CORRECT = time prove
 (`!z k x n pc.
        nonoverlapping (word pc,0x828) (z,8 * 4) /\
        1 <= val k /\ val k <= 1000
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_mc /\
                  read PC s = word(pc + 0x5f0) /\
                  C_ARGUMENTS [z; k; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x824) /\
                  bignum_from_memory (z,4) s =
                  (n EXP (2 EXP val k)) MOD p_25519)
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Top-level squaring loop ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x5f8` `pc + 0x7f4`
   `\i s. (read X0 s = z /\
           read X1 s = word(k - i) /\
           (bignum_of_wordlist
             [read X10 s; read X11 s; read X12 s; read X13 s] ==
            n EXP (2 EXP i)) (mod p_25519) /\
           (1 <= i
            ==> bignum_of_wordlist
                 [read X10 s; read X11 s; read X12 s; read X13 s]
                < 2 * p_25519)) /\
          (read ZF s <=> i = k)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LE_1];

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (x,8 * 4)) s0` THEN
    ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP; EXP_1; CONG_REFL; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV;

    ALL_TAC; (*** Main loop invariant ***)

    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_SQRT_P25519_EXEC [1];

    GHOST_INTRO_TAC `x_0:int64` `read X10` THEN
    GHOST_INTRO_TAC `x_1:int64` `read X11` THEN
    GHOST_INTRO_TAC `x_2:int64` `read X12` THEN
    GHOST_INTRO_TAC `x_3:int64` `read X13` THEN
    ASM_REWRITE_TAC[] THEN
    ARM_ACCSIM_TAC BIGNUM_SQRT_P25519_EXEC (2--5) (1--12) THEN
    CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s12" THEN
    REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    ABBREV_TAC `m = bignum_of_wordlist [x_0; x_1; x_2; x_3]` THEN
    MAP_EVERY EXISTS_TAC
     [`255`;
      `if m < p_25519 then &m:real else &m - &p_25519`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ALL_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I [CONG]) THEN
      ASM_SIMP_TAC[MOD_CASES] THEN
      SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT] THEN MESON_TAC[]] THEN
    REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [REAL_OF_NUM_ADD]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    REWRITE_TAC[MOD_MULT_ADD; VAL_WORD_ADD; VAL_WORD] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_MOD_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `(m < p_25519 <=> m + 19 < 2 EXP 255) /\
      (&m - &p_25519:real = &(m + 19) - &2 pow 255)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 256 * bitval carry_s5 +
      bignum_of_wordlist [sum_s2; sum_s3; sum_s4; sum_s5] = m + 19`
    MP_TAC THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `2 EXP 256 * c + s = mm
      ==> mm < 2 EXP 256 /\ (2 EXP 256 * c < 2 EXP 256 * 1 ==> c = 0)
          ==> mm = s`)) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `m < 2 * p_25519` THEN
      REWRITE_TAC[p_25519; LT_MULT_LCANCEL] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[NOT_LE; ARITH_RULE
     `x < 2 EXP 255 <=> x DIV 2 EXP 192 < 2 EXP 63`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    REAL_INTEGER_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `n_0:int64` `read X10` THEN
  GHOST_INTRO_TAC `n_1:int64` `read X11` THEN
  GHOST_INTRO_TAC `n_2:int64` `read X12` THEN
  GHOST_INTRO_TAC `n_3:int64` `read X13` THEN
  REWRITE_TAC[EXP_ADD; GSYM EXP_EXP; EXP_1] THEN
  SPEC_TAC(`n EXP (2 EXP i)`,`n':num`) THEN GEN_TAC THEN
  ABBREV_TAC `n = bignum_of_wordlist [n_0; n_1; n_2; n_3]` THEN

  (*** Start at s2 for straight copy of proof with initial loads ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s2" THEN
  FIRST_ASSUM(fun th ->
   REWRITE_TAC[MATCH_MP
    (NUMBER_RULE `!n a p. (n == a) (mod p)
                  ==> !x. (x == a EXP 2) (mod p) <=>
                          (x == n EXP 2) (mod p)`) th]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `n':num` o concl))) THEN


  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)
  (*** First of all, squaring the lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
   [7;9;14;16;18;19;20;21;22;23;24] (3--24) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_0; n_1] EXP 2 =
    bignum_of_wordlist[sum_s7; sum_s22; sum_s23; sum_s24]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`n_0:int64`; `n_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Squaring the upper half ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
   [29;31;36;38;40;41;42;43;44;45;46] (25--46) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_2; n_3] EXP 2 =
    bignum_of_wordlist[sum_s29; sum_s44; sum_s45; sum_s46]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`n_2:int64`; `n_3:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC [47;48;51;53] (47--53) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; WORD_UNMASK_64]) THEN
  SUBGOAL_THEN
   `abs(&(bignum_of_wordlist[n_0;n_1]) -
        &(bignum_of_wordlist[n_2;n_3])):real =
    &(bignum_of_wordlist[sum_s51;sum_s53])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_abs; REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN
     `bignum_of_wordlist [n_2; n_3] <= bignum_of_wordlist [n_0; n_1] <=>
      ~carry_s48`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
      EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      REWRITE_TAC[COND_SWAP] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
      REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; VAL_WORD_BITVAL] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The augmented H' = H + L_top computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (54--57) (54--57) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s29; sum_s44; sum_s45; sum_s46]):real =
    &(bignum_of_wordlist[sum_s54; sum_s55; sum_s56; sum_s57]) -
    &(bignum_of_wordlist[sum_s23; sum_s24])`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
     (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
        MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Squaring the absolute difference ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
   [62;64;69;71;73;74;75;76;77;78;79] (58--79) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[sum_s51;sum_s53] EXP 2 =
    bignum_of_wordlist[sum_s62; sum_s77; sum_s78; sum_s79]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`sum_s51:int64`; `sum_s53:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The overall Karatsuba composition to get the full square ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC (80--90) (80--90) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
    [COND_SWAP; WORD_UNMASK_64; REAL_BITVAL_NOT; DIMINDEX_64;
     GSYM WORD_NOT_MASK; REAL_VAL_WORD_NOT;REAL_VAL_WORD_MASK]) THEN

  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[sum_s7; sum_s22; sum_s85; sum_s86]`;
    `h = bignum_of_wordlist[sum_s87; sum_s88; sum_s89; sum_s90]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(2,2)] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_ARITH
     `(l + &2 pow 128 * h) pow 2 =
      &2 pow 256 * h pow 2 + l pow 2 +
      &2 pow 128 * (h pow 2 + l pow 2 - (l - h) pow 2)`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPECL [`h:num`; `l:num`] p25519redlemma32) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    LET_TAC THEN STRIP_TAC] THEN

  (*** The somewhat fiddly reduction with 32-bit operations etc. ***)

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (91--115) THEN
  MAP_EVERY (fun t -> REABBREV_TAC t THEN POP_ASSUM MP_TAC)
   [`u0 = read X2 s115`;
    `u1 = read X3 s115`;
    `u2 = read X4 s115`;
    `u3 = read X5 s115`;
    `u4 = read X6 s115`;
    `u5 = read X7 s115`;
    `u6 = read X8 s115`;
    `u7 = read X9 s115`] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [word_add; modular; ADD_CLAUSES; VAL_WORD; VAL_WORD_ZX_GEN;
    VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
   `n < 2 EXP 64 ==> n MOD 2 EXP 32 * 38 < 2 EXP 64`] THEN
  STRIP_TAC THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC [120;122;124;128] (116--129) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
    DISCH_THEN SUBST1_TAC] THEN
  VAL_INT64_TAC `k - (i + 1)` THEN
  ASM_SIMP_TAC[SUB_EQ_0; ARITH_RULE
   `i < k ==> (k <= i + 1 <=> i + 1 = k)`] THEN
  REWRITE_TAC[ARITH_RULE `1 <= i + 1`] THEN

  SUBGOAL_THEN `word_ushr u7 31:int64 = word q` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_USHR] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT] THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s86:int64) DIV 2 EXP 32 +
           val(sum_s90:int64) DIV 2 EXP 32 * 38):int64 = u7`)) THEN
    MAP_EVERY EXPAND_TAC ["q"; "l"; "h"] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD; ARITH_RULE `a + b * 38 = 38 * b + a`] THEN
    MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN
    REWRITE_TAC[GSYM VAL_WORD_USHR] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_add (u0:int64)
       (word(0 + 19 * val((word_zx:int64->int32)(word q)))))):real =
    &(val u0) + &19 * &q`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; VAL_WORD; VAL_WORD_ZX_GEN;
                DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `q <= 77 ==> q < 2 EXP MIN 64 32`; MOD_LT] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    MATCH_MP_TAC MOD_LT THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s87:int64) MOD 2 EXP 32 * 38 +
           val(sum_s7:int64) MOD 2 EXP 32):int64 = u0`)) THEN
    MATCH_MP_TAC(ARITH_RULE
     `w <= 2 EXP 63 /\ q <= 77 ==> w + 19 * q < 2 EXP 64`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_LE; FIRST_ASSUM ACCEPT_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  REWRITE_TAC[REAL_VAL_WORD_XOR; WORD_AND_POW2_BITVAL;
              REWRITE_RULE[DIMINDEX_64; NUM_REDUCE_CONV `64 - 1`]
                (ISPEC `x:int64` WORD_SHL_LSB)] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIVMOD_63_64] THEN
  SIMP_TAC[MOD_LT; BITVAL_BOUND_ALT; GSYM REAL_OF_NUM_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM VAL_MOD_2; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  STRIP_TAC THEN

  REWRITE_TAC[GSYM CONG; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\
        (&0 <= ca - q * p /\ ca - q * p < p2) /\
        (&0 <= ca - q * p /\ ca - q * p < p2 ==> x = ca - q * p)
        ==> (x == ca) (mod p) /\ x:int < p2`) THEN
  EXISTS_TAC `&q:int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(q + 1) * p_25519 <= (38 * h + l) + p_25519`;
      `38 * h + l < (q + 1) * p_25519 + p_25519`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    STRIP_TAC] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  SUBGOAL_THEN
   `38 * h + l =
    bignum_of_wordlist[u0;u1;u2;u3] +
    2 EXP 32 * bignum_of_wordlist[u4;u5;u6;u7]`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (can (term_match [] `word x = n`) o concl))) THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
      `m < 2 EXP 64 /\ n < 2 EXP 64
       ==> m DIV 2 EXP 32 + n DIV 2 EXP 32 * 38 < 2 EXP 64`;
      ARITH_RULE `m MOD 2 EXP 32 * 38 + n MOD 2 EXP 32 < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 32 * bignum_of_wordlist [u4; u5; u6; u7] =
    bignum_of_wordlist
     [word_shl u4 32;
      word_subword ((word_join:int64->int64->int128) u5 u4) (32,64);
      word_subword ((word_join:int64->int64->int128) u6 u5) (32,64);
      word_subword ((word_join:int64->int64->int128) u7 u6) (32,64);
      word_ushr u7 32]`
  SUBST1_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
              int_mul_th; int_pow_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_NSQR_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (bignum_sqrt_p25519_mc,BIGNUM_SQRT_P25519_EXEC,
    0x0,bignum_sqrt_p25519_mc,LOCAL_NSQR_P25519_CORRECT)
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s`;
   `pc:num`];;

(* ------------------------------------------------------------------------- *)
(* Finding modular square roots in this setting.                             *)
(* ------------------------------------------------------------------------- *)

let MODULAR_SQRT_5MOD8 = prove
 (`!p a i.
        prime p /\ (p == 5) (mod 8) /\ (i EXP 2 + 1 == 0) (mod p)
        ==> let y = a EXP ((p + 3) DIV 8) in
            ((?x. (x EXP 2 == a) (mod p)) <=>
             (y EXP 2 == a) (mod p) \/ ((i * y) EXP 2 == a) (mod p))`,
  REPEAT STRIP_TAC THEN CONV_TAC let_CONV THEN
  EQ_TAC THENL [DISCH_TAC; MESON_TAC[]] THEN
  ASM_SIMP_TAC[NUMBER_RULE
   `(i EXP 2 + 1 == 0) (mod p)
    ==> (((i * y) EXP 2 == a) (mod p) <=> (y EXP 2 + a == 0) (mod p))`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INT_CONG; INT_SUB_RZERO] THEN
  ASM_SIMP_TAC[GSYM PRIME_INT_DIVPROD_EQ] THEN
  REWRITE_TAC[INTEGER_RULE
   `(p:int) divides ((x - a) * (x + a)) <=> (x pow 2 == a pow 2) (mod p)`] THEN
  REWRITE_TAC[INT_POW_POW] THEN
  SUBGOAL_THEN `(p + 3) DIV 8 * 2 * 2 = 2 + (p - 1) DIV 2` SUBST1_TAC THENL
   [UNDISCH_TAC `(p == 5) (mod 8)` THEN ASM_SIMP_TAC[CONG_CASE; ARITH] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ARITH_RULE `(q * 8 + 5) + 3 = 8 * (q + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `(q * 8 + 5) - 1 = 2 * (q * 4 + 2)`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC;
    REWRITE_TAC[INT_POW_ADD]] THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  MP_TAC(SPECL [`p:num`; `a:num`] EULER_CRITERION) THEN
  ASM_REWRITE_TAC[] THEN NUMBER_TAC);;

let MODULAR_I_5MOD8 = prove
 (`!p. prime p /\ (p == 5) (mod 8)
       ==> ((2 EXP ((p - 1) DIV 4)) EXP 2 + 1 == 0) (mod p)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[CONG] THEN ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[EXP_EXP] THEN
  SUBGOAL_THEN `(p - 1) DIV 4 * 2 = (p - 1) DIV 2` SUBST1_TAC THENL
   [UNDISCH_TAC `(p == 5) (mod 8)` THEN ASM_SIMP_TAC[CONG_CASE; ARITH] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ARITH_RULE `(q * 8 + 5) - 1 = 2 * 2 * (2 * q + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `x DIV 4 = x DIV 2 DIV 2`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!x:int. (x == a) (mod p) /\ (x == --b) (mod p)
            ==> (a + b == &0) (mod p)`) THEN
  EXISTS_TAC `jacobi(2,p)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[JACOBI_EULER_ALT]; ALL_TAC] THEN
  MP_TAC(SPEC `p:num` JACOBI_OF_2_CASES) THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_ODD; NOT_ODD]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONG]) THEN
  ASM_REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INTEGER_RULE);;

let MODULAR_SQRT_5MOD8_EXPLICIT = prove
 (`!p a.
        prime p /\ (p == 5) (mod 8)
        ==> let i = 2 EXP ((p - 1) DIV 4) in
            let y = a EXP ((p + 3) DIV 8) in
            ((?x. (x EXP 2 == a) (mod p)) <=>
             (y EXP 2 == a) (mod p) \/ ((i * y) EXP 2 == a) (mod p))`,
  REPEAT STRIP_TAC THEN CONV_TAC let_CONV THEN
  MATCH_MP_TAC MODULAR_SQRT_5MOD8 THEN ASM_SIMP_TAC[MODULAR_I_5MOD8]);;

let P_25519 = prove
 (`p_25519 = 2 EXP 255 - 19`,
  REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let PRIME_P25519 = prove
 (`prime p_25519`,
  REWRITE_TAC[p_25519] THEN (CONV_TAC o PRIME_RULE)
   ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
    "43"; "47"; "53"; "59"; "83"; "97"; "103"; "107"; "127"; "131"; "173";
    "223"; "239"; "353"; "419"; "479"; "487"; "991"; "1723"; "2437"; "3727";
    "4153"; "9463"; "32573"; "37853"; "57467"; "65147"; "75707"; "132049";
    "430751"; "569003"; "1923133"; "8574133"; "2773320623"; "72106336199";
    "1919519569386763"; "31757755568855353";
    "75445702479781427272750846543864801";
    "74058212732561358302231226437062788676166966415465897661863160754340907";
"57896044618658097711785492504343953926634992332820282019728792003956564819949"
]);;

let j_25519 = define
 `j_25519 =
19681161376707505956807079304988542015446066515923890162744021073123829784752`;;

let MODULAR_SQRT_P25519 = prove
 (`!a. let y = (a EXP (2 EXP 252 - 2)) MOD p_25519 in
       (?x. (x EXP 2 == a) (mod p_25519)) <=>
       (y EXP 2 == a) (mod p_25519) \/
       ((j_25519 * y) EXP 2 == a) (mod p_25519)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`p_25519`; `a:num`; `j_25519`] MODULAR_SQRT_5MOD8) THEN
  REWRITE_TAC[PRIME_P25519] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  SUBGOAL_THEN `(p_25519 + 3) DIV 8 = 2 EXP 252 - 2` SUBST1_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC] THEN
  REWRITE_TAC[p_25519; j_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Overall proof.                                                            *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SQRT_P25519_CORRECT = time prove
 (`!z x n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,128))
            [(word pc,0x828); (z,8 * 4); (x,8 * 4)] /\
        nonoverlapping (word pc,0x828) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_mc /\
                  read PC s = word(pc + 0x8) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x310) /\
                  ival(C_RETURN s) = jacobi(n,p_25519) /\
                  bignum_from_memory (z,4) s < p_25519 /\
                  EVEN(bignum_from_memory (z,4) s) /\
                  (jacobi(n,p_25519) >= &0
                   ==> (bignum_from_memory (z,4) s EXP 2 == n) (mod p_25519)))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                         X11; X12; X13; X14; X15; X16; X17; X19; X30] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(stackpointer,128)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initial modular reduction, trivial tweak of bignum_mod_p25519_4 ***)

  ENSURES_SEQUENCE_TAC `pc + 0x54`
   `\s. read SP s = stackpointer /\
        read X19 s = z /\
        bignum_from_memory(stackpointer,4) s = n MOD p_25519` THEN
  CONJ_TAC THENL
   [BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN
    ABBREV_TAC `b <=> bit 63 (n_3:int64)` THEN
    SUBGOAL_THEN
     `val(n_3:int64) DIV 2 EXP 63 = bitval b /\
      n DIV 2 EXP 255 = bitval b`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      EXPAND_TAC "b" THEN REWRITE_TAC[BIT_VAL] THEN
      SUBGOAL_THEN `val(n_3:int64) DIV 2 EXP 63 < 2` MP_TAC THENL
       [MP_TAC(SPEC `n_3:int64` VAL_BOUND_64) THEN ARITH_TAC;
        SPEC_TAC(`val(n_3:int64) DIV 2 EXP 63`,`bb:num`)] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ARITH; BITVAL_CLAUSES];
      ALL_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC
     [7;8;9;11;13;14;15;16] (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&(val(word(19 + 19 * val(word_ushr (n_3:int64) 63)):int64)):real =
      &19 * (&1 + &(bitval b))`
    SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; DIMINDEX_64] THEN
      MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_or n_3 (word 9223372036854775808):int64)):real =
      &(val n_3) + &2 pow 63 * (&1 - &(bitval b))`
    SUBST_ALL_TAC THENL
     [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
       `word_or x m = word_or (word_and x (word_not m)) m`] THEN
      SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
       `word_and (word_and x (word_not m)) m = word 0`] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s19" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`255`;
      `if n < (bitval b + 1) * p_25519
       then &n - &(bitval b) * &p_25519
       else &n - (&(bitval b) + &1) * &p_25519:real`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ALL_TAC;
      ASM_SIMP_TAC[REAL_OF_NUM_MOD; EQT_ELIM
       ((REWRITE_CONV[p_25519] THENC (EQT_INTRO o ARITH_RULE))
        `n < 2 EXP (64 * 4)
         ==> n DIV p_25519 =
             if n < (n DIV 2 EXP 255 + 1) * p_25519
             then n DIV 2 EXP 255 else n DIV 2 EXP 255 + 1`)] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES]] THEN
    SUBGOAL_THEN `n < (bitval b + 1) * p_25519 <=> ~carry_s11` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
      EXISTS_TAC `256` THEN
      EXPAND_TAC "n" THEN REWRITE_TAC[p_25519; bignum_of_wordlist] THEN
      REWRITE_TAC[REAL_BITVAL_NOT; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      EXPAND_TAC "n" THEN REWRITE_TAC[COND_SWAP; bignum_of_wordlist] THEN
      REWRITE_TAC[p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_CASES_TAC `carry_s11:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REAL_INTEGER_TAC];
    ONCE_REWRITE_TAC[GSYM CONG_RMOD; GSYM JACOBI_MOD] THEN
    SUBGOAL_THEN `n MOD p_25519 < p_25519` MP_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ; p_25519; ARITH_EQ]; ALL_TAC] THEN
    SPEC_TAC(`n MOD p_25519`,`n:num`) THEN REPEAT STRIP_TAC] THEN

  (*** The big exponentiation tower ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (1--4) THEN LOCAL_NSQR_TAC 5 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (6--10) THEN LOCAL_MUL_TAC 11 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (12--16) THEN LOCAL_NSQR_TAC 17 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (18--22) THEN LOCAL_MUL_TAC 23 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (24--28) THEN LOCAL_NSQR_TAC 29 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (30--34) THEN LOCAL_MUL_TAC 35 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (36--40) THEN LOCAL_NSQR_TAC 41 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (42--46) THEN LOCAL_MUL_TAC 47 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (48--52) THEN LOCAL_NSQR_TAC 53 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (54--58) THEN LOCAL_MUL_TAC 59 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (60--64) THEN LOCAL_NSQR_TAC 65 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (66--70) THEN LOCAL_MUL_TAC 71 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (72--76) THEN LOCAL_NSQR_TAC 77 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (78--82) THEN LOCAL_MUL_TAC 83 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (84--88) THEN LOCAL_NSQR_TAC 89 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (90--94) THEN LOCAL_MUL_TAC 95 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (96--100) THEN LOCAL_NSQR_TAC 101 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (102--106) THEN LOCAL_MUL_TAC 107 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (108--112) THEN LOCAL_NSQR_TAC 113 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (114--118) THEN LOCAL_MUL_TAC 119 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (120--124) THEN LOCAL_NSQR_TAC 125 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (126--130) THEN LOCAL_MUL_TAC 131 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (132--136) THEN LOCAL_NSQR_TAC 137 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC [138] THEN
  REABBREV_TAC
   `c =
    read (memory :> bytes (word_add stackpointer (word 64),8 * 4)) s138` THEN
  POP_ASSUM(MP_TAC o CONV_RULE MOD_DOWN_CONV) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
  REWRITE_TAC[MULT_EXP] THEN REWRITE_TAC[EXP_EXP] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  DISCH_TAC THEN

  (*** Multiplication by j_25519 ***)

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (139--160) THEN
  SUBGOAL_THEN
    `read (memory :> bytes(word_add stackpointer (word 96),8 * 4)) s160 =
     j_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; j_25519] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_TAC 161 THEN

  (*** Squaring of s ***)

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (162--166) THEN
  LOCAL_NSQR_TAC 167 THEN

  (*** Comparison and multiplexing ***)

  BIGNUM_LDIGITIZE_TAC "a_"
   `read (memory :> bytes (stackpointer,8 * 4)) s167` THEN
  BIGNUM_LDIGITIZE_TAC "b_"
   `read (memory :> bytes (word_add stackpointer (word 32),8 * 4)) s167` THEN
  BIGNUM_LDIGITIZE_TAC "c_"
   `read (memory :> bytes (word_add stackpointer (word 64),8 * 4)) s167` THEN
  BIGNUM_LDIGITIZE_TAC "d_"
   `read (memory :> bytes (word_add stackpointer (word 96),8 * 4)) s167` THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (168--188) THEN
  MAP_EVERY ABBREV_TAC
   [`e_0 = read X10 s188`; `e_1 = read X11 s188`;
    `e_2 = read X12 s188`; `e_3 = read X13 s188`] THEN
  ABBREV_TAC `e = bignum_of_wordlist[e_0; e_1; e_2; e_3]` THEN

  SUBGOAL_THEN
   `e < p_25519 /\
    ((?x. (x EXP 2 == n) (mod p_25519)) <=> (e EXP 2 == n) (mod p_25519))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `e = if (c EXP 2 == n) (mod p_25519) then c
          else (c * j_25519) MOD p_25519`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; WORD_OR_EQ_0] THEN
      REWRITE_TAC[WORD_XOR_EQ_0; GSYM CONJ_ASSOC] THEN
      SUBGOAL_THEN
       `a_0:int64 = b_0 /\ a_1:int64 = b_1 /\
        a_2:int64 = b_2 /\ a_3:int64 = b_3 <=>
        (c EXP 2 == n) (mod p_25519)`
      SUBST1_TAC THENL
       [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[]] THEN
      TRANS_TAC EQ_TRANS
       `bignum_of_wordlist [a_0; a_1; a_2; a_3] =
        bignum_of_wordlist [b_0; b_1; b_2; b_3]` THEN
      CONJ_TAC THENL [REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CONG; MOD_LT] THEN
      REWRITE_TAC[VAL_WORD_1; EXP_1] THEN MESON_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 252 - 2`)]) THEN
    CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `n EXP (2 EXP 252 - 2) MOD p_25519 = c`)) THEN
      COND_CASES_TAC THEN REWRITE_TAC[MOD_LT_EQ; p_25519] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `n:num` MODULAR_SQRT_P25519) THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(c EXP 2 == n) (mod p_25519)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CONG; MULT_SYM] THEN CONV_TAC MOD_DOWN_CONV THEN
    REFL_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`p = if x then y else z`]] THEN

  (*** Negation to zero the LSB ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_EXEC [190;192;194;195] (189--203) THEN
  ABBREV_TAC `f = read (memory :> bytes (z,8 * 4)) s203` THEN
  SUBGOAL_THEN `(if EVEN e then e else p_25519 - e) = f` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "e" THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV o RAND_CONV)
     [bignum_of_wordlist] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; EVEN_EXP; ARITH] THEN
    REWRITE_TAC[WORD_AND_1_BITVAL; VAL_WORD_BITVAL] THEN
    REWRITE_TAC[BITVAL_EQ_0; BIT_LSB; GSYM NOT_EVEN; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `(e EXP 2 == n) (mod p_25519) <=> (f EXP 2 == n) (mod p_25519)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    REWRITE_TAC[INTEGER_RULE
     `((p - x:int) pow 2 == n) (mod p) <=> (x pow 2 == n) (mod p)`];
    ALL_TAC] THEN

  (*** Final computations to get return value ***)

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (204--206) THEN LOCAL_NSQR_TAC 207 THEN
  BIGNUM_LDIGITIZE_TAC "g_"
   `read (memory :> bytes (word_add stackpointer (word 32),8 * 4)) s207` THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_EXEC (208--227) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  GEN_REWRITE_TAC I [TAUT `p /\ q /\ r /\ s <=> q /\ r /\ p /\ s`] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `(if EVEN e then e else p_25519 - e) = f`)) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[EVEN] `~EVEN x ==> ~(x = 0)`)) THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `(if EVEN e then e else p_25519 - e) = f`)) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[EVEN_SUB] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[JACOBI_PRIME; PRIME_P25519] THEN
  ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_0; WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
  MP_TAC(SPEC `[a_0:int64; a_1; a_2; a_3]` BIGNUM_OF_WORDLIST_EQ_0) THEN
  ASM_REWRITE_TAC[ALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN POP_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [SYM th]) THEN
    EXISTS_TAC `0` THEN CONV_TAC NUMBER_RULE;
    REWRITE_TAC[WORD_XOR_EQ_0]] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC INT_ARITH] THEN
  MP_TAC(SPECL
   [`a_0:int64`; `[a_1:int64; a_2; a_3]`;
    `g_0:int64`; `[g_1:int64; g_2; g_3]`]
   BIGNUM_OF_WORDLIST_EQ) THEN
  ASM_REWRITE_TAC[VAL_WORD_1; EXP_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ; WORD_XOR_EQ_0] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[CONG; MOD_LT; EQ_SYM_EQ] THEN
  COND_CASES_TAC THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let BIGNUM_SQRT_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [word pc,0x828; z,8 * 4; x,8 * 4] /\
        nonoverlapping (word pc,0x828) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read PC s = returnaddress /\
                  ival(C_RETURN s) = jacobi (n,p_25519) /\
                  bignum_from_memory (z,4) s < p_25519 /\
                  EVEN (bignum_from_memory (z,4) s) /\
                  (jacobi (n,p_25519) >= &0
                   ==> (bignum_from_memory (z,4) s EXP 2 == n) (mod p_25519)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                    memory :> bytes(word_sub stackpointer (word 144),144)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_SQRT_P25519_EXEC BIGNUM_SQRT_P25519_CORRECT
   `[X19;X30]` 144);;
