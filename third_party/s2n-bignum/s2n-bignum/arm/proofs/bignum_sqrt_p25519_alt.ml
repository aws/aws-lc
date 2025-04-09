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

(**** print_literal_from_elf "arm/curve25519/bignum_sqrt_p25519_alt.o";;
 ****)

let bignum_sqrt_p25519_alt_mc = define_assert_from_elf "bignum_sqrt_p25519_alt_mc" "arm/curve25519/bignum_sqrt_p25519_alt.o"
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
  0x94000114;       (* arm_BL (word 1104) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x940000ab;       (* arm_BL (word 684) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800041;       (* arm_MOV X1 (rvalue (word 2)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x9400010c;       (* arm_BL (word 1072) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x940000a3;       (* arm_BL (word 652) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x94000104;       (* arm_BL (word 1040) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x9400009b;       (* arm_BL (word 620) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x940000fc;       (* arm_BL (word 1008) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000093;       (* arm_BL (word 588) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800141;       (* arm_MOV X1 (rvalue (word 10)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x940000f4;       (* arm_BL (word 976) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x9400008b;       (* arm_BL (word 556) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x940000ec;       (* arm_BL (word 944) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000083;       (* arm_BL (word 524) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x940000e4;       (* arm_BL (word 912) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x9400007b;       (* arm_BL (word 492) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800641;       (* arm_MOV X1 (rvalue (word 50)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x940000dc;       (* arm_BL (word 880) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x94000073;       (* arm_BL (word 460) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x940000d4;       (* arm_BL (word 848) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x9400006b;       (* arm_BL (word 428) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800fa1;       (* arm_MOV X1 (rvalue (word 125)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x940000cc;       (* arm_BL (word 816) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000063;       (* arm_BL (word 396) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x940000c4;       (* arm_BL (word 784) *)
  0x910183e0;       (* arm_ADD X0 SP (rvalue (word 96)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x9400005b;       (* arm_BL (word 364) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910183e2;       (* arm_ADD X2 SP (rvalue (word 96)) *)
  0x940000bc;       (* arm_BL (word 752) *)
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
  0x940000a2;       (* arm_BL (word 648) *)
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
  0x9400007c;       (* arm_BL (word 496) *)
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
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bca7c83;       (* arm_UMULH X3 X4 X10 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9b077cab;       (* arm_MUL X11 X5 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7cab;       (* arm_MUL X11 X5 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bca7ca4;       (* arm_UMULH X4 X5 X10 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b077ccb;       (* arm_MUL X11 X6 X7 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b087ccb;       (* arm_MUL X11 X6 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097ccb;       (* arm_MUL X11 X6 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7ccb;       (* arm_MUL X11 X6 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9bca7cc5;       (* arm_UMULH X5 X6 X10 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0xb24101ef;       (* arm_ORR X15 X15 (rvalue (word 9223372036854775808)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b081ceb;       (* arm_MADD X11 X7 X8 X7 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9a9f30e7;       (* arm_CSEL X7 X7 XZR Condition_CC *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0xa900340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&0))) *)
  0xa9013c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c46;       (* arm_LDP X6 X3 X2 (Immediate_Offset (iword (&0))) *)
  0xa9411444;       (* arm_LDP X4 X5 X2 (Immediate_Offset (iword (&16))) *)
  0xaa0603e2;       (* arm_MOV X2 X6 *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070102;       (* arm_ADDS X2 X8 X7 *)
  0xba040123;       (* arm_ADCS X3 X9 X4 *)
  0xba0d0144;       (* arm_ADCS X4 X10 X13 *)
  0x9a1f0165;       (* arm_ADC X5 X11 XZR *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fff761;       (* arm_BNE (word 2096876) *)
  0xb1004c46;       (* arm_ADDS X6 X2 (rvalue (word 19)) *)
  0xba1f0067;       (* arm_ADCS X7 X3 XZR *)
  0xba1f0088;       (* arm_ADCS X8 X4 XZR *)
  0xba1f00a9;       (* arm_ADCS X9 X5 XZR *)
  0x9a865042;       (* arm_CSEL X2 X2 X6 Condition_PL *)
  0x9a875063;       (* arm_CSEL X3 X3 X7 Condition_PL *)
  0x9a885084;       (* arm_CSEL X4 X4 X8 Condition_PL *)
  0x9a8950a5;       (* arm_CSEL X5 X5 X9 Condition_PL *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQRT_P25519_ALT_EXEC = ARM_MK_EXEC_RULE bignum_sqrt_p25519_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Local subroutine correctness.                                             *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let LOCAL_MUL_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x604) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_alt_mc /\
                  read PC s = word(pc + 0x31c) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x4ac) /\
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
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (1--67) (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (68--92) (68--92) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s86:int64) + 1) <= 80 /\
    (val(sum_s86:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s86:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64)) +
        2 EXP 64 * val(mulhi_s69:int64) +
        2 EXP 128 * val(mulhi_s72:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  SUBGOAL_THEN
   `&(val(word(19 + 19 * val(sum_s86:int64)):int64)):real =
    &19 * (&(val(sum_s86:int64)) + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `19 * (x + 1) = 19 + 19 * x`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s86:int64) + 1 <= 80` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_or sum_s82 (word 9223372036854775808:int64))):real =
    &2 pow 63 + &(val(sum_s84:int64)) / &2`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or m (word_and x (word_not m))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and m (word_and x (word_not m)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s86:int64) + val(sum_s84:int64) =
      2 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 pow 256 * (&(bitval carry_s92) - &1:real) +
    &(bignum_of_wordlist[sum_s89; sum_s90; sum_s91; sum_s92]):real =
    &(38 * h + l) - &((val(sum_s86:int64) + 1) * p_25519)`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (93--100) (93--100) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s86:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l < (val(sum_s86:int64) + 1) * p_25519 <=> ~carry_s92`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[REAL_BITVAL_NOT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x - y = &2 pow 256 * c + s`)) THEN
    BOUNDER_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x = &2 pow 256 * c + s + y`)) THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s92:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let LOCAL_MUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (bignum_sqrt_p25519_alt_mc,BIGNUM_SQRT_P25519_ALT_EXEC,
    0x0,bignum_sqrt_p25519_alt_mc,LOCAL_MUL_P25519_CORRECT)
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s`;
   `pc:num`];;

let LOCAL_NSQR_P25519_CORRECT = time prove
 (`!z k x n pc.
        nonoverlapping (word pc,0x604) (z,8 * 4) /\
        1 <= val k /\ val k <= 1000
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_alt_mc /\
                  read PC s = word(pc + 0x4b0) /\
                  C_ARGUMENTS [z; k; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x600) /\
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

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x4bc` `pc + 0x5d0`
   `\i s. (read X0 s = z /\
           read X1 s = word(k - i) /\
           (bignum_of_wordlist
             [read X2 s; read X3 s; read X4 s; read X5 s] ==
            n EXP (2 EXP i)) (mod p_25519) /\
           (1 <= i
            ==> bignum_of_wordlist
                 [read X2 s; read X3 s; read X4 s; read X5 s]
                < 2 * p_25519)) /\
          (read ZF s <=> i = k)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LE_1];

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (x,8 * 4)) s0` THEN
    ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP; EXP_1; CONG_REFL; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV;

    ALL_TAC; (*** Main loop invariant ***)

    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_SQRT_P25519_ALT_EXEC [1];

    GHOST_INTRO_TAC `x_0:int64` `read X2` THEN
    GHOST_INTRO_TAC `x_1:int64` `read X3` THEN
    GHOST_INTRO_TAC `x_2:int64` `read X4` THEN
    GHOST_INTRO_TAC `x_3:int64` `read X5` THEN
    ASM_REWRITE_TAC[] THEN
    ARM_ACCSIM_TAC BIGNUM_SQRT_P25519_ALT_EXEC (2--5) (1--12) THEN
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
  GHOST_INTRO_TAC `n_0:int64` `read X2` THEN
  GHOST_INTRO_TAC `n_1:int64` `read X3` THEN
  GHOST_INTRO_TAC `n_2:int64` `read X4` THEN
  GHOST_INTRO_TAC `n_3:int64` `read X5` THEN
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

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (3--45) (3--45) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s31; sum_s33; sum_s35; sum_s37]`;
    `h = bignum_of_wordlist[sum_s39; sum_s41; sum_s43; sum_s45]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
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

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (46--70) (46--71) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s64:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s64:int64) + 1) <= 80 /\
    (val(sum_s64:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s64:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s64:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s61:int64) + val(sum_s60:int64)) +
        2 EXP 64 * val(mulhi_s47:int64) +
        2 EXP 128 * val(mulhi_s50:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
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

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  UNDISCH_TAC
   `&2 pow 64 * &(val(mulhi_s66:int64)) + &(val(mullo_s66:int64)) =
    &19 * &(val(sum_s64:int64))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= 80 ==> a < 80`)) THEN
  DISCH_THEN(fun bth -> DISCH_THEN(fun th ->
        MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE [bth] [th])))) THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT2) THEN

  SUBGOAL_THEN
   `&(val(word_and sum_s60 (word 9223372036854775807:int64))):real =
    &(val(sum_s62:int64)) / &2`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s64:int64) + val(sum_s62:int64) =
      2 * (2 EXP 64 * val(sum_s61:int64) + val(sum_s60:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN

  REWRITE_TAC[GSYM CONG; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\
        (&0 <= ca - q * p /\ ca - q * p < p2) /\
        (&0 <= ca - q * p /\ ca - q * p < p2 ==> x = ca - q * p)
        ==> (x == ca) (mod p) /\ x:int < p2`) THEN
  EXISTS_TAC `&(val(sum_s64:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(val(sum_s64:int64) + 1) * p_25519 <= (38 * h + l) + p_25519`;
      `38 * h + l < (val(sum_s64:int64) + 1) * p_25519 + p_25519`] THEN
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
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
              int_mul_th; int_pow_th] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let LOCAL_NSQR_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (bignum_sqrt_p25519_alt_mc,BIGNUM_SQRT_P25519_ALT_EXEC,
    0x0,bignum_sqrt_p25519_alt_mc,LOCAL_NSQR_P25519_CORRECT)
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

let BIGNUM_SQRT_P25519_ALT_CORRECT = time prove
 (`!z x n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,128))
            [(word pc,0x604); (z,8 * 4); (x,8 * 4)] /\
        nonoverlapping (word pc,0x604) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_alt_mc /\
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
    ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC
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
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (1--4) THEN LOCAL_NSQR_TAC 5 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (6--10) THEN LOCAL_MUL_TAC 11 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (12--16) THEN LOCAL_NSQR_TAC 17 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (18--22) THEN LOCAL_MUL_TAC 23 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (24--28) THEN LOCAL_NSQR_TAC 29 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (30--34) THEN LOCAL_MUL_TAC 35 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (36--40) THEN LOCAL_NSQR_TAC 41 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (42--46) THEN LOCAL_MUL_TAC 47 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (48--52) THEN LOCAL_NSQR_TAC 53 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (54--58) THEN LOCAL_MUL_TAC 59 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (60--64) THEN LOCAL_NSQR_TAC 65 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (66--70) THEN LOCAL_MUL_TAC 71 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (72--76) THEN LOCAL_NSQR_TAC 77 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (78--82) THEN LOCAL_MUL_TAC 83 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (84--88) THEN LOCAL_NSQR_TAC 89 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (90--94) THEN LOCAL_MUL_TAC 95 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (96--100) THEN LOCAL_NSQR_TAC 101 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (102--106) THEN LOCAL_MUL_TAC 107 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (108--112) THEN LOCAL_NSQR_TAC 113 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (114--118) THEN LOCAL_MUL_TAC 119 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (120--124) THEN LOCAL_NSQR_TAC 125 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (126--130) THEN LOCAL_MUL_TAC 131 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (132--136) THEN LOCAL_NSQR_TAC 137 THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC [138] THEN
  REABBREV_TAC
   `c =
    read (memory :> bytes (word_add stackpointer (word 64),8 * 4)) s138` THEN
  POP_ASSUM(MP_TAC o CONV_RULE MOD_DOWN_CONV) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
  REWRITE_TAC[MULT_EXP] THEN REWRITE_TAC[EXP_EXP] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  DISCH_TAC THEN

  (*** Multiplication by j_25519 ***)

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (139--160) THEN
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

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (162--166) THEN
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
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (168--188) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC [190;192;194;195] (189--203) THEN
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

  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (204--206) THEN LOCAL_NSQR_TAC 207 THEN
  BIGNUM_LDIGITIZE_TAC "g_"
   `read (memory :> bytes (word_add stackpointer (word 32),8 * 4)) s207` THEN
  ARM_STEPS_TAC BIGNUM_SQRT_P25519_ALT_EXEC (208--227) THEN
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

let BIGNUM_SQRT_P25519_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [word pc,0x604; z,8 * 4; x,8 * 4] /\
        nonoverlapping (word pc,0x604) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqrt_p25519_alt_mc /\
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
   BIGNUM_SQRT_P25519_ALT_EXEC BIGNUM_SQRT_P25519_ALT_CORRECT
   `[X19;X30]` 144);;
