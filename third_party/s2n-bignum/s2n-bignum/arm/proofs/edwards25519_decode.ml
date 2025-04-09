(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decoding of compressed form of point on edwards25519.                     *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/edwards25519.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/curve25519/edwards25519_decode.o";;
 ****)

let edwards25519_decode_mc = define_assert_from_elf "edwards25519_decode_mc" "arm/curve25519/edwards25519_decode.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf5;       (* arm_STP X21 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10303ff;       (* arm_SUB SP SP (rvalue (word 192)) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0x39400020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 0)) *)
  0xd3481c04;       (* arm_LSL X4 X0 56 *)
  0x39400420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 1)) *)
  0x93c42004;       (* arm_EXTR X4 X0 X4 8 *)
  0x39400820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 2)) *)
  0x93c42004;       (* arm_EXTR X4 X0 X4 8 *)
  0x39400c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 3)) *)
  0x93c42004;       (* arm_EXTR X4 X0 X4 8 *)
  0x39401020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 4)) *)
  0x93c42004;       (* arm_EXTR X4 X0 X4 8 *)
  0x39401420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 5)) *)
  0x93c42004;       (* arm_EXTR X4 X0 X4 8 *)
  0x39401820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 6)) *)
  0x93c42004;       (* arm_EXTR X4 X0 X4 8 *)
  0x39401c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 7)) *)
  0x93c42004;       (* arm_EXTR X4 X0 X4 8 *)
  0x39402020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 8)) *)
  0xd3481c05;       (* arm_LSL X5 X0 56 *)
  0x39402420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 9)) *)
  0x93c52005;       (* arm_EXTR X5 X0 X5 8 *)
  0x39402820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 10)) *)
  0x93c52005;       (* arm_EXTR X5 X0 X5 8 *)
  0x39402c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 11)) *)
  0x93c52005;       (* arm_EXTR X5 X0 X5 8 *)
  0x39403020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 12)) *)
  0x93c52005;       (* arm_EXTR X5 X0 X5 8 *)
  0x39403420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 13)) *)
  0x93c52005;       (* arm_EXTR X5 X0 X5 8 *)
  0x39403820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 14)) *)
  0x93c52005;       (* arm_EXTR X5 X0 X5 8 *)
  0x39403c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 15)) *)
  0x93c52005;       (* arm_EXTR X5 X0 X5 8 *)
  0x39404020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 16)) *)
  0xd3481c06;       (* arm_LSL X6 X0 56 *)
  0x39404420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 17)) *)
  0x93c62006;       (* arm_EXTR X6 X0 X6 8 *)
  0x39404820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 18)) *)
  0x93c62006;       (* arm_EXTR X6 X0 X6 8 *)
  0x39404c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 19)) *)
  0x93c62006;       (* arm_EXTR X6 X0 X6 8 *)
  0x39405020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 20)) *)
  0x93c62006;       (* arm_EXTR X6 X0 X6 8 *)
  0x39405420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 21)) *)
  0x93c62006;       (* arm_EXTR X6 X0 X6 8 *)
  0x39405820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 22)) *)
  0x93c62006;       (* arm_EXTR X6 X0 X6 8 *)
  0x39405c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 23)) *)
  0x93c62006;       (* arm_EXTR X6 X0 X6 8 *)
  0x39406020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 24)) *)
  0xd3481c07;       (* arm_LSL X7 X0 56 *)
  0x39406420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 25)) *)
  0x93c72007;       (* arm_EXTR X7 X0 X7 8 *)
  0x39406820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 26)) *)
  0x93c72007;       (* arm_EXTR X7 X0 X7 8 *)
  0x39406c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 27)) *)
  0x93c72007;       (* arm_EXTR X7 X0 X7 8 *)
  0x39407020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 28)) *)
  0x93c72007;       (* arm_EXTR X7 X0 X7 8 *)
  0x39407420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 29)) *)
  0x93c72007;       (* arm_EXTR X7 X0 X7 8 *)
  0x39407820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 30)) *)
  0x93c72007;       (* arm_EXTR X7 X0 X7 8 *)
  0x39407c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 31)) *)
  0x93c72007;       (* arm_EXTR X7 X0 X7 8 *)
  0xa90017e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&0))) *)
  0xd37ffcf4;       (* arm_LSR X20 X7 63 *)
  0x9240f8e7;       (* arm_AND X7 X7 (rvalue (word 9223372036854775807)) *)
  0xa9011fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&16))) *)
  0xb1004c9f;       (* arm_CMN X4 (rvalue (word 19)) *)
  0xba1f00bf;       (* arm_ADCS XZR X5 XZR *)
  0xba1f00df;       (* arm_ADCS XZR X6 XZR *)
  0xba1f00ff;       (* arm_ADCS XZR X7 XZR *)
  0x9a9f57f5;       (* arm_CSET X21 Condition_MI *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910003e2;       (* arm_ADD X2 SP (rvalue (word 0)) *)
  0x94000197;       (* arm_BL (word 1628) *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa9490fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0xd2f00004;       (* arm_MOVZ X4 (word 32768) 48 *)
  0xf1005000;       (* arm_SUBS X0 X0 (rvalue (word 20)) *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda040063;       (* arm_SBC X3 X3 X4 *)
  0xa90607e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xa9070fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0xd28f1460;       (* arm_MOV X0 (rvalue (word 30883)) *)
  0xf2a26b20;       (* arm_MOVK X0 (word 4953) 16 *)
  0xf2c9b940;       (* arm_MOVK X0 (word 19914) 32 *)
  0xf2eebd60;       (* arm_MOVK X0 (word 30187) 48 *)
  0xd29b1561;       (* arm_MOV X1 (rvalue (word 55467)) *)
  0xf2a82821;       (* arm_MOVK X1 (word 16705) 16 *)
  0xf2c149a1;       (* arm_MOVK X1 (word 2637) 32 *)
  0xf2e00e01;       (* arm_MOVK X1 (word 112) 48 *)
  0xd29d1302;       (* arm_MOV X2 (rvalue (word 59544)) *)
  0xf2aeef22;       (* arm_MOVK X2 (word 30585) 16 *)
  0xf2c80f22;       (* arm_MOVK X2 (word 16505) 32 *)
  0xf2f198e2;       (* arm_MOVK X2 (word 36039) 48 *)
  0xd29fce63;       (* arm_MOV X3 (rvalue (word 65139)) *)
  0xf2a56de3;       (* arm_MOVK X3 (word 11119) 16 *)
  0xf2cd9dc3;       (* arm_MOVK X3 (word 27886) 32 *)
  0xf2ea4063;       (* arm_MOVK X3 (word 20995) 48 *)
  0xa90a07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa90b0fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&176))) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x940000c3;       (* arm_BL (word 780) *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa9490fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0xb1000400;       (* arm_ADDS X0 X0 (rvalue (word 1)) *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xa90807e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa9090fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x940000b7;       (* arm_BL (word 732) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x94000168;       (* arm_BL (word 1440) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x940000af;       (* arm_BL (word 700) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800041;       (* arm_MOV X1 (rvalue (word 2)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000160;       (* arm_BL (word 1408) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x940000a7;       (* arm_BL (word 668) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000158;       (* arm_BL (word 1376) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x9400009f;       (* arm_BL (word 636) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000150;       (* arm_BL (word 1344) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000097;       (* arm_BL (word 604) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800141;       (* arm_MOV X1 (rvalue (word 10)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000148;       (* arm_BL (word 1312) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x9400008f;       (* arm_BL (word 572) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000140;       (* arm_BL (word 1280) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000087;       (* arm_BL (word 540) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000138;       (* arm_BL (word 1248) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x9400007f;       (* arm_BL (word 508) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800641;       (* arm_MOV X1 (rvalue (word 50)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000130;       (* arm_BL (word 1216) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000077;       (* arm_BL (word 476) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000128;       (* arm_BL (word 1184) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x9400006f;       (* arm_BL (word 444) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800fa1;       (* arm_MOV X1 (rvalue (word 125)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000120;       (* arm_BL (word 1152) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000067;       (* arm_BL (word 412) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800041;       (* arm_MOV X1 (rvalue (word 2)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000118;       (* arm_BL (word 1120) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x9400005f;       (* arm_BL (word 380) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000110;       (* arm_BL (word 1088) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910203e1;       (* arm_ADD X1 SP (rvalue (word 128)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x94000057;       (* arm_BL (word 348) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x94000053;       (* arm_BL (word 332) *)
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
  0xa90407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9050fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&80))) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x9400003d;       (* arm_BL (word 244) *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa9490fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0x927ff804;       (* arm_AND X4 X0 (rvalue (word 18446744073709551614)) *)
  0xaa010084;       (* arm_ORR X4 X4 X1 *)
  0xaa030045;       (* arm_ORR X5 X2 X3 *)
  0xaa050084;       (* arm_ORR X4 X4 X5 *)
  0x91005000;       (* arm_ADD X0 X0 (rvalue (word 20)) *)
  0x91000421;       (* arm_ADD X1 X1 (rvalue (word 1)) *)
  0xaa010000;       (* arm_ORR X0 X0 X1 *)
  0x91000442;       (* arm_ADD X2 X2 (rvalue (word 1)) *)
  0xd240f863;       (* arm_EOR X3 X3 (rvalue (word 9223372036854775807)) *)
  0xaa030042;       (* arm_ORR X2 X2 X3 *)
  0xaa020000;       (* arm_ORR X0 X0 X2 *)
  0xeb1f009f;       (* arm_CMP X4 XZR *)
  0xa9422fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&32))) *)
  0xa9443fee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&64))) *)
  0x9a8e014a;       (* arm_CSEL X10 X10 X14 Condition_EQ *)
  0x9a8f016b;       (* arm_CSEL X11 X11 X15 Condition_EQ *)
  0xa94337ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&48))) *)
  0xa94547f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&80))) *)
  0x9a90018c;       (* arm_CSEL X12 X12 X16 Condition_EQ *)
  0x9a9101ad;       (* arm_CSEL X13 X13 X17 Condition_EQ *)
  0xa9022fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&32))) *)
  0xa90337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&48))) *)
  0xfa5f1004;       (* arm_CCMP X0 XZR (word 4) Condition_NE *)
  0x9a9f07e0;       (* arm_CSET X0 Condition_NE *)
  0xaa0002b5;       (* arm_ORR X21 X21 X0 *)
  0xa94207e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&32))) *)
  0xa9430fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0x92800244;       (* arm_MOVN X4 (word 18) 0 *)
  0xeb000084;       (* arm_SUBS X4 X4 X0 *)
  0x92800006;       (* arm_MOVN X6 (word 0) 0 *)
  0xfa0100c5;       (* arm_SBCS X5 X6 X1 *)
  0xfa0200c6;       (* arm_SBCS X6 X6 X2 *)
  0x92f00007;       (* arm_MOVN X7 (word 32768) 48 *)
  0xda0300e7;       (* arm_SBC X7 X7 X3 *)
  0x92400009;       (* arm_AND X9 X0 (rvalue (word 1)) *)
  0xca140134;       (* arm_EOR X20 X9 X20 *)
  0xaa010008;       (* arm_ORR X8 X0 X1 *)
  0xaa030049;       (* arm_ORR X9 X2 X3 *)
  0xaa090108;       (* arm_ORR X8 X8 X9 *)
  0xaa1402aa;       (* arm_ORR X10 X21 X20 *)
  0xeb1f011f;       (* arm_CMP X8 XZR *)
  0x9a950155;       (* arm_CSEL X21 X10 X21 Condition_EQ *)
  0xfa5f1284;       (* arm_CCMP X20 XZR (word 4) Condition_NE *)
  0x9a840000;       (* arm_CSEL X0 X0 X4 Condition_EQ *)
  0x9a850021;       (* arm_CSEL X1 X1 X5 Condition_EQ *)
  0x9a860042;       (* arm_CSEL X2 X2 X6 Condition_EQ *)
  0x9a870063;       (* arm_CSEL X3 X3 X7 Condition_EQ *)
  0xa94027e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9412fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa9000660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&0))) *)
  0xa9010e62;       (* arm_STP X2 X3 X19 (Immediate_Offset (iword (&16))) *)
  0xa9022668;       (* arm_STP X8 X9 X19 (Immediate_Offset (iword (&32))) *)
  0xa9032e6a;       (* arm_STP X10 X11 X19 (Immediate_Offset (iword (&48))) *)
  0xaa1503e0;       (* arm_MOV X0 X21 *)
  0x910303ff;       (* arm_ADD SP SP (rvalue (word 192)) *)
  0xa8c17bf5;       (* arm_LDP X21 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
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

let EDWARDS25519_DECODE_EXEC = ARM_MK_EXEC_RULE edwards25519_decode_mc;;

(* ------------------------------------------------------------------------- *)
(* Local subroutine correctness.                                             *)
(* ------------------------------------------------------------------------- *)

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
        nonoverlapping (word pc,0x9d4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_mc /\
                  read PC s = word(pc + 0x4c8) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x798) /\
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC [9;11;12;14] (1--14) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC [34;36;37;39] (26--39) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC (69--72) (69--72) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (113--137) THEN

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
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC [142;144;146;150] (138--150) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC (154--157) (151--160) THEN
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
   (edwards25519_decode_mc,EDWARDS25519_DECODE_EXEC,
    0x0,edwards25519_decode_mc,LOCAL_MUL_P25519_CORRECT)
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s`;
   `pc:num`];;

let LOCAL_NSQR_P25519_CORRECT = time prove
 (`!z k x n pc.
        nonoverlapping (word pc,0x9d4) (z,8 * 4) /\
        1 <= val k /\ val k <= 1000
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_mc /\
                  read PC s = word(pc + 0x79c) /\
                  C_ARGUMENTS [z; k; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x9d0) /\
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

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x7a4` `pc + 0x9a0`
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
    ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP; EXP_1; CONG_REFL; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV;

    ALL_TAC; (*** Main loop invariant ***)

    REPEAT STRIP_TAC THEN ARM_SIM_TAC EDWARDS25519_DECODE_EXEC [1];

    GHOST_INTRO_TAC `x_0:int64` `read X10` THEN
    GHOST_INTRO_TAC `x_1:int64` `read X11` THEN
    GHOST_INTRO_TAC `x_2:int64` `read X12` THEN
    GHOST_INTRO_TAC `x_3:int64` `read X13` THEN
    ASM_REWRITE_TAC[] THEN
    ARM_ACCSIM_TAC EDWARDS25519_DECODE_EXEC (2--5) (1--12) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC [47;48;51;53] (47--53) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC (54--57) (54--57) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC (80--90) (80--90) THEN
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

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (91--115) THEN
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
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC [120;122;124;128] (116--129) THEN
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
   (edwards25519_decode_mc,EDWARDS25519_DECODE_EXEC,
    0x0,edwards25519_decode_mc,LOCAL_NSQR_P25519_CORRECT)
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s`;
   `pc:num`];;

(* ------------------------------------------------------------------------- *)
(* Definitions and lemmas to express specification and support proof.        *)
(* ------------------------------------------------------------------------- *)

let ed25519_encode = new_definition
  `ed25519_encode (X,Y) =
        let x = num_of_int(X rem &p_25519)
        and y = num_of_int(Y rem &p_25519) in
        2 EXP 255 * x MOD 2 + y`;;

let ed25519_validencode = new_definition
  `ed25519_validencode n <=>
        ?P. P IN group_carrier edwards25519_group /\
            ed25519_encode P = n`;;

let ed25519_decode = new_definition
 `ed25519_decode n =
        @P. P IN group_carrier edwards25519_group /\
            ed25519_encode P = n`;;

let EDWARDS25519_NONZERO_DENOMINATORS = prove
 (`!y. coprime(&1 + &d_25519 * y pow 2,&p_25519)`,
  ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
  REWRITE_TAC[GSYM INT_FORALL_ABS; INT_OF_NUM_CLAUSES; GSYM num_coprime] THEN
  X_GEN_TAC `y:num` THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
  DISCH_THEN(MP_TAC o SPEC `inverse_mod p_25519 d_25519` o
    MATCH_MP (NUMBER_RULE
     `p divides (1 + d * y)
      ==> !d'. (d * d' == 1) (mod p) ==> p divides (y + d')`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN REWRITE_TAC[p_25519; d_25519] THEN
  CONV_TAC(ONCE_DEPTH_CONV COPRIME_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `p divides y + z ==> (y:int == --z) (mod p)`)) THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM INT_CONG_RREM] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  DISCH_THEN(MP_TAC o SIMPLE_EXISTS `y:num`) THEN
  REWRITE_TAC[GSYM p_25519] THEN SIMP_TAC[EULER_CRITERION; PRIME_P25519] THEN
  REWRITE_TAC[p_25519; d_25519] THEN
  CONV_TAC(DEPTH_CONV(NUM_SUB_CONV ORELSEC DIVIDES_CONV)) THEN
  REWRITE_TAC[CONG] THEN
  CONV_TAC(RAND_CONV(RAND_CONV NUM_MOD_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  CONV_TAC(RAND_CONV(LAND_CONV EXP_MOD_CONV)) THEN
  ARITH_TAC);;

let IN_GROUP_CARRIER_EDWARDS25519 = prove
 (`!x y. (x,y) IN group_carrier edwards25519_group <=>
         &0 <= x /\ x < &p_25519 /\ &0 <= y /\ y < &p_25519 /\
         ((&1 + &d_25519 * y pow 2) * x pow 2 == y pow 2 - &1) (mod &p_25519)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EDWARDS25519_GROUP] THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[edwards_curve; edwards25519] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[p_25519; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[GSYM p_25519; GSYM CONJ_ASSOC] THEN REPEAT AP_TERM_TAC THEN
  SUBGOAL_THEN `&e_25519:int = &p_25519 - &1` SUBST1_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN INT_ARITH_TAC;
    CONV_TAC INT_REM_DOWN_CONV] THEN
  REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE);;

let EXISTS_IN_GROUP_CARRIER_EDWARDS25519 = prove
 (`!y. (?x. (x,&y) IN group_carrier edwards25519_group) <=>
       y < p_25519 /\
       ?x. (x EXP 2 == ((p_25519 - 1) + y EXP 2) * (1 + d_25519 * y EXP 2))
           (mod p_25519)`,
  GEN_TAC THEN REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519] THEN
  REWRITE_TAC[GSYM INT_EXISTS_POS] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
  ASM_CASES_TAC `y < p_25519` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[EDWARDS25519_NONZERO_DENOMINATORS; INTEGER_RULE
   `coprime(d:int,p)
    ==> ((d * n pow 2 == y - &1) (mod p) <=>
         ((d * n) pow 2 == ((p - &1) + y) * d) (mod p))`] THEN
  SUBGOAL_THEN `&p_25519 - &1:int = &(p_25519 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    SPEC_TAC(`p_25519 - 1`,`e:num`) THEN GEN_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `(inverse_mod p_25519 (1 + d_25519 * y EXP 2) * n) MOD p_25519` THEN
  CONJ_TAC THENL [REWRITE_TAC[MOD_LT_EQ; p_25519; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(d * i == 1) (mod p) /\ (x EXP 2 == a) (mod p)
    ==> ((d * i * x) EXP 2 == a) (mod p)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  REWRITE_TAC[num_coprime; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS]);;

let EXISTS_IN_GROUP_CARRIER_EDWARDS25519_EULER = prove
 (`!y w. ((((p_25519 - 1) + y EXP 2) * (1 + d_25519 * y EXP 2)) EXP
          (2 EXP 253 - 5) == w) (mod p_25519)
         ==> ((?x. (x,&y) IN group_carrier edwards25519_group) <=>
              y < p_25519 /\
              ((w == 0) (mod p_25519) \/
               (w == 1) (mod p_25519) \/
               (w == p_25519 - 1) (mod p_25519)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
   `(x == w) (mod p) ==> !y:num. (w == y) (mod p) <=> (x == y) (mod p)`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXISTS_IN_GROUP_CARRIER_EDWARDS25519] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`p_25519`; `1`] CONG_SQUARE_1_PRIME_POWER) THEN
  SIMP_TAC[EULER_CRITERION; PRIME_P25519; EXP_1; RIGHT_FORALL_IMP_THM] THEN
  ANTS_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  SIMP_TAC[EXP_EXP; CONG_0_DIVIDES; PRIME_DIVEXP_EQ; PRIME_P25519] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let ED25519_ENCODE_INJECTIVE = prove
 (`!P Q. P IN group_carrier edwards25519_group /\
         Q IN group_carrier edwards25519_group
         ==> (ed25519_encode P = ed25519_encode Q <=> P = Q)`,
  REWRITE_TAC[GSYM INJECTIVE_ON_ALT] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  X_GEN_TAC `x1:num` THEN DISCH_TAC THEN
  X_GEN_TAC `y1:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `x2:num` THEN DISCH_TAC THEN
  X_GEN_TAC `y2:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ed25519_encode; INT_OF_NUM_REM; MOD_LT] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(fun th ->
    MP_TAC(AP_TERM `\x. x MOD 2 EXP 255` th) THEN
    MP_TAC(AP_TERM `\x. x DIV 2 EXP 255` th)) THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN `!z. z < p_25519 ==> z < 2 EXP 255` MP_TAC THENL
   [REWRITE_TAC[p_25519] THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT; DIV_LT]] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[PAIR_EQ; INT_OF_NUM_EQ] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_REM_EQ])) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(a * x pow 2 == a * y pow 2) (mod p)
    ==> coprime(a:int,p) ==> p divides ((x - y) * (x + y))`)) THEN
  REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS] THEN
  SIMP_TAC[PRIME_INT_DIVPROD_EQ; PRIME_P25519] THEN
  REWRITE_TAC[GSYM INT_CONG; GSYM num_congruent; CONG] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
  DISCH_THEN(MP_TAC o SPEC `2` o MATCH_MP (NUMBER_RULE
   `p divides x + y
    ==> !q:num. q divides x + y /\ coprime(p,q) ==> p * q divides x + y`)) THEN
  REWRITE_TAC[DIVIDES_2; COPRIME_2; EVEN_ADD] THEN
  ASM_REWRITE_TAC[EVEN_MOD] THEN ANTS_TAC THENL
   [REWRITE_TAC[p_25519; ARITH_EVEN; ARITH_ODD];
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE)] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let j_25519 = define
 `j_25519 =
19681161376707505956807079304988542015446066515923890162744021073123829784752`;;

(* ------------------------------------------------------------------------- *)
(* Overall proof.                                                            *)
(* ------------------------------------------------------------------------- *)

let EDWARDS25519_DECODE_CORRECT = time prove
 (`!z c n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,192))
            [(word pc,0x9d4); (z,8 * 8); (c,8 * 4)] /\
        nonoverlapping (word pc,0x9d4) (z,8 * 8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_mc /\
                  read PC s = word(pc + 0xc) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read PC s = word (pc + 0x4b8) /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                         X12; X13; X14; X15; X16; X17; X19; X20; X21; X30] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                         memory :> bytes(stackpointer,192)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initial bytewise load and split ***)

  REWRITE_TAC[ARITH_RULE `32 = 8 * 4`] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; NUM_REDUCE_CONV `8 * 4`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NUM_REDUCE_CONV `64 * 4`]) THEN
  MAP_EVERY ABBREV_TAC [`y = n MOD 2 EXP 255`; `b = n DIV 2 EXP 255`] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x134`
   `\s. read SP s = stackpointer /\
        read X19 s = z /\
        read X20 s = word b /\
        bignum_from_memory(stackpointer,4) s = y /\
        read X21 s = word(bitval(p_25519 <= y))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BYTES_DIGITIZE_TAC "c_" `read (memory :> bytes (c,32)) s0` THEN
    ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (1--17) THEN
    REABBREV_TAC `n_0 = read X4 s17` THEN
    ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (18--33) THEN
    REABBREV_TAC `n_1 = read X5 s33` THEN
    ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (34--49) THEN
    REABBREV_TAC `n_2 = read X6 s49` THEN
    ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (50--65) THEN
    REABBREV_TAC `n_3 = read X7 s65` THEN
    ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC (70--73) (66--74) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o
     GEN_REWRITE_RULE LAND_CONV [READ_RVALUE])) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL] THEN
    DISCARD_STATE_TAC "s74" THEN
    MATCH_MP_TAC(TAUT `(p /\ q) /\ (q ==> r) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["y"; "b"] THEN REWRITE_TAC[word_ushr] THEN
      MATCH_MP_TAC(MESON[]
       `q = q' /\ r = r' ==> word q' = word q /\ r' = r`) THEN
      MATCH_MP_TAC DIVMOD_UNIQ THEN
      CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `63 = 64 - 1`; GSYM DIMINDEX_64] THEN
      REWRITE_TAC[GSYM BITVAL_MSB] THEN
      REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
      MAP_EVERY EXPAND_TAC ["n_0"; "n_1"; "n_2"; "n_3"; "n"] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN AP_TERM_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 255 <= bignum_of_wordlist[sum_s70;sum_s71;sum_s72;sum_s73]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `2 EXP 255 <= n <=> 2 EXP 63 <= n DIV 2 EXP 192`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL] THEN
      REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE
     `p + 19 = e /\ x = y + 19 ==> (e <= x <=> p <= y)`) THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Computation of y^2 ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (1--4) THEN LOCAL_NSQR_TAC 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_1; EXP_1]) THEN

  (*** Computation of u ***)

  BIGNUM_LDIGITIZE_TAC "y2_"
   `read (memory :> bytes(word_add stackpointer (word 128),8 * 4)) s5` THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add stackpointer (word 128),8 * 4)) s5 =
     y EXP 2 MOD p_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC (10--13) (6--15) THEN
  ABBREV_TAC `u = (p_25519 - 1) + y EXP 2 MOD p_25519` THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 96),8 * 4)) s15 = u`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ]] THEN
      EXPAND_TAC "u" THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [y2_0; y2_1; y2_2; y2_3] = y EXP 2 MOD p_25519`)) THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM(fun th -> DISCH_TAC THEN ASSUME_TAC th)] THEN

  (*** Computation of v ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (16--37) THEN
  SUBGOAL_THEN
    `read (memory :> bytes(word_add stackpointer (word 160),8 * 4)) s37 =
     d_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; d_25519] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_TAC 38 THEN RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN

  BIGNUM_LDIGITIZE_TAC "d_"
   `read (memory :> bytes (word_add stackpointer (word 128),8 * 4)) s38` THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC (42--45) (39--47) THEN

  ABBREV_TAC `v = 1 + (d_25519 * y EXP 2) MOD p_25519` THEN

  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 128),8 * 4)) s47 = v`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [EXPAND_TAC "v" THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ]] THEN
    EXPAND_TAC "v" THEN
     SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [d_0; d_1; d_2; d_3] =
      (d_25519 * y EXP 2) MOD p_25519`)) THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM(fun th -> DISCH_TAC THEN ASSUME_TAC th)] THEN

  (*** Computation of w ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (48--51) THEN LOCAL_MUL_TAC 52 THEN
  ABBREV_TAC `w = (u * v) MOD p_25519` THEN

  (*** The power tower ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (53--57) THEN LOCAL_NSQR_TAC 58 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (59--63) THEN LOCAL_MUL_TAC 64 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (65--69) THEN LOCAL_NSQR_TAC 70 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (71--75) THEN LOCAL_MUL_TAC 76 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (77--81) THEN LOCAL_NSQR_TAC 82 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (83--87) THEN LOCAL_MUL_TAC 88 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (89--93) THEN LOCAL_NSQR_TAC 94 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (95--99) THEN LOCAL_MUL_TAC 100 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (101--105) THEN LOCAL_NSQR_TAC 106 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (107--111) THEN LOCAL_MUL_TAC 112 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (113--117) THEN LOCAL_NSQR_TAC 118 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (119--123) THEN LOCAL_MUL_TAC 124 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (125--129) THEN LOCAL_NSQR_TAC 130 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (131--135) THEN LOCAL_MUL_TAC 136 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (137--141) THEN LOCAL_NSQR_TAC 142 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (143--147) THEN LOCAL_MUL_TAC 148 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (149--153) THEN LOCAL_NSQR_TAC 154 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (155--159) THEN LOCAL_MUL_TAC 160 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (161--165) THEN LOCAL_NSQR_TAC 166 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (167--171) THEN LOCAL_MUL_TAC 172 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (173--177) THEN LOCAL_NSQR_TAC 178 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (179--183) THEN LOCAL_MUL_TAC 184 THEN

  REABBREV_TAC
   `e =
    read (memory :> bytes (word_add stackpointer (word 32),8 * 4)) s184` THEN
  POP_ASSUM(MP_TAC o CONV_RULE MOD_DOWN_CONV) THEN

  CONV_TAC(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
  REWRITE_TAC[MULT_EXP] THEN REWRITE_TAC[EXP_EXP] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  ONCE_REWRITE_TAC[MESON[EXP; MULT_SYM] `x EXP n * x = x EXP SUC n`] THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 252 - 3`)] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
   (free_in `val(word 1:int64)` o concl))) THEN

  (*** e^2 * w computation ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (185--189) THEN LOCAL_NSQR_TAC 190 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_1; EXP_1]) THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (191--195) THEN LOCAL_MUL_TAC 196 THEN
  RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN

  (*** s = u * e ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (197--201) THEN LOCAL_MUL_TAC 202 THEN
  RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN
  ABBREV_TAC `s = (u * e) MOD p_25519` THEN

  (*** t = j_25519 * s ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (203--225) THEN
  SUBGOAL_THEN
    `read (memory :> bytes(word_add stackpointer (word 64),8 * 4)) s225 =
     j_25519`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; j_25519] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_TAC 226 THEN

  (*** Comparison with 0 or 1 ***)

  ABBREV_TAC `f = (e EXP 2 * w) MOD p_25519` THEN
  BIGNUM_LDIGITIZE_TAC "f_"
   `read (memory :> bytes(word_add stackpointer (word 128),8 * 4)) s226` THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (227--233) THEN
  REABBREV_TAC `f01 = read X4 s233` THEN
  SUBGOAL_THEN
   `f01:int64 = word 0 <=>
    (w * e EXP 2 == 0) (mod p_25519) \/
    (w * e EXP 2 == 1) (mod p_25519)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[CONG] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    EXPAND_TAC "f01" THEN REWRITE_TAC[WORD_OR_EQ_0] THEN
    SUBGOAL_THEN `1 = bignum_of_wordlist[word 1;word 0;word 0;word 0]`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SUBST1_TAC(SYM(ASSUME
       `bignum_of_wordlist [f_0; f_1; f_2; f_3] = f`))] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ; BIGNUM_OF_WORDLIST_EQ_0] THEN
    REWRITE_TAC[ALL; GSYM CONJ_ASSOC; GSYM RIGHT_OR_DISTRIB] THEN
    REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM RIGHT_OR_DISTRIB] THEN
    REWRITE_TAC[TAUT `~p \/ p`];
    ALL_TAC] THEN

  (*** Comparison with -1 ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (234--240) THEN
  REABBREV_TAC `fm1 = read X0 s240` THEN
  SUBGOAL_THEN
   `fm1:int64 = word 0 <=> (w * e EXP 2 == p_25519 - 1) (mod p_25519)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[CONG] THEN
    SUBGOAL_THEN `(p_25519 - 1) MOD p_25519 =
                  bignum_of_wordlist[word(2 EXP 64 - 20); word(2 EXP 64 - 1);
                                     word(2 EXP 64 - 1); word(2 EXP 63 - 1)]`
    SUBST1_TAC THENL
     [REWRITE_TAC[p_25519; bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SUBST1_TAC(SYM(ASSUME
       `bignum_of_wordlist [f_0; f_1; f_2; f_3] = f`))] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ; ALL] THEN
    EXPAND_TAC "fm1" THEN REWRITE_TAC[WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_XOR_EQ_0; GSYM CONJ_ASSOC; WORD_RULE
     `word_add x y = word 0 <=> x = word_neg y`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN

  (*** Multiplexing of s or t ***)

  BIGNUM_LDIGITIZE_TAC "s_"
   `read (memory :> bytes(word_add stackpointer (word 32),8 * 4)) s240` THEN
  BIGNUM_LDIGITIZE_TAC "t_"
   `read (memory :> bytes(word_add stackpointer (word 64),8 * 4)) s240` THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (241--251) THEN
  ABBREV_TAC `x = if (w * e EXP 2 == 0) (mod p_25519) \/
                     (w * e EXP 2 == 1) (mod p_25519)
                  then s else (s * j_25519) MOD p_25519` THEN
  SUBGOAL_THEN `x < p_25519` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN SUBST1_TAC(SYM(ASSUME `(u * e) MOD p_25519 = s`)) THEN
    COND_CASES_TAC THEN REWRITE_TAC[MOD_LT_EQ] THEN
    REWRITE_TAC[p_25519; ARITH_EQ];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 32),8 * 4)) s251 = x`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_0] THEN EXPAND_TAC "x" THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Error indication (so far) ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (252--254) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[]
   `read X21 s = a ==> read X21 s = a`)) THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_0; COND_SWAP] THEN
  REWRITE_TAC[TAUT `(if p then T else q) <=> p \/ q`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COND_SWAP] THEN
  ASM_REWRITE_TAC[GSYM WORD_BITVAL; DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[WORD_OR_CONDITIONS] THEN DISCH_TAC THEN

  (*** Computation of p_25519 - x ***)

  DISCARD_MATCHING_ASSUMPTIONS
   [`read (memory :> mm) s = if val a = 0 then x else y`] THEN
  BIGNUM_LDIGITIZE_TAC "x_"
   `read (memory :> bytes(word_add stackpointer (word 32),8 * 4)) s254` THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_EXEC [258;260;261;263] (255--263) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s258;sum_s260;sum_s261;sum_s263] = p_25519 - x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN EXPAND_TAC "x" THEN
    REWRITE_TAC[p_25519; GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final selection and return ***)

  BIGNUM_LDIGITIZE_TAC "y_"
   `read (memory :> bytes(stackpointer,8 * 4)) s263` THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_EXEC (264--283) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  REWRITE_TAC[bignum_pair_from_memory; BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[WORD_RULE `word(8 * 4) = word 32`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_0; WORD_OR_EQ_0; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[COND_SWAP; TAUT `(if p then T else q) <=> p \/ q`] THEN
  DISCARD_STATE_TAC "s283" THEN

  (*** The final mathematics ***)

  ASM_REWRITE_TAC[GSYM(REWRITE_RULE[ALL]
   (SPEC `[x_0; x_1; x_2; x_3]:int64 list` BIGNUM_OF_WORDLIST_EQ_0))] THEN
  SUBGOAL_THEN `b < 2` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN UNDISCH_TAC `n < 2 EXP 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_and x_0 (word 1)) (word b):int64 =
    word(bitval(~(x MOD 2 = b)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_AND_1_BITVAL; BIT_LSB; MOD_2_CASES] THEN
    EXPAND_TAC "x" THEN
    REWRITE_TAC[bignum_of_wordlist; EVEN_MULT; EVEN_ADD; EVEN_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `b < 2` THEN
    SPEC_TAC(`b:num`,`b:num`) THEN REWRITE_TAC[GSYM NOT_ODD; COND_SWAP] THEN
    CONV_TAC EXPAND_CASES_CONV THEN COND_CASES_TAC THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    REWRITE_TAC[WORD_OR_CONDITIONS]] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COND_RAND] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COND_RAND] THEN
  REWRITE_TAC[TAUT `(if p then q \/ r else q) <=> (q \/ p /\ r)`] THEN
  REWRITE_TAC[ARITH_RULE `x = 0 /\ ~(x MOD 2 = b) <=> x = 0 /\ ~(b = 0)`] THEN
  REWRITE_TAC[WORD_BITVAL_EQ_0] THEN
  REWRITE_TAC[MESON[]
   `[if p then x else y] = if p then [x] else [y]`] THEN
  REWRITE_TAC[MESON[]
   `CONS (if p then x else y) (if p then u else v) =
    if p then CONS x u else CONS y v`] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ASM_REWRITE_TAC[] THEN

  MP_TAC(SPECL [`y:num`; `w * e EXP 2`]
   EXISTS_IN_GROUP_CARRIER_EDWARDS25519_EULER) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    REWRITE_TAC[EXP_EXP; GSYM(CONJUNCT2 EXP)] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC CONG_EXP THEN
    MAP_EVERY EXPAND_TAC ["w"; "u"; "v"] THEN
    REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP
   (TAUT `(p <=> q) ==> ~p /\ ~q \/ p /\ q`))
  THENL
   [REWRITE_TAC[DE_MORGAN_THM; NOT_LT] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~ed25519_validencode n` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ed25519_validencode; NOT_EXISTS_THM; FORALL_PAIR_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[FORALL_PAIR_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; ed25519_encode; LET_DEF; LET_END_DEF] THEN
    SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; MOD_LT] THEN
    REWRITE_TAC[LE_0; NUM_OF_INT_OF_NUM] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `X:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `X:num` th) THEN ASM_REWRITE_TAC[]) THEN
    DISCH_THEN(fun th -> X_GEN_TAC `Y:num` THEN DISCH_TAC THEN MP_TAC th) THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> ~r <=> r ==> p ==> ~q`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 255`) THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Y < 2 EXP 255` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
      [UNDISCH_TAC `Y < p_25519` THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
       ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT; GSYM DE_MORGAN_THM] THEN
  SUBGOAL_THEN `(&x,&y) IN group_carrier edwards25519_group` ASSUME_TAC THENL
   [REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
    SUBGOAL_THEN `(v * x EXP 2 == u) (mod p_25519)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_disj o concl));
      MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
      REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM;
                  GSYM INT_REM_EQ] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[INT_REM_EQ; INTEGER_RULE
       `(e + y:int == y - &1) (mod p) <=> p divides (e + &1)`] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_DIVIDES_REFL]] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`bignum_of_wordlist l = n`] THEN
    EXPAND_TAC "x" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[DISJ_ASSOC] THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `u * (u * v) MOD p_25519 * e EXP 2` THEN CONJ_TAC THENL
       [REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC(NUMBER_RULE
        `(u == 0) (mod p) \/ (x == 1) (mod p) ==> (u * x == u) (mod p)`) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN SIMP_TAC[] THEN
      EXPAND_TAC "e" THEN REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      REWRITE_TAC[EXP_EXP; GSYM(CONJUNCT2 EXP)] THEN
      DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN
      EXPAND_TAC "w" THEN REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      REWRITE_TAC[CONG_0_DIVIDES] THEN
      SIMP_TAC[PRIME_DIVEXP_EQ; PRIME_P25519; PRIME_DIVPROD_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
      REWRITE_TAC[GSYM CONG_0_DIVIDES] THEN EXPAND_TAC "v" THEN
      REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      REWRITE_TAC[CONG_0_DIVIDES] THEN DISCH_THEN(MP_TAC o MATCH_MP(NUMBER_RULE
       `p divides n ==> coprime(n,p) ==> p = 1`)) THEN
      REWRITE_TAC[p_25519; ARITH_EQ] THEN REWRITE_TAC[GSYM p_25519] THEN
      REWRITE_TAC[num_coprime; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS];

      MAP_EVERY EXPAND_TAC ["w"; "s"] THEN REWRITE_TAC[CONG] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `(a * j EXP 2 == 1) (mod p)
        ==> ((u * v) * e EXP 2 == a) (mod p)
            ==> (v * ((u * e) * j) EXP 2 == u) (mod p)`) THEN
      REWRITE_TAC[CONG; p_25519; j_25519] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN

  ASM_SIMP_TAC[ARITH_RULE `b < 2 ==> (~(b = 0) <=> b = 1)`] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN
  ASM_CASES_TAC `x = 0 /\ b = 1` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[WORD_BITVAL_EQ_0; WORD_BITVAL_EQ_1] THENL
   [REWRITE_TAC[TAUT `~p /\ (p ==> q) <=> ~p`] THEN
    REWRITE_TAC[ed25519_validencode; NOT_EXISTS_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; ed25519_encode; LET_DEF; LET_END_DEF] THEN
    SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; MOD_LT] THEN
    REWRITE_TAC[LE_0; NUM_OF_INT_OF_NUM] THEN
    X_GEN_TAC `X:num` THEN DISCH_TAC THEN
    X_GEN_TAC `Y:num` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
    DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\x. x MOD 2 EXP 255` th) THEN
      MP_TAC(AP_TERM `\x. x DIV 2 EXP 255` th)) THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `Y < 2 EXP 255` (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [UNDISCH_TAC `Y < p_25519` THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; TAUT `p ==> ~q <=> ~(p /\ q)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `(&0:int == r) (mod p) /\ (a * x pow 2 == r) (mod p)
      ==> p divides a * x pow 2`)) THEN
    SIMP_TAC[INT_POW_2; PRIME_INT_DIVPROD_EQ; PRIME_P25519] THEN
    REWRITE_TAC[DE_MORGAN_THM; INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM EXP_2] THEN DISCH_THEN(MP_TAC o MATCH_MP(NUMBER_RULE
       `p divides n ==> coprime(n,p) ==> p = 1`)) THEN
      REWRITE_TAC[p_25519; ARITH_EQ] THEN REWRITE_TAC[GSYM p_25519] THEN
      REWRITE_TAC[num_coprime; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[EDWARDS25519_NONZERO_DENOMINATORS];
      ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT] THEN
      UNDISCH_TAC `X MOD 2 = 1` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
    REWRITE_TAC[TAUT `p /\ (p ==> q) <=> p /\ q`]] THEN

  ABBREV_TAC `x' = if x = 0 \/ x MOD 2 = b then x else p_25519 - x` THEN
  SUBGOAL_THEN `(&x',&y) IN group_carrier edwards25519_group` ASSUME_TAC THENL
   [EXPAND_TAC "x'" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    REWRITE_TAC[IN_GROUP_CARRIER_EDWARDS25519] THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_LT_SUB_RADD] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; LT_ADD; LE_0] THEN
    ASM_SIMP_TAC[LE_1; LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN

  SUBGOAL_THEN `ed25519_encode(&x',&y) = n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; ed25519_encode; LET_DEF; LET_END_DEF;
                INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
    SUBGOAL_THEN `!z. z < p_25519 ==> z < 2 EXP 255` MP_TAC THENL
     [REWRITE_TAC[p_25519] THEN ARITH_TAC; SIMP_TAC[MOD_LT]] THEN
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [ARITH_RULE `n = 2 EXP 255 * n DIV 2 EXP 255 + n MOD 2 EXP 255`] THEN
    ASM_REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "x'" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(x = 0 /\ b = 1)` THEN
      ASM_SIMP_TAC[ARITH_RULE `b < 2 ==> (~(b = 1) <=> b = 0)`] THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
      REWRITE_TAC[MOD_2_CASES; EVEN_SUB] THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[MOD_2_CASES] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `b < 2` THEN SPEC_TAC(`b:num`,`b:num`) THEN
      REWRITE_TAC[COND_SWAP] THEN CONV_TAC EXPAND_CASES_CONV THEN ARITH_TAC];
    ALL_TAC] THEN

  CONJ_TAC THENL
   [REWRITE_TAC[ed25519_validencode] THEN EXISTS_TAC `&x':int,&y:int` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ed25519_decode n = &x',&y` SUBST1_TAC THENL
   [REWRITE_TAC[ed25519_decode] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    MESON_TAC[ED25519_ENCODE_INJECTIVE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [IN_GROUP_CARRIER_EDWARDS25519]) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; ed25519_encode; LET_DEF; LET_END_DEF;
              INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  SIMP_TAC[paired; modular_encode; MOD_LT; INT_OF_NUM_REM;
           NUM_OF_INT_OF_NUM]);;

let EDWARDS25519_DECODE_SUBROUTINE_CORRECT = time prove
 (`!z c n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 224),224))
            [word pc,0x9d4; z,8 * 8; c,8 * 4] /\
        nonoverlapping (word pc,0x9d4) (z,8 * 8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; c] s /\
                  read (memory :> bytes(c,32)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word(bitval(~ed25519_validencode n)) /\
                  (ed25519_validencode n
                   ==> bignum_pair_from_memory(z,4) s =
                       paired (modular_encode (256,p_25519))
                              (ed25519_decode n)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 224),224)])`,
  ARM_ADD_RETURN_STACK_TAC
   EDWARDS25519_DECODE_EXEC EDWARDS25519_DECODE_CORRECT
   `[X19;X20;X21;X30]` 224);;
