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

(**** print_literal_from_elf "arm/curve25519/edwards25519_decode_alt.o";;
 ****)

let edwards25519_decode_alt_mc = define_assert_from_elf "edwards25519_decode_alt_mc" "arm/curve25519/edwards25519_decode_alt.o"
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
  0x94000147;       (* arm_BL (word 1308) *)
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
  0x94000118;       (* arm_BL (word 1120) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x940000af;       (* arm_BL (word 700) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800041;       (* arm_MOV X1 (rvalue (word 2)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000110;       (* arm_BL (word 1088) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x940000a7;       (* arm_BL (word 668) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000108;       (* arm_BL (word 1056) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x9400009f;       (* arm_BL (word 636) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000100;       (* arm_BL (word 1024) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000097;       (* arm_BL (word 604) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800141;       (* arm_MOV X1 (rvalue (word 10)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x940000f8;       (* arm_BL (word 992) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x9400008f;       (* arm_BL (word 572) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd28000a1;       (* arm_MOV X1 (rvalue (word 5)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x940000f0;       (* arm_BL (word 960) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000087;       (* arm_BL (word 540) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x940000e8;       (* arm_BL (word 928) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x9400007f;       (* arm_BL (word 508) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800641;       (* arm_MOV X1 (rvalue (word 50)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x940000e0;       (* arm_BL (word 896) *)
  0x910103e0;       (* arm_ADD X0 SP (rvalue (word 64)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x94000077;       (* arm_BL (word 476) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800321;       (* arm_MOV X1 (rvalue (word 25)) *)
  0x910103e2;       (* arm_ADD X2 SP (rvalue (word 64)) *)
  0x940000d8;       (* arm_BL (word 864) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x9400006f;       (* arm_BL (word 444) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800fa1;       (* arm_MOV X1 (rvalue (word 125)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x940000d0;       (* arm_BL (word 832) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000067;       (* arm_BL (word 412) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0xd2800041;       (* arm_MOV X1 (rvalue (word 2)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x940000c8;       (* arm_BL (word 800) *)
  0x910083e0;       (* arm_ADD X0 SP (rvalue (word 32)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x9400005f;       (* arm_BL (word 380) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x910083e2;       (* arm_ADD X2 SP (rvalue (word 32)) *)
  0x940000c0;       (* arm_BL (word 768) *)
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

let EDWARDS25519_DECODE_ALT_EXEC = ARM_MK_EXEC_RULE edwards25519_decode_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Local subroutine correctness.                                             *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x7b0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_alt_mc /\
                  read PC s = word(pc + 0x4c8) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x658) /\
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--67) (1--67) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (68--92) (68--92) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (93--100) (93--100) THEN
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
   (edwards25519_decode_alt_mc,EDWARDS25519_DECODE_ALT_EXEC,
    0x0,edwards25519_decode_alt_mc,LOCAL_MUL_P25519_CORRECT)
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s`;
   `pc:num`];;

let LOCAL_NSQR_P25519_CORRECT = time prove
 (`!z k x n pc.
        nonoverlapping (word pc,0x7b0) (z,8 * 4) /\
        1 <= val k /\ val k <= 1000
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_alt_mc /\
                  read PC s = word(pc + 0x65c) /\
                  C_ARGUMENTS [z; k; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x7ac) /\
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

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x668` `pc + 0x77c`
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
    ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP; EXP_1; CONG_REFL; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV;

    ALL_TAC; (*** Main loop invariant ***)

    REPEAT STRIP_TAC THEN ARM_SIM_TAC EDWARDS25519_DECODE_ALT_EXEC [1];

    GHOST_INTRO_TAC `x_0:int64` `read X2` THEN
    GHOST_INTRO_TAC `x_1:int64` `read X3` THEN
    GHOST_INTRO_TAC `x_2:int64` `read X4` THEN
    GHOST_INTRO_TAC `x_3:int64` `read X5` THEN
    ASM_REWRITE_TAC[] THEN
    ARM_ACCSIM_TAC EDWARDS25519_DECODE_ALT_EXEC (2--5) (1--12) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (3--45) (3--45) THEN
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

  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (46--70) (46--71) THEN
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
   (edwards25519_decode_alt_mc,EDWARDS25519_DECODE_ALT_EXEC,
    0x0,edwards25519_decode_alt_mc,LOCAL_NSQR_P25519_CORRECT)
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

let EDWARDS25519_DECODE_ALT_CORRECT = time prove
 (`!z c n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,192))
            [(word pc,0x7b0); (z,8 * 8); (c,8 * 4)] /\
        nonoverlapping (word pc,0x7b0) (z,8 * 8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_alt_mc /\
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
    ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--17) THEN
    REABBREV_TAC `n_0 = read X4 s17` THEN
    ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (18--33) THEN
    REABBREV_TAC `n_1 = read X5 s33` THEN
    ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (34--49) THEN
    REABBREV_TAC `n_2 = read X6 s49` THEN
    ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (50--65) THEN
    REABBREV_TAC `n_3 = read X7 s65` THEN
    ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (70--73) (66--74) THEN
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
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (1--4) THEN LOCAL_NSQR_TAC 5 THEN
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
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (10--13) (6--15) THEN
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

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (16--37) THEN
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
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (42--45) (39--47) THEN

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

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (48--51) THEN LOCAL_MUL_TAC 52 THEN
  ABBREV_TAC `w = (u * v) MOD p_25519` THEN

  (*** The power tower ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (53--57) THEN LOCAL_NSQR_TAC 58 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (59--63) THEN LOCAL_MUL_TAC 64 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (65--69) THEN LOCAL_NSQR_TAC 70 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (71--75) THEN LOCAL_MUL_TAC 76 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (77--81) THEN LOCAL_NSQR_TAC 82 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (83--87) THEN LOCAL_MUL_TAC 88 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (89--93) THEN LOCAL_NSQR_TAC 94 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (95--99) THEN LOCAL_MUL_TAC 100 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (101--105) THEN LOCAL_NSQR_TAC 106 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (107--111) THEN LOCAL_MUL_TAC 112 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (113--117) THEN LOCAL_NSQR_TAC 118 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (119--123) THEN LOCAL_MUL_TAC 124 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (125--129) THEN LOCAL_NSQR_TAC 130 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (131--135) THEN LOCAL_MUL_TAC 136 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (137--141) THEN LOCAL_NSQR_TAC 142 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (143--147) THEN LOCAL_MUL_TAC 148 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (149--153) THEN LOCAL_NSQR_TAC 154 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (155--159) THEN LOCAL_MUL_TAC 160 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (161--165) THEN LOCAL_NSQR_TAC 166 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (167--171) THEN LOCAL_MUL_TAC 172 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (173--177) THEN LOCAL_NSQR_TAC 178 THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (179--183) THEN LOCAL_MUL_TAC 184 THEN

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

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (185--189) THEN LOCAL_NSQR_TAC 190 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_1; EXP_1]) THEN
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (191--195) THEN LOCAL_MUL_TAC 196 THEN
  RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN

  (*** s = u * e ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (197--201) THEN LOCAL_MUL_TAC 202 THEN
  RULE_ASSUM_TAC(CONV_RULE MOD_DOWN_CONV) THEN
  ABBREV_TAC `s = (u * e) MOD p_25519` THEN

  (*** t = j_25519 * s ***)

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (203--225) THEN
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
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (227--233) THEN
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

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (234--240) THEN
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
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (241--251) THEN
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

  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (252--254) THEN
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
  ARM_ACCSTEPS_TAC EDWARDS25519_DECODE_ALT_EXEC [258;260;261;263] (255--263) THEN
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
  ARM_STEPS_TAC EDWARDS25519_DECODE_ALT_EXEC (264--283) THEN
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

let EDWARDS25519_DECODE_ALT_SUBROUTINE_CORRECT = time prove
 (`!z c n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 224),224))
            [word pc,0x7b0; z,8 * 8; c,8 * 4] /\
        nonoverlapping (word pc,0x7b0) (z,8 * 8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) edwards25519_decode_alt_mc /\
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
   EDWARDS25519_DECODE_ALT_EXEC EDWARDS25519_DECODE_ALT_CORRECT
   `[X19;X20;X21;X30]` 224);;
