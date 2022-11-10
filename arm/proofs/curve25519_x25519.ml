(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 *)

(* ========================================================================= *)
(* The x25519 function for curve25519.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bignum_modinv.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/x25519.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/curve25519/curve25519_x25519.o";;
 ****)

let curve25519_x25519_mc = define_assert_from_elf
  "curve25519_x25519_mc" "arm/curve25519/curve25519_x25519.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10603ff;       (* arm_SUB SP SP (rvalue (word 384)) *)
  0xaa0003f7;       (* arm_MOV X23 X0 *)
  0xa9402c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&0))) *)
  0x927df14a;       (* arm_AND X10 X10 (rvalue (word 18446744073709551608)) *)
  0xa9002fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0xa941342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&16))) *)
  0xb24201ad;       (* arm_ORR X13 X13 (rvalue (word 4611686018427387904)) *)
  0xa90137ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  0xa9402c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&0))) *)
  0xb1004d46;       (* arm_ADDS X6 X10 (rvalue (word 19)) *)
  0xba1f0167;       (* arm_ADCS X7 X11 XZR *)
  0xa941344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&16))) *)
  0x9240f9ad;       (* arm_AND X13 X13 (rvalue (word 9223372036854775807)) *)
  0xba1f0188;       (* arm_ADCS X8 X12 XZR *)
  0x92f00009;       (* arm_MOVN X9 (word 32768) 48 *)
  0xfa0901a9;       (* arm_SBCS X9 X13 X9 *)
  0x9a8a20ca;       (* arm_CSEL X10 X6 X10 Condition_CS *)
  0x9a8b20eb;       (* arm_CSEL X11 X7 X11 Condition_CS *)
  0x9a8c210c;       (* arm_CSEL X12 X8 X12 Condition_CS *)
  0x9a8d212d;       (* arm_CSEL X13 X9 X13 Condition_CS *)
  0xa9022fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&32))) *)
  0xa90337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&48))) *)
  0xd2800022;       (* arm_MOV X2 (rvalue (word 1)) *)
  0xa9147fe2;       (* arm_STP X2 XZR SP (Immediate_Offset (iword (&320))) *)
  0xa9157fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&336))) *)
  0xa90a7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&160))) *)
  0xa90b7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&176))) *)
  0xa9102fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&256))) *)
  0xa91137ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&272))) *)
  0xa9047fe2;       (* arm_STP X2 XZR SP (Immediate_Offset (iword (&64))) *)
  0xa9057fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&80))) *)
  0xaa1f03f5;       (* arm_MOV X21 XZR *)
  0xd2801fd4;       (* arm_MOV X20 (rvalue (word 254)) *)
  0xa9501be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa9440fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&64))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xa9450fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&80))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xd2f00004;       (* arm_MOVZ X4 (word 32768) 48 *)
  0xda040108;       (* arm_SBC X8 X8 X4 *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa95407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&320))) *)
  0xa94a17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&160))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa9550fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&336))) *)
  0xa94b1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&176))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0x9a070063;       (* arm_ADC X3 X3 X7 *)
  0xa90607e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xa9070fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0xa9541be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&320))) *)
  0xa94a0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&160))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&336))) *)
  0xa94b0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&176))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xd2f00004;       (* arm_MOVZ X4 (word 32768) 48 *)
  0xda040108;       (* arm_SBC X8 X8 X4 *)
  0xa90a1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa90b23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xa95007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&256))) *)
  0xa94417e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&64))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa9510fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&272))) *)
  0xa9451fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&80))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0x9a070063;       (* arm_ADC X3 X3 X7 *)
  0xa90407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9050fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&80))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
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
  0xa94713e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&112))) *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0x9bc57c6c;       (* arm_UMULH X12 X3 X5 *)
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
  0xa94713e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&112))) *)
  0xa94643ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&96))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa94803ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&128))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060006;       (* arm_SBCS X6 X0 X6 *)
  0xda9f23e0;       (* arm_CSETM X0 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca0000a5;       (* arm_EOR X5 X5 X0 *)
  0xeb0000a5;       (* arm_SUBS X5 X5 X0 *)
  0xca0000c6;       (* arm_EOR X6 X6 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xca100010;       (* arm_EOR X16 X0 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c60;       (* arm_UMULH X0 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab0001ef;       (* arm_ADDS X15 X15 X0 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0040;       (* arm_ADDS X0 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba0000a0;       (* arm_ADCS X0 X5 X0 *)
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
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x92407d65;       (* arm_AND X5 X11 (rvalue (word 4294967295)) *)
  0xd360fd64;       (* arm_LSR X4 X11 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b047c64;       (* arm_MUL X4 X3 X4 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x92407d85;       (* arm_AND X5 X12 (rvalue (word 4294967295)) *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0c7c6c;       (* arm_MUL X12 X3 X12 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x92407da5;       (* arm_AND X5 X13 (rvalue (word 4294967295)) *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0d7c6d;       (* arm_MUL X13 X3 X13 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x92407dc5;       (* arm_AND X5 X14 (rvalue (word 4294967295)) *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0e7c6e;       (* arm_MUL X14 X3 X14 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a9f37eb;       (* arm_CSET X11 Condition_CS *)
  0xd3607c85;       (* arm_LSL X5 X4 32 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x93c48185;       (* arm_EXTR X5 X12 X4 32 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x93cc81a5;       (* arm_EXTR X5 X13 X12 32 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x93cd81c5;       (* arm_EXTR X5 X14 X13 32 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0xd360fdc5;       (* arm_LSR X5 X14 32 *)
  0x9a05016b;       (* arm_ADC X11 X11 X5 *)
  0xa90c23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0xa90d2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0xf90073eb;       (* arm_STR X11 SP (Immediate_Offset (word 224)) *)
  0xd346fe80;       (* arm_LSR X0 X20 6 *)
  0xf8607be2;       (* arm_LDR X2 SP (Shiftreg_Offset X0 3) *)
  0x9ad42442;       (* arm_LSRV X2 X2 X20 *)
  0x92400042;       (* arm_AND X2 X2 (rvalue (word 1)) *)
  0xeb0202bf;       (* arm_CMP X21 X2 *)
  0xaa0203f5;       (* arm_MOV X21 X2 *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa94a0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&160))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91607e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&352))) *)
  0xa94907e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&144))) *)
  0xa94b0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&176))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91707e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&368))) *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9460fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&96))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&320))) *)
  0xa94507e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&80))) *)
  0xa9470fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91507e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&336))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa94a1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
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
  0xa94513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&80))) *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0x9bc57c6c;       (* arm_UMULH X12 X3 X5 *)
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
  0xa94513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&80))) *)
  0xa94443ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&64))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa94a03ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&160))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060006;       (* arm_SBCS X6 X0 X6 *)
  0xda9f23e0;       (* arm_CSETM X0 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca0000a5;       (* arm_EOR X5 X5 X0 *)
  0xeb0000a5;       (* arm_SUBS X5 X5 X0 *)
  0xca0000c6;       (* arm_EOR X6 X6 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xca100010;       (* arm_EOR X16 X0 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c60;       (* arm_UMULH X0 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab0001ef;       (* arm_ADDS X15 X15 X0 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0040;       (* arm_ADDS X0 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba0000a0;       (* arm_ADCS X0 X5 X0 *)
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
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x92407d65;       (* arm_AND X5 X11 (rvalue (word 4294967295)) *)
  0xd360fd64;       (* arm_LSR X4 X11 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b047c64;       (* arm_MUL X4 X3 X4 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x92407d85;       (* arm_AND X5 X12 (rvalue (word 4294967295)) *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0c7c6c;       (* arm_MUL X12 X3 X12 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x92407da5;       (* arm_AND X5 X13 (rvalue (word 4294967295)) *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0d7c6d;       (* arm_MUL X13 X3 X13 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x92407dc5;       (* arm_AND X5 X14 (rvalue (word 4294967295)) *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0e7c6e;       (* arm_MUL X14 X3 X14 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a9f37eb;       (* arm_CSET X11 Condition_CS *)
  0xd3607c85;       (* arm_LSL X5 X4 32 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x93c48185;       (* arm_EXTR X5 X12 X4 32 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x93cc81a5;       (* arm_EXTR X5 X13 X12 32 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x93cd81c5;       (* arm_EXTR X5 X14 X13 32 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0xd360fdc5;       (* arm_LSR X5 X14 32 *)
  0x9a05016b;       (* arm_ADC X11 X11 X5 *)
  0xa91023e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xa9112be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0xf90093eb;       (* arm_STR X11 SP (Immediate_Offset (word 288)) *)
  0xa9561fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&352))) *)
  0xa9572fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&368))) *)
  0x9b0a7cc4;       (* arm_MUL X4 X6 X10 *)
  0x9b0b7ce9;       (* arm_MUL X9 X7 X11 *)
  0x9bca7ccc;       (* arm_UMULH X12 X6 X10 *)
  0xeb0700cd;       (* arm_SUBS X13 X6 X7 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xeb0a0162;       (* arm_SUBS X2 X11 X10 *)
  0xda822442;       (* arm_CNEG X2 X2 Condition_CC *)
  0x9b027da8;       (* arm_MUL X8 X13 X2 *)
  0x9bc27da2;       (* arm_UMULH X2 X13 X2 *)
  0xda832063;       (* arm_CINV X3 X3 Condition_CC *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0xca030042;       (* arm_EOR X2 X2 X3 *)
  0xab0c0085;       (* arm_ADDS X5 X4 X12 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bcb7ced;       (* arm_UMULH X13 X7 X11 *)
  0xab0900a5;       (* arm_ADDS X5 X5 X9 *)
  0xba0d018c;       (* arm_ADCS X12 X12 X13 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab09018c;       (* arm_ADDS X12 X12 X9 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0x9a0301ad;       (* arm_ADC X13 X13 X3 *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0x9b067cc2;       (* arm_MUL X2 X6 X6 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cc3;       (* arm_UMULH X3 X6 X6 *)
  0x9bc77ce9;       (* arm_UMULH X9 X7 X7 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab080084;       (* arm_ADDS X4 X4 X8 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b0a7d46;       (* arm_MUL X6 X10 X10 *)
  0x9b0b7d68;       (* arm_MUL X8 X11 X11 *)
  0x9b0b7d4f;       (* arm_MUL X15 X10 X11 *)
  0x9bca7d47;       (* arm_UMULH X7 X10 X10 *)
  0x9bcb7d69;       (* arm_UMULH X9 X11 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0c00c6;       (* arm_ADDS X6 X6 X12 *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd28004ca;       (* arm_MOV X10 (rvalue (word 38)) *)
  0x92407ccb;       (* arm_AND X11 X6 (rvalue (word 4294967295)) *)
  0xd360fccc;       (* arm_LSR X12 X6 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b0c7d4c;       (* arm_MUL X12 X10 X12 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x92407ceb;       (* arm_AND X11 X7 (rvalue (word 4294967295)) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b077d47;       (* arm_MUL X7 X10 X7 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x92407d0b;       (* arm_AND X11 X8 (rvalue (word 4294967295)) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b087d48;       (* arm_MUL X8 X10 X8 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x92407d2b;       (* arm_AND X11 X9 (rvalue (word 4294967295)) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b097d49;       (* arm_MUL X9 X10 X9 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x93cc80eb;       (* arm_EXTR X11 X7 X12 32 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x93c7810b;       (* arm_EXTR X11 X8 X7 32 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x93c8812b;       (* arm_EXTR X11 X9 X8 32 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0xd360fd2b;       (* arm_LSR X11 X9 32 *)
  0x9a0b00c6;       (* arm_ADC X6 X6 X11 *)
  0xab0500bf;       (* arm_CMN X5 X5 *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0x9a0600cd;       (* arm_ADC X13 X6 X6 *)
  0xd280026a;       (* arm_MOV X10 (rvalue (word 19)) *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9160fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&352))) *)
  0xa91717e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&368))) *)
  0xa94c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xa95017e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&256))) *)
  0xeb040000;       (* arm_SUBS X0 X0 X4 *)
  0xfa050021;       (* arm_SBCS X1 X1 X5 *)
  0xa94d0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0xa9511fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&272))) *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xf94073e4;       (* arm_LDR X4 SP (Immediate_Offset (word 224)) *)
  0xf94093e5;       (* arm_LDR X5 SP (Immediate_Offset (word 288)) *)
  0xda050084;       (* arm_SBC X4 X4 X5 *)
  0x928946e7;       (* arm_MOVN X7 (word 18999) 0 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xd2803e67;       (* arm_MOV X7 (rvalue (word 499)) *)
  0x9a070084;       (* arm_ADC X4 X4 X7 *)
  0xab03007f;       (* arm_CMN X3 X3 *)
  0x9240f863;       (* arm_AND X3 X3 (rvalue (word 9223372036854775807)) *)
  0x9a040088;       (* arm_ADC X8 X4 X4 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa90407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9050fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&80))) *)
  0xa9541fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&320))) *)
  0xa9552fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&336))) *)
  0x9b0a7cc4;       (* arm_MUL X4 X6 X10 *)
  0x9b0b7ce9;       (* arm_MUL X9 X7 X11 *)
  0x9bca7ccc;       (* arm_UMULH X12 X6 X10 *)
  0xeb0700cd;       (* arm_SUBS X13 X6 X7 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xeb0a0162;       (* arm_SUBS X2 X11 X10 *)
  0xda822442;       (* arm_CNEG X2 X2 Condition_CC *)
  0x9b027da8;       (* arm_MUL X8 X13 X2 *)
  0x9bc27da2;       (* arm_UMULH X2 X13 X2 *)
  0xda832063;       (* arm_CINV X3 X3 Condition_CC *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0xca030042;       (* arm_EOR X2 X2 X3 *)
  0xab0c0085;       (* arm_ADDS X5 X4 X12 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bcb7ced;       (* arm_UMULH X13 X7 X11 *)
  0xab0900a5;       (* arm_ADDS X5 X5 X9 *)
  0xba0d018c;       (* arm_ADCS X12 X12 X13 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab09018c;       (* arm_ADDS X12 X12 X9 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0x9a0301ad;       (* arm_ADC X13 X13 X3 *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0x9b067cc2;       (* arm_MUL X2 X6 X6 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cc3;       (* arm_UMULH X3 X6 X6 *)
  0x9bc77ce9;       (* arm_UMULH X9 X7 X7 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab080084;       (* arm_ADDS X4 X4 X8 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b0a7d46;       (* arm_MUL X6 X10 X10 *)
  0x9b0b7d68;       (* arm_MUL X8 X11 X11 *)
  0x9b0b7d4f;       (* arm_MUL X15 X10 X11 *)
  0x9bca7d47;       (* arm_UMULH X7 X10 X10 *)
  0x9bcb7d69;       (* arm_UMULH X9 X11 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0c00c6;       (* arm_ADDS X6 X6 X12 *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd28004ca;       (* arm_MOV X10 (rvalue (word 38)) *)
  0x92407ccb;       (* arm_AND X11 X6 (rvalue (word 4294967295)) *)
  0xd360fccc;       (* arm_LSR X12 X6 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b0c7d4c;       (* arm_MUL X12 X10 X12 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x92407ceb;       (* arm_AND X11 X7 (rvalue (word 4294967295)) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b077d47;       (* arm_MUL X7 X10 X7 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x92407d0b;       (* arm_AND X11 X8 (rvalue (word 4294967295)) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b087d48;       (* arm_MUL X8 X10 X8 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x92407d2b;       (* arm_AND X11 X9 (rvalue (word 4294967295)) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b097d49;       (* arm_MUL X9 X10 X9 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x93cc80eb;       (* arm_EXTR X11 X7 X12 32 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x93c7810b;       (* arm_EXTR X11 X8 X7 32 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x93c8812b;       (* arm_EXTR X11 X9 X8 32 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0xd360fd2b;       (* arm_LSR X11 X9 32 *)
  0x9a0b00c6;       (* arm_ADC X6 X6 X11 *)
  0xab0500bf;       (* arm_CMN X5 X5 *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0x9a0600cd;       (* arm_ADC X13 X6 X6 *)
  0xd280026a;       (* arm_MOV X10 (rvalue (word 19)) *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9140fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&320))) *)
  0xa91517e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&336))) *)
  0xa94c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xa95017e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&256))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa94d0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0xa9511fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&272))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xf94073e4;       (* arm_LDR X4 SP (Immediate_Offset (word 224)) *)
  0xf94093e5;       (* arm_LDR X5 SP (Immediate_Offset (word 288)) *)
  0x9a050084;       (* arm_ADC X4 X4 X5 *)
  0xab03007f;       (* arm_CMN X3 X3 *)
  0x9240f863;       (* arm_AND X3 X3 (rvalue (word 9223372036854775807)) *)
  0x9a040088;       (* arm_ADC X8 X4 X4 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa91007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&256))) *)
  0xa9110fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&272))) *)
  0xa9441fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&64))) *)
  0xa9452fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&80))) *)
  0x9b0a7cc4;       (* arm_MUL X4 X6 X10 *)
  0x9b0b7ce9;       (* arm_MUL X9 X7 X11 *)
  0x9bca7ccc;       (* arm_UMULH X12 X6 X10 *)
  0xeb0700cd;       (* arm_SUBS X13 X6 X7 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xeb0a0162;       (* arm_SUBS X2 X11 X10 *)
  0xda822442;       (* arm_CNEG X2 X2 Condition_CC *)
  0x9b027da8;       (* arm_MUL X8 X13 X2 *)
  0x9bc27da2;       (* arm_UMULH X2 X13 X2 *)
  0xda832063;       (* arm_CINV X3 X3 Condition_CC *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0xca030042;       (* arm_EOR X2 X2 X3 *)
  0xab0c0085;       (* arm_ADDS X5 X4 X12 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bcb7ced;       (* arm_UMULH X13 X7 X11 *)
  0xab0900a5;       (* arm_ADDS X5 X5 X9 *)
  0xba0d018c;       (* arm_ADCS X12 X12 X13 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab09018c;       (* arm_ADDS X12 X12 X9 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0x9a0301ad;       (* arm_ADC X13 X13 X3 *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0x9b067cc2;       (* arm_MUL X2 X6 X6 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cc3;       (* arm_UMULH X3 X6 X6 *)
  0x9bc77ce9;       (* arm_UMULH X9 X7 X7 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab080084;       (* arm_ADDS X4 X4 X8 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b0a7d46;       (* arm_MUL X6 X10 X10 *)
  0x9b0b7d68;       (* arm_MUL X8 X11 X11 *)
  0x9b0b7d4f;       (* arm_MUL X15 X10 X11 *)
  0x9bca7d47;       (* arm_UMULH X7 X10 X10 *)
  0x9bcb7d69;       (* arm_UMULH X9 X11 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0c00c6;       (* arm_ADDS X6 X6 X12 *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd28004ca;       (* arm_MOV X10 (rvalue (word 38)) *)
  0x92407ccb;       (* arm_AND X11 X6 (rvalue (word 4294967295)) *)
  0xd360fccc;       (* arm_LSR X12 X6 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b0c7d4c;       (* arm_MUL X12 X10 X12 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x92407ceb;       (* arm_AND X11 X7 (rvalue (word 4294967295)) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b077d47;       (* arm_MUL X7 X10 X7 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x92407d0b;       (* arm_AND X11 X8 (rvalue (word 4294967295)) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b087d48;       (* arm_MUL X8 X10 X8 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x92407d2b;       (* arm_AND X11 X9 (rvalue (word 4294967295)) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b097d49;       (* arm_MUL X9 X10 X9 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x93cc80eb;       (* arm_EXTR X11 X7 X12 32 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x93c7810b;       (* arm_EXTR X11 X8 X7 32 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x93c8812b;       (* arm_EXTR X11 X9 X8 32 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0xd360fd2b;       (* arm_LSR X11 X9 32 *)
  0x9a0b00c6;       (* arm_ADC X6 X6 X11 *)
  0xab0500bf;       (* arm_CMN X5 X5 *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0x9a0600cd;       (* arm_ADC X13 X6 X6 *)
  0xd280026a;       (* arm_MOV X10 (rvalue (word 19)) *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9040fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&64))) *)
  0xa90517e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&80))) *)
  0xa9541be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&320))) *)
  0xa9560fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&352))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&336))) *)
  0xa9570fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&368))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa90c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa9501fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&256))) *)
  0xa9512fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&272))) *)
  0x9b0a7cc4;       (* arm_MUL X4 X6 X10 *)
  0x9b0b7ce9;       (* arm_MUL X9 X7 X11 *)
  0x9bca7ccc;       (* arm_UMULH X12 X6 X10 *)
  0xeb0700cd;       (* arm_SUBS X13 X6 X7 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xeb0a0162;       (* arm_SUBS X2 X11 X10 *)
  0xda822442;       (* arm_CNEG X2 X2 Condition_CC *)
  0x9b027da8;       (* arm_MUL X8 X13 X2 *)
  0x9bc27da2;       (* arm_UMULH X2 X13 X2 *)
  0xda832063;       (* arm_CINV X3 X3 Condition_CC *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0xca030042;       (* arm_EOR X2 X2 X3 *)
  0xab0c0085;       (* arm_ADDS X5 X4 X12 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bcb7ced;       (* arm_UMULH X13 X7 X11 *)
  0xab0900a5;       (* arm_ADDS X5 X5 X9 *)
  0xba0d018c;       (* arm_ADCS X12 X12 X13 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab09018c;       (* arm_ADDS X12 X12 X9 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0x9a0301ad;       (* arm_ADC X13 X13 X3 *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0x9b067cc2;       (* arm_MUL X2 X6 X6 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cc3;       (* arm_UMULH X3 X6 X6 *)
  0x9bc77ce9;       (* arm_UMULH X9 X7 X7 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab080084;       (* arm_ADDS X4 X4 X8 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b0a7d46;       (* arm_MUL X6 X10 X10 *)
  0x9b0b7d68;       (* arm_MUL X8 X11 X11 *)
  0x9b0b7d4f;       (* arm_MUL X15 X10 X11 *)
  0x9bca7d47;       (* arm_UMULH X7 X10 X10 *)
  0x9bcb7d69;       (* arm_UMULH X9 X11 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0c00c6;       (* arm_ADDS X6 X6 X12 *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd28004ca;       (* arm_MOV X10 (rvalue (word 38)) *)
  0x92407ccb;       (* arm_AND X11 X6 (rvalue (word 4294967295)) *)
  0xd360fccc;       (* arm_LSR X12 X6 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b0c7d4c;       (* arm_MUL X12 X10 X12 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x92407ceb;       (* arm_AND X11 X7 (rvalue (word 4294967295)) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b077d47;       (* arm_MUL X7 X10 X7 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x92407d0b;       (* arm_AND X11 X8 (rvalue (word 4294967295)) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b087d48;       (* arm_MUL X8 X10 X8 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x92407d2b;       (* arm_AND X11 X9 (rvalue (word 4294967295)) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b097d49;       (* arm_MUL X9 X10 X9 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x93cc80eb;       (* arm_EXTR X11 X7 X12 32 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x93c7810b;       (* arm_EXTR X11 X8 X7 32 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x93c8812b;       (* arm_EXTR X11 X9 X8 32 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0xd360fd2b;       (* arm_LSR X11 X9 32 *)
  0x9a0b00c6;       (* arm_ADC X6 X6 X11 *)
  0xab0500bf;       (* arm_CMN X5 X5 *)
  0xb24100a5;       (* arm_ORR X5 X5 (rvalue (word 9223372036854775808)) *)
  0x9a0600cd;       (* arm_ADC X13 X6 X6 *)
  0xd280026a;       (* arm_MOV X10 (rvalue (word 19)) *)
  0x9b0d294b;       (* arm_MADD X11 X10 X13 X10 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a9f314a;       (* arm_CSEL X10 X10 XZR Condition_CC *)
  0xeb0a0042;       (* arm_SUBS X2 X2 X10 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xa9100fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&256))) *)
  0xa91117e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&272))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0x9b077c23;       (* arm_MUL X3 X1 X7 *)
  0x9b087c24;       (* arm_MUL X4 X1 X8 *)
  0x9b097c25;       (* arm_MUL X5 X1 X9 *)
  0x9b0a7c26;       (* arm_MUL X6 X1 X10 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa95623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&352))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa95723e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&368))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0600df;       (* arm_CMN X6 X6 *)
  0x9240f8c6;       (* arm_AND X6 X6 (rvalue (word 9223372036854775807)) *)
  0x9a0a0148;       (* arm_ADC X8 X10 X10 *)
  0xd2800269;       (* arm_MOV X9 (rvalue (word 19)) *)
  0x9b097d07;       (* arm_MUL X7 X8 X9 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa95413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&320))) *)
  0xa9561be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&352))) *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
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
  0xa95513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&336))) *)
  0xa9571be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&368))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0x9bc57c6c;       (* arm_UMULH X12 X3 X5 *)
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
  0xa95513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&336))) *)
  0xa95443ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&320))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa95603ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&352))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060006;       (* arm_SBCS X6 X0 X6 *)
  0xda9f23e0;       (* arm_CSETM X0 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca0000a5;       (* arm_EOR X5 X5 X0 *)
  0xeb0000a5;       (* arm_SUBS X5 X5 X0 *)
  0xca0000c6;       (* arm_EOR X6 X6 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xca100010;       (* arm_EOR X16 X0 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c60;       (* arm_UMULH X0 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab0001ef;       (* arm_ADDS X15 X15 X0 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0040;       (* arm_ADDS X0 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba0000a0;       (* arm_ADCS X0 X5 X0 *)
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
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x92407d65;       (* arm_AND X5 X11 (rvalue (word 4294967295)) *)
  0xd360fd64;       (* arm_LSR X4 X11 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b047c64;       (* arm_MUL X4 X3 X4 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x92407d85;       (* arm_AND X5 X12 (rvalue (word 4294967295)) *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0c7c6c;       (* arm_MUL X12 X3 X12 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x92407da5;       (* arm_AND X5 X13 (rvalue (word 4294967295)) *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0d7c6d;       (* arm_MUL X13 X3 X13 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x92407dc5;       (* arm_AND X5 X14 (rvalue (word 4294967295)) *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0e7c6e;       (* arm_MUL X14 X3 X14 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a9f37eb;       (* arm_CSET X11 Condition_CS *)
  0xd3607c85;       (* arm_LSL X5 X4 32 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x93c48185;       (* arm_EXTR X5 X12 X4 32 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x93cc81a5;       (* arm_EXTR X5 X13 X12 32 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x93cd81c5;       (* arm_EXTR X5 X14 X13 32 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0xd360fdc5;       (* arm_LSR X5 X14 32 *)
  0x9a05016b;       (* arm_ADC X11 X11 X5 *)
  0xab0a015f;       (* arm_CMN X10 X10 *)
  0xb241014a;       (* arm_ORR X10 X10 (rvalue (word 9223372036854775808)) *)
  0x9a0b0160;       (* arm_ADC X0 X11 X11 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b000c65;       (* arm_MADD X5 X3 X0 X3 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a9f3063;       (* arm_CSEL X3 X3 XZR Condition_CC *)
  0xeb0300e7;       (* arm_SUBS X7 X7 X3 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0x9240f94a;       (* arm_AND X10 X10 (rvalue (word 9223372036854775807)) *)
  0xa91423e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&320))) *)
  0xa9152be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&336))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa9421be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
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
  0xa94513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&80))) *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0x9bc57c6c;       (* arm_UMULH X12 X3 X5 *)
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
  0xa94513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&80))) *)
  0xa94443ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&64))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa94203ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&32))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060006;       (* arm_SBCS X6 X0 X6 *)
  0xda9f23e0;       (* arm_CSETM X0 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca0000a5;       (* arm_EOR X5 X5 X0 *)
  0xeb0000a5;       (* arm_SUBS X5 X5 X0 *)
  0xca0000c6;       (* arm_EOR X6 X6 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xca100010;       (* arm_EOR X16 X0 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c60;       (* arm_UMULH X0 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab0001ef;       (* arm_ADDS X15 X15 X0 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0040;       (* arm_ADDS X0 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba0000a0;       (* arm_ADCS X0 X5 X0 *)
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
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x92407d65;       (* arm_AND X5 X11 (rvalue (word 4294967295)) *)
  0xd360fd64;       (* arm_LSR X4 X11 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b047c64;       (* arm_MUL X4 X3 X4 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x92407d85;       (* arm_AND X5 X12 (rvalue (word 4294967295)) *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0c7c6c;       (* arm_MUL X12 X3 X12 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x92407da5;       (* arm_AND X5 X13 (rvalue (word 4294967295)) *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0d7c6d;       (* arm_MUL X13 X3 X13 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x92407dc5;       (* arm_AND X5 X14 (rvalue (word 4294967295)) *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0e7c6e;       (* arm_MUL X14 X3 X14 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a9f37eb;       (* arm_CSET X11 Condition_CS *)
  0xd3607c85;       (* arm_LSL X5 X4 32 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x93c48185;       (* arm_EXTR X5 X12 X4 32 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x93cc81a5;       (* arm_EXTR X5 X13 X12 32 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x93cd81c5;       (* arm_EXTR X5 X14 X13 32 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0xd360fdc5;       (* arm_LSR X5 X14 32 *)
  0x9a05016b;       (* arm_ADC X11 X11 X5 *)
  0xab0a015f;       (* arm_CMN X10 X10 *)
  0xb241014a;       (* arm_ORR X10 X10 (rvalue (word 9223372036854775808)) *)
  0x9a0b0160;       (* arm_ADC X0 X11 X11 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b000c65;       (* arm_MADD X5 X3 X0 X3 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a9f3063;       (* arm_CSEL X3 X3 XZR Condition_CC *)
  0xeb0300e7;       (* arm_SUBS X7 X7 X3 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0x9240f94a;       (* arm_AND X10 X10 (rvalue (word 9223372036854775807)) *)
  0xa90423e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0xa9052be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
  0xa94a1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
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
  0xa94d13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&208))) *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0x9bc57c6c;       (* arm_UMULH X12 X3 X5 *)
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
  0xa94d13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&208))) *)
  0xa94c43ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&192))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa94a03ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&160))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060006;       (* arm_SBCS X6 X0 X6 *)
  0xda9f23e0;       (* arm_CSETM X0 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca0000a5;       (* arm_EOR X5 X5 X0 *)
  0xeb0000a5;       (* arm_SUBS X5 X5 X0 *)
  0xca0000c6;       (* arm_EOR X6 X6 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xca100010;       (* arm_EOR X16 X0 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c60;       (* arm_UMULH X0 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab0001ef;       (* arm_ADDS X15 X15 X0 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0040;       (* arm_ADDS X0 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba0000a0;       (* arm_ADCS X0 X5 X0 *)
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
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x92407d65;       (* arm_AND X5 X11 (rvalue (word 4294967295)) *)
  0xd360fd64;       (* arm_LSR X4 X11 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b047c64;       (* arm_MUL X4 X3 X4 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x92407d85;       (* arm_AND X5 X12 (rvalue (word 4294967295)) *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0c7c6c;       (* arm_MUL X12 X3 X12 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x92407da5;       (* arm_AND X5 X13 (rvalue (word 4294967295)) *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0d7c6d;       (* arm_MUL X13 X3 X13 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x92407dc5;       (* arm_AND X5 X14 (rvalue (word 4294967295)) *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0e7c6e;       (* arm_MUL X14 X3 X14 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a9f37eb;       (* arm_CSET X11 Condition_CS *)
  0xd3607c85;       (* arm_LSL X5 X4 32 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x93c48185;       (* arm_EXTR X5 X12 X4 32 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x93cc81a5;       (* arm_EXTR X5 X13 X12 32 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x93cd81c5;       (* arm_EXTR X5 X14 X13 32 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0xd360fdc5;       (* arm_LSR X5 X14 32 *)
  0x9a05016b;       (* arm_ADC X11 X11 X5 *)
  0xab0a015f;       (* arm_CMN X10 X10 *)
  0xb241014a;       (* arm_ORR X10 X10 (rvalue (word 9223372036854775808)) *)
  0x9a0b0160;       (* arm_ADC X0 X11 X11 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b000c65;       (* arm_MADD X5 X3 X0 X3 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a9f3063;       (* arm_CSEL X3 X3 XZR Condition_CC *)
  0xeb0300e7;       (* arm_SUBS X7 X7 X3 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0x9240f94a;       (* arm_AND X10 X10 (rvalue (word 9223372036854775807)) *)
  0xa90a23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xf1000694;       (* arm_SUBS X20 X20 (rvalue (word 1)) *)
  0x54ff51a2;       (* arm_BCS (word 2091572) *)
  0x92800240;       (* arm_MOVN X0 (word 18) 0 *)
  0x92800001;       (* arm_MOVN X1 (word 0) 0 *)
  0x92f00002;       (* arm_MOVN X2 (word 32768) 48 *)
  0xa90607e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xa9070be1;       (* arm_STP X1 X2 SP (Immediate_Offset (iword (&112))) *)
  0xd2800080;       (* arm_MOV X0 (rvalue (word 4)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x910183e3;       (* arm_ADD X3 SP (rvalue (word 96)) *)
  0x910303e4;       (* arm_ADD X4 SP (rvalue (word 192)) *)
  0xd37df00a;       (* arm_LSL X10 X0 3 *)
  0x8b0a0095;       (* arm_ADD X21 X4 X10 *)
  0x8b0a02b6;       (* arm_ADD X22 X21 X10 *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xf86a784b;       (* arm_LDR X11 X2 (Shiftreg_Offset X10 3) *)
  0xf86a786c;       (* arm_LDR X12 X3 (Shiftreg_Offset X10 3) *)
  0xf82a7aab;       (* arm_STR X11 X21 (Shiftreg_Offset X10 3) *)
  0xf82a7acc;       (* arm_STR X12 X22 (Shiftreg_Offset X10 3) *)
  0xf82a788c;       (* arm_STR X12 X4 (Shiftreg_Offset X10 3) *)
  0xf82a783f;       (* arm_STR XZR X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xeb00015f;       (* arm_CMP X10 X0 *)
  0x54ffff03;       (* arm_BCC (word 2097120) *)
  0xf940008b;       (* arm_LDR X11 X4 (Immediate_Offset (word 0)) *)
  0xd100056c;       (* arm_SUB X12 X11 (rvalue (word 1)) *)
  0xf900008c;       (* arm_STR X12 X4 (Immediate_Offset (word 0)) *)
  0xd37ef574;       (* arm_LSL X20 X11 2 *)
  0xcb140174;       (* arm_SUB X20 X11 X20 *)
  0xd27f0294;       (* arm_EOR X20 X20 (rvalue (word 2)) *)
  0xd280002c;       (* arm_MOV X12 (rvalue (word 1)) *)
  0x9b14316c;       (* arm_MADD X12 X11 X20 X12 *)
  0x9b0c7d8b;       (* arm_MUL X11 X12 X12 *)
  0x9b145194;       (* arm_MADD X20 X12 X20 X20 *)
  0x9b0b7d6c;       (* arm_MUL X12 X11 X11 *)
  0x9b145174;       (* arm_MADD X20 X11 X20 X20 *)
  0x9b0c7d8b;       (* arm_MUL X11 X12 X12 *)
  0x9b145194;       (* arm_MADD X20 X12 X20 X20 *)
  0x9b145174;       (* arm_MADD X20 X11 X20 X20 *)
  0xd379e002;       (* arm_LSL X2 X0 7 *)
  0x9100fc4a;       (* arm_ADD X10 X2 (rvalue (word 63)) *)
  0xd346fd45;       (* arm_LSR X5 X10 6 *)
  0xeb0000bf;       (* arm_CMP X5 X0 *)
  0x9a852005;       (* arm_CSEL X5 X0 X5 Condition_CS *)
  0xaa1f03ed;       (* arm_MOV X13 XZR *)
  0xaa1f03ef;       (* arm_MOV X15 XZR *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xaa1f03f0;       (* arm_MOV X16 XZR *)
  0xaa1f03f3;       (* arm_MOV X19 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xf86a7aab;       (* arm_LDR X11 X21 (Shiftreg_Offset X10 3) *)
  0xf86a7acc;       (* arm_LDR X12 X22 (Shiftreg_Offset X10 3) *)
  0xaa0c0171;       (* arm_ORR X17 X11 X12 *)
  0xeb1f023f;       (* arm_CMP X17 XZR *)
  0x8a0d0271;       (* arm_AND X17 X19 X13 *)
  0x9a8f122f;       (* arm_CSEL X15 X17 X15 Condition_NE *)
  0x8a0e0271;       (* arm_AND X17 X19 X14 *)
  0x9a901230;       (* arm_CSEL X16 X17 X16 Condition_NE *)
  0x9a8d116d;       (* arm_CSEL X13 X11 X13 Condition_NE *)
  0x9a8e118e;       (* arm_CSEL X14 X12 X14 Condition_NE *)
  0xda9f03f3;       (* arm_CSETM X19 Condition_NE *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xeb05015f;       (* arm_CMP X10 X5 *)
  0x54fffe63;       (* arm_BCC (word 2097100) *)
  0xaa0e01ab;       (* arm_ORR X11 X13 X14 *)
  0xdac0116c;       (* arm_CLZ X12 X11 *)
  0xeb0c03f1;       (* arm_NEGS X17 X12 *)
  0x9acc21ad;       (* arm_LSLV X13 X13 X12 *)
  0x9a9f11ef;       (* arm_CSEL X15 X15 XZR Condition_NE *)
  0x9acc21ce;       (* arm_LSLV X14 X14 X12 *)
  0x9a9f1210;       (* arm_CSEL X16 X16 XZR Condition_NE *)
  0x9ad125ef;       (* arm_LSRV X15 X15 X17 *)
  0x9ad12610;       (* arm_LSRV X16 X16 X17 *)
  0xaa0f01ad;       (* arm_ORR X13 X13 X15 *)
  0xaa1001ce;       (* arm_ORR X14 X14 X16 *)
  0xf94002af;       (* arm_LDR X15 X21 (Immediate_Offset (word 0)) *)
  0xf94002d0;       (* arm_LDR X16 X22 (Immediate_Offset (word 0)) *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xd2800029;       (* arm_MOV X9 (rvalue (word 1)) *)
  0xd280074a;       (* arm_MOV X10 (rvalue (word 58)) *)
  0xf24001ff;       (* arm_TST X15 (rvalue (word 1)) *)
  0x9a9f11cb;       (* arm_CSEL X11 X14 XZR Condition_NE *)
  0x9a9f120c;       (* arm_CSEL X12 X16 XZR Condition_NE *)
  0x9a9f1111;       (* arm_CSEL X17 X8 XZR Condition_NE *)
  0x9a9f1133;       (* arm_CSEL X19 X9 XZR Condition_NE *)
  0xfa4e11a2;       (* arm_CCMP X13 X14 (word 2) Condition_NE *)
  0xcb0b01ab;       (* arm_SUB X11 X13 X11 *)
  0xcb0c01ec;       (* arm_SUB X12 X15 X12 *)
  0x9a8d21ce;       (* arm_CSEL X14 X14 X13 Condition_CS *)
  0xda8b256b;       (* arm_CNEG X11 X11 Condition_CC *)
  0x9a8f2210;       (* arm_CSEL X16 X16 X15 Condition_CS *)
  0xda8c258f;       (* arm_CNEG X15 X12 Condition_CC *)
  0x9a862108;       (* arm_CSEL X8 X8 X6 Condition_CS *)
  0x9a872129;       (* arm_CSEL X9 X9 X7 Condition_CS *)
  0xf27f019f;       (* arm_TST X12 (rvalue (word 2)) *)
  0x8b1100c6;       (* arm_ADD X6 X6 X17 *)
  0x8b1300e7;       (* arm_ADD X7 X7 X19 *)
  0xd341fd6d;       (* arm_LSR X13 X11 1 *)
  0xd341fdef;       (* arm_LSR X15 X15 1 *)
  0x8b080108;       (* arm_ADD X8 X8 X8 *)
  0x8b090129;       (* arm_ADD X9 X9 X9 *)
  0xd100054a;       (* arm_SUB X10 X10 (rvalue (word 1)) *)
  0xb5fffd6a;       (* arm_CBNZ X10 (word 2097068) *)
  0xaa1f03ed;       (* arm_MOV X13 XZR *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xaa1f03f1;       (* arm_MOV X17 XZR *)
  0xaa1f03f3;       (* arm_MOV X19 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xf86a788b;       (* arm_LDR X11 X4 (Shiftreg_Offset X10 3) *)
  0xf86a782c;       (* arm_LDR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9b0b7ccf;       (* arm_MUL X15 X6 X11 *)
  0x9b0c7cf0;       (* arm_MUL X16 X7 X12 *)
  0xab0d01ef;       (* arm_ADDS X15 X15 X13 *)
  0x9bcb7ccd;       (* arm_UMULH X13 X6 X11 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab1001ef;       (* arm_ADDS X15 X15 X16 *)
  0x93d1e9f1;       (* arm_EXTR X17 X15 X17 58 *)
  0xf82a7891;       (* arm_STR X17 X4 (Shiftreg_Offset X10 3) *)
  0xaa0f03f1;       (* arm_MOV X17 X15 *)
  0x9bcc7cef;       (* arm_UMULH X15 X7 X12 *)
  0x9a0f01ad;       (* arm_ADC X13 X13 X15 *)
  0x9b0b7d0f;       (* arm_MUL X15 X8 X11 *)
  0x9b0c7d30;       (* arm_MUL X16 X9 X12 *)
  0xab0e01ef;       (* arm_ADDS X15 X15 X14 *)
  0x9bcb7d0e;       (* arm_UMULH X14 X8 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab1001ef;       (* arm_ADDS X15 X15 X16 *)
  0x93d3e9f3;       (* arm_EXTR X19 X15 X19 58 *)
  0xf82a7833;       (* arm_STR X19 X1 (Shiftreg_Offset X10 3) *)
  0xaa0f03f3;       (* arm_MOV X19 X15 *)
  0x9bcc7d2f;       (* arm_UMULH X15 X9 X12 *)
  0x9a0f01ce;       (* arm_ADC X14 X14 X15 *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xeb00015f;       (* arm_CMP X10 X0 *)
  0x54fffcc3;       (* arm_BCC (word 2097048) *)
  0x93d1e9ad;       (* arm_EXTR X13 X13 X17 58 *)
  0x93d3e9ce;       (* arm_EXTR X14 X14 X19 58 *)
  0xf940008b;       (* arm_LDR X11 X4 (Immediate_Offset (word 0)) *)
  0x9b147d71;       (* arm_MUL X17 X11 X20 *)
  0xf940006c;       (* arm_LDR X12 X3 (Immediate_Offset (word 0)) *)
  0x9b0c7e2f;       (* arm_MUL X15 X17 X12 *)
  0x9bcc7e30;       (* arm_UMULH X16 X17 X12 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xd280002a;       (* arm_MOV X10 (rvalue (word 1)) *)
  0xd100040b;       (* arm_SUB X11 X0 (rvalue (word 1)) *)
  0xb40001ab;       (* arm_CBZ X11 (word 52) *)
  0xf86a786b;       (* arm_LDR X11 X3 (Shiftreg_Offset X10 3) *)
  0xf86a788c;       (* arm_LDR X12 X4 (Shiftreg_Offset X10 3) *)
  0x9b0b7e2f;       (* arm_MUL X15 X17 X11 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9bcb7e30;       (* arm_UMULH X16 X17 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab0f018c;       (* arm_ADDS X12 X12 X15 *)
  0xd100054f;       (* arm_SUB X15 X10 (rvalue (word 1)) *)
  0xf82f788c;       (* arm_STR X12 X4 (Shiftreg_Offset X15 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5fffeab;       (* arm_CBNZ X11 (word 2097108) *)
  0xba0d0210;       (* arm_ADCS X16 X16 X13 *)
  0x9a1f03ed;       (* arm_ADC X13 XZR XZR *)
  0xd100054f;       (* arm_SUB X15 X10 (rvalue (word 1)) *)
  0xf82f7890;       (* arm_STR X16 X4 (Shiftreg_Offset X15 3) *)
  0xeb1f03ea;       (* arm_NEGS X10 XZR *)
  0xf86a788b;       (* arm_LDR X11 X4 (Shiftreg_Offset X10 3) *)
  0xf86a786c;       (* arm_LDR X12 X3 (Shiftreg_Offset X10 3) *)
  0xfa0c017f;       (* arm_SBCS XZR X11 X12 *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5ffff6b;       (* arm_CBNZ X11 (word 2097132) *)
  0xfa1f01bf;       (* arm_SBCS XZR X13 XZR *)
  0xda9f33ed;       (* arm_CSETM X13 Condition_CS *)
  0xeb1f03ea;       (* arm_NEGS X10 XZR *)
  0xf86a788b;       (* arm_LDR X11 X4 (Shiftreg_Offset X10 3) *)
  0xf86a786c;       (* arm_LDR X12 X3 (Shiftreg_Offset X10 3) *)
  0x8a0d018c;       (* arm_AND X12 X12 X13 *)
  0xfa0c016b;       (* arm_SBCS X11 X11 X12 *)
  0xf82a788b;       (* arm_STR X11 X4 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5ffff2b;       (* arm_CBNZ X11 (word 2097124) *)
  0xf940002b;       (* arm_LDR X11 X1 (Immediate_Offset (word 0)) *)
  0x9b147d71;       (* arm_MUL X17 X11 X20 *)
  0xf940006c;       (* arm_LDR X12 X3 (Immediate_Offset (word 0)) *)
  0x9b0c7e2f;       (* arm_MUL X15 X17 X12 *)
  0x9bcc7e30;       (* arm_UMULH X16 X17 X12 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xd280002a;       (* arm_MOV X10 (rvalue (word 1)) *)
  0xd100040b;       (* arm_SUB X11 X0 (rvalue (word 1)) *)
  0xb40001ab;       (* arm_CBZ X11 (word 52) *)
  0xf86a786b;       (* arm_LDR X11 X3 (Shiftreg_Offset X10 3) *)
  0xf86a782c;       (* arm_LDR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9b0b7e2f;       (* arm_MUL X15 X17 X11 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9bcb7e30;       (* arm_UMULH X16 X17 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab0f018c;       (* arm_ADDS X12 X12 X15 *)
  0xd100054f;       (* arm_SUB X15 X10 (rvalue (word 1)) *)
  0xf82f782c;       (* arm_STR X12 X1 (Shiftreg_Offset X15 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5fffeab;       (* arm_CBNZ X11 (word 2097108) *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xd100054f;       (* arm_SUB X15 X10 (rvalue (word 1)) *)
  0xf82f7830;       (* arm_STR X16 X1 (Shiftreg_Offset X15 3) *)
  0xeb1f03ea;       (* arm_NEGS X10 XZR *)
  0xf86a782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X10 3) *)
  0xf86a786c;       (* arm_LDR X12 X3 (Shiftreg_Offset X10 3) *)
  0xfa0c017f;       (* arm_SBCS XZR X11 X12 *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5ffff6b;       (* arm_CBNZ X11 (word 2097132) *)
  0xfa1f01df;       (* arm_SBCS XZR X14 XZR *)
  0xda9f33ee;       (* arm_CSETM X14 Condition_CS *)
  0xeb1f03ea;       (* arm_NEGS X10 XZR *)
  0xf86a782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X10 3) *)
  0xf86a786c;       (* arm_LDR X12 X3 (Shiftreg_Offset X10 3) *)
  0x8a0e018c;       (* arm_AND X12 X12 X14 *)
  0xfa0c016b;       (* arm_SBCS X11 X11 X12 *)
  0xf82a782b;       (* arm_STR X11 X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5ffff2b;       (* arm_CBNZ X11 (word 2097124) *)
  0xaa1f03ed;       (* arm_MOV X13 XZR *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xaa1f03f1;       (* arm_MOV X17 XZR *)
  0xaa1f03f3;       (* arm_MOV X19 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xf86a7aab;       (* arm_LDR X11 X21 (Shiftreg_Offset X10 3) *)
  0xf86a7acc;       (* arm_LDR X12 X22 (Shiftreg_Offset X10 3) *)
  0x9b0b7ccf;       (* arm_MUL X15 X6 X11 *)
  0x9b0c7cf0;       (* arm_MUL X16 X7 X12 *)
  0xab0d01ef;       (* arm_ADDS X15 X15 X13 *)
  0x9bcb7ccd;       (* arm_UMULH X13 X6 X11 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xeb1001ef;       (* arm_SUBS X15 X15 X16 *)
  0xf82a7aaf;       (* arm_STR X15 X21 (Shiftreg_Offset X10 3) *)
  0x9bcc7cef;       (* arm_UMULH X15 X7 X12 *)
  0xcb1101f1;       (* arm_SUB X17 X15 X17 *)
  0xfa1101ad;       (* arm_SBCS X13 X13 X17 *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0x9b0b7d0f;       (* arm_MUL X15 X8 X11 *)
  0x9b0c7d30;       (* arm_MUL X16 X9 X12 *)
  0xab0e01ef;       (* arm_ADDS X15 X15 X14 *)
  0x9bcb7d0e;       (* arm_UMULH X14 X8 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xeb1001ef;       (* arm_SUBS X15 X15 X16 *)
  0xf82a7acf;       (* arm_STR X15 X22 (Shiftreg_Offset X10 3) *)
  0x9bcc7d2f;       (* arm_UMULH X15 X9 X12 *)
  0xcb1301f3;       (* arm_SUB X19 X15 X19 *)
  0xfa1301ce;       (* arm_SBCS X14 X14 X19 *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xeb05015f;       (* arm_CMP X10 X5 *)
  0x54fffcc3;       (* arm_BCC (word 2097048) *)
  0xab11023f;       (* arm_CMN X17 X17 *)
  0xf94002af;       (* arm_LDR X15 X21 (Immediate_Offset (word 0)) *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xd10004a6;       (* arm_SUB X6 X5 (rvalue (word 1)) *)
  0xb4000166;       (* arm_CBZ X6 (word 44) *)
  0x9100214b;       (* arm_ADD X11 X10 (rvalue (word 8)) *)
  0xf86b6aac;       (* arm_LDR X12 X21 (Register_Offset X11) *)
  0x93cfe98f;       (* arm_EXTR X15 X12 X15 58 *)
  0xca1101ef;       (* arm_EOR X15 X15 X17 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xf82a6aaf;       (* arm_STR X15 X21 (Register_Offset X10) *)
  0xaa0c03ef;       (* arm_MOV X15 X12 *)
  0x9100214a;       (* arm_ADD X10 X10 (rvalue (word 8)) *)
  0xd10004c6;       (* arm_SUB X6 X6 (rvalue (word 1)) *)
  0xb5fffee6;       (* arm_CBNZ X6 (word 2097116) *)
  0x93cfe9af;       (* arm_EXTR X15 X13 X15 58 *)
  0xca1101ef;       (* arm_EOR X15 X15 X17 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xf82a6aaf;       (* arm_STR X15 X21 (Register_Offset X10) *)
  0xab13027f;       (* arm_CMN X19 X19 *)
  0xf94002cf;       (* arm_LDR X15 X22 (Immediate_Offset (word 0)) *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xd10004a6;       (* arm_SUB X6 X5 (rvalue (word 1)) *)
  0xb4000166;       (* arm_CBZ X6 (word 44) *)
  0x9100214b;       (* arm_ADD X11 X10 (rvalue (word 8)) *)
  0xf86b6acc;       (* arm_LDR X12 X22 (Register_Offset X11) *)
  0x93cfe98f;       (* arm_EXTR X15 X12 X15 58 *)
  0xca1301ef;       (* arm_EOR X15 X15 X19 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xf82a6acf;       (* arm_STR X15 X22 (Register_Offset X10) *)
  0xaa0c03ef;       (* arm_MOV X15 X12 *)
  0x9100214a;       (* arm_ADD X10 X10 (rvalue (word 8)) *)
  0xd10004c6;       (* arm_SUB X6 X6 (rvalue (word 1)) *)
  0xb5fffee6;       (* arm_CBNZ X6 (word 2097116) *)
  0x93cfe9cf;       (* arm_EXTR X15 X14 X15 58 *)
  0xca1301ef;       (* arm_EOR X15 X15 X19 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xf82a6acf;       (* arm_STR X15 X22 (Register_Offset X10) *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xab11023f;       (* arm_CMN X17 X17 *)
  0xf86a786b;       (* arm_LDR X11 X3 (Shiftreg_Offset X10 3) *)
  0xf86a788c;       (* arm_LDR X12 X4 (Shiftreg_Offset X10 3) *)
  0x8a11016b;       (* arm_AND X11 X11 X17 *)
  0xca11018c;       (* arm_EOR X12 X12 X17 *)
  0xba0c016b;       (* arm_ADCS X11 X11 X12 *)
  0xf82a788b;       (* arm_STR X11 X4 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5ffff0b;       (* arm_CBNZ X11 (word 2097120) *)
  0xaa3303f3;       (* arm_MVN X19 X19 *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xab13027f;       (* arm_CMN X19 X19 *)
  0xf86a786b;       (* arm_LDR X11 X3 (Shiftreg_Offset X10 3) *)
  0xf86a782c;       (* arm_LDR X12 X1 (Shiftreg_Offset X10 3) *)
  0x8a13016b;       (* arm_AND X11 X11 X19 *)
  0xca13018c;       (* arm_EOR X12 X12 X19 *)
  0xba0c016b;       (* arm_ADCS X11 X11 X12 *)
  0xf82a782b;       (* arm_STR X11 X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014b;       (* arm_SUB X11 X10 X0 *)
  0xb5ffff0b;       (* arm_CBNZ X11 (word 2097120) *)
  0xf100e842;       (* arm_SUBS X2 X2 (rvalue (word 58)) *)
  0x54ffdd28;       (* arm_BHI (word 2096036) *)
  0xa94a07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa94b0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&176))) *)
  0xaa010000;       (* arm_ORR X0 X0 X1 *)
  0xaa030042;       (* arm_ORR X2 X2 X3 *)
  0xaa020004;       (* arm_ORR X4 X0 X2 *)
  0xeb1f009f;       (* arm_CMP X4 XZR *)
  0xa95407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&320))) *)
  0x9a9f1000;       (* arm_CSEL X0 X0 XZR Condition_NE *)
  0x9a9f1021;       (* arm_CSEL X1 X1 XZR Condition_NE *)
  0xa9550fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&336))) *)
  0xa91407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&320))) *)
  0x9a9f1042;       (* arm_CSEL X2 X2 XZR Condition_NE *)
  0x9a9f1063;       (* arm_CSEL X3 X3 XZR Condition_NE *)
  0xa9150fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&336))) *)
  0xa95413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&320))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
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
  0xa95513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&336))) *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0x9bc57c6c;       (* arm_UMULH X12 X3 X5 *)
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
  0xa95513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&336))) *)
  0xa95443ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&320))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa94403ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&64))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060006;       (* arm_SBCS X6 X0 X6 *)
  0xda9f23e0;       (* arm_CSETM X0 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca0000a5;       (* arm_EOR X5 X5 X0 *)
  0xeb0000a5;       (* arm_SUBS X5 X5 X0 *)
  0xca0000c6;       (* arm_EOR X6 X6 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xca100010;       (* arm_EOR X16 X0 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c60;       (* arm_UMULH X0 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab0001ef;       (* arm_ADDS X15 X15 X0 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0040;       (* arm_ADDS X0 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba0000a0;       (* arm_ADCS X0 X5 X0 *)
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
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x92407d65;       (* arm_AND X5 X11 (rvalue (word 4294967295)) *)
  0xd360fd64;       (* arm_LSR X4 X11 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b047c64;       (* arm_MUL X4 X3 X4 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x92407d85;       (* arm_AND X5 X12 (rvalue (word 4294967295)) *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0c7c6c;       (* arm_MUL X12 X3 X12 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x92407da5;       (* arm_AND X5 X13 (rvalue (word 4294967295)) *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0d7c6d;       (* arm_MUL X13 X3 X13 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x92407dc5;       (* arm_AND X5 X14 (rvalue (word 4294967295)) *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9b057c65;       (* arm_MUL X5 X3 X5 *)
  0x9b0e7c6e;       (* arm_MUL X14 X3 X14 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a9f37eb;       (* arm_CSET X11 Condition_CS *)
  0xd3607c85;       (* arm_LSL X5 X4 32 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0x93c48185;       (* arm_EXTR X5 X12 X4 32 *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0x93cc81a5;       (* arm_EXTR X5 X13 X12 32 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x93cd81c5;       (* arm_EXTR X5 X14 X13 32 *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0xd360fdc5;       (* arm_LSR X5 X14 32 *)
  0x9a05016b;       (* arm_ADC X11 X11 X5 *)
  0xab0a015f;       (* arm_CMN X10 X10 *)
  0xb241014a;       (* arm_ORR X10 X10 (rvalue (word 9223372036854775808)) *)
  0x9a0b0160;       (* arm_ADC X0 X11 X11 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b000c65;       (* arm_MADD X5 X3 X0 X3 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a9f3063;       (* arm_CSEL X3 X3 XZR Condition_CC *)
  0xeb0300e7;       (* arm_SUBS X7 X7 X3 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0x9240f94a;       (* arm_AND X10 X10 (rvalue (word 9223372036854775807)) *)
  0xa90022e7;       (* arm_STP X7 X8 X23 (Immediate_Offset (iword (&0))) *)
  0xa9012ae9;       (* arm_STP X9 X10 X23 (Immediate_Offset (iword (&16))) *)
  0x910603ff;       (* arm_ADD SP SP (rvalue (word 384)) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CURVE25519_X25519_EXEC = ARM_MK_EXEC_RULE curve25519_x25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Abbreviations used to state the specification.                            *)
(* ------------------------------------------------------------------------- *)

let p_25519 = define `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let curve25519x = define
 `curve25519x (f:A ring) = (f,ring_of_num f A_25519,ring_of_num f 1)`;;

let curve25519x_canonically_represents = new_definition
 `curve25519x_canonically_represents (f:A ring) P (X,Z) <=>
        X < p_25519 /\ Z < p_25519 /\
        montgomery_xz f P (ring_of_num f X,ring_of_num f Z)`;;

let CURVE25519X_CANONICALLY_REPRESENTS_BOUND = prove
 (`!(f:A ring) P X Z.
        curve25519x_canonically_represents (f:A ring) P (X,Z)
        ==> X < p_25519 /\ Z < p_25519`,
  SIMP_TAC[curve25519x_canonically_represents]);;

(* ------------------------------------------------------------------------- *)
(* Common lemmas and tactics for the component proofs.                       *)
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

let alemma1 = prove
 (`!(x0:num) x1 (y0:num) y1.
       (if y0 <= y1
        then if x1 <= x0 then word 0 else word 18446744073709551615
        else word_not
         (if x1 <= x0 then word 0 else word 18446744073709551615)):int64 =
   word_neg(word(bitval(y0 <= y1 <=> x0 < x1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let alemma2 = prove
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

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let shiftandlemma = prove
 (`!x:int64. &(val(word_and x (word 4294967295))):real =
             &(val x) - &2 pow 32 * &(val(word_ushr x 32))`,
  GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[val_def; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ARITH_TAC);;

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

let p25519weakredlemma = prove
 (`!n. n <= 2 EXP 62 * 2 EXP 256
       ==> let q = n DIV 2 EXP 255 in
           q < 2 EXP 64 /\
           q * p_25519 <= n /\
           n < q * p_25519 + 2 * p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let lvs =
 ["resx",[`X23`;`0`];
  "x",[`SP`;`32`];
  "zm",[`SP`;`64`];
  "sm",[`SP`;`64`];
  "dpro",[`SP`;`64`];
  "sn",[`SP`;`96`];
  "dm",[`SP`;`128`];
  "zn",[`SP`;`160`];
  "dn",[`SP`;`160`];
  "e",[`SP`;`160`];
  "dmsn",[`SP`;`192`];
  "p",[`SP`;`192`];
  "xm",[`SP`;`256`];
  "dnsm",[`SP`;`256`];
  "spro",[`SP`;`256`];
  "xn",[`SP`;`320`];
  "s",[`SP`;`320`];
  "d",[`SP`;`352`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 161 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                     X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** First nested block multiplying the lower halves ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [3;5;10;11;15;17;18;19;22;24;25] (1--25) THEN
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

  (*** Second nested block multiplying the upper halves ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [28;30;35;36;40;42;43;44;47;49;50] (26--50) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (69--72) (69--72) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
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

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [116;117;118;121;122;123;126;127;128;131;132;133;136;138;140;142;144]
   (113--144) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s136; sum_s138; sum_s140; sum_s142; sum_s144]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN

    TRANS_TAC EQ_TRANS
     `bignum_of_wordlist[sum_s118; sum_s123; sum_s128; sum_s133;
                       word(bitval carry_s133)] +
      2 EXP 32 *
      bignum_of_wordlist[mullo_s117; mullo_s122; mullo_s127; mullo_s132]` THEN
    CONJ_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THENL
     [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 snd o chop_list 5);
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 fst o chop_list 5)] THEN
    REWRITE_TAC[shiftandlemma] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_0] THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ARITH
      `x + --c * y:real = z <=> x = c * y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM ADD_ASSOC] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LT; ARITH_LE] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`; MOD_MULT2] THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (145--147) (145--147) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s136; sum_s138; sum_s140;
    word_or sum_s142 (word 9223372036854775808)]` THEN
    SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s136; sum_s138; sum_s140] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s147:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s145; sum_s147] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (159--160) THEN
  ABBREV_TAC `qm:int64 = word(19 + 19 * val(sum_s147:int64))` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(sum_s147:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `c + c * q = c * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s147:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (150--161) (150--161) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s147:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(sum_s147:int64) + 1) * p_25519 <=> ~carry_s153`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s153:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_p25519 (actually there is only one).                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 114 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
        aligned 16 (read SP t) /\
        nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                  read PC s = pcin /\
                  read SP s = read SP t /\
                  read X23 s = read X23 t /\
                  read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
             (\s. read PC s = pcout /\
                  read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s = (n EXP 2) MOD p_25519)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [3; 4; 11; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29;
    30; 31; 32; 33; 34; 35; 39; 40; 41; 42; 43; 44; 45; 46; 47;
    48; 49; 50; 51; 52; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65]
   (1--65) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s33; sum_s42; sum_s45; sum_s46]`;
    `h = bignum_of_wordlist[sum_s62; sum_s63; sum_s64; sum_s65]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[alemma1; alemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter(is_ratconst o rand o concl) o
                DECARRY_RULE o CONJUNCTS) THEN
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

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [69;70;71;74;75;76;79;80;81;84;85;86;89;91;93;95;97]
   (66--97) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s89; sum_s91; sum_s93; sum_s95; sum_s97]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    TRANS_TAC EQ_TRANS
     `bignum_of_wordlist[sum_s71; sum_s76; sum_s81; sum_s86;
                       word(bitval carry_s86)] +
      2 EXP 32 *
      bignum_of_wordlist[mullo_s70; mullo_s75; mullo_s80; mullo_s85]` THEN
    CONJ_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THENL
     [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 snd o chop_list 5);
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 fst o chop_list 5)] THEN
    REWRITE_TAC[shiftandlemma] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_0] THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ARITH
      `x + --c * y:real = z <=> x = c * y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM ADD_ASSOC] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LT; ARITH_LE] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`; MOD_MULT2] THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (98--100) (98--100) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s89; sum_s91; sum_s93;
    word_or sum_s95 (word 9223372036854775808)]` THEN
    SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s89; sum_s91; sum_s93] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s100:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s98; sum_s100] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (101--102) THEN
  ABBREV_TAC `qm:int64 = word(19 + 19 * val(sum_s100:int64))` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(sum_s100:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `c + c * q = c * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s100:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (103--114) (103--114) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s100:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(sum_s100:int64) + 1) * p_25519 <=> ~carry_s106`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s106:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of mul_5                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_5_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 147 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 5)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 5)) s
                < 39 * 2 EXP 256 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 5)) s ==
                 m * n) (mod p_25519))
        (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                     X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 5)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** First nested block multiplying the lower halves ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [3;5;10;11;15;17;18;19;22;24;25] (1--25) THEN
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

  (*** Second nested block multiplying the upper halves ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [28;30;35;36;40;42;43;44;47;49;50] (26--50) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (69--72) (69--72) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
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

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [116;117;118;121;122;123;126;127;128;131;132;133;136;138;140;142;144]
   (113--147) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `y < n /\ x = y ==> x < n /\ x MOD p = y MOD p`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  (*** Final fiddly constant multiplication using masking ***)

  CONV_TAC SYM_CONV THEN MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  TRANS_TAC EQ_TRANS
   `bignum_of_wordlist[sum_s118; sum_s123; sum_s128; sum_s133;
                     word(bitval carry_s133)] +
    2 EXP 32 *
    bignum_of_wordlist[mullo_s117; mullo_s122; mullo_s127; mullo_s132]` THEN
  CONJ_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  REWRITE_TAC[VAL_WORD_BITVAL] THENL
   [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                               snd o chop_list 5);
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                               fst o chop_list 5)] THEN
  REWRITE_TAC[shiftandlemma] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM REAL_SUB_0] THEN
  CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
  REWRITE_TAC[REAL_ADD_ASSOC; REAL_ARITH
    `x + --c * y:real = z <=> x = c * y + z`] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM ADD_ASSOC] THEN
  SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LT; ARITH_LE] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`; MOD_MULT2] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 108 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n.
      read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 n EXP 2)
                (mod p_25519))
        (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                    X10; X11; X12; X13; X14; X15; X16] ,,
         MAYCHANGE
          [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [3; 4; 11; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29;
    30; 31; 32; 33; 34; 35; 39; 40; 41; 42; 43; 44; 45; 46; 47;
    48; 49; 50; 51; 52; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65]
   (1--65) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s33; sum_s42; sum_s45; sum_s46]`;
    `h = bignum_of_wordlist[sum_s62; sum_s63; sum_s64; sum_s65]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[alemma1; alemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter(is_ratconst o rand o concl) o
                DECARRY_RULE o CONJUNCTS) THEN
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

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [69;70;71;74;75;76;79;80;81;84;85;86;89;91;93;95;97]
   (66--97) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s89; sum_s91; sum_s93; sum_s95; sum_s97]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    TRANS_TAC EQ_TRANS
     `bignum_of_wordlist[sum_s71; sum_s76; sum_s81; sum_s86;
                       word(bitval carry_s86)] +
      2 EXP 32 *
      bignum_of_wordlist[mullo_s70; mullo_s75; mullo_s80; mullo_s85]` THEN
    CONJ_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THENL
     [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 snd o chop_list 5);
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 fst o chop_list 5)] THEN
    REWRITE_TAC[shiftandlemma] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_0] THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ARITH
      `x + --c * y:real = z <=> x = c * y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM ADD_ASSOC] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LT; ARITH_LE] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`; MOD_MULT2] THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (98--100) (98--100) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s100:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s98; sum_s100] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (101--102) THEN
  ABBREV_TAC `qm:int64 = word(0 + val(sum_s100:int64) * 19)` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(sum_s100:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s100:int64) + 1 <= 78` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (103--106) (103--108) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s100:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ONCE_REWRITE_TAC[INT_ARITH
     `ca:int < s * p + &2 * p <=> ca < (s + &1) * p + p`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `s * p <= ca <=> (s + 1) * p <= ca + p`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(sum_s100:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 10 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < p_25519 /\ n < p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                     m + n))
        (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC [3;4;7;8] (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add5_4 (actually there is only one).                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD5_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 22 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) s = n)
           (\s. read PC s = pcout /\
                (m + n < 2 EXP 58 * 2 EXP 256
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (bignum_from_memory
                       (word_add (read p3 t) (word n3),4) s ==
                      m + n) (mod p_25519)))
        (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X11] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `m + n < 2 EXP 58 * 2 EXP 256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC CURVE25519_X25519_EXEC (1--22)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC [3;4;7;8;11] (1--11) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s3; sum_s4; sum_s7; sum_s8; sum_s11]` THEN
  SUBGOAL_THEN `m + n = ca` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN MATCH_MP_TAC CONG_IMP_EQ THEN
    EXISTS_TAC `2 EXP 320` THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `m + n < 2 EXP 58 * 2 EXP 256` THEN ARITH_TAC;
      BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p25519weakredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ca < 2 EXP 58 * 2 EXP 256` THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (12--14) (12--14) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s14:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `ca < 2 EXP 58 * 2 EXP 256
      ==> ca DIV 2 EXP 192 DIV 2 EXP 63 < 2 EXP 59`)) THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s12; sum_s14] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (15--16) THEN
  ABBREV_TAC `qm:int64 = word(0 + 19 * val(sum_s14:int64))` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(sum_s14:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC MOD_LT THEN MAP_EVERY UNDISCH_TAC
     [`val(sum_s14:int64) * p_25519 <= ca`;
      `ca < 2 EXP 58 * 2 EXP 256`] THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (17--20) (17--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s14:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(sum_s14:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < p_25519 /\ n < p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (&(bignum_from_memory
                         (word_add (read p3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [3;4;7;8;10;11;12;14] (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x' < &e /\ &x = x'
             ==> x < e /\ (&x:int == a) (mod p)`) THEN
  EXISTS_TAC `(&m - &n) + &p_25519:int` THEN REPEAT CONJ_TAC THENL
   [CONV_TAC INTEGER_RULE;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x:int < e /\ &0 <= y /\ y < e ==> abs(x - y) < e`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_RULE
     `(x:int == m - n + c) (mod e) <=> (n + x == m + c) (mod e)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4 (actually there is only one).                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < 2 * p_25519 /\ n < 2 * p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (&(bignum_from_memory
                         (word_add (read p3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (11--14) (9--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x' < &e /\ &x = x'
             ==> x < e /\ (&x:int == a) (mod p)`) THEN
  EXISTS_TAC `if m < n then &m - &n + &2 * &p_25519:int else &m - &n` THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub5_4 (actually there is only one).                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB5_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 29 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) s = n)
           (\s. read PC s = pcout /\
                (m < 39 * 2 EXP 256 /\ n < 39 * 2 EXP 256
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519 /\
                     (&(bignum_from_memory
                       (word_add (read p3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X11] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `m < 39 * 2 EXP 256 /\ n < 39 * 2 EXP 256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC CURVE25519_X25519_EXEC (1--29)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [3;4;7;8;11;13;14;15;16;18] (1--18) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s13; sum_s14; sum_s15; sum_s16; sum_s18]` THEN
  SUBGOAL_THEN `&ca:int = &m - &n + &1000 * &p_25519` ASSUME_TAC THENL
   [EXPAND_TAC "ca" THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow 320` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `&0 <= x /\ x:int < e /\ &0 <= y /\ y < e ==> abs(x - y) < e`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`m < 39 * 2 EXP 256`; `n < 39 * 2 EXP 256`] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      REWRITE_TAC[INTEGER_RULE
       `(x:int == m - n + c) (mod e) <=> (n + x == m + c) (mod e)`] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  REWRITE_TAC[GSYM INT_REM_EQ] THEN
  SUBGOAL_THEN `(&m - &n) rem &p_25519 = &ca rem &p_25519` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[INT_REM_MUL_ADD];
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[GSYM CONG]] THEN
  SUBGOAL_THEN `ca < 600 * 2 EXP 256` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`m < 39 * 2 EXP 256`; `n < 39 * 2 EXP 256`] THEN
    ASM_REWRITE_TAC[p_25519; GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `&ca:int = &m - &n + &1000 * &p_25519` (K ALL_TAC) THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p25519weakredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ca < 600 * 2 EXP 256` THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (19--21) (19--21) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s21:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `ca < 600 * 2 EXP 256
      ==> ca DIV 2 EXP 192 DIV 2 EXP 63 < 2 EXP 59`)) THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s19; sum_s21] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (22--23) THEN
  ABBREV_TAC `qm:int64 = word(0 + 19 * val(sum_s21:int64))` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(sum_s21:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC MOD_LT THEN MAP_EVERY UNDISCH_TAC
     [`val(sum_s21:int64) * p_25519 <= ca`;
      `ca < 600 * 2 EXP 256`] THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (24--27) (24--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s21:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(sum_s21:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of cmadd_4 (actually there is only one, specific constant).     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMADD_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 32 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read X1 s = word 121666 /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s <
                2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 121666 * m + n) (mod p_25519))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC
   [3;4;5;6;11;12;13;14;16;17;19;20;21] (1--21) THEN

  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s16; sum_s17; sum_s19; sum_s20; sum_s21]` THEN
  SUBGOAL_THEN `121666 * m + n < 2 EXP 17 * 2 EXP 256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `121666 * m + n = ca` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `121666 * m + n < 2 EXP 17 * 2 EXP 256` THEN ARITH_TAC;
      EXPAND_TAC "ca" THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p25519weakredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ca < 2 EXP 17 * 2 EXP 256` THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (22--24) (22--24) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s24:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `ca < 2 EXP 17 * 2 EXP 256
      ==> ca DIV 2 EXP 192 DIV 2 EXP 63 < 2 EXP 59`)) THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s22; sum_s24] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (25--26) THEN
  ABBREV_TAC `qm:int64 = word(0 + val(sum_s24:int64) * 19)` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(sum_s24:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC MOD_LT THEN MAP_EVERY UNDISCH_TAC
     [`val(sum_s24:int64) * p_25519 <= ca`;
      `ca < 2 EXP 17 * 2 EXP 256`] THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC (27--30) (27--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s24:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(sum_s24:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of mux_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUX_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_mc 10 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !b. read ZF t = b
     ==>
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1e2c) (word_add (read p3 t) (word n3),8 * 4) /\
      nonoverlapping (stackpointer:int64,320) (res,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read ZF s = b /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (if b then n else m))
        (MAYCHANGE [PC; X0; X1; X2; X3] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Instances of modular inverse inlining                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MODINV_TAC =
  let cth =
    (GEN_REWRITE_CONV RAND_CONV [bignum_modinv_mc] THENC TRIM_LIST_CONV)
    `TRIM_LIST (12,12) bignum_modinv_mc`
  and th = CONV_RULE (DEPTH_CONV WORD_NUM_RED_CONV)
                     (SPEC `word 4:int64` CORE_MODINV_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (curve25519_x25519_mc,CURVE25519_X25519_EXEC,0x1688,cth,th)
   [`read X1 s`; `read X2 s`;
    `read (memory :> bytes(read X2 s,8 * 4)) s`;
    `read X3 s`;
    `read (memory :> bytes(read X3 s,8 * 4)) s`;
    `read X4 s`;
    `pc + 0x1688`];;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let nintlemma = prove
 (`&(num_of_int(x rem &p_25519)) = x rem &p_25519`,
  MATCH_MP_TAC INT_OF_NUM_OF_INT THEN MATCH_MP_TAC INT_REM_POS THEN
  REWRITE_TAC[INT_OF_NUM_EQ; p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let lemma = prove
 (`X = num_of_int(x rem &p_25519) ==> X < p_25519 /\ &X = x rem &p_25519`,
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; nintlemma; INT_LT_REM_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_LT; p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let lemma_double = prove
 (`P IN group_carrier (curve25519x_group(f:(int#int) ring)) /\
   montgomery_xz f (group_pow (curve25519x_group f) P n) (x,y)
   ==> field f /\ ring_char f = p_25519
       ==> montgomery_xz f
            (group_pow (curve25519x_group f) P (2 * n))
               (montgomery_xzdouble (curve25519x f) (x,y))`,
  REWRITE_TAC[curve25519x; curve25519x_group] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MONTGOMERY_XZDOUBLE_GROUP THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM curve25519x; MONTGOMERY_NONSINGULAR_CURVE25519X] THEN
  REWRITE_TAC[A_25519; p_25519; RING_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let lemma_diffadd1 = prove
 (`field f /\ ring_char f = p_25519 /\
   ~(x:(int#int) = ring_0 f) /\
   P IN group_carrier (curve25519x_group f) /\
   montgomery_xz f P (x,ring_of_num f 1) /\
   montgomery_xz f
     (group_pow (curve25519x_group f) P (n + 1)) (xn,zn) /\
   montgomery_xz f
     (group_pow (curve25519x_group f) P n) (xm,zm)
   ==> montgomery_xz f
            (group_pow (curve25519x_group f) P (2 * n + 1))
            (montgomery_xzdiffadd (curve25519x f) (x,ring_of_num f 1)
                  (xn,zn) (xm,zm))`,
  REWRITE_TAC[curve25519x; curve25519x_group] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MONTGOMERY_XZDIFFADD_GROUP THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM curve25519x; MONTGOMERY_NONSINGULAR_CURVE25519X] THEN
  REWRITE_TAC[A_25519; p_25519; RING_OF_NUM] THEN
  ASM_SIMP_TAC[RING_OF_NUM_1; FIELD_NONTRIVIAL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let lemma_diffadd2 = prove
 (`field f /\ ring_char f = p_25519 /\
   ~(x:(int#int) = ring_0 f) /\
   P IN group_carrier (curve25519x_group f) /\
   montgomery_xz f P (x,ring_of_num f 1) /\
   montgomery_xz f
     (group_pow (curve25519x_group f) P (n + 1)) (xm,zm) /\
   montgomery_xz f
     (group_pow (curve25519x_group f) P n) (xn,zn)
   ==> montgomery_xz f
            (group_pow (curve25519x_group f) P (2 * n + 1))
            (montgomery_xzdiffadd (curve25519x f) (x,ring_of_num f 1)
                  (xn,zn) (xm,zm))`,
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP lemma_diffadd1) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP MONTGOMERY_XZ_IN_CARRIER)) THEN
  ASM_SIMP_TAC[montgomery_xzdiffadd; curve25519x; RING_MUL_SYM; PAIR_EQ] THEN
  RING_TAC);;

let CURVE25519_X25519_CORRECT = time prove
 (`!res scalar n point X pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,384))
        [(word pc,0x1e2c); (res,32); (scalar,32); (point,32)] /\
    nonoverlapping (res,32) (word pc,0x1e2c)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
              read PC s = word(pc + 0x10) /\
              read SP s = stackpointer /\
              C_ARGUMENTS [res; scalar; point] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_from_memory (point,4) s = X)
         (\s. read PC s = word (pc + 0x1e18) /\
              bignum_from_memory (res,4) s = rfcx25519(n,X))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(res,32);
                      memory :> bytes(stackpointer,384)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `n_input:num`; `point:int64`; `X_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  (*** The modified forms of the inputs that get computed early on  ***)
  (*** The nn' is the computed value without masking of the top bit ***)

  ABBREV_TAC `nn = 2 EXP 254 + n_input MOD 2 EXP 254 - n_input MOD 8` THEN
  ABBREV_TAC `X = (X_input MOD 2 EXP 255) MOD p_25519` THEN
  ABBREV_TAC `nn' = 2 EXP 255 * n_input DIV 2 EXP 255 + nn` THEN
  REWRITE_TAC[rfcx25519] THEN ONCE_REWRITE_TAC[GSYM PUREX25519_MOD] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_PDOWN_TAC `255` `pc + 0x90` `pc + 0x165c`
   `\i s.
     (read SP s = stackpointer /\
      read X23 s = res /\
      read X20 s = word_sub (word i) (word 1) /\
      bignum_from_memory (stackpointer,4) s = nn' /\
      bignum_from_memory (word_add stackpointer (word 32),4) s = X /\
      read X21 s = word(bitval(ODD(nn DIV 2 EXP i))) /\
      !(f:(int#int) ring) P.
        field f /\ ring_char f = p_25519 /\
        P IN group_carrier(curve25519x_group f) /\
        curve25519x_canonically_represents f P (X,1)
      ==>
      if X = 0 then
        bignum_from_memory(word_add stackpointer (word 64),4) s <= 1 /\
        bignum_from_memory(word_add stackpointer (word 160),4) s = 0 /\
        bignum_from_memory(word_add stackpointer (word 256),4) s = 0 /\
        bignum_from_memory(word_add stackpointer (word 320),4) s <= 1
      else
      curve25519x_canonically_represents f
       (group_pow (curve25519x_group f) P
           (if ODD(nn DIV 2 EXP i)
            then nn DIV 2 EXP i + 1 else nn DIV 2 EXP i))
       (bignum_from_memory(word_add stackpointer (word 320),4) s,
        bignum_from_memory(word_add stackpointer (word 160),4) s) /\
      curve25519x_canonically_represents f
       (group_pow (curve25519x_group f) P
          (if ODD(nn DIV 2 EXP i)
           then nn DIV 2 EXP i else nn DIV 2 EXP i + 1))
       (bignum_from_memory(word_add stackpointer (word 256),4) s,
        bignum_from_memory(word_add stackpointer (word 64),4) s)) /\
     (read CF s <=> ~(i = 0))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial setup and modification of the inputs ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (scalar,8 * 4)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (point,8 * 4)) s0` THEN

    ARM_ACCSTEPS_TAC CURVE25519_X25519_EXEC [9;10;13;15] (1--32) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[COND_SWAP] THEN
    CONJ_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["nn'"; "nn"; "n_input"] THEN
      MATCH_MP_TAC(ARITH_RULE
        `n MOD 8 <= n MOD 2 EXP 254 /\
         2 EXP 254 * n DIV 2 EXP 254 + n MOD 8 + a = b + c + n
         ==> a = b + c + n MOD 2 EXP 254 - n MOD 8`) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [ARITH_RULE `x MOD 8 = x MOD 2 EXP (MIN 254 3)`] THEN
      REWRITE_TAC[GSYM MOD_MOD_EXP_MIN; MOD_LE] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN
      ONCE_REWRITE_TAC[ARITH_RULE
       `a + 2 EXP 64 * b = a + 8 * 2 EXP 61 * b`] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN
      REWRITE_TAC[val_def; ARITH_RULE `8 = 2 EXP 3`; DIMINDEX_64] THEN
      SIMP_TAC[BINARY_DIGITSUM_DIV; BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[IN_ELIM_THM; ARITH_RULE
       `i < 64 /\ a <= i <=> a <= i /\ i <= 63`] THEN
      REWRITE_TAC[ARITH_RULE `i < 64 /\ i < 3 <=> i < 3`] THEN
      REWRITE_TAC[NUMSEG_LT; ARITH_EQ; GSYM numseg] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV
       (WORD_NUM_RED_CONV ORELSEC
        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["X"; "X_input"] THEN
      SUBGOAL_THEN
       `bignum_of_wordlist [x_0; x_1; x_2; x_3] MOD 2 EXP 255 =
        bignum_of_wordlist [x_0; x_1; x_2; word_and x_3 (word(2 EXP 63 - 1))]`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `m + 2 EXP 255 * n DIV 2 EXP 255 = n
          ==> n MOD 2 EXP 255 = m`) THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
        ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD; p_25519] THEN
        CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN
       `bignum_of_wordlist
         [x_0; x_1; x_2; word_and x_3 (word 9223372036854775807)] < p_25519 <=>
        carry_s15`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
        EXISTS_TAC `256` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_25519] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_BITVAL_NOT; p_25519] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(ARITH_RULE `a + b:num = c ==> a = c - b`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_BITVAL_NOT; p_25519] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `nn < 2 EXP 255` (fun t -> SIMP_TAC[t; DIV_LT; MOD_LT]) THENL
     [EXPAND_TAC "nn" THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_SIMP_TAC[GROUP_POW_1] THEN REWRITE_TAC[group_pow] THEN
    SIMP_TAC[CURVE25519X_GROUP] THEN
    REWRITE_TAC[curve25519x_canonically_represents; montgomery_xz] THEN
    REWRITE_TAC[RING_OF_NUM] THEN
    REWRITE_TAC[RING_OF_NUM_1; RING_OF_NUM_0; p_25519] THEN
    SIMP_TAC[FIELD_NONTRIVIAL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID];

    (*** The main loop invariant for the Montgomery ladder ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add stackpointer (word 320),4)` THEN
    GHOST_INTRO_TAC `zn:num`
     `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
    GHOST_INTRO_TAC `xm:num`
     `bignum_from_memory (word_add stackpointer (word 256),4)` THEN
    GHOST_INTRO_TAC `zm:num`
     `bignum_from_memory(word_add stackpointer (word 64),4)` THEN
    REWRITE_TAC[WORD_RULE `word_sub (word (i + 1)) (word 1) = word i`] THEN

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    LOCAL_SUB_4_TAC 0 ["dm"; "xm"; "zm"] THEN
    LOCAL_ADD_4_TAC 0 ["sn"; "xn"; "zn"] THEN
    LOCAL_SUB_4_TAC 0 ["dn"; "xn"; "zn"] THEN
    LOCAL_ADD_4_TAC 0 ["sm"; "xm"; "zm"] THEN
    LOCAL_MUL_5_TAC 0 ["dmsn"; "sn"; "dm"] THEN

    SUBGOAL_THEN
     `read(memory :> bytes64(word_add stackpointer
       (word(8 * val(word_ushr (word i:int64) 6))))) s5 =
      word(nn' DIV (2 EXP (64 * i DIV 64)) MOD 2 EXP (64 * 1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "nn'" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 255 ==> MIN (4 - i DIV 64) 1 = 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
      VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC CURVE25519_X25519_EXEC (6--11) THEN
    SUBGOAL_THEN
     `word_and
        (word_jushr (word((nn' DIV 2 EXP (64 * i DIV 64)) MOD 2 EXP 64))
                    (word i))
        (word 1:int64) =
      word(bitval(ODD(nn DIV 2 EXP i)))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[WORD_AND_1_BITVAL; word_jushr; MOD_64_CLAUSES;
                  DIMINDEX_64; VAL_WORD; MOD_MOD_REFL] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[BIT_LSB; VAL_WORD_USHR] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
      REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + 64 = i + (64 - i MOD 64)`] THEN
      REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; ODD_MOD_POW2] THEN
      MATCH_MP_TAC(TAUT `p /\ (q <=> q')==> (p /\ q <=> q')`) THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM CONG_MOD_2_ALT] THEN MATCH_MP_TAC CONG_DIV2 THEN
      REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP))] THEN
      UNDISCH_THEN
       `2 EXP 255 * n_input DIV 2 EXP 255 + nn = nn'`
       (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(NUMBER_RULE
       `n divides e ==> (e * x + y:num == y) (mod n)`) THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_REWRITE_TAC[LE_SUC_LT];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_SUB_EQ_0;
      MESON[VAL_WORD_BITVAL; VAL_EQ; EQ_BITVAL]
       `word(bitval b) = word(bitval c) <=> (b <=> c)`]) THEN

    LOCAL_MUX_4_TAC 0 ["d"; "dm"; "dn"] THEN
    LOCAL_MUX_4_TAC 0 ["s"; "sm"; "sn"] THEN
    LOCAL_MUL_5_TAC 0 ["dnsm"; "sm"; "dn"] THEN
    LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN
    LOCAL_SUB5_4_TAC 0 ["dpro"; "dmsn"; "dnsm"] THEN
    LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
    LOCAL_ADD5_4_TAC 0 ["spro"; "dmsn"; "dnsm"] THEN
    LOCAL_SQR_4_TAC 0 ["dpro"; "dpro"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
    LOCAL_SQR_P25519_TAC 0 ["xm"; "spro"] THEN
    LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
    LOCAL_MUL_P25519_TAC 0 ["xn"; "s"; "d"] THEN
    LOCAL_MUL_P25519_TAC 0 ["zm"; "dpro"; "x"] THEN
    LOCAL_MUL_P25519_TAC 0 ["zn"; "p"; "e"] THEN
    ARM_STEPS_TAC CURVE25519_X25519_EXEC [28] THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `(MAYCHANGE a ,, b) s s'` o concl))) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN MP_TAC th) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN

    ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT;
                 ARITH_RULE `i < 255 ==> i < 2 EXP 64`] THEN
    REWRITE_TAC[ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
    DISCARD_STATE_TAC "s28" THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`aligned a b`; `val(word i) = i`; `nonoverlapping_modulo a b c`] THEN

    MAP_EVERY X_GEN_TAC [`f:(int#int) ring`; `P:((int#int)#(int#int))option`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:(int#int) ring`; `P:((int#int)#(int#int))option`]) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
       (fun th -> SUBST_ALL_TAC th ORELSE ASSUME_TAC th)) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
      REPEAT(ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
        RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[p_25519]) THEN
        ASM BOUNDER_TAC[];
        STRIP_TAC]) THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
      ONCE_REWRITE_TAC[GSYM INT_POW_REM; GSYM INT_MUL_REM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
       (ARITH_RULE `n <= 1 ==> n = 0 \/ n = 1`))) THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN

    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TAUT
     `(ODD n <=> b) <=> (b <=> ODD n)`]) THEN
    ABBREV_TAC `n = nn DIV 2 EXP (i + 1)` THEN
    ABBREV_TAC `b = ODD(nn DIV 2 EXP i)` THEN
    SUBGOAL_THEN `nn DIV 2 EXP i = 2 * n + bitval b` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["b"; "n"] THEN
      REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; BITVAL_ODD] THEN ARITH_TAC;
      SIMP_TAC[BITVAL_CLAUSES; ADD_CLAUSES; COND_ID]] THEN

    REPEAT(FIRST_X_ASSUM(K ALL_TAC o
     check (free_in `n_input:num`) o concl)) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o
     check (free_in `X_input:num`) o concl)) THEN

    DISCH_TAC THEN
    SUBGOAL_THEN
     `(ring_of_num f xm':(int#int),ring_of_num f zm') =
       montgomery_xzdiffadd (curve25519x f)
           (ring_of_num f X,ring_of_num f 1)
           (ring_of_num f xn,ring_of_num f zn)
           (ring_of_num f xm,ring_of_num f zm) /\
      (ring_of_num f xn',ring_of_num f zn') =
       montgomery_xzdouble (curve25519x f)
        (if b <=> ODD n then (ring_of_num f xn,ring_of_num f zn)
         else (ring_of_num f xm,ring_of_num f zm))`
    MP_TAC THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN (STRIP_ASSUME_TAC o
        MATCH_MP CURVE25519X_CANONICALLY_REPRESENTS_BOUND)) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        MATCH_MP CURVE25519X_CANONICALLY_REPRESENTS_BOUND) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
      REPEAT(ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[montgomery_xzdiffadd; montgomery_xzdouble;
                      curve25519x; PAIR_EQ] THEN
      STRIP_TAC THEN
      REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_CLAUSES] THEN
      ASM_REWRITE_TAC[RING_OF_INT_EQ] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_REM_EQ;
                  GSYM INT_OF_NUM_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[PAIR_EQ; GSYM INT_OF_NUM_EQ; nintlemma] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
      ONCE_REWRITE_TAC[GSYM INT_POW_REM; GSYM INT_MUL_REM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[A_25519] THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN SIMP_TAC[curve25519x_canonically_represents] THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[MOD_LT_EQ; p_25519; ARITH_EQ] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN(MP_TAC o last o CONJUNCTS o
         GEN_REWRITE_RULE I
       [curve25519x_canonically_represents])) THEN
      GEN_REWRITE_TAC I [GSYM IMP_CONJ_ALT] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [curve25519x_canonically_represents]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2)) THEN
      UNDISCH_TAC `P IN group_carrier(curve25519x_group(f:(int#int) ring))`] THEN

    SUBGOAL_THEN `~(ring_of_num (f:(int#int) ring) X = ring_0 f)` MP_TAC THENL
     [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_REWRITE_TAC[NOT_LE];
      MAP_EVERY UNDISCH_TAC
       [`ring_char(f:(int#int) ring) = p_25519`; `field(f:(int#int) ring)`] THEN
      POP_ASSUM_LIST(K ALL_TAC)] THEN

    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [DISJ_CASES_THEN SUBST_ALL_TAC
        (TAUT `(b <=> ODD n) \/ (b <=> ~ODD n)`) THEN
      REWRITE_TAC[TAUT `~(~p <=> p)`] THENL
       [FIRST_X_ASSUM(MP_TAC o CONJUNCT1);
        FIRST_X_ASSUM(MP_TAC o CONJUNCT2)] THEN
      UNDISCH_TAC `P IN group_carrier(curve25519x_group(f:(int#int) ring))` THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma_double) THEN
      ASM_REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN
      REWRITE_TAC[ARITH_RULE `(2 * n + 1) + 1 = 2 * (n + 1)`];

      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[lemma_diffadd1] THEN
      GEN_REWRITE_TAC (LAND_CONV o funpow 5 RAND_CONV) [CONJ_SYM] THEN
      REWRITE_TAC[lemma_diffadd2]];

    (*** The trivial loop-back subgoal ***)

    REPEAT STRIP_TAC THEN ARM_SIM_TAC CURVE25519_X25519_EXEC [1];

    ALL_TAC] THEN

  (*** Clean up final goal and observe that the modified n is even ***)

  REWRITE_TAC[WORD_BITVAL_EQ_0; EXP; DIV_1] THEN
  GHOST_INTRO_TAC `xn:num`
   `bignum_from_memory (word_add stackpointer (word 320),4)` THEN
  GHOST_INTRO_TAC `zn:num`
   `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
  GHOST_INTRO_TAC `xm:num`
   `bignum_from_memory (word_add stackpointer (word 256),4)` THEN
  GHOST_INTRO_TAC `zm:num`
   `bignum_from_memory(word_add stackpointer (word 64),4)` THEN
  SUBGOAL_THEN `ODD nn <=> F` SUBST1_TAC THENL
   [EXPAND_TAC "nn" THEN REWRITE_TAC[ARITH_RULE `8 = 2 EXP 3`] THEN
    REWRITE_TAC[ODD_ADD; ODD_EXP; ODD_MOD_POW2; ODD_SUB] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES]] THEN

  SUBGOAL_THEN `X < p_25519` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[MOD_LT_EQ; p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
   check (free_in `n_input:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
   check (free_in `X_input:num`) o concl)) THEN

  (*** The state setup for the modular inverse ***)

  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (1--11) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add stackpointer (word 96),8 * 4)) s11 =
    p_25519`
  ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; p_25519] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN

  (*** The inlining of modular inverse ***)

  LOCAL_MODINV_TAC 12 THEN
  ABBREV_TAC
   `zn' =
    read(memory :> bytes(word_add stackpointer (word 64),8 * 4)) s12` THEN

  (*** The tweaking to force xn = 0 whenever zn = 0 ***)

  BIGNUM_LDIGITIZE_TAC "xn_"
   `read(memory :> bytes(word_add stackpointer (word 320),8 * 4)) s12` THEN
  BIGNUM_LDIGITIZE_TAC "zn_"
   `read(memory :> bytes(word_add stackpointer (word 160),8 * 4)) s12` THEN
  ARM_STEPS_TAC CURVE25519_X25519_EXEC (13--26) THEN

  SUBGOAL_THEN
   `read(memory :> bytes(word_add stackpointer (word 320),8 * 4)) s26 =
    if zn = 0 then 0 else xn`
  ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["zn"; "xn"] THEN
    REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; WORD_OR_EQ_0] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN
    REWRITE_TAC[COND_SWAP; CONJ_ACI] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN

  (*** Final multiplication ***)

  LOCAL_MUL_P25519_TAC 0 ["resx"; "xn"; "zm"] THEN

  (*** Completing the mathematics ***)

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC PUREX25519_UNIQUE_IMP THEN
  CONJ_TAC THENL [REWRITE_TAC[MOD_LT_EQ; p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`f:(int#int)ring`; `P:((int#int)#(int#int))option`] THEN

  ASM_CASES_TAC `X = 0` THEN
  ASM_REWRITE_TAC[RING_OF_NUM_0] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL
     [`f:(int#int)ring`; `ring_of_num f A_25519:int#int`;
      `ring_of_num f 1:int#int`; `P:((int#int)#(int#int))option`;
      `nn:num`] MONTGOMERY_XMAP_EQ_0_POW) THEN
    ASM_REWRITE_TAC[GSYM curve25519x_group; GSYM curve25519x] THEN
    ASM_SIMP_TAC[MONTGOMERY_NONSINGULAR_CURVE25519X; RING_OF_NUM] THEN
    ANTS_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`f:(int#int)ring`; `SOME(ring_0 f:int#int,ring_0 f)`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[MULT_CLAUSES; MOD_0; RING_OF_NUM_0]] THEN
    REWRITE_TAC[curve25519x_canonically_represents] THEN
    ASM_SIMP_TAC[CURVE25519X_GROUP; montgomery_xz] THEN
    GEN_REWRITE_TAC LAND_CONV [IN] THEN
    REWRITE_TAC[montgomery_curve; RING_OF_NUM; curve25519x] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[RING_OF_NUM_1; RING_OF_NUM_0; FIELD_NONTRIVIAL; RING_0] THEN
    UNDISCH_TAC `field(f:(int#int)ring)` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN FIELD_TAC;
    ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o SPECL
   [`f:(int#int)ring`; `P:((int#int)#(int#int))option`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[curve25519x_canonically_represents] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[RING_OF_NUM_1] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MONTGOMERY_XZ_XMAP o snd) THEN
    ASM_REWRITE_TAC[RING_OF_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_MOD] THEN
    ASM_SIMP_TAC[MOD_LT];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN

  REWRITE_TAC[curve25519x_canonically_represents] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o MATCH_MP GROUP_POW) THEN
  SPEC_TAC(`group_pow (curve25519x_group(f:(int#int)ring)) P nn`,
           `Q:((int#int)#(int#int))option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_xz; montgomery_xmap] THEN
  ASM_SIMP_TAC[RING_OF_NUM_EQ_0; DIVIDES_MOD; MOD_LT] THEN
  REWRITE_TAC[RING_OF_NUM] THEN ONCE_REWRITE_TAC[IN] THEN
  ASM_SIMP_TAC[CURVE25519X_GROUP] THEN
  REWRITE_TAC[montgomery_curve; curve25519x] THEN
  SIMP_TAC[MULT_CLAUSES; MOD_0; RING_OF_NUM_0] THEN
  MAP_EVERY X_GEN_TAC [`u:int#int`; `v:int#int`] THEN
  STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPEC `f:(int#int)ring` RING_OF_NUM_MOD) THEN
  ASM_SIMP_TAC[RING_OF_NUM_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[ring_div] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RING_RINV_UNIQUE THEN
  REWRITE_TAC[RING_OF_NUM; GSYM RING_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM RING_OF_NUM_1; RING_OF_NUM_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
  ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV);;

let CURVE25519_X25519_SUBROUTINE_CORRECT = time prove
 (`!res scalar n point X pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 432),432))
        [(word pc,0x1e2c); (res,32); (scalar,32); (point,32)] /\
    nonoverlapping (res,32) (word pc,0x1e2c)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [res; scalar; point] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_from_memory (point,4) s = X)
         (\s. read PC s = returnaddress /\
              bignum_from_memory (res,4) s = rfcx25519(n,X))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(res,32);
                      memory :> bytes(word_sub stackpointer (word 432),432)])`,
  ARM_ADD_RETURN_STACK_TAC CURVE25519_X25519_EXEC
    CURVE25519_X25519_CORRECT
    `[X19; X20; X21; X22; X23; X24]` 432);;
