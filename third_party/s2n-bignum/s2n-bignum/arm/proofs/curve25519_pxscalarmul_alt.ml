(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication for curve25519 with result in projective form.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/x25519.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/curve25519/curve25519_pxscalarmul_alt.o";;
 ****)

let curve25519_pxscalarmul_alt_mc = define_assert_from_elf
  "curve25519_pxscalarmul_alt_mc" "arm/curve25519/curve25519_pxscalarmul_alt.o"
[
  0xa9bf5bf3;       (* arm_STP X19 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf57f4;       (* arm_STP X20 X21 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10403ff;       (* arm_SUB SP SP (rvalue (word 256)) *)
  0xaa0003f1;       (* arm_MOV X17 X0 *)
  0xaa0103f4;       (* arm_MOV X20 X1 *)
  0xaa0203f3;       (* arm_MOV X19 X2 *)
  0xd2800022;       (* arm_MOV X2 (rvalue (word 1)) *)
  0xa90c7fe2;       (* arm_STP X2 XZR SP (Immediate_Offset (iword (&192))) *)
  0xa90d7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&208))) *)
  0xa9067fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&96))) *)
  0xa9077fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&112))) *)
  0xa9400660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&0))) *)
  0xa90a07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa9410660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&16))) *)
  0xa90b07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&176))) *)
  0xa9420660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&32))) *)
  0xa9007fe2;       (* arm_STP X2 XZR SP (Immediate_Offset (iword (&0))) *)
  0xa9017fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&16))) *)
  0xaa1f03f6;       (* arm_MOV X22 XZR *)
  0xd2801ff5;       (* arm_MOV X21 (rvalue (word 255)) *)
  0xa94a1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94b23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xd2f00004;       (* arm_MOVZ X4 (word 32768) 48 *)
  0xda040108;       (* arm_SBC X8 X8 X4 *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa94c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xa94617e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&96))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa94d0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0xa9471fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&112))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0x9a070063;       (* arm_ADC X3 X3 X7 *)
  0xa90207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&32))) *)
  0xa9030fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0xa94c1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa9460fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&96))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94d23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa9470fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&112))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xd2f00004;       (* arm_MOVZ X4 (word 32768) 48 *)
  0xda040108;       (* arm_SBC X8 X8 X4 *)
  0xa9061be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&96))) *)
  0xa90723e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xa94a07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa94017e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&0))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa94b0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&176))) *)
  0xa9411fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&16))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0x9a070063;       (* arm_ADC X3 X3 X7 *)
  0xa90007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9010fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  0xa9093fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&144))) *)
  0xd346fea0;       (* arm_LSR X0 X21 6 *)
  0xf8607a82;       (* arm_LDR X2 X20 (Shiftreg_Offset X0 3) *)
  0x9ad52442;       (* arm_LSRV X2 X2 X21 *)
  0x92400042;       (* arm_AND X2 X2 (rvalue (word 1)) *)
  0xeb0202df;       (* arm_CMP X22 X2 *)
  0xaa0203f6;       (* arm_MOV X22 X2 *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9460fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&96))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa90e07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&224))) *)
  0xa94507e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&80))) *)
  0xa9470fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa90f07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&240))) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9420fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa90c07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xa94107e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&16))) *)
  0xa9430fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa90d07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&208))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9472be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
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
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  0xa94e0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&224))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94f17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&240))) *)
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
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90e27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&224))) *)
  0xa90f2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&240))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa94a0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&160))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa94b0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&176))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9001be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa90123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa94c0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&192))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94d17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&208))) *)
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
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90c27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&192))) *)
  0xa90d2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&208))) *)
  0xa94813e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa94b23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa9400fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&16))) *)
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
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa94c1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa94e0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&224))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94d23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa94f0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&240))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa94a0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&160))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94b17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&176))) *)
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
  0xb241016b;       (* arm_ORR X11 X11 (rvalue (word 9223372036854775808)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b020c67;       (* arm_MADD X7 X3 X2 X3 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0x9a9f3063;       (* arm_CSEL X3 X3 XZR Condition_CC *)
  0xeb030108;       (* arm_SUBS X8 X8 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0xa90a27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
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
  0xa94e23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&224))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94f23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&240))) *)
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
  0xa90613e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9071be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
  0xa94e23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&224))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94f2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&240))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa94d1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
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
  0xa90c37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&192))) *)
  0xa90d3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&208))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9402267;       (* arm_LDP X7 X8 X19 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412a69;       (* arm_LDP X9 X10 X19 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
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
  0xa90037ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&0))) *)
  0xa9013fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&16))) *)
  0xa94813e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9472be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
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
  0xa90637ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&96))) *)
  0xa9073fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&112))) *)
  0xf10006b5;       (* arm_SUBS X21 X21 (rvalue (word 1)) *)
  0x54ff8a22;       (* arm_BCS (word 2093380) *)
  0xa9400660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&0))) *)
  0xaa010000;       (* arm_ORR X0 X0 X1 *)
  0xa9410e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&16))) *)
  0xaa030042;       (* arm_ORR X2 X2 X3 *)
  0xaa020000;       (* arm_ORR X0 X0 X2 *)
  0xeb1f001f;       (* arm_CMP X0 XZR *)
  0x9a9f17e0;       (* arm_CSET X0 Condition_EQ *)
  0xf94003e1;       (* arm_LDR X1 SP (Immediate_Offset (word 0)) *)
  0xaa000021;       (* arm_ORR X1 X1 X0 *)
  0xf90003e1;       (* arm_STR X1 SP (Immediate_Offset (word 0)) *)
  0xf94063e2;       (* arm_LDR X2 SP (Immediate_Offset (word 192)) *)
  0xaa000042;       (* arm_ORR X2 X2 X0 *)
  0xf90063e2;       (* arm_STR X2 SP (Immediate_Offset (word 192)) *)
  0xeb1f02df;       (* arm_CMP X22 XZR *)
  0xa94a07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa94c0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&192))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa9000620;       (* arm_STP X0 X1 X17 (Immediate_Offset (iword (&0))) *)
  0xa94b07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&176))) *)
  0xa94d0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa9010620;       (* arm_STP X0 X1 X17 (Immediate_Offset (iword (&16))) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9460fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&96))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa9020620;       (* arm_STP X0 X1 X17 (Immediate_Offset (iword (&32))) *)
  0xa94107e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&16))) *)
  0xa9470fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa9030620;       (* arm_STP X0 X1 X17 (Immediate_Offset (iword (&48))) *)
  0x910403ff;       (* arm_ADD SP SP (rvalue (word 256)) *)
  0xa8c157f4;       (* arm_LDP X20 X21 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf3;       (* arm_LDP X19 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CURVE25519_PXSCALARMUL_ALT_EXEC = ARM_MK_EXEC_RULE curve25519_pxscalarmul_alt_mc;;

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

let p25519weakredlemma = prove
 (`!n. n <= 2 EXP 62 * 2 EXP 256
       ==> let q = n DIV 2 EXP 255 in
           q < 2 EXP 64 /\
           q * p_25519 <= n /\
           n < q * p_25519 + 2 * p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let lvs =
 ["x",[`X19`;`0`];
  "resx",[`X17`;`0`];
  "resz",[`X17`;`32`];
  "zm",[`SP`;`0`];
  "sm",[`SP`;`0`];
  "dpro",[`SP`;`0`];
  "sn",[`SP`;`32`];
  "dm",[`SP`;`64`];
  "zn",[`SP`;`96`];
  "dn",[`SP`;`96`];
  "e",[`SP`;`96`];
  "dmsn",[`SP`;`128`];
  "p",[`SP`;`128`];
  "xm",[`SP`;`160`];
  "dnsm",[`SP`;`160`];
  "spro",[`SP`;`160`];
  "xn",[`SP`;`192`];
  "s",[`SP`;`192`];
  "d",[`SP`;`224`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 100 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                    X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--67) (1--67) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (68--92) (68--92) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (93--100) (93--100) THEN
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

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_p25519                                                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 78 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
        aligned 16 (read SP t) /\
        nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                  read PC s = pcin /\
                  read SP s = read SP t /\
                  read X17 s = read X17 t /\
                  read X19 s = read X19 t /\
                  read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
             (\s. read PC s = pcout /\
                  read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s = (n EXP 2) MOD p_25519)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14] ,,
           MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--45) (1--45) THEN
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

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (46--70) (46--70) THEN
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

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  SUBGOAL_THEN
   `&(val(word(19 + 19 * val(sum_s64:int64)):int64)):real =
    &19 * (&(val(sum_s64:int64)) + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `19 * (x + 1) = 19 + 19 * x`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s64:int64) + 1 <= 80` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_or sum_s60 (word 9223372036854775808:int64))):real =
    &2 pow 63 + &(val(sum_s62:int64)) / &2`
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
  SUBGOAL_THEN
   `&2 pow 256 * (&(bitval carry_s70) - &1:real) +
    &(bignum_of_wordlist[sum_s67; sum_s68; sum_s69; sum_s70]):real =
    &(38 * h + l) - &((val(sum_s64:int64) + 1) * p_25519)`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (71--78) (71--78) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s64:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l < (val(sum_s64:int64) + 1) * p_25519 <=> ~carry_s70`
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
    ASM_CASES_TAC `carry_s70:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of mul_4                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 94 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 m * n) (mod p_25519))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                    X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--67) (1--67) THEN
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

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (68--92) (68--94) THEN
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
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  UNDISCH_TAC
   `&2 pow 64 * &(val(mulhi_s88:int64)) + &(val(mullo_s88:int64)) =
    &19 * &(val(sum_s86:int64))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= 80 ==> a < 80`)) THEN
  DISCH_THEN(fun bth -> DISCH_THEN(fun th ->
        MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE [bth] [th])))) THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT2) THEN

  SUBGOAL_THEN
   `&(val(word_and sum_s82 (word 9223372036854775807:int64))):real =
    &(val(sum_s84:int64)) / &2`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
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

  REWRITE_TAC[GSYM CONG; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\
        (&0 <= ca - q * p /\ ca - q * p < p2) /\
        (&0 <= ca - q * p /\ ca - q * p < p2 ==> x = ca - q * p)
        ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s86:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519`;
      `38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`] THEN
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

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 72 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n.
      read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 n EXP 2)
                (mod p_25519))
        (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                    X10; X11; X12; X13; X14] ,,
         MAYCHANGE
          [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--45) (1--45) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (46--70) (46--72) THEN
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
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

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
        ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
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

(* ------------------------------------------------------------------------- *)
(* Instances of add_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 10 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < p_25519 /\ n < p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                     m + n))
        (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC [3;4;7;8] (1--10) THEN
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
(* Instances of sub_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
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
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC
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
(* Instances of add_twice4                                                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < 2 * p_25519 /\ n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                      m + n) (mod p_25519)))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (11--14) (9--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= m + n then (&m + &n) - &2 * &p_25519:int else &m + &n` THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
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
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= m + n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4                                                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
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
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (11--14) (9--16) THEN
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
(* Instances of cmadd_4 (actually there is only one, specific constant).     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMADD_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 32 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
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
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (22--24) (22--24) THEN
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
  ARM_STEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (25--26) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (27--30) (27--32) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_pxscalarmul_alt_mc 10 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !b. read ZF t = b
     ==>
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0xfa8) (word_add (read p3 t) (word n3),8 * 4) /\
      nonoverlapping (stackpointer:int64,256) (res,64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
                read ZF s = b /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (if b then n else m))
        (MAYCHANGE [PC; X0; X1; X2; X3] ,, MAYCHANGE [events] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_STEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

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
 (`P IN group_carrier (curve25519x_group(f:A ring)) /\
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
   ~(x:A = ring_0 f) /\
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
   ~(x:A = ring_0 f) /\
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

let CURVE25519_PXSCALARMUL_ALT_CORRECT = time prove
 (`!res scalar n point X pc stackpointer.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(res,64); (stackpointer,256)]
      [(word pc,0xfa8); (scalar,32); (point,32)] /\
    nonoverlapping (res,64) (stackpointer,256)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
              read PC s = word(pc + 0xc) /\
              read SP s = stackpointer /\
              C_ARGUMENTS [res; scalar; point] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_from_memory (point,4) s = X)
         (\s. read PC s = word (pc + 0xf98) /\
              !(f:A ring) P.
                  field f /\ ring_char f = p_25519 /\
                  P IN group_carrier(curve25519x_group f) /\
                  curve25519x_canonically_represents f P (X,1)
                  ==> curve25519x_canonically_represents f
                        (group_pow (curve25519x_group f) P n)
                        (bignum_pair_from_memory(res,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(stackpointer,256)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `nn:num`; `point:int64`; `X:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  ENSURES_WHILE_PDOWN_TAC `256` `pc + 0x50` `pc + 0xf0c`
   `\i s.
     (read SP s = stackpointer /\
      read X17 s = res /\
      read X19 s = point /\
      read X20 s = scalar /\
      read X21 s = word_sub (word i) (word 1) /\
      bignum_from_memory (point,4) s = X /\
      bignum_from_memory (scalar,4) s = nn /\
      read X22 s =
      word(bitval(ODD(nn DIV 2 EXP i))) /\
      !(f:A ring) P.
        field f /\ ring_char f = p_25519 /\
        P IN group_carrier(curve25519x_group f) /\
        curve25519x_canonically_represents f P (X,1)
      ==>
      if X = 0 then
        bignum_from_memory(stackpointer,4) s <= 1 /\
        bignum_from_memory(word_add stackpointer (word 96),4) s = 0 /\
        bignum_from_memory(word_add stackpointer (word 160),4) s = 0 /\
        bignum_from_memory(word_add stackpointer (word 192),4) s <= 1
      else
      curve25519x_canonically_represents f
       (group_pow (curve25519x_group f) P
           (if ODD(nn DIV 2 EXP i)
            then nn DIV 2 EXP i + 1 else nn DIV 2 EXP i))
       (bignum_from_memory(word_add stackpointer (word 192),4) s,
        bignum_from_memory(word_add stackpointer (word 96),4) s) /\
      curve25519x_canonically_represents f
       (group_pow (curve25519x_group f) P
          (if ODD(nn DIV 2 EXP i)
           then nn DIV 2 EXP i else nn DIV 2 EXP i + 1))
       (bignum_from_memory(word_add stackpointer (word 160),4) s,
        bignum_from_memory(stackpointer,4) s)) /\
     (read CF s <=> ~(i = 0))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    BIGNUM_TERMRANGE_TAC `4` `nn:num` THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (point,8 * 4)) s0` THEN
    ARM_STEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DIV_LT] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_SIMP_TAC[GROUP_POW_1] THEN REWRITE_TAC[group_pow] THEN
    SIMP_TAC[CURVE25519X_GROUP] THEN
    REWRITE_TAC[curve25519x_canonically_represents; montgomery_xz] THEN
    REWRITE_TAC[RING_OF_NUM] THEN
    REWRITE_TAC[RING_OF_NUM_1; RING_OF_NUM_0; p_25519] THEN
    SIMP_TAC[FIELD_NONTRIVIAL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID];

    ALL_TAC; (*** The interesting part is done below ***)

    REPEAT STRIP_TAC THEN ARM_SIM_TAC CURVE25519_PXSCALARMUL_ALT_EXEC [1];

    REWRITE_TAC[WORD_BITVAL_EQ_0; EXP; DIV_1] THEN
    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add stackpointer (word 192),4)` THEN
    GHOST_INTRO_TAC `zn:num`
     `bignum_from_memory (word_add stackpointer (word 96),4)` THEN
    GHOST_INTRO_TAC `xm:num`
     `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
    GHOST_INTRO_TAC `zm:num` `bignum_from_memory(stackpointer,4)` THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read(memory :> bytes(point,8 * 4)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "zm_"
     `read(memory :> bytes(stackpointer,8 * 4)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "xn_"
     `read(memory :> bytes(word_add stackpointer (word 192),8 * 4)) s0` THEN
    ARM_STEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (1--14) THEN
    SUBGOAL_THEN
     `(if ~(val
            (word_sub (word_or (word_or x_0 x_1) (word_or x_2 x_3):int64)
                      (word 0)) =
            0)
       then word 0
       else word 1):int64 =
      word(bitval(X = 0))`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "X" THEN
      REWRITE_TAC[VAL_EQ_0; WORD_SUB_0; BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN
      SIMP_TAC[bitval; COND_SWAP; WORD_OR_EQ_0; CONJ_ACI] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `read(memory :> bytes(stackpointer,8 * 4)) s14 =
      bignum_of_wordlist
       [word_or zm_0 (word(bitval(X = 0))); zm_1; zm_2; zm_3] /\
      read(memory :> bytes(word_add stackpointer (word 192),8 * 4)) s14 =
      bignum_of_wordlist[word_or xn_0 (word(bitval(X = 0))); xn_1; xn_2; xn_3]`
    STRIP_ASSUME_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    LOCAL_MUX_4_TAC 1 ["resx"; "xm"; "xn"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_SUB_0; WORD_BITVAL_EQ_0]) THEN
    LOCAL_MUX_4_TAC 0 ["resz"; "zm"; "zn"] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`f:A ring`; `P:(A#A)option`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:A ring`; `P:(A#A)option`]) THEN
    ASM_REWRITE_TAC[WORD_RULE `word(8 * 4) = word 32`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `X = 0` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0; VAL_WORD_1] THENL
     [SUBGOAL_THEN
       `group_pow (curve25519x_group (f:A ring)) P nn =
        if EVEN nn then NONE else SOME(ring_0 f,ring_0 f)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `P IN group_carrier (curve25519x_group(f:A ring))` THEN
        FIRST_X_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I
         [curve25519x_canonically_represents]) THEN
        SPEC_TAC(`P:(A#A)option`,`P:(A#A)option`) THEN
        ASM_REWRITE_TAC[montgomery_xz; FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
        ASM_SIMP_TAC[CURVE25519X_GROUP; RING_OF_NUM_0] THEN
        REWRITE_TAC[SET_RULE `SOME p IN s <=> s(SOME p)`] THEN
        SIMP_TAC[ring_div; RING_MUL_LZERO; RING_OF_NUM; RING_INV] THEN
        ASM_SIMP_TAC[RING_0; RING_OF_NUM_1; FIELD_NONTRIVIAL] THEN
        REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1] THEN
        X_GEN_TAC `y:A` THEN REWRITE_TAC[GSYM RING_OF_NUM_0] THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL [`f:A ring`; `0:num`; `y:A`]
         SPECIALLY_NONSINGULAR_CURVE25519X) THEN
        ASM_REWRITE_TAC[RING_OF_NUM_0] THEN DISCH_THEN SUBST1_TAC THEN
        SPEC_TAC(`nn:num`,`n:num`) THEN INDUCT_TAC THEN
        ASM_REWRITE_TAC[ARITH_EVEN; EVEN; COND_SWAP; group_pow] THEN
        ASM_SIMP_TAC[CURVE25519X_GROUP] THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[montgomery_add; curve25519x];
        ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["zm"; "xn"] THEN
      REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
      SUBGOAL_THEN
       `1 = bignum_of_wordlist[word 1:int64; word 0; word 0; word 0]`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
       [REWRITE_TAC[bignum_of_wordlist] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ; BIGNUM_OF_WORDLIST_EQ_0]] THEN
      REWRITE_TAC[ALL; VAL_WORD_BITVAL; BITVAL_EQ_0; NOT_ODD] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[curve25519x_canonically_represents; montgomery_xz] THEN
      ASM_SIMP_TAC[RING_OF_NUM_1; RING_OF_NUM_0; FIELD_NONTRIVIAL; ring_div;
                   RING_0; RING_1; RING_MUL_LZERO; RING_INV; RING_1] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[WORD_OR_0; VAL_WORD_BITVAL; BITVAL_EQ_0; COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]]] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_BITVAL_EQ_0; EXP; DIV_1] THEN
  GHOST_INTRO_TAC `xn:num`
   `bignum_from_memory (word_add stackpointer (word 192),4)` THEN
  GHOST_INTRO_TAC `zn:num`
   `bignum_from_memory (word_add stackpointer (word 96),4)` THEN
  GHOST_INTRO_TAC `xm:num`
   `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
  GHOST_INTRO_TAC `zm:num` `bignum_from_memory(stackpointer,4)` THEN
  REWRITE_TAC[WORD_RULE `word_sub (word (i + 1)) (word 1) = word i`] THEN

  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_SUB_4_TAC 0 ["dm"; "xm"; "zm"] THEN
  LOCAL_ADD_4_TAC 0 ["sn"; "xn"; "zn"] THEN
  LOCAL_SUB_4_TAC 0 ["dn"; "xn"; "zn"] THEN
  LOCAL_ADD_4_TAC 0 ["sm"; "xm"; "zm"] THEN
  LOCAL_MUL_4_TAC 0 ["dmsn"; "sn"; "dm"] THEN

  SUBGOAL_THEN
   `read(memory :> bytes64
      (word_add scalar (word(8 * val(word_ushr (word i:int64) 6))))) s5 =
    word(nn DIV (2 EXP (64 * i DIV 64)) MOD 2 EXP (64 * 1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 256 ==> MIN (4 - i DIV 64) 1 = 1`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
    VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC (6--11) THEN
  SUBGOAL_THEN
   `word_and
      (word_jushr (word((nn DIV 2 EXP (64 * i DIV 64)) MOD 2 EXP 64))
                  (word i))
      (word 1:int64) =
    word(bitval(ODD(nn DIV 2 EXP i)))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_AND_1_BITVAL; word_jushr; MOD_64_CLAUSES;
                DIMINDEX_64; VAL_WORD; MOD_MOD_REFL] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[BIT_LSB; VAL_WORD_USHR] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
    REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
    REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + 64 = i + (64 - i MOD 64)`] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; ODD_MOD_POW2] THEN
    MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_SUB_EQ_0;
    MESON[VAL_WORD_BITVAL; VAL_EQ; EQ_BITVAL]
     `word(bitval b) = word(bitval c) <=> (b <=> c)`]) THEN

  LOCAL_MUX_4_TAC 0 ["d"; "dm"; "dn"] THEN
  LOCAL_MUX_4_TAC 0 ["s"; "sm"; "sn"] THEN
  LOCAL_MUL_4_TAC 0 ["dnsm"; "sm"; "dn"] THEN
  LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["dpro"; "dmsn"; "dnsm"] THEN
  LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["spro"; "dmsn"; "dnsm"] THEN
  LOCAL_SQR_4_TAC 0 ["dpro"; "dpro"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
  LOCAL_SQR_P25519_TAC 0 ["xm"; "spro"] THEN
  LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
  LOCAL_MUL_P25519_TAC 0 ["xn"; "s"; "d"] THEN
  LOCAL_MUL_P25519_TAC 0 ["zm"; "dpro"; "x"] THEN
  LOCAL_MUL_P25519_TAC 0 ["zn"; "p"; "e"] THEN

  ARM_STEPS_TAC CURVE25519_PXSCALARMUL_ALT_EXEC [28] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN
  REWRITE_TAC[BITVAL_BOUND; ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
  DISCARD_STATE_TAC "s28" THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`aligned a b`; `val(word i) = i`; `nonoverlapping_modulo a b c`] THEN

  (*** Get started and handle the degenerate X = 0 case ***)

  MAP_EVERY X_GEN_TAC [`f:A ring`; `P:(A#A)option`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:A ring`; `P:(A#A)option`]) THEN
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

  DISCH_TAC THEN
  SUBGOAL_THEN
   `(ring_of_num f xm':A,ring_of_num f zm') =
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
    FIRST_X_ASSUM(CONJUNCTS_THEN(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I
     [curve25519x_canonically_represents])) THEN
    GEN_REWRITE_TAC I [GSYM IMP_CONJ_ALT] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [curve25519x_canonically_represents]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2)) THEN
    UNDISCH_TAC `P IN group_carrier(curve25519x_group(f:A ring))`] THEN

  SUBGOAL_THEN `~(ring_of_num (f:A ring) X = ring_0 f)` MP_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[NOT_LE];
    MAP_EVERY UNDISCH_TAC
     [`ring_char(f:A ring) = p_25519`; `field(f:A ring)`] THEN
    POP_ASSUM_LIST(K ALL_TAC)] THEN

  REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [DISJ_CASES_THEN SUBST_ALL_TAC (TAUT `(b <=> ODD n) \/ (b <=> ~ODD n)`) THEN
    REWRITE_TAC[TAUT `~(~p <=> p)`] THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1);
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2)] THEN
    UNDISCH_TAC `P IN group_carrier(curve25519x_group(f:A ring))` THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma_double) THEN
    ASM_REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN
    REWRITE_TAC[ARITH_RULE `(2 * n + 1) + 1 = 2 * (n + 1)`];

    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[lemma_diffadd1] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 5 RAND_CONV) [CONJ_SYM] THEN
    REWRITE_TAC[lemma_diffadd2]]);;

let CURVE25519_PXSCALARMUL_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar n point X pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(res,64); (word_sub stackpointer (word 288),288)]
      [(word pc,0xfa8); (scalar,32); (point,32)] /\
    nonoverlapping (res,64) (word_sub stackpointer (word 288),288)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_pxscalarmul_alt_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [res; scalar; point] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_from_memory (point,4) s = X)
         (\s. read PC s = returnaddress /\
              !(f:A ring) P.
                  field f /\ ring_char f = p_25519 /\
                  P IN group_carrier(curve25519x_group f) /\
                  curve25519x_canonically_represents f P (X,1)
                  ==> curve25519x_canonically_represents f
                        (group_pow (curve25519x_group f) P n)
                        (bignum_pair_from_memory(res,4) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(word_sub stackpointer (word 288),288)])`,
  ARM_ADD_RETURN_STACK_TAC CURVE25519_PXSCALARMUL_ALT_EXEC
    CURVE25519_PXSCALARMUL_ALT_CORRECT
    `[X19; X20; X21; X22]` 288);;
