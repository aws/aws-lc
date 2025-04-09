(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Jacobian coordinates for SECG secp256k1 curve.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/secp256k1.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/secp256k1/secp256k1_jdouble_alt.o";;
 ****)

let secp256k1_jdouble_alt_mc = define_assert_from_elf
  "secp256k1_jdouble_alt_mc" "arm/secp256k1/secp256k1_jdouble_alt.o"
[
  0xd10603ff;       (* arm_SUB SP SP (rvalue (word 384)) *)
  0xaa0003ef;       (* arm_MOV X15 X0 *)
  0xaa0103f0;       (* arm_MOV X16 X1 *)
  0xd2807a31;       (* arm_MOV X17 (rvalue (word 977)) *)
  0xb2600231;       (* arm_ORR X17 X17 (rvalue (word 4294967296)) *)
  0xa9420e02;       (* arm_LDP X2 X3 X16 (Immediate_Offset (iword (&32))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9431604;       (* arm_LDP X4 X5 X16 (Immediate_Offset (iword (&48))) *)
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
  0x9b0c7e27;       (* arm_MUL X7 X17 X12 *)
  0x9bcc7e24;       (* arm_UMULH X4 X17 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7e27;       (* arm_MUL X7 X17 X13 *)
  0x9bcd7e2d;       (* arm_UMULH X13 X17 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7e27;       (* arm_MUL X7 X17 X14 *)
  0x9bce7e2e;       (* arm_UMULH X14 X17 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067e27;       (* arm_MUL X7 X17 X6 *)
  0x9bc67e26;       (* arm_UMULH X6 X17 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab040129;       (* arm_ADDS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0x91000582;       (* arm_ADD X2 X12 (rvalue (word 1)) *)
  0x9b027e27;       (* arm_MUL X7 X17 X2 *)
  0x9bc27e26;       (* arm_UMULH X6 X17 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0x9a9f3223;       (* arm_CSEL X3 X17 XZR Condition_CC *)
  0xeb030108;       (* arm_SUBS X8 X8 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xa90227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&32))) *)
  0xa9032fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&48))) *)
  0xa9400e02;       (* arm_LDP X2 X3 X16 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9411604;       (* arm_LDP X4 X5 X16 (Immediate_Offset (iword (&16))) *)
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
  0x9b0c7e27;       (* arm_MUL X7 X17 X12 *)
  0x9bcc7e24;       (* arm_UMULH X4 X17 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7e27;       (* arm_MUL X7 X17 X13 *)
  0x9bcd7e2d;       (* arm_UMULH X13 X17 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7e27;       (* arm_MUL X7 X17 X14 *)
  0x9bce7e2e;       (* arm_UMULH X14 X17 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067e27;       (* arm_MUL X7 X17 X6 *)
  0x9bc67e26;       (* arm_UMULH X6 X17 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab040129;       (* arm_ADDS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0x91000582;       (* arm_ADD X2 X12 (rvalue (word 1)) *)
  0x9b027e27;       (* arm_MUL X7 X17 X2 *)
  0x9bc27e26;       (* arm_UMULH X6 X17 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0x9a9f3223;       (* arm_CSEL X3 X17 XZR Condition_CC *)
  0xeb030108;       (* arm_SUBS X8 X8 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa9420a01;       (* arm_LDP X1 X2 X16 (Immediate_Offset (iword (&32))) *)
  0xd37ff820;       (* arm_LSL X0 X1 1 *)
  0xa9431203;       (* arm_LDP X3 X4 X16 (Immediate_Offset (iword (&48))) *)
  0xf241009f;       (* arm_TST X4 (rvalue (word 9223372036854775808)) *)
  0x9a9f1225;       (* arm_CSEL X5 X17 XZR Condition_NE *)
  0x93c1fc41;       (* arm_EXTR X1 X2 X1 63 *)
  0xab050000;       (* arm_ADDS X0 X0 X5 *)
  0x93c2fc62;       (* arm_EXTR X2 X3 X2 63 *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0x93c3fc83;       (* arm_EXTR X3 X4 X3 63 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xa90607e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9070fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0xa9401203;       (* arm_LDP X3 X4 X16 (Immediate_Offset (iword (&0))) *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9432be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c60;       (* arm_UMULH X0 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c61;       (* arm_UMULH X1 X3 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa9411a05;       (* arm_LDP X5 X6 X16 (Immediate_Offset (iword (&16))) *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9bca7c83;       (* arm_UMULH X3 X4 X10 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9b077cab;       (* arm_MUL X11 X5 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9b0a7cab;       (* arm_MUL X11 X5 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bca7ca4;       (* arm_UMULH X4 X5 X10 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b077ccb;       (* arm_MUL X11 X6 X7 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0x9b087ccb;       (* arm_MUL X11 X6 X8 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9b097ccb;       (* arm_MUL X11 X6 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7ccb;       (* arm_MUL X11 X6 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9bca7cc5;       (* arm_UMULH X5 X6 X10 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9b017e2b;       (* arm_MUL X11 X17 X1 *)
  0x9bc17e29;       (* arm_UMULH X9 X17 X1 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037e2b;       (* arm_MUL X11 X17 X3 *)
  0x9bc37e23;       (* arm_UMULH X3 X17 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047e2b;       (* arm_MUL X11 X17 X4 *)
  0x9bc47e24;       (* arm_UMULH X4 X17 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057e2b;       (* arm_MUL X11 X17 X5 *)
  0x9bc57e25;       (* arm_UMULH X5 X17 X5 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a9f37e1;       (* arm_CSET X1 Condition_CS *)
  0xab0901ad;       (* arm_ADDS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0xba040000;       (* arm_ADCS X0 X0 X4 *)
  0x9a050021;       (* arm_ADC X1 X1 X5 *)
  0xa91437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&320))) *)
  0xa91503ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&336))) *)
  0xf900b3e1;       (* arm_STR X1 SP (Immediate_Offset (word 352)) *)
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
  0x9b0c7e27;       (* arm_MUL X7 X17 X12 *)
  0x9bcc7e24;       (* arm_UMULH X4 X17 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7e27;       (* arm_MUL X7 X17 X13 *)
  0x9bcd7e2d;       (* arm_UMULH X13 X17 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7e27;       (* arm_MUL X7 X17 X14 *)
  0x9bce7e2e;       (* arm_UMULH X14 X17 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067e27;       (* arm_MUL X7 X17 X6 *)
  0x9bc67e26;       (* arm_UMULH X6 X17 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab040129;       (* arm_ADDS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xa90827e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&128))) *)
  0xa9092fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&144))) *)
  0xf90053ec;       (* arm_STR X12 SP (Immediate_Offset (word 160)) *)
  0xa9441203;       (* arm_LDP X3 X4 X16 (Immediate_Offset (iword (&64))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9472be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c60;       (* arm_UMULH X0 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c61;       (* arm_UMULH X1 X3 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa9451a05;       (* arm_LDP X5 X6 X16 (Immediate_Offset (iword (&80))) *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9bca7c83;       (* arm_UMULH X3 X4 X10 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9b077cab;       (* arm_MUL X11 X5 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9b0a7cab;       (* arm_MUL X11 X5 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bca7ca4;       (* arm_UMULH X4 X5 X10 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b077ccb;       (* arm_MUL X11 X6 X7 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0x9b087ccb;       (* arm_MUL X11 X6 X8 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9b097ccb;       (* arm_MUL X11 X6 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7ccb;       (* arm_MUL X11 X6 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9bca7cc5;       (* arm_UMULH X5 X6 X10 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9b017e2b;       (* arm_MUL X11 X17 X1 *)
  0x9bc17e29;       (* arm_UMULH X9 X17 X1 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037e2b;       (* arm_MUL X11 X17 X3 *)
  0x9bc37e23;       (* arm_UMULH X3 X17 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047e2b;       (* arm_MUL X11 X17 X4 *)
  0x9bc47e24;       (* arm_UMULH X4 X17 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057e2b;       (* arm_MUL X11 X17 X5 *)
  0x9bc57e25;       (* arm_UMULH X5 X17 X5 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a9f37e1;       (* arm_CSET X1 Condition_CS *)
  0xab0901ad;       (* arm_ADDS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0xba040000;       (* arm_ADCS X0 X0 X4 *)
  0x9a050021;       (* arm_ADC X1 X1 X5 *)
  0x91000428;       (* arm_ADD X8 X1 (rvalue (word 1)) *)
  0x9b087e2b;       (* arm_MUL X11 X17 X8 *)
  0x9bc87e29;       (* arm_UMULH X9 X17 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0x9a9f3227;       (* arm_CSEL X7 X17 XZR Condition_CC *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f0000;       (* arm_SBC X0 X0 XZR *)
  0xa90435ec;       (* arm_STP X12 X13 X15 (Immediate_Offset (iword (&64))) *)
  0xa90501ee;       (* arm_STP X14 X0 X15 (Immediate_Offset (iword (&80))) *)
  0xd280018a;       (* arm_MOV X10 (rvalue (word 12)) *)
  0xa95417e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&320))) *)
  0x9b0a7c80;       (* arm_MUL X0 X4 X10 *)
  0x9b0a7ca1;       (* arm_MUL X1 X5 X10 *)
  0xa9551fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&336))) *)
  0x9b0a7cc2;       (* arm_MUL X2 X6 X10 *)
  0x9b0a7ce3;       (* arm_MUL X3 X7 X10 *)
  0xf940b3ed;       (* arm_LDR X13 SP (Immediate_Offset (word 352)) *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab040021;       (* arm_ADDS X1 X1 X4 *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xba050042;       (* arm_ADCS X2 X2 X5 *)
  0x9bca7cc6;       (* arm_UMULH X6 X6 X10 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0x9bca7ce4;       (* arm_UMULH X4 X7 X10 *)
  0x9b0a7dad;       (* arm_MUL X13 X13 X10 *)
  0x9a0d0089;       (* arm_ADC X9 X4 X13 *)
  0xb2580129;       (* arm_ORR X9 X9 (rvalue (word 1099511627776)) *)
  0xd280012a;       (* arm_MOV X10 (rvalue (word 9)) *)
  0xa9483bed;       (* arm_LDP X13 X14 SP (Immediate_Offset (iword (&128))) *)
  0x9b0a7dc5;       (* arm_MUL X5 X14 X10 *)
  0x9bca7dc6;       (* arm_UMULH X6 X14 X10 *)
  0xab5160a5;       (* arm_ADDS X5 X5 (Shiftedreg X17 LSR 24) *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0x9b0a7da4;       (* arm_MUL X4 X13 X10 *)
  0xab11a084;       (* arm_ADDS X4 X4 (Shiftedreg X17 LSL 40) *)
  0x9bca7dad;       (* arm_UMULH X13 X13 X10 *)
  0xba0d00a5;       (* arm_ADCS X5 X5 X13 *)
  0xa9493bed;       (* arm_LDP X13 X14 SP (Immediate_Offset (iword (&144))) *)
  0x9b0a7dac;       (* arm_MUL X12 X13 X10 *)
  0x9bca7da7;       (* arm_UMULH X7 X13 X10 *)
  0xf94053ed;       (* arm_LDR X13 SP (Immediate_Offset (word 160)) *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0x9b0a7dcc;       (* arm_MUL X12 X14 X10 *)
  0x9bca7dc8;       (* arm_UMULH X8 X14 X10 *)
  0x9b0a7dad;       (* arm_MUL X13 X13 X10 *)
  0xba0c00e7;       (* arm_ADCS X7 X7 X12 *)
  0x9a0d0108;       (* arm_ADC X8 X8 X13 *)
  0xeb040000;       (* arm_SUBS X0 X0 X4 *)
  0xfa050021;       (* arm_SBCS X1 X1 X5 *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xda080124;       (* arm_SBC X4 X9 X8 *)
  0x9100048a;       (* arm_ADD X10 X4 (rvalue (word 1)) *)
  0x9b0a7e24;       (* arm_MUL X4 X17 X10 *)
  0x9bca7e25;       (* arm_UMULH X5 X17 X10 *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0x9a9f322b;       (* arm_CSEL X11 X17 XZR Condition_CC *)
  0xeb0b0000;       (* arm_SUBS X0 X0 X11 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xa90407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0063;       (* arm_SBC X3 X3 XZR *)
  0xa9050fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&80))) *)
  0xa9420fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&48))) *)
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
  0x9b0c7e27;       (* arm_MUL X7 X17 X12 *)
  0x9bcc7e24;       (* arm_UMULH X4 X17 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7e27;       (* arm_MUL X7 X17 X13 *)
  0x9bcd7e2d;       (* arm_UMULH X13 X17 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7e27;       (* arm_MUL X7 X17 X14 *)
  0x9bce7e2e;       (* arm_UMULH X14 X17 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067e27;       (* arm_MUL X7 X17 X6 *)
  0x9bc67e26;       (* arm_UMULH X6 X17 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab040129;       (* arm_ADDS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xa90c27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&192))) *)
  0xa90d2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&208))) *)
  0xf90073ec;       (* arm_STR X12 SP (Immediate_Offset (word 224)) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c60;       (* arm_UMULH X0 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c61;       (* arm_UMULH X1 X3 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9bca7c83;       (* arm_UMULH X3 X4 X10 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9b077cab;       (* arm_MUL X11 X5 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9b0a7cab;       (* arm_MUL X11 X5 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bca7ca4;       (* arm_UMULH X4 X5 X10 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b077ccb;       (* arm_MUL X11 X6 X7 *)
  0xab0b0000;       (* arm_ADDS X0 X0 X11 *)
  0x9b087ccb;       (* arm_MUL X11 X6 X8 *)
  0xba0b0021;       (* arm_ADCS X1 X1 X11 *)
  0x9b097ccb;       (* arm_MUL X11 X6 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9b0a7ccb;       (* arm_MUL X11 X6 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9bca7cc5;       (* arm_UMULH X5 X6 X10 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9b017e2b;       (* arm_MUL X11 X17 X1 *)
  0x9bc17e29;       (* arm_UMULH X9 X17 X1 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037e2b;       (* arm_MUL X11 X17 X3 *)
  0x9bc37e23;       (* arm_UMULH X3 X17 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047e2b;       (* arm_MUL X11 X17 X4 *)
  0x9bc47e24;       (* arm_UMULH X4 X17 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057e2b;       (* arm_MUL X11 X17 X5 *)
  0x9bc57e25;       (* arm_UMULH X5 X17 X5 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a9f37e1;       (* arm_CSET X1 Condition_CS *)
  0xab0901ad;       (* arm_ADDS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0xba040000;       (* arm_ADCS X0 X0 X4 *)
  0x9a050021;       (* arm_ADC X1 X1 X5 *)
  0xa91037ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&256))) *)
  0xa91103ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&272))) *)
  0xf90093e1;       (* arm_STR X1 SP (Immediate_Offset (word 288)) *)
  0xa9540be1;       (* arm_LDP X1 X2 SP (Immediate_Offset (iword (&320))) *)
  0xd37ef420;       (* arm_LSL X0 X1 2 *)
  0xa9441fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&64))) *)
  0xeb060000;       (* arm_SUBS X0 X0 X6 *)
  0x93c1f841;       (* arm_EXTR X1 X2 X1 62 *)
  0xfa070021;       (* arm_SBCS X1 X1 X7 *)
  0xa95513e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&336))) *)
  0x93c2f862;       (* arm_EXTR X2 X3 X2 62 *)
  0xa9451fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&80))) *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0x93c3f883;       (* arm_EXTR X3 X4 X3 62 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xf940b3e5;       (* arm_LDR X5 SP (Immediate_Offset (word 352)) *)
  0x93c4f8a4;       (* arm_EXTR X4 X5 X4 62 *)
  0xda1f0084;       (* arm_SBC X4 X4 XZR *)
  0x91000485;       (* arm_ADD X5 X4 (rvalue (word 1)) *)
  0x9b057e24;       (* arm_MUL X4 X17 X5 *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0x9bc57e25;       (* arm_UMULH X5 X17 X5 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0x9a9f3224;       (* arm_CSEL X4 X17 XZR Condition_CC *)
  0xeb040000;       (* arm_SUBS X0 X0 X4 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xa90005e0;       (* arm_STP X0 X1 X15 (Immediate_Offset (iword (&0))) *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0063;       (* arm_SBC X3 X3 XZR *)
  0xa9010de2;       (* arm_STP X2 X3 X15 (Immediate_Offset (iword (&16))) *)
  0xd280006a;       (* arm_MOV X10 (rvalue (word 3)) *)
  0xa95017e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&256))) *)
  0x9b0a7c80;       (* arm_MUL X0 X4 X10 *)
  0x9b0a7ca1;       (* arm_MUL X1 X5 X10 *)
  0xa9511fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&272))) *)
  0x9b0a7cc2;       (* arm_MUL X2 X6 X10 *)
  0x9b0a7ce3;       (* arm_MUL X3 X7 X10 *)
  0xf94093ed;       (* arm_LDR X13 SP (Immediate_Offset (word 288)) *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab040021;       (* arm_ADDS X1 X1 X4 *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xba050042;       (* arm_ADCS X2 X2 X5 *)
  0x9bca7cc6;       (* arm_UMULH X6 X6 X10 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0x9bca7ce4;       (* arm_UMULH X4 X7 X10 *)
  0x9b0a7dad;       (* arm_MUL X13 X13 X10 *)
  0x9a0d0089;       (* arm_ADC X9 X4 X13 *)
  0xb2580129;       (* arm_ORR X9 X9 (rvalue (word 1099511627776)) *)
  0xd3585e2c;       (* arm_LSL X12 X17 40 *)
  0xa94c3bed;       (* arm_LDP X13 X14 SP (Immediate_Offset (iword (&192))) *)
  0xd37df1a4;       (* arm_LSL X4 X13 3 *)
  0xab0c0084;       (* arm_ADDS X4 X4 X12 *)
  0x93cdf5c5;       (* arm_EXTR X5 X14 X13 61 *)
  0xd358fe2c;       (* arm_LSR X12 X17 24 *)
  0xba0c00a5;       (* arm_ADCS X5 X5 X12 *)
  0xa94d33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&208))) *)
  0x93cef566;       (* arm_EXTR X6 X11 X14 61 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xf94073ed;       (* arm_LDR X13 SP (Immediate_Offset (word 224)) *)
  0x93cbf587;       (* arm_EXTR X7 X12 X11 61 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0x93ccf5a8;       (* arm_EXTR X8 X13 X12 61 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xeb040000;       (* arm_SUBS X0 X0 X4 *)
  0xfa050021;       (* arm_SBCS X1 X1 X5 *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xda080124;       (* arm_SBC X4 X9 X8 *)
  0x9100048a;       (* arm_ADD X10 X4 (rvalue (word 1)) *)
  0x9b0a7e24;       (* arm_MUL X4 X17 X10 *)
  0x9bca7e25;       (* arm_UMULH X5 X17 X10 *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0x9a9f322b;       (* arm_CSEL X11 X17 XZR Condition_CC *)
  0xeb0b0000;       (* arm_SUBS X0 X0 X11 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xa90205e0;       (* arm_STP X0 X1 X15 (Immediate_Offset (iword (&32))) *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0063;       (* arm_SBC X3 X3 XZR *)
  0xa9030de2;       (* arm_STP X2 X3 X15 (Immediate_Offset (iword (&48))) *)
  0x910603ff;       (* arm_ADD SP SP (rvalue (word 384)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let SECP256K1_JDOUBLE_ALT_EXEC = ARM_MK_EXEC_RULE secp256k1_jdouble_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p256k1redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256k1 - 1)
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let p256k1shortintredlemma = prove
 (`!n. --(&p_256k1) <= n /\ n <= &17179873097 * &p_256k1
       ==> let q = (&2 pow 256 + n) div &2 pow 256 in
           &0 <= q /\ q < &2 pow 35 /\
           q < &2 pow 64 /\
           q * &p_256k1 <= n + &p_256k1 /\
           n < q * &p_256k1 + &p_256k1`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 256 + n:int = &1 * &2 pow 256 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 256` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_256k1` THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_256k1` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_256k1] THEN INT_ARITH_TAC);;

let lvs =
 ["x_1",[`X16`;`0`];
  "y_1",[`X16`;`32`];
  "z_1",[`X16`;`64`];
  "x_3",[`X15`;`0`];
  "y_3",[`X15`;`32`];
  "z_3",[`X15`;`64`];
  "x_2",[`SP`;`0`];
  "y_2",[`SP`;`32`];
  "d",[`SP`;`64`];
  "tmp",[`SP`;`96`];
  "x_4",[`SP`;`128`];
  "y_4",[`SP`;`192`];
  "dx2",[`SP`;`256`];
  "xy2",[`SP`;`320`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 76 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  read(memory :> bytes(word_add (read p3 t) (word n3),
                       8 * 4)) s = (n EXP 2) MOD p_256k1)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (1--45) (1--45) THEN
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
    `(2 EXP 256 * h + l) MOD p_256k1 = (4294968273 * h + l) MOD p_256k1`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `4294968273 * h + l` p256k1redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_256k1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (46--62) (46--62) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s48; sum_s59; sum_s60; sum_s61; sum_s62]` THEN
  SUBGOAL_THEN `(4294968273 * h + l) DIV 2 EXP 256 + 1 <= 2 EXP 33`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `4294968273 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s62:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN
  ARM_STEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC [63] THEN
  ABBREV_TAC `q:int64 = word_add sum_s62 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s62:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (64--76) (64--76) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s69` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s62:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN
       `word_add sum_s62 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s69:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of mul.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 98 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  read(memory :> bytes(word_add (read p3 t) (word n3),
                       8 * 4)) s = (m * n) MOD p_256k1)
            (MAYCHANGE [PC; X0; X1; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8 ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (1--67) (1--67) THEN
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
    `(2 EXP 256 * h + l) MOD p_256k1 = (4294968273 * h + l) MOD p_256k1`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `4294968273 * h + l` p256k1redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_256k1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (68--84) (68--84) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s70; sum_s81; sum_s82; sum_s83; sum_s84]` THEN
  SUBGOAL_THEN `(4294968273 * h + l) DIV 2 EXP 256 + 1 <= 2 EXP 33`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `4294968273 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s84:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN
  ARM_STEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC [85] THEN
  ABBREV_TAC `q:int64 = word_add sum_s84 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s84:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (86--98) (86--98) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s91` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s84:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN
       `word_add sum_s84 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s91:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of roughsqr.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ROUGHSQR_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 65 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),40)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              n)
         (\s. read PC s = pcout /\
              read(memory :> bytes(word_add (read p3 t) (word n3),
                   8 * 5)) s < 4294968274 * 2 EXP 256 /\
              (read(memory :> bytes(word_add (read p3 t) (word n3),
                    8 * 5)) s == n EXP 2) (mod p_256k1))
         (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13; X14] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 5)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (1--45) (1--45) THEN
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

  (*** Reduction from 8 digits to 5 digits ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_256k1 = (4294968273 * h + l) MOD p_256k1`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (46--62) (46--65) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(MESON[] `y < n /\ x = y ==> x < n /\ x MOD p = y MOD p`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of roughmul.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ROUGHMUL_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 87 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),40)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
         (\s. read PC s = pcout /\
              read(memory :> bytes(word_add (read p3 t) (word n3),
                   8 * 5)) s < 4294968274 * 2 EXP 256 /\
              (read(memory :> bytes(word_add (read p3 t) (word n3),
                    8 * 5)) s == m * n) (mod p_256k1))
         (MAYCHANGE [PC; X0; X1; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13; X14] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 5)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8 ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (1--67) (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_256k1 = (4294968273 * h + l) MOD p_256k1`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (68--84) (68--87) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(MESON[] `y < n /\ x = y ==> x < n /\ x MOD p = y MOD p`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of weakdouble.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKDOUBLE_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 14 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  read(memory :> bytes(word_add (read p3 t) (word n3),
                       8 * 4)) s < 2 EXP 256 /\
                  (n < p_256k1
                   ==> (read(memory :> bytes(word_add (read p3 t) (word n3),
                             8 * 4)) s == 2 * n) (mod p_256k1)))
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC [7;9;11;13] (1--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; DISCH_TAC] THEN

  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!x':int. x = x' /\ (x' == &2 * n) (mod p)
             ==> (x == &2 * n) (mod p)`) THEN
  EXISTS_TAC
   `if &2 pow 255 <= (&n:int) then &2 * &n - &p_256k1 else &2 * (&n:int)` THEN
  CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN CONV_TAC INTEGER_RULE] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `(&0 <= x /\ x < e) /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_OF_NUM_LT]) THEN
    REWRITE_TAC[p_256k1] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_INT_CONGRUENCE; int_of_num_th] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_sub_th; int_mul_th; int_of_num_th; int_pow_th;
              int_eq; int_le] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; EXP_EQ_0; ARITH_EQ] THEN

  SUBGOAL_THEN
   `~(val (word_and n_3 (word 9223372036854775808):int64) = 0) <=>
    2 EXP 255 <= n`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[ARITH_RULE
      `2 EXP 255 <= n <=> 2 EXP 63 <= n DIV 2 EXP 192`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[ARITH_RULE `63 = 64 - 1`; GSYM DIMINDEX_64; GSYM MSB_VAL] THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63`); DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD_AND_POW2; NUM_REDUCE_CONV `64 - 1`] THEN
    REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; BITVAL_EQ_0; ARITH_EQ];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 * n =
    bignum_of_wordlist
     [word_shl n_0 1;
      word_subword ((word_join:int64->int64->int128) n_1 n_0) (63,64);
      word_subword ((word_join:int64->int64->int128) n_2 n_1) (63,64);
      word_subword ((word_join:int64->int64->int128) n_3 n_2) (63,64);
      word_ushr n_3 63]`
  SUBST1_TAC THENL
   [EXPAND_TAC "n" THEN
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
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `bb <=> 2 EXP 255 <= n` THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[p_256k1] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 57 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) s =
              n)
         (\s. read PC s = pcout /\
              (m < 4294968274 * 2 EXP 256 /\ n < 4294968274 * 2 EXP 256
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 4)) s) = (&12 * &m - &9 * &n) rem &p_256k1))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13; X14] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC
    `m < 4294968274 * 2 EXP 256 /\ n < 4294968274 * 2 EXP 256`
  THENL [ASM_REWRITE_TAC[]; ARM_SIM_TAC SECP256K1_JDOUBLE_ALT_EXEC (1--57)] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The accumulation of 12 * m, without the final 2^296 bump ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC
   [3;4;6;7;10;12;14;16;17] (1--18) THEN
  ABBREV_TAC
   `m12 =
    bignum_of_wordlist[mullo_s3; sum_s10; sum_s12; sum_s14; sum_s17]` THEN
  SUBGOAL_THEN `m12 = 12 * m` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [EXPAND_TAC "m12" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `m < 4294968274 * 2 EXP 256` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "m12"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The extra bump ***)

  ABBREV_TAC
   `m12' =
    bignum_of_wordlist[mullo_s3; sum_s10; sum_s12; sum_s14;
                       word_or sum_s17 (word 1099511627776)]` THEN
  SUBGOAL_THEN `m12' = 2 EXP 40 * 2 EXP 256 + 12 * m` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    EXPAND_TAC "m12'" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(ISPECL [`sum_s17:int64`; `word 1099511627776:int64`]
        VAL_WORD_OR_DISJOINT) THEN
    CONV_TAC WORD_REDUCE_CONV THEN ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    REWRITE_TAC[WORD_AND_EQ_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[DISJOINT_SING; IN_BITS_OF_WORD; BIT_VAL] THEN
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `(12 * m) DIV 2 EXP 256 < 2 EXP 40` MP_TAC THENL
     [UNDISCH_TAC `m < 4294968274 * 2 EXP 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The accumulation of 9 * n + 2^40 * 4294968273 ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC
   [21;23;24;25;26;28;30;33;34;36;37;38] (19--38) THEN
  ABBREV_TAC
   `n9' =
    bignum_of_wordlist[sum_s26; sum_s28; sum_s33; sum_s37; sum_s38]` THEN
  SUBGOAL_THEN `n9' = 2 EXP 40 * 4294968273 + 9 * n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [EXPAND_TAC "n9'" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `n < 4294968274 * 2 EXP 256` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["n"; "n9'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE) THEN
    DISCH_THEN SUBST1_TAC THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The subtraction giving the nonnegative result to reduce modulo ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (39--43) (39--43) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s39; sum_s40; sum_s41; sum_s42; sum_s43]` THEN
  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) = &ca:int - &2 pow 40 * &p_256k1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&p_256k1:int = &2 pow 256 - &4294968273` SUBST1_TAC THENL
     [REWRITE_TAC[p_256k1] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH
     `m - n:int = ca - &2 pow 40 * (e - k) <=>
      (&2 pow 40 * e + m) - (&2 pow 40 * k + n) = ca`] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 320` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `(&0 <= x /\ x < e) /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`m < 4294968274 * 2 EXP 256`; `n < 4294968274 * 2 EXP 256`] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
        EXPAND_TAC "ca" THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[]];
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
        [SYM th]) THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
        [SYM th])] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
    REWRITE_TAC[int_sub_th; int_mul_th; int_of_num_th; int_pow_th;
                int_eq; int_le] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ASM_REWRITE_TAC[INT_REM_MUL_ADD; INT_ARITH
   `x - k * p:int = x + (--k) * p`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p256k1redlemma) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
      `mnt:int = ca - ep ==> mnt + ep <= b ==> ca <= b`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`m < 4294968274 * 2 EXP 256`; `n < 4294968274 * 2 EXP 256`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_ARITH;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s43:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN
  ARM_STEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC [44] THEN
  ABBREV_TAC `q:int64 = word_add sum_s43 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s43:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC
   [45;47;48;49;50;52;53;55;56] (45--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s50` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s43:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN `word_add sum_s43 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s50:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of cmsub38.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 52 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) s =
              n)
         (\s. read PC s = pcout /\
              (m < 4294968274 * 2 EXP 256 /\ n < 4294968274 * 2 EXP 256
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 4)) s) = (&3 * &m - &8 * &n) rem &p_256k1))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13; X14] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC
    `m < 4294968274 * 2 EXP 256 /\ n < 4294968274 * 2 EXP 256`
  THENL [ASM_REWRITE_TAC[]; ARM_SIM_TAC SECP256K1_JDOUBLE_ALT_EXEC (1--52)] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The accumulation of 3 * m, without the final 2^296 bump ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC
   [3;4;6;7;10;12;14;16;17] (1--18) THEN
  ABBREV_TAC
   `m3 =
    bignum_of_wordlist[mullo_s3; sum_s10; sum_s12; sum_s14; sum_s17]` THEN
  SUBGOAL_THEN `m3 = 3 * m` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [EXPAND_TAC "m3" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `m < 4294968274 * 2 EXP 256` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "m3"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The extra bump ***)

  ABBREV_TAC
   `m3' =
    bignum_of_wordlist[mullo_s3; sum_s10; sum_s12; sum_s14;
                       word_or sum_s17 (word 1099511627776)]` THEN
  SUBGOAL_THEN `m3' = 2 EXP 40 * 2 EXP 256 + 3 * m` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    EXPAND_TAC "m3'" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(ISPECL [`sum_s17:int64`; `word 1099511627776:int64`]
        VAL_WORD_OR_DISJOINT) THEN
    CONV_TAC WORD_REDUCE_CONV THEN ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    REWRITE_TAC[WORD_AND_EQ_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[DISJOINT_SING; IN_BITS_OF_WORD; BIT_VAL] THEN
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `(3 * m) DIV 2 EXP 256 < 2 EXP 40` MP_TAC THENL
     [UNDISCH_TAC `m < 4294968274 * 2 EXP 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The accumulation of 8 * n + 2^40 * 4294968273 ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC [22;25;28;31;33] (19--33) THEN
  ABBREV_TAC
   `n8' =
    bignum_of_wordlist[sum_s22; sum_s25; sum_s28; sum_s31; sum_s33]` THEN
  SUBGOAL_THEN `n8' = 2 EXP 40 * 4294968273 + 8 * n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [EXPAND_TAC "n8'" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `n < 4294968274 * 2 EXP 256` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
    SUBGOAL_THEN
     `8 * n =
      bignum_of_wordlist
         [word_shl n_0 3;
          word_subword ((word_join:int64->int64->int128) n_1 n_0) (61,64);
          word_subword ((word_join:int64->int64->int128) n_2 n_1) (61,64);
          word_subword ((word_join:int64->int64->int128) n_3 n_2) (61,64);
          word_subword ((word_join:int64->int64->int128) n_4 n_3) (61,64);
          word_ushr n_4 61]`
    SUBST1_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[bignum_of_wordlist] THEN
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
      MAP_EVERY EXPAND_TAC ["n"; "n8'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The subtraction giving the nonnegative result to reduce modulo ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC (34--38) (34--38) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s34; sum_s35; sum_s36; sum_s37; sum_s38]` THEN
  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) = &ca:int - &2 pow 40 * &p_256k1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&p_256k1:int = &2 pow 256 - &4294968273` SUBST1_TAC THENL
     [REWRITE_TAC[p_256k1] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH
     `m - n:int = ca - &2 pow 40 * (e - k) <=>
      (&2 pow 40 * e + m) - (&2 pow 40 * k + n) = ca`] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 320` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `(&0 <= x /\ x < e) /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`m < 4294968274 * 2 EXP 256`; `n < 4294968274 * 2 EXP 256`] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
        EXPAND_TAC "ca" THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[]];
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
        [SYM th]) THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
        [SYM th])] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
    REWRITE_TAC[int_sub_th; int_mul_th; int_of_num_th; int_pow_th;
                int_eq; int_le] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ASM_REWRITE_TAC[INT_REM_MUL_ADD; INT_ARITH
   `x - k * p:int = x + (--k) * p`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p256k1redlemma) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
      `mnt:int = ca - ep ==> mnt + ep <= b ==> ca <= b`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`m < 4294968274 * 2 EXP 256`; `n < 4294968274 * 2 EXP 256`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_ARITH;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s38:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN
  ARM_STEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC [39] THEN
  ABBREV_TAC `q:int64 = word_add sum_s38 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s38:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC
   [40;42;43;44;45;47;48;50;51] (40--52) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s45` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s38:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN `word_add sum_s38 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s45:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of cmsub41.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P256K1_TAC =
  ARM_MACRO_SIM_ABBREV_TAC secp256k1_jdouble_alt_mc 29 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0xb24) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = word 4294968273 /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
         (\s. read PC s = pcout /\
              (m < 4294968274 * 2 EXP 256 /\ n < p_256k1
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 4)) s) = (&4 * &m - &n) rem &p_256k1))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `m < 4294968274 * 2 EXP 256 /\ n < p_256k1` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC SECP256K1_JDOUBLE_ALT_EXEC (1--29)] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Instantiate the (integer) quotient approximation lemma ***)

  MP_TAC(SPEC `&4 * &m - &n:int` p256k1shortintredlemma) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_LT; INT_ARITH
     `n:int < p ==> --p <= &4 * &m - n`] THEN
    UNDISCH_TAC `m < 4294968274 * 2 EXP 256` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_256k1] THEN INT_ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Main shift-subtract block ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC [4;6;10;12;15;16] (1--16) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s4; sum_s6; sum_s10; sum_s12; sum_s16]` THEN
  SUBGOAL_THEN `&2 pow 256 + &4 * &m - &n:int = &ca`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_pow_th;
                int_mul_th; int_of_num_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`320`; `&0:real`] THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN BOUNDER_TAC[];
        UNDISCH_TAC `m < 4294968274 * 2 EXP 256` THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_256k1] THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "ca" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&4 * &m:real =
      &(bignum_of_wordlist
         [word_shl m_0 2;
          word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
          word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
          word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
          word_subword ((word_join:int64->int64->int128) m_4 m_3) (62,64);
          word_ushr m_4 62])`
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s16` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s16:int64` o concl))) THEN
  SUBGOAL_THEN `&ca div &2 pow 256 = &(val(q:int64))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV] THEN
    EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC SECP256K1_JDOUBLE_ALT_EXEC
   [17;18;20;21;22; 24;25;27;28] (17--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED_MOD THEN
  MAP_EVERY EXISTS_TAC [`&(val(q:int64)):int`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; p_256k1] THEN BOUNDER_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `&4 * m - n:int = (&2 pow 256 + &4 * m - n) - &2 pow 256`] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN
    `(&ca - &2 pow 256):int < &(val(q:int64)) * &p_256k1 <=> ~carry_s22`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_LT_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_RULE
     `(a:int == b + c - p) (mod p) <=> (a == b + c) (mod p)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s22:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_256k1 ==> x < p_256k1 /\ &x = &a rem &p_256k1`,
  REWRITE_TAC[INT_OF_NUM_REM; p_256k1] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_256k1 ==> x < p_256k1 /\ &x = a rem &p_256k1`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_256k1] THEN INT_ARITH_TAC);;

let weierstrass_of_jacobian_p256k1_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional secp256k1
         (x1 rem &p_256k1,y1 rem &p_256k1,z1 rem &p_256k1) =
        (x3 rem &p_256k1,y3 rem &p_256k1,z3 rem &p_256k1)
        ==> weierstrass_of_jacobian (integer_mod_ring p_256k1)
                (x1 rem &p_256k1,y1 rem &p_256k1,z1 rem &p_256k1) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_256k1)
                  (x3 rem &p_256k1,y3 rem &p_256k1,z3 rem &p_256k1) =
                group_mul p256k1_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[secp256k1; P256K1_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P256K1] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_256k1] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p256k1 = new_definition
 `represents_p256k1 P (x,y,z) <=>
        x < p_256k1 /\ y < p_256k1 /\ z < p_256k1 /\
        weierstrass_of_jacobian (integer_mod_ring p_256k1)
         (tripled (modular_decode (256,p_256k1)) (x,y,z)) = P`;;

let SECP256K1_JDOUBLE_ALT_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,384))
            [(word pc,0xb24); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0xb24)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
                  read PC s = word(pc + 0x4) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read PC s = word (pc + 0xb1c) /\
                  !P. represents_p256k1 P t1
                      ==> represents_p256k1 (group_mul p256k1_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,384)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x:num`; `y:num`; `z:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SQR_P256K1_TAC 4 ["y_2";"y_1"] THEN
  LOCAL_SQR_P256K1_TAC 0 ["x_2";"x_1"] THEN
  LOCAL_WEAKDOUBLE_P256K1_TAC 0 ["tmp";"y_1"] THEN
  LOCAL_ROUGHMUL_P256K1_TAC 0 ["xy2";"x_1";"y_2"] THEN
  LOCAL_ROUGHSQR_P256K1_TAC 0 ["x_4";"x_2"] THEN
  LOCAL_MUL_P256K1_TAC 0 ["z_3";"z_1";"tmp"] THEN
  LOCAL_CMSUBC9_P256K1_TAC 0 ["d";"xy2";"x_4"] THEN
  LOCAL_ROUGHSQR_P256K1_TAC 0 ["y_4";"y_2"] THEN
  LOCAL_ROUGHMUL_P256K1_TAC 0 ["dx2";"x_2";"d"] THEN
  LOCAL_CMSUB41_P256K1_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P256K1_TAC 0 ["y_3";"dx2";"y_4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s15" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p256k1; tripled] THEN
  REWRITE_TAC[modular_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC INT_LT_REM THEN REWRITE_TAC[p_256k1; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[p_256k1; INT_LT_REM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  REPEAT(DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC(SYM th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_MUL_REM]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  ASM_CASES_TAC `&z rem &p_256k1 = &0` THENL
   [ASM_REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_REM_ZERO] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[P256K1_GROUP; weierstrass_add];
    ALL_TAC] THEN
  SIMP_TAC[] THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p256k1_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; secp256k1;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let SECP256K1_JDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 384),384))
            [(word pc,0xb24); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0xb24)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) secp256k1_jdouble_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read PC s = returnaddress /\
                  !P. represents_p256k1 P t1
                      ==> represents_p256k1 (group_mul p256k1_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 384),384)])`,
  ARM_ADD_RETURN_STACK_TAC SECP256K1_JDOUBLE_ALT_EXEC
   SECP256K1_JDOUBLE_ALT_CORRECT `[]` 384);;
