(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Montgomery-Jacobian coordinates for NIST P-256 curve.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp256.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/p256/p256_montjdouble_alt.o";;
 ****)

let p256_montjdouble_alt_mc = define_assert_from_elf
  "p256_montjdouble_alt_mc" "arm/p256/p256_montjdouble_alt.o"
[
  0xd10303ff;       (* arm_SUB SP SP (rvalue (word 192)) *)
  0xaa0003ef;       (* arm_MOV X15 X0 *)
  0xaa0103f0;       (* arm_MOV X16 X1 *)
  0xa9440e02;       (* arm_LDP X2 X3 X16 (Immediate_Offset (iword (&64))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9451604;       (* arm_LDP X4 X5 X16 (Immediate_Offset (iword (&80))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9bc47c47;       (* arm_UMULH X7 X2 X4 *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c66;       (* arm_MUL X6 X3 X4 *)
  0x9bc47c67;       (* arm_UMULH X7 X3 X4 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06016b;       (* arm_ADDS X11 X11 X6 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9b057c66;       (* arm_MUL X6 X3 X5 *)
  0x9bc57c67;       (* arm_UMULH X7 X3 X5 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0x9bc27c46;       (* arm_UMULH X6 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9b037c66;       (* arm_MUL X6 X3 X3 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9bc37c66;       (* arm_UMULH X6 X3 X3 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c86;       (* arm_MUL X6 X4 X4 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9bc47c86;       (* arm_UMULH X6 X4 X4 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0x9bc57ca6;       (* arm_UMULH X6 X5 X5 *)
  0x9a0600e7;       (* arm_ADC X7 X7 X6 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9b057d02;       (* arm_MUL X2 X8 X5 *)
  0x9bc57d08;       (* arm_UMULH X8 X8 X5 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0x9b057d22;       (* arm_MUL X2 X9 X5 *)
  0x9bc57d29;       (* arm_UMULH X9 X9 X5 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x9b057d42;       (* arm_MUL X2 X10 X5 *)
  0x9bc57d4a;       (* arm_UMULH X10 X10 X5 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9b057d62;       (* arm_MUL X2 X11 X5 *)
  0x9bc57d6b;       (* arm_UMULH X11 X11 X5 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0xb100050c;       (* arm_ADDS X12 X8 (rvalue (word 1)) *)
  0xfa03012d;       (* arm_SBCS X13 X9 X3 *)
  0xfa1f014e;       (* arm_SBCS X14 X10 XZR *)
  0xfa050167;       (* arm_SBCS X7 X11 X5 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8c3108;       (* arm_CSEL X8 X8 X12 Condition_CC *)
  0x9a8d3129;       (* arm_CSEL X9 X9 X13 Condition_CC *)
  0x9a8e314a;       (* arm_CSEL X10 X10 X14 Condition_CC *)
  0x9a87316b;       (* arm_CSEL X11 X11 X7 Condition_CC *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa9420e02;       (* arm_LDP X2 X3 X16 (Immediate_Offset (iword (&32))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9431604;       (* arm_LDP X4 X5 X16 (Immediate_Offset (iword (&48))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9bc47c47;       (* arm_UMULH X7 X2 X4 *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c66;       (* arm_MUL X6 X3 X4 *)
  0x9bc47c67;       (* arm_UMULH X7 X3 X4 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06016b;       (* arm_ADDS X11 X11 X6 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9b057c66;       (* arm_MUL X6 X3 X5 *)
  0x9bc57c67;       (* arm_UMULH X7 X3 X5 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0x9bc27c46;       (* arm_UMULH X6 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9b037c66;       (* arm_MUL X6 X3 X3 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9bc37c66;       (* arm_UMULH X6 X3 X3 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c86;       (* arm_MUL X6 X4 X4 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9bc47c86;       (* arm_UMULH X6 X4 X4 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0x9bc57ca6;       (* arm_UMULH X6 X5 X5 *)
  0x9a0600e7;       (* arm_ADC X7 X7 X6 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9b057d02;       (* arm_MUL X2 X8 X5 *)
  0x9bc57d08;       (* arm_UMULH X8 X8 X5 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0x9b057d22;       (* arm_MUL X2 X9 X5 *)
  0x9bc57d29;       (* arm_UMULH X9 X9 X5 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x9b057d42;       (* arm_MUL X2 X10 X5 *)
  0x9bc57d4a;       (* arm_UMULH X10 X10 X5 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9b057d62;       (* arm_MUL X2 X11 X5 *)
  0x9bc57d6b;       (* arm_UMULH X11 X11 X5 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0xb100050c;       (* arm_ADDS X12 X8 (rvalue (word 1)) *)
  0xfa03012d;       (* arm_SBCS X13 X9 X3 *)
  0xfa1f014e;       (* arm_SBCS X14 X10 XZR *)
  0xfa050167;       (* arm_SBCS X7 X11 X5 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8c3108;       (* arm_CSEL X8 X8 X12 Condition_CC *)
  0x9a8d3129;       (* arm_CSEL X9 X9 X13 Condition_CC *)
  0x9a8e314a;       (* arm_CSEL X10 X10 X14 Condition_CC *)
  0x9a87316b;       (* arm_CSEL X11 X11 X7 Condition_CC *)
  0xa90227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&32))) *)
  0xa9032fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&48))) *)
  0xa9401a05;       (* arm_LDP X5 X6 X16 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412207;       (* arm_LDP X7 X8 X16 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92407c64;       (* arm_AND X4 X3 (rvalue (word 4294967295)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0x92608064;       (* arm_AND X4 X3 (rvalue (word 18446744069414584321)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9061be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&96))) *)
  0xa90723e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xa9401a05;       (* arm_LDP X5 X6 X16 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412207;       (* arm_LDP X7 X8 X16 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xda9f33e3;       (* arm_CSETM X3 Condition_CS *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0x92407c61;       (* arm_AND X1 X3 (rvalue (word 4294967295)) *)
  0xfa0100c6;       (* arm_SBCS X6 X6 X1 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0x92608062;       (* arm_AND X2 X3 (rvalue (word 18446744069414584321)) *)
  0xda020108;       (* arm_SBC X8 X8 X2 *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
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
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
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
  0xb26083ea;       (* arm_MOV X10 (rvalue (word 18446744069414584321)) *)
  0xab0c81ad;       (* arm_ADDS X13 X13 (Shiftedreg X12 LSL 32) *)
  0xd360fd8b;       (* arm_LSR X11 X12 32 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7d8b;       (* arm_MUL X11 X12 X10 *)
  0x9bca7d8c;       (* arm_UMULH X12 X12 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xab0d81ce;       (* arm_ADDS X14 X14 (Shiftedreg X13 LSL 32) *)
  0xd360fdab;       (* arm_LSR X11 X13 32 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0x9bca7dad;       (* arm_UMULH X13 X13 X10 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e8000;       (* arm_ADDS X0 X0 (Shiftedreg X14 LSL 32) *)
  0xd360fdcb;       (* arm_LSR X11 X14 32 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9b0a7dcb;       (* arm_MUL X11 X14 X10 *)
  0x9bca7dce;       (* arm_UMULH X14 X14 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab00818c;       (* arm_ADDS X12 X12 (Shiftedreg X0 LSL 32) *)
  0xd360fc0b;       (* arm_LSR X11 X0 32 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b0a7c0b;       (* arm_MUL X11 X0 X10 *)
  0x9bca7c00;       (* arm_UMULH X0 X0 X10 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xfa1f01c4;       (* arm_SBCS X4 X14 XZR *)
  0xfa0a0005;       (* arm_SBCS X5 X0 X10 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90637ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&96))) *)
  0xa90703ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&112))) *)
  0xa9421a05;       (* arm_LDP X5 X6 X16 (Immediate_Offset (iword (&32))) *)
  0xa9440e04;       (* arm_LDP X4 X3 X16 (Immediate_Offset (iword (&64))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9432207;       (* arm_LDP X7 X8 X16 (Immediate_Offset (iword (&48))) *)
  0xa9450e04;       (* arm_LDP X4 X3 X16 (Immediate_Offset (iword (&80))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0xfa0400df;       (* arm_SBCS XZR X6 X4 *)
  0xfa1f00ff;       (* arm_SBCS XZR X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0xfa04011f;       (* arm_SBCS XZR X8 X4 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0x92407c64;       (* arm_AND X4 X3 (rvalue (word 4294967295)) *)
  0xfa0400c6;       (* arm_SBCS X6 X6 X4 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0x92608064;       (* arm_AND X4 X3 (rvalue (word 18446744069414584321)) *)
  0xda040108;       (* arm_SBC X8 X8 X4 *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
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
  0xb26083ea;       (* arm_MOV X10 (rvalue (word 18446744069414584321)) *)
  0xab0c81ad;       (* arm_ADDS X13 X13 (Shiftedreg X12 LSL 32) *)
  0xd360fd8b;       (* arm_LSR X11 X12 32 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7d8b;       (* arm_MUL X11 X12 X10 *)
  0x9bca7d8c;       (* arm_UMULH X12 X12 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xab0d81ce;       (* arm_ADDS X14 X14 (Shiftedreg X13 LSL 32) *)
  0xd360fdab;       (* arm_LSR X11 X13 32 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0x9bca7dad;       (* arm_UMULH X13 X13 X10 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e8000;       (* arm_ADDS X0 X0 (Shiftedreg X14 LSL 32) *)
  0xd360fdcb;       (* arm_LSR X11 X14 32 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9b0a7dcb;       (* arm_MUL X11 X14 X10 *)
  0x9bca7dce;       (* arm_UMULH X14 X14 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab00818c;       (* arm_ADDS X12 X12 (Shiftedreg X0 LSL 32) *)
  0xd360fc0b;       (* arm_LSR X11 X0 32 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b0a7c0b;       (* arm_MUL X11 X0 X10 *)
  0x9bca7c00;       (* arm_UMULH X0 X0 X10 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xfa1f01c4;       (* arm_SBCS X4 X14 XZR *)
  0xfa0a0005;       (* arm_SBCS X5 X0 X10 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  0xa90903ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&144))) *)
  0xa9460fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&96))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94717e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&112))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9bc47c47;       (* arm_UMULH X7 X2 X4 *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c66;       (* arm_MUL X6 X3 X4 *)
  0x9bc47c67;       (* arm_UMULH X7 X3 X4 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06016b;       (* arm_ADDS X11 X11 X6 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9b057c66;       (* arm_MUL X6 X3 X5 *)
  0x9bc57c67;       (* arm_UMULH X7 X3 X5 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0x9bc27c46;       (* arm_UMULH X6 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9b037c66;       (* arm_MUL X6 X3 X3 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9bc37c66;       (* arm_UMULH X6 X3 X3 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c86;       (* arm_MUL X6 X4 X4 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9bc47c86;       (* arm_UMULH X6 X4 X4 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0x9bc57ca6;       (* arm_UMULH X6 X5 X5 *)
  0x9a0600e7;       (* arm_ADC X7 X7 X6 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9b057d02;       (* arm_MUL X2 X8 X5 *)
  0x9bc57d08;       (* arm_UMULH X8 X8 X5 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0x9b057d22;       (* arm_MUL X2 X9 X5 *)
  0x9bc57d29;       (* arm_UMULH X9 X9 X5 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x9b057d42;       (* arm_MUL X2 X10 X5 *)
  0x9bc57d4a;       (* arm_UMULH X10 X10 X5 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9b057d62;       (* arm_MUL X2 X11 X5 *)
  0x9bc57d6b;       (* arm_UMULH X11 X11 X5 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0xb100050c;       (* arm_ADDS X12 X8 (rvalue (word 1)) *)
  0xfa03012d;       (* arm_SBCS X13 X9 X3 *)
  0xfa1f014e;       (* arm_SBCS X14 X10 XZR *)
  0xfa050167;       (* arm_SBCS X7 X11 X5 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8c3108;       (* arm_CSEL X8 X8 X12 Condition_CC *)
  0x9a8d3129;       (* arm_CSEL X9 X9 X13 Condition_CC *)
  0x9a8e314a;       (* arm_CSEL X10 X10 X14 Condition_CC *)
  0x9a87316b;       (* arm_CSEL X11 X11 X7 Condition_CC *)
  0xa90a27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0xa9440fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&64))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94517e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&80))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9bc47c47;       (* arm_UMULH X7 X2 X4 *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c66;       (* arm_MUL X6 X3 X4 *)
  0x9bc47c67;       (* arm_UMULH X7 X3 X4 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06016b;       (* arm_ADDS X11 X11 X6 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9b057c66;       (* arm_MUL X6 X3 X5 *)
  0x9bc57c67;       (* arm_UMULH X7 X3 X5 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0x9bc27c46;       (* arm_UMULH X6 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9b037c66;       (* arm_MUL X6 X3 X3 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9bc37c66;       (* arm_UMULH X6 X3 X3 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c86;       (* arm_MUL X6 X4 X4 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9bc47c86;       (* arm_UMULH X6 X4 X4 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0x9bc57ca6;       (* arm_UMULH X6 X5 X5 *)
  0x9a0600e7;       (* arm_ADC X7 X7 X6 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9b057d02;       (* arm_MUL X2 X8 X5 *)
  0x9bc57d08;       (* arm_UMULH X8 X8 X5 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0x9b057d22;       (* arm_MUL X2 X9 X5 *)
  0x9bc57d29;       (* arm_UMULH X9 X9 X5 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x9b057d42;       (* arm_MUL X2 X10 X5 *)
  0x9bc57d4a;       (* arm_UMULH X10 X10 X5 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9b057d62;       (* arm_MUL X2 X11 X5 *)
  0x9bc57d6b;       (* arm_UMULH X11 X11 X5 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0xb100050c;       (* arm_ADDS X12 X8 (rvalue (word 1)) *)
  0xfa03012d;       (* arm_SBCS X13 X9 X3 *)
  0xfa1f014e;       (* arm_SBCS X14 X10 XZR *)
  0xfa050167;       (* arm_SBCS X7 X11 X5 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8c3108;       (* arm_CSEL X8 X8 X12 Condition_CC *)
  0x9a8d3129;       (* arm_CSEL X9 X9 X13 Condition_CC *)
  0x9a8e314a;       (* arm_CSEL X10 X10 X14 Condition_CC *)
  0x9a87316b;       (* arm_CSEL X11 X11 X7 Condition_CC *)
  0xa90427e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&64))) *)
  0xa9052fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&80))) *)
  0xd2800121;       (* arm_MOV X1 (rvalue (word 9)) *)
  0x92800002;       (* arm_MOVN X2 (word 0) 0 *)
  0xa94a2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&160))) *)
  0xeb090049;       (* arm_SUBS X9 X2 X9 *)
  0xb2407fe2;       (* arm_MOV X2 (rvalue (word 4294967295)) *)
  0xfa0a004a;       (* arm_SBCS X10 X2 X10 *)
  0xa94b33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&176))) *)
  0xfa0b03eb;       (* arm_NGCS X11 X11 *)
  0xb26083e2;       (* arm_MOV X2 (rvalue (word 18446744069414584321)) *)
  0xda0c004c;       (* arm_SBC X12 X2 X12 *)
  0x9b097c23;       (* arm_MUL X3 X1 X9 *)
  0x9b0a7c24;       (* arm_MUL X4 X1 X10 *)
  0x9b0b7c25;       (* arm_MUL X5 X1 X11 *)
  0x9b0c7c26;       (* arm_MUL X6 X1 X12 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0x9bcb7c2b;       (* arm_UMULH X11 X1 X11 *)
  0x9bcc7c27;       (* arm_UMULH X7 X1 X12 *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xd2800181;       (* arm_MOV X1 (rvalue (word 12)) *)
  0xa9482be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&128))) *)
  0x9b017d28;       (* arm_MUL X8 X9 X1 *)
  0x9bc17d29;       (* arm_UMULH X9 X9 X1 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9b017d48;       (* arm_MUL X8 X10 X1 *)
  0x9bc17d4a;       (* arm_UMULH X10 X10 X1 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94933eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&144))) *)
  0x9b017d68;       (* arm_MUL X8 X11 X1 *)
  0x9bc17d6b;       (* arm_UMULH X11 X11 X1 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9b017d88;       (* arm_MUL X8 X12 X1 *)
  0x9bc17d8c;       (* arm_UMULH X12 X12 X1 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a0c00e7;       (* arm_ADC X7 X7 X12 *)
  0x910004e8;       (* arm_ADD X8 X7 (rvalue (word 1)) *)
  0xd3607d0a;       (* arm_LSL X10 X8 32 *)
  0xab0a00c6;       (* arm_ADDS X6 X6 X10 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xcb0803e9;       (* arm_NEG X9 X8 *)
  0xd100054a;       (* arm_SUB X10 X10 (rvalue (word 1)) *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa0a0084;       (* arm_SBCS X4 X4 X10 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa0800c6;       (* arm_SBCS X6 X6 X8 *)
  0xda0800e8;       (* arm_SBC X8 X7 X8 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x92407d09;       (* arm_AND X9 X8 (rvalue (word 4294967295)) *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xcb0903ea;       (* arm_NEG X10 X9 *)
  0x9a0a00c6;       (* arm_ADC X6 X6 X10 *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92407c64;       (* arm_AND X4 X3 (rvalue (word 4294967295)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0x92608064;       (* arm_AND X4 X3 (rvalue (word 18446744069414584321)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9420fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&48))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9bc47c47;       (* arm_UMULH X7 X2 X4 *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c66;       (* arm_MUL X6 X3 X4 *)
  0x9bc47c67;       (* arm_UMULH X7 X3 X4 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06016b;       (* arm_ADDS X11 X11 X6 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9b057c66;       (* arm_MUL X6 X3 X5 *)
  0x9bc57c67;       (* arm_UMULH X7 X3 X5 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab06018c;       (* arm_ADDS X12 X12 X6 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0x9bc27c46;       (* arm_UMULH X6 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9b037c66;       (* arm_MUL X6 X3 X3 *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9bc37c66;       (* arm_UMULH X6 X3 X3 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c86;       (* arm_MUL X6 X4 X4 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9bc47c86;       (* arm_UMULH X6 X4 X4 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0x9bc57ca6;       (* arm_UMULH X6 X5 X5 *)
  0x9a0600e7;       (* arm_ADC X7 X7 X6 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9b057d02;       (* arm_MUL X2 X8 X5 *)
  0x9bc57d08;       (* arm_UMULH X8 X8 X5 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0x9b057d22;       (* arm_MUL X2 X9 X5 *)
  0x9bc57d29;       (* arm_UMULH X9 X9 X5 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x9b057d42;       (* arm_MUL X2 X10 X5 *)
  0x9bc57d4a;       (* arm_UMULH X10 X10 X5 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9b057d62;       (* arm_MUL X2 X11 X5 *)
  0x9bc57d6b;       (* arm_UMULH X11 X11 X5 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0xb100050c;       (* arm_ADDS X12 X8 (rvalue (word 1)) *)
  0xfa03012d;       (* arm_SBCS X13 X9 X3 *)
  0xfa1f014e;       (* arm_SBCS X14 X10 XZR *)
  0xfa050167;       (* arm_SBCS X7 X11 X5 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8c3108;       (* arm_CSEL X8 X8 X12 Condition_CC *)
  0x9a8d3129;       (* arm_CSEL X9 X9 X13 Condition_CC *)
  0x9a8e314a;       (* arm_CSEL X10 X10 X14 Condition_CC *)
  0x9a87316b;       (* arm_CSEL X11 X11 X7 Condition_CC *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
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
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
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
  0xb26083ea;       (* arm_MOV X10 (rvalue (word 18446744069414584321)) *)
  0xab0c81ad;       (* arm_ADDS X13 X13 (Shiftedreg X12 LSL 32) *)
  0xd360fd8b;       (* arm_LSR X11 X12 32 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7d8b;       (* arm_MUL X11 X12 X10 *)
  0x9bca7d8c;       (* arm_UMULH X12 X12 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xab0d81ce;       (* arm_ADDS X14 X14 (Shiftedreg X13 LSL 32) *)
  0xd360fdab;       (* arm_LSR X11 X13 32 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0x9bca7dad;       (* arm_UMULH X13 X13 X10 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e8000;       (* arm_ADDS X0 X0 (Shiftedreg X14 LSL 32) *)
  0xd360fdcb;       (* arm_LSR X11 X14 32 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9b0a7dcb;       (* arm_MUL X11 X14 X10 *)
  0x9bca7dce;       (* arm_UMULH X14 X14 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab00818c;       (* arm_ADDS X12 X12 (Shiftedreg X0 LSL 32) *)
  0xd360fc0b;       (* arm_LSR X11 X0 32 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b0a7c0b;       (* arm_MUL X11 X0 X10 *)
  0x9bca7c00;       (* arm_UMULH X0 X0 X10 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a1f0000;       (* arm_ADC X0 X0 XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xfa1f01c4;       (* arm_SBCS X4 X14 XZR *)
  0xfa0a0005;       (* arm_SBCS X5 X0 X10 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90637ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&96))) *)
  0xa90703ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&112))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92407c64;       (* arm_AND X4 X3 (rvalue (word 4294967295)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0x92608064;       (* arm_AND X4 X3 (rvalue (word 18446744069414584321)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa90419e5;       (* arm_STP X5 X6 X15 (Immediate_Offset (iword (&64))) *)
  0xa90521e7;       (* arm_STP X7 X8 X15 (Immediate_Offset (iword (&80))) *)
  0xa9480be1;       (* arm_LDP X1 X2 SP (Immediate_Offset (iword (&128))) *)
  0xd37ef420;       (* arm_LSL X0 X1 2 *)
  0xa94a1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&160))) *)
  0xeb060000;       (* arm_SUBS X0 X0 X6 *)
  0x93c1f841;       (* arm_EXTR X1 X2 X1 62 *)
  0xfa070021;       (* arm_SBCS X1 X1 X7 *)
  0xa94913e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0x93c2f862;       (* arm_EXTR X2 X3 X2 62 *)
  0xa94b1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&176))) *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0x93c3f883;       (* arm_EXTR X3 X4 X3 62 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xd37efc84;       (* arm_LSR X4 X4 62 *)
  0xda1f0084;       (* arm_SBC X4 X4 XZR *)
  0x91000485;       (* arm_ADD X5 X4 (rvalue (word 1)) *)
  0xd3607ca8;       (* arm_LSL X8 X5 32 *)
  0xeb0803e6;       (* arm_NEGS X6 X8 *)
  0xfa1f03e7;       (* arm_NGCS X7 XZR *)
  0xda050108;       (* arm_SBC X8 X8 X5 *)
  0xab050000;       (* arm_ADDS X0 X0 X5 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xda9f23e5;       (* arm_CSETM X5 Condition_CC *)
  0xab050000;       (* arm_ADDS X0 X0 X5 *)
  0x92407ca6;       (* arm_AND X6 X5 (rvalue (word 4294967295)) *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xcb0603e7;       (* arm_NEG X7 X6 *)
  0x9a070063;       (* arm_ADC X3 X3 X7 *)
  0xa90005e0;       (* arm_STP X0 X1 X15 (Immediate_Offset (iword (&0))) *)
  0xa9010de2;       (* arm_STP X2 X3 X15 (Immediate_Offset (iword (&16))) *)
  0xd2800101;       (* arm_MOV X1 (rvalue (word 8)) *)
  0x92800002;       (* arm_MOVN X2 (word 0) 0 *)
  0xa9402be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&0))) *)
  0xeb090049;       (* arm_SUBS X9 X2 X9 *)
  0xb2407fe2;       (* arm_MOV X2 (rvalue (word 4294967295)) *)
  0xfa0a004a;       (* arm_SBCS X10 X2 X10 *)
  0xa94133eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&16))) *)
  0xfa0b03eb;       (* arm_NGCS X11 X11 *)
  0xb26083e2;       (* arm_MOV X2 (rvalue (word 18446744069414584321)) *)
  0xda0c004c;       (* arm_SBC X12 X2 X12 *)
  0xd37df123;       (* arm_LSL X3 X9 3 *)
  0x93c9f544;       (* arm_EXTR X4 X10 X9 61 *)
  0x93caf565;       (* arm_EXTR X5 X11 X10 61 *)
  0x93cbf586;       (* arm_EXTR X6 X12 X11 61 *)
  0xd37dfd87;       (* arm_LSR X7 X12 61 *)
  0xd2800061;       (* arm_MOV X1 (rvalue (word 3)) *)
  0xa9462be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&96))) *)
  0x9b017d28;       (* arm_MUL X8 X9 X1 *)
  0x9bc17d29;       (* arm_UMULH X9 X9 X1 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9b017d48;       (* arm_MUL X8 X10 X1 *)
  0x9bc17d4a;       (* arm_UMULH X10 X10 X1 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94733eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&112))) *)
  0x9b017d68;       (* arm_MUL X8 X11 X1 *)
  0x9bc17d6b;       (* arm_UMULH X11 X11 X1 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9b017d88;       (* arm_MUL X8 X12 X1 *)
  0x9bc17d8c;       (* arm_UMULH X12 X12 X1 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a0c00e7;       (* arm_ADC X7 X7 X12 *)
  0x910004e8;       (* arm_ADD X8 X7 (rvalue (word 1)) *)
  0xd3607d0a;       (* arm_LSL X10 X8 32 *)
  0xab0a00c6;       (* arm_ADDS X6 X6 X10 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xcb0803e9;       (* arm_NEG X9 X8 *)
  0xd100054a;       (* arm_SUB X10 X10 (rvalue (word 1)) *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa0a0084;       (* arm_SBCS X4 X4 X10 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa0800c6;       (* arm_SBCS X6 X6 X8 *)
  0xda0800e8;       (* arm_SBC X8 X7 X8 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x92407d09;       (* arm_AND X9 X8 (rvalue (word 4294967295)) *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xcb0903ea;       (* arm_NEG X10 X9 *)
  0x9a0a00c6;       (* arm_ADC X6 X6 X10 *)
  0xa90211e3;       (* arm_STP X3 X4 X15 (Immediate_Offset (iword (&32))) *)
  0xa90319e5;       (* arm_STP X5 X6 X15 (Immediate_Offset (iword (&48))) *)
  0x910303ff;       (* arm_ADD SP SP (rvalue (word 192)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P256_MONTJDOUBLE_ALT_EXEC = ARM_MK_EXEC_RULE p256_montjdouble_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p256shortishredlemma = prove
 (`!n. n < 24 * 2 EXP 256
       ==> let q = n DIV 2 EXP 256 + 1 in
           q <= 24 /\
           q < 2 EXP 64 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let p256shortintredlemma = prove
 (`!n. --(&p_256) <= n /\ n <= &4 * &2 pow 256
       ==> let q = (&2 pow 256 + n) div &2 pow 256 in
           &0 <= q /\ q < &6 /\
           q < &2 pow 64 /\
           q * &p_256 <= n + &p_256 /\
           n < q * &p_256 + &p_256`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 256 + n:int = &1 * &2 pow 256 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 256` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_256` THEN REWRITE_TAC[p_256] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_256` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_256] THEN INT_ARITH_TAC);;

let lvs =
 ["x_1",[`X16`; `0`];
  "y_1",[`X16`; `32`];
  "z_1",[`X16`; `64`];
  "x_3",[`X15`; `0`];
  "y_3",[`X15`; `32`];
  "z_3",[`X15`; `64`];
  "z2",[`SP`; `0`];
  "y4",[`SP`; `0`];
  "y2",[`SP`; `32`];
  "t1",[`SP`; `64`];
  "t2",[`SP`; `96`];
  "x2p",[`SP`; `96`];
  "dx2",[`SP`; `96`];
  "xy2",[`SP`; `128`];
  "x4p",[`SP`; `160`];
  "d",[`SP`; `160`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 91 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a)
             (\s. read PC s = pcout /\
                  (a EXP 2 <= 2 EXP 256 * p_256
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 4)) s =
                       (inverse_mod p_256 (2 EXP 256) * a EXP 2) MOD p_256))
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                       X10; X11; X12; X13; X14] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_256  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--91)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--79) (1--79) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s75; sum_s76; sum_s77; sum_s78; word(bitval carry_s78)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\ (2 EXP 256 * t == a EXP 2) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (81--85) (80--91) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256 then &t:real else &t - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s85 <=> t < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 113 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = b
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              b)
             (\s. read PC s = pcout /\
                  (a * b <= 2 EXP 256 * p_256
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s =
                       (inverse_mod p_256 (2 EXP 256) * a * b) MOD p_256))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                        X13; X14] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_256  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--113)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--101) (1--101) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s97; sum_s98; sum_s99; sum_s100;
           word(bitval carry_s100)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\ (2 EXP 256 * t == a * b) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (103--107) (102--113) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256 then &t:real else &t - &p_256`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s107 <=> t < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 17 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < p_256 /\ n < p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&m - &n) rem &p_256))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
           MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--8) (1--8) THEN

  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ARM_STEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [9] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (10--17) (10--17) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s17" THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `--(&(bitval(m < n))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
  REWRITE_TAC[INT_ARITH `m - n:int = --b * p + z <=> z = b * p + m - n`] THEN
  REWRITE_TAC[int_eq; int_le; int_lt] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th; int_sub_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC(REAL_ARITH
  `!t:real. p < t /\
            (&0 <= a /\ a < p) /\
            (&0 <= z /\ z < t) /\
            ((&0 <= z /\ z < t) /\ (&0 <= a /\ a < t) ==> z = a)
            ==> z = a /\ &0 <= z /\ z < p`) THEN
  EXISTS_TAC `(&2:real) pow 256` THEN

  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_256] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; STRIP_TAC] THEN

  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of weakadd                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKADD_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 17 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (m + n < 2 EXP 256 + p_256
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s < 2 EXP 256 /\
                       (&(read(memory :> bytes(word_add (read p3 t) (word n3),
                               8 * 4)) s):int == &m + &n) (mod &p_256)))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [9] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (10--17) (10--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!x. (x < 2 EXP 256 /\ P x) /\ y = x ==> y < 2 EXP 256 /\ P y`) THEN
  EXISTS_TAC `if m + n < 2 EXP 256 then m + n else (m + n) - p_256` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `m + n < 2 EXP 256 + p_256` THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_CONG_REFL] THEN
    MATCH_MP_TAC(INTEGER_RULE `y - p:int = x ==> (x == y) (mod p)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC INT_OF_NUM_SUB THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `b <=> 2 EXP 256 <= m + n` THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCARD_STATE_TAC "s27" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; COND_SWAP] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `m + n < 2 EXP 256 + p_256` THEN
    EXPAND_TAC "b" THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `&(if b then (m + n) - p_256 else m + n):real =
    if b then (&m + &n) - &p_256 else &m + &n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    UNDISCH_TAC `b:bool` THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 25 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
         (\s. read PC s = pcout /\
              (m < p_256 /\ n < p_256
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 4)) s = (m + n) MOD p_256))
         (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
          MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--9) (1--9) THEN

  SUBGOAL_THEN
   `2 EXP 256 * bitval carry_s8 +
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8] =
    m + n`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (10--15) (10--15) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN

  SUBGOAL_THEN
   `carry_s15 <=>
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8] < p_256`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_256;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(BINOP_CONV(BINOP_CONV REAL_POLY_CONV)) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_STEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [16;17] THEN

  FIRST_X_ASSUM(MP_TAC o
    SPEC `word_neg(word(bitval(p_256 <= m + n))):int64` o
    MATCH_MP (MESON[] `read X3 s = z ==> !a. z = a ==> read X3 s = a`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; ADD_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[BITVAL_BOUND; MOD_LT; ADD_EQ_0; BITVAL_EQ_0;
             ARITH_RULE `a <= 1 /\ b <= 1 ==> a + b <  2 EXP 64`] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 5 RAND_CONV) [SYM th]) THEN
    BOOL_CASES_TAC `carry_s8:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; COND_SWAP; MULT_CLAUSES;
                ADD_CLAUSES; WORD_MASK] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (18--25) (18--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s25" THEN

  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[p_256] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ]
   `a:num = m + n ==> &m + &n = &a`)) THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_256] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 61 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&12 * &m - &9 * &n) rem &p_256))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--61)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_256 =
    (&12 * &m + &9 * (&p_256 - &n)) rem &p_256`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--10) (1--10) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist[sum_s4; sum_s6; sum_s8; sum_s10]` THEN
  SUBGOAL_THEN `p_256 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_256]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The main multiply-add accumulation without the final bump ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (11--42) (11--42) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s27; sum_s39; sum_s40; sum_s41; sum_s42]` THEN
  SUBGOAL_THEN `12 * m + 9 * n' < 24 * p_256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_256] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `12 * m + 9 * n' = ca` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "ca" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = ca DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 24` ASSUME_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `sum_s42:int64 = word h` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `ca:num` p256shortishredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of ca - (h + 1) * p_256 ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (45::46::(49--53)) (43--53) THEN
  MP_TAC(SPECL
   [`sum_s53:int64`;
    `&(bignum_of_wordlist[sum_s49; sum_s50; sum_s51; sum_s52]):real`;
    `256`; `ca:num`; `(h + 1) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= ca + p_256`;
        `ca < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [sum_s27; sum_s39; sum_s40; sum_s41; word h] =
      ca`)) THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 24` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [54;56;57;59] (54--61) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> ca < (h + 1) * p_256` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &ca - y + z ==> &ca = x + y - z`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub41_p256 (actually there is only one).                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 32 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
         (\s. read PC s = pcout /\
              (n < p_256
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 4)) s) = (&4 * &m - &n) rem &p_256))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_256 assumption ***)

  ASM_CASES_TAC `n < p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--32)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Instantiate the (integer) quotient approximation lemma ***)

  MP_TAC(SPEC `&4 * &m - &n:int` p256shortintredlemma) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_LT; INT_ARITH
     `n:int < p ==> --p <= &4 * &m - n`] THEN
    MATCH_MP_TAC(INT_ARITH `x:int <= a ==> x - &n <= a`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN EXPAND_TAC "m" THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Main shift-subtract block ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [4;6;10;12;14;15] (1--15) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s4; sum_s6; sum_s10; sum_s12; sum_s15]` THEN
  SUBGOAL_THEN `&2 pow 256 + &4 * &m - &n:int = &ca`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_pow_th;
                int_mul_th; int_of_num_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`320`; `&0:real`] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN BOUNDER_TAC[];
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
          word_ushr m_3 62])`
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

  ABBREV_TAC `q:int64 = sum_s15` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s15:int64` o concl))) THEN
  SUBGOAL_THEN `&ca div &2 pow 256 = &(val(q:int64))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV] THEN
    EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC
   [20;21;22;23; 25;27;28;30] (16--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED_MOD THEN
  MAP_EVERY EXISTS_TAC [`&(val(q:int64)):int`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; p_256] THEN BOUNDER_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `&4 * m - n:int = (&2 pow 256 + &4 * m - n) - &2 pow 256`] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Usual finale, but all split explicitly over q for simplicity ***)

  SUBGOAL_THEN
    `(&ca - &2 pow 256):int < &(val(q:int64)) * &p_256 <=> ~carry_s23`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_LT_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SUBST1_TAC(SYM(ISPEC `q:int64` WORD_VAL)) THEN
    UNDISCH_TAC `&(val(q:int64)):int < &6` THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    SPEC_TAC(`val(q:int64)`,`qv:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_RULE
     `(a:int == b + c - p) (mod p) <=> (a == b + c) (mod p)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    SUBST1_TAC(SYM(ISPEC `q:int64` WORD_VAL)) THEN
    UNDISCH_TAC `&(val(q:int64)):int < &6` THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    SPEC_TAC(`val(q:int64)`,`qv:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s23:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub38 (there is only one).                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P256_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p256_montjdouble_alt_mc 54 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x103c) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_256
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&3 * &m - &8 * &n) rem &p_256))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_256` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P256_MONTJDOUBLE_ALT_EXEC (1--54)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) rem &p_256 =
    (&3 * &m + &8 * (&p_256 - &n)) rem &p_256`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (1--10) (1--10) THEN
  ABBREV_TAC `n' = bignum_of_wordlist[sum_s4; sum_s6; sum_s8; sum_s10]` THEN
  SUBGOAL_THEN `p_256 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_256]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The main multiply-add accumulation without the final bump ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC
   [18;20;21;23;25;27;28;30;31;32;33;34;35] (11--35) THEN
  ABBREV_TAC
   `ca =
    bignum_of_wordlist[sum_s20; sum_s32; sum_s33; sum_s34; sum_s35]` THEN
  SUBGOAL_THEN `3 * m + 8 * n' < 24 * p_256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_256] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `3 * m + 8 * n' = ca` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "ca" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `8 * n' =
      bignum_of_wordlist
       [word_shl sum_s4 3;
        word_subword ((word_join:int64->int64->int128) sum_s6 sum_s4) (61,64);
        word_subword ((word_join:int64->int64->int128) sum_s8 sum_s6) (61,64);
        word_subword ((word_join:int64->int64->int128) sum_s10 sum_s8) (61,64);
        word_ushr sum_s10 61]`
    SUBST1_TAC THENL
     [EXPAND_TAC "n'" THEN REWRITE_TAC[bignum_of_wordlist] THEN
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
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV  THEN
      MAP_EVERY EXPAND_TAC ["m"; "ca"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = ca DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 24` ASSUME_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `sum_s35:int64 = word h` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `ca:num` p256shortishredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ca < 24 * p_256` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[p_256] THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of ca - (h + 1) * p_256 ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC (38::39::(42--46)) (36--46) THEN
  MP_TAC(SPECL
   [`sum_s46:int64`;
    `&(bignum_of_wordlist[sum_s42; sum_s43; sum_s44; sum_s45]):real`;
    `256`; `ca:num`; `(h + 1) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= ca + p_256`;
        `ca < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [sum_s20; sum_s32; sum_s33; sum_s34; word h] =
      ca`)) THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 24` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  ARM_ACCSTEPS_TAC P256_MONTJDOUBLE_ALT_EXEC [47;49;50;52] (47--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> ca < (h + 1) * p_256` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &ca - y + z ==> &ca = x + y - z`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_256 ==> x < p_256 /\ &x = &a rem &p_256`,
  REWRITE_TAC[INT_OF_NUM_REM; p_256] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_256 ==> x < p_256 /\ &x = a rem &p_256`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_256] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_256 = (&i * x rem &p_256 * y rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_256 = (&(NUMERAL n) * &x rem &p_256) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) *
    (&2 pow 256 * x) rem &p_256 * (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * x * y) rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_256] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 256 * x) rem &p_256 + (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x + y)) rem &p_256 /\
   ((&2 pow 256 * x) rem &p_256 - (&2 pow 256 * y) rem &p_256) rem &p_256 =
   (&2 pow 256 * (x - y)) rem &p_256 /\
  (&(NUMERAL n) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   (&2 pow 256 * (&(NUMERAL n) * x)) rem &p_256`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_256 (2 EXP 256)) * (&2 pow 256 * x) rem &p_256) rem &p_256 =
   x rem &p_256`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_256
         ==> x =
             (2 EXP 256 * (inverse_mod p_256 (2 EXP 256) * x) MOD p_256) MOD
             p_256`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_256] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_jacobian_p256_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp256
         (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) =
        (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256)
       ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                (x1 rem &p_256,y1 rem &p_256,z1 rem &p_256) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_256)
                  (x3 rem &p_256,y3 rem &p_256,z3 rem &p_256) =
                group_mul p256_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp256; P256_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_256; b_256] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p256 = new_definition
 `represents_p256 P (x,y,z) <=>
        x < p_256 /\ y < p_256 /\ z < p_256 /\
        weierstrass_of_jacobian (integer_mod_ring p_256)
         (tripled (montgomery_decode (256,p_256)) (x,y,z)) = P`;;

let P256_MONTJDOUBLE_ALT_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,192))
            [(word pc,0x103c); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0x103c)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
                  read PC s = word(pc + 0x4) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read PC s = word (pc + 0x1034) /\
                 !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_P256_TAC 2 ["z2";"z_1"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["y2";"y_1"] THEN
  LOCAL_SUB_P256_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_WEAKADD_P256_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P256_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["t1";"t1"] THEN
  LOCAL_CMSUBC9_P256_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P256_TAC 0 ["t1";"t1";"z2"] THEN
  LOCAL_MONTSQR_P256_TAC 0 ["y4";"y2"] THEN
  LOCAL_MONTMUL_P256_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_SUB_P256_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_CMSUB41_P256_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P256_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s18" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p256; tripled] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_256] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_256]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma) [`z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_256 (2 EXP 256) * x1`;
    `y1d = inverse_mod p_256 (2 EXP 256) * y1`;
    `z1d = inverse_mod p_256 (2 EXP 256) * z1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REM_DOWN_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_ADD_REM; GSYM INT_SUB_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[lemont; demont]) THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_REM_REM] THEN
  REWRITE_TAC[pumont; dismont; unmont] THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p256_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp256;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let P256_MONTJDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,0x103c); (p1,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0x103c)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_montjdouble_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,4) s = t1)
             (\s. read PC s = returnaddress /\
                 !P. represents_p256 P t1
                      ==> represents_p256 (group_mul p256_group P P)
                            (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 192),192)])`,
  ARM_ADD_RETURN_STACK_TAC P256_MONTJDOUBLE_ALT_EXEC
    P256_MONTJDOUBLE_ALT_CORRECT `[]` 192);;
