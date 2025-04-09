(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point addition in Montgomery-Jacobian coordinates for CC SM2 curve.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/ccsm2.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/sm2/sm2_montjadd_alt.o";;
 ****)

let sm2_montjadd_alt_mc = define_assert_from_elf
  "sm2_montjadd_alt_mc" "arm/sm2/sm2_montjadd_alt.o"
[
  0xd10383ff;       (* arm_SUB SP SP (rvalue (word 224)) *)
  0xaa0003ef;       (* arm_MOV X15 X0 *)
  0xaa0103f0;       (* arm_MOV X16 X1 *)
  0xaa0203f1;       (* arm_MOV X17 X2 *)
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
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0xd360fd05;       (* arm_LSR X5 X8 32 *)
  0xeb080082;       (* arm_SUBS X2 X4 X8 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020129;       (* arm_SUBS X9 X9 X2 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xda050108;       (* arm_SBC X8 X8 X5 *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0xd360fd25;       (* arm_LSR X5 X9 32 *)
  0xeb090082;       (* arm_SUBS X2 X4 X9 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02014a;       (* arm_SUBS X10 X10 X2 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0xda050129;       (* arm_SBC X9 X9 X5 *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0xd360fd45;       (* arm_LSR X5 X10 32 *)
  0xeb0a0082;       (* arm_SUBS X2 X4 X10 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02016b;       (* arm_SUBS X11 X11 X2 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xda05014a;       (* arm_SBC X10 X10 X5 *)
  0xd3607d64;       (* arm_LSL X4 X11 32 *)
  0xd360fd65;       (* arm_LSR X5 X11 32 *)
  0xeb0b0082;       (* arm_SUBS X2 X4 X11 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0xda9f33e2;       (* arm_CSETM X2 Condition_CS *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0x92607c43;       (* arm_AND X3 X2 (rvalue (word 18446744069414584320)) *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0x925ff845;       (* arm_AND X5 X2 (rvalue (word 18446744069414584319)) *)
  0xfa02014a;       (* arm_SBCS X10 X10 X2 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa9440e22;       (* arm_LDP X2 X3 X17 (Immediate_Offset (iword (&64))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9451624;       (* arm_LDP X4 X5 X17 (Immediate_Offset (iword (&80))) *)
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
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0xd360fd05;       (* arm_LSR X5 X8 32 *)
  0xeb080082;       (* arm_SUBS X2 X4 X8 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020129;       (* arm_SUBS X9 X9 X2 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xda050108;       (* arm_SBC X8 X8 X5 *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0xd360fd25;       (* arm_LSR X5 X9 32 *)
  0xeb090082;       (* arm_SUBS X2 X4 X9 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02014a;       (* arm_SUBS X10 X10 X2 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0xda050129;       (* arm_SBC X9 X9 X5 *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0xd360fd45;       (* arm_LSR X5 X10 32 *)
  0xeb0a0082;       (* arm_SUBS X2 X4 X10 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02016b;       (* arm_SUBS X11 X11 X2 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xda05014a;       (* arm_SBC X10 X10 X5 *)
  0xd3607d64;       (* arm_LSL X4 X11 32 *)
  0xd360fd65;       (* arm_LSR X5 X11 32 *)
  0xeb0b0082;       (* arm_SUBS X2 X4 X11 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0xda9f33e2;       (* arm_CSETM X2 Condition_CS *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0x92607c43;       (* arm_AND X3 X2 (rvalue (word 18446744069414584320)) *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0x925ff845;       (* arm_AND X5 X2 (rvalue (word 18446744069414584319)) *)
  0xfa02014a;       (* arm_SBCS X10 X10 X2 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xa90a27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0xa9441223;       (* arm_LDP X3 X4 X17 (Immediate_Offset (iword (&64))) *)
  0xa9422207;       (* arm_LDP X7 X8 X16 (Immediate_Offset (iword (&32))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9432a09;       (* arm_LDP X9 X10 X16 (Immediate_Offset (iword (&48))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c60;       (* arm_UMULH X0 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c61;       (* arm_UMULH X1 X3 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa9451a25;       (* arm_LDP X5 X6 X17 (Immediate_Offset (iword (&80))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90c37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&192))) *)
  0xa90d03ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&208))) *)
  0xa9441203;       (* arm_LDP X3 X4 X16 (Immediate_Offset (iword (&64))) *)
  0xa9422227;       (* arm_LDP X7 X8 X17 (Immediate_Offset (iword (&32))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9432a29;       (* arm_LDP X9 X10 X17 (Immediate_Offset (iword (&48))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&32))) *)
  0xa90303ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&48))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9402227;       (* arm_LDP X7 X8 X17 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412a29;       (* arm_LDP X9 X10 X17 (Immediate_Offset (iword (&16))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&64))) *)
  0xa90503ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&80))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa9402207;       (* arm_LDP X7 X8 X16 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412a09;       (* arm_LDP X9 X10 X16 (Immediate_Offset (iword (&16))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  0xa90903ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&144))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&32))) *)
  0xa90303ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&48))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90c37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&192))) *)
  0xa90d03ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&208))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9480fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&128))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9490fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&144))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa90a1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa90b23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xa9421be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa94c0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&192))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa94d0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&208))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9021be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa90323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa94a0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&160))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94b17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&176))) *)
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
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0xd360fd05;       (* arm_LSR X5 X8 32 *)
  0xeb080082;       (* arm_SUBS X2 X4 X8 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020129;       (* arm_SUBS X9 X9 X2 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xda050108;       (* arm_SBC X8 X8 X5 *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0xd360fd25;       (* arm_LSR X5 X9 32 *)
  0xeb090082;       (* arm_SUBS X2 X4 X9 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02014a;       (* arm_SUBS X10 X10 X2 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0xda050129;       (* arm_SBC X9 X9 X5 *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0xd360fd45;       (* arm_LSR X5 X10 32 *)
  0xeb0a0082;       (* arm_SUBS X2 X4 X10 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02016b;       (* arm_SUBS X11 X11 X2 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xda05014a;       (* arm_SBC X10 X10 X5 *)
  0xd3607d64;       (* arm_LSL X4 X11 32 *)
  0xd360fd65;       (* arm_LSR X5 X11 32 *)
  0xeb0b0082;       (* arm_SUBS X2 X4 X11 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0xda9f33e2;       (* arm_CSETM X2 Condition_CS *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0x92607c43;       (* arm_AND X3 X2 (rvalue (word 18446744069414584320)) *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0x925ff845;       (* arm_AND X5 X2 (rvalue (word 18446744069414584319)) *)
  0xfa02014a;       (* arm_SBCS X10 X10 X2 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xa90627e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&96))) *)
  0xa9072fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&112))) *)
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
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0xd360fd05;       (* arm_LSR X5 X8 32 *)
  0xeb080082;       (* arm_SUBS X2 X4 X8 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020129;       (* arm_SUBS X9 X9 X2 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xda050108;       (* arm_SBC X8 X8 X5 *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0xd360fd25;       (* arm_LSR X5 X9 32 *)
  0xeb090082;       (* arm_SUBS X2 X4 X9 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02014a;       (* arm_SUBS X10 X10 X2 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa040108;       (* arm_SBCS X8 X8 X4 *)
  0xda050129;       (* arm_SBC X9 X9 X5 *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0xd360fd45;       (* arm_LSR X5 X10 32 *)
  0xeb0a0082;       (* arm_SUBS X2 X4 X10 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb02016b;       (* arm_SUBS X11 X11 X2 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xda05014a;       (* arm_SBC X10 X10 X5 *)
  0xd3607d64;       (* arm_LSL X4 X11 32 *)
  0xd360fd65;       (* arm_LSR X5 X11 32 *)
  0xeb0b0082;       (* arm_SUBS X2 X4 X11 *)
  0xda1f00a3;       (* arm_SBC X3 X5 XZR *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2607fe3;       (* arm_MOV X3 (rvalue (word 18446744069414584320)) *)
  0x92c00025;       (* arm_MOVN X5 (word 1) 32 *)
  0xb100050c;       (* arm_ADDS X12 X8 (rvalue (word 1)) *)
  0xfa03012d;       (* arm_SBCS X13 X9 X3 *)
  0xba1f014e;       (* arm_ADCS X14 X10 XZR *)
  0xfa050167;       (* arm_SBCS X7 X11 X5 *)
  0xfa1f005f;       (* arm_SBCS XZR X2 XZR *)
  0x9a8c3108;       (* arm_CSEL X8 X8 X12 Condition_CC *)
  0x9a8d3129;       (* arm_CSEL X9 X9 X13 Condition_CC *)
  0x9a8e314a;       (* arm_CSEL X10 X10 X14 Condition_CC *)
  0x9a87316b;       (* arm_CSEL X11 X11 X7 Condition_CC *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c60;       (* arm_UMULH X0 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c61;       (* arm_UMULH X1 X3 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  0xa90903ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&144))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
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
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&64))) *)
  0xa90503ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&80))) *)
  0xa9401be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa9480fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&128))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9490fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&144))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9001be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa90123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9480fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&128))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9490fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&144))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9061be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&96))) *)
  0xa90723e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa9442207;       (* arm_LDP X7 X8 X16 (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452a09;       (* arm_LDP X9 X10 X16 (Immediate_Offset (iword (&80))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b03ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&176))) *)
  0xa9401be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa9440fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&64))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9450fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&80))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9001be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa90123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c60;       (* arm_UMULH X0 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c61;       (* arm_UMULH X1 X3 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90637ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&96))) *)
  0xa90703ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&112))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa9442227;       (* arm_LDP X7 X8 X17 (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452a29;       (* arm_LDP X9 X10 X17 (Immediate_Offset (iword (&80))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b03ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&176))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c60;       (* arm_UMULH X0 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c61;       (* arm_UMULH X1 X3 X10 *)
  0xba0b0000;       (* arm_ADCS X0 X0 X11 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xd360fd86;       (* arm_LSR X6 X12 32 *)
  0xeb0c0168;       (* arm_SUBS X8 X11 X12 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ad;       (* arm_SUBS X13 X13 X8 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa0b0000;       (* arm_SBCS X0 X0 X11 *)
  0xda06018c;       (* arm_SBC X12 X12 X6 *)
  0xd3607dab;       (* arm_LSL X11 X13 32 *)
  0xd360fda6;       (* arm_LSR X6 X13 32 *)
  0xeb0d0168;       (* arm_SUBS X8 X11 X13 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb0801ce;       (* arm_SUBS X14 X14 X8 *)
  0xfa070000;       (* arm_SBCS X0 X0 X7 *)
  0xfa0b018c;       (* arm_SBCS X12 X12 X11 *)
  0xda0601ad;       (* arm_SBC X13 X13 X6 *)
  0xd3607dcb;       (* arm_LSL X11 X14 32 *)
  0xd360fdc6;       (* arm_LSR X6 X14 32 *)
  0xeb0e0168;       (* arm_SUBS X8 X11 X14 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb080000;       (* arm_SUBS X0 X0 X8 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xda0601ce;       (* arm_SBC X14 X14 X6 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xd360fc06;       (* arm_LSR X6 X0 32 *)
  0xeb000168;       (* arm_SUBS X8 X11 X0 *)
  0xda1f00c7;       (* arm_SBC X7 X6 XZR *)
  0xeb08018c;       (* arm_SUBS X12 X12 X8 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa0b01ce;       (* arm_SBCS X14 X14 X11 *)
  0xda060000;       (* arm_SBC X0 X0 X6 *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba050000;       (* arm_ADCS X0 X0 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x92c00026;       (* arm_MOVN X6 (word 1) 32 *)
  0xb1000581;       (* arm_ADDS X1 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xfa060005;       (* arm_SBCS X5 X0 X6 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a81318c;       (* arm_CSEL X12 X12 X1 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a853000;       (* arm_CSEL X0 X0 X5 Condition_CC *)
  0xa90837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  0xa90903ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&144))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa9460fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&96))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9470fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&112))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0x92607c64;       (* arm_AND X4 X3 (rvalue (word 18446744069414584320)) *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0x925ff864;       (* arm_AND X4 X3 (rvalue (word 18446744069414584319)) *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9440600;       (* arm_LDP X0 X1 X16 (Immediate_Offset (iword (&64))) *)
  0xa9450e02;       (* arm_LDP X2 X3 X16 (Immediate_Offset (iword (&80))) *)
  0xaa01000c;       (* arm_ORR X12 X0 X1 *)
  0xaa03004d;       (* arm_ORR X13 X2 X3 *)
  0xaa0d018c;       (* arm_ORR X12 X12 X13 *)
  0xeb1f019f;       (* arm_CMP X12 XZR *)
  0x9a9f07ec;       (* arm_CSET X12 Condition_NE *)
  0xa9441624;       (* arm_LDP X4 X5 X17 (Immediate_Offset (iword (&64))) *)
  0xa9451e26;       (* arm_LDP X6 X7 X17 (Immediate_Offset (iword (&80))) *)
  0xaa05008d;       (* arm_ORR X13 X4 X5 *)
  0xaa0700ce;       (* arm_ORR X14 X6 X7 *)
  0xaa0e01ad;       (* arm_ORR X13 X13 X14 *)
  0xeb1f01bf;       (* arm_CMP X13 XZR *)
  0x9a9f07ed;       (* arm_CSET X13 Condition_NE *)
  0xeb0c01bf;       (* arm_CMP X13 X12 *)
  0xa94a27e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&160))) *)
  0x9a883008;       (* arm_CSEL X8 X0 X8 Condition_CC *)
  0x9a893029;       (* arm_CSEL X9 X1 X9 Condition_CC *)
  0x9a888088;       (* arm_CSEL X8 X4 X8 Condition_HI *)
  0x9a8980a9;       (* arm_CSEL X9 X5 X9 Condition_HI *)
  0xa94b2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0x9a8a304a;       (* arm_CSEL X10 X2 X10 Condition_CC *)
  0x9a8b306b;       (* arm_CSEL X11 X3 X11 Condition_CC *)
  0x9a8a80ca;       (* arm_CSEL X10 X6 X10 Condition_HI *)
  0x9a8b80eb;       (* arm_CSEL X11 X7 X11 Condition_HI *)
  0xa940360c;       (* arm_LDP X12 X13 X16 (Immediate_Offset (iword (&0))) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0x9a803180;       (* arm_CSEL X0 X12 X0 Condition_CC *)
  0x9a8131a1;       (* arm_CSEL X1 X13 X1 Condition_CC *)
  0xa940362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&0))) *)
  0x9a808180;       (* arm_CSEL X0 X12 X0 Condition_HI *)
  0x9a8181a1;       (* arm_CSEL X1 X13 X1 Condition_HI *)
  0xa941360c;       (* arm_LDP X12 X13 X16 (Immediate_Offset (iword (&16))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0x9a823182;       (* arm_CSEL X2 X12 X2 Condition_CC *)
  0x9a8331a3;       (* arm_CSEL X3 X13 X3 Condition_CC *)
  0xa941362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&16))) *)
  0x9a828182;       (* arm_CSEL X2 X12 X2 Condition_HI *)
  0x9a8381a3;       (* arm_CSEL X3 X13 X3 Condition_HI *)
  0xa942360c;       (* arm_LDP X12 X13 X16 (Immediate_Offset (iword (&32))) *)
  0xa94817e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&128))) *)
  0x9a843184;       (* arm_CSEL X4 X12 X4 Condition_CC *)
  0x9a8531a5;       (* arm_CSEL X5 X13 X5 Condition_CC *)
  0xa942362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&32))) *)
  0x9a848184;       (* arm_CSEL X4 X12 X4 Condition_HI *)
  0x9a8581a5;       (* arm_CSEL X5 X13 X5 Condition_HI *)
  0xa943360c;       (* arm_LDP X12 X13 X16 (Immediate_Offset (iword (&48))) *)
  0xa9491fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&144))) *)
  0x9a863186;       (* arm_CSEL X6 X12 X6 Condition_CC *)
  0x9a8731a7;       (* arm_CSEL X7 X13 X7 Condition_CC *)
  0xa943362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&48))) *)
  0x9a868186;       (* arm_CSEL X6 X12 X6 Condition_HI *)
  0x9a8781a7;       (* arm_CSEL X7 X13 X7 Condition_HI *)
  0xa90005e0;       (* arm_STP X0 X1 X15 (Immediate_Offset (iword (&0))) *)
  0xa9010de2;       (* arm_STP X2 X3 X15 (Immediate_Offset (iword (&16))) *)
  0xa90215e4;       (* arm_STP X4 X5 X15 (Immediate_Offset (iword (&32))) *)
  0xa9031de6;       (* arm_STP X6 X7 X15 (Immediate_Offset (iword (&48))) *)
  0xa90425e8;       (* arm_STP X8 X9 X15 (Immediate_Offset (iword (&64))) *)
  0xa9052dea;       (* arm_STP X10 X11 X15 (Immediate_Offset (iword (&80))) *)
  0x910383ff;       (* arm_ADD SP SP (rvalue (word 224)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let SM2_MONTJADD_ALT_EXEC = ARM_MK_EXEC_RULE sm2_montjadd_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let lvs =
 ["x_1",[`X16`;`0`];
  "y_1",[`X16`;`32`];
  "z_1",[`X16`;`64`];
  "x_2",[`X17`;`0`];
  "y_2",[`X17`;`32`];
  "z_2",[`X17`;`64`];
  "x_3",[`X15`;`0`];
  "y_3",[`X15`;`32`];
  "z_3",[`X15`;`64`];
  "z1sq",[`SP`;`0`];
  "ww",[`SP`;`0`];
  "resx",[`SP`;`0`];
  "yd",[`SP`;`32`];
  "y2a",[`SP`;`32`];
  "x2a",[`SP`;`64`];
  "zzx2",[`SP`;`64`];
  "zz",[`SP`;`96`];
  "t1",[`SP`;`96`];
  "t2",[`SP`;`128`];
  "x1a",[`SP`;`128`];
  "zzx1",[`SP`;`128`];
  "resy",[`SP`;`128`];
  "xd",[`SP`;`160`];
  "z2sq",[`SP`;`160`];
  "resz",[`SP`;`160`];
  "y1a",[`SP`;`192`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_SM2_TAC =
  ARM_MACRO_SIM_ABBREV_TAC sm2_montjadd_alt_mc 95 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x1e84) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) sm2_montjadd_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = read X17 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a)
             (\s. read PC s = pcout /\
                  (a EXP 2 <= 2 EXP 256 * p_sm2
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 4)) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a EXP 2) MOD p_sm2))
           (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14] ,,
            MAYCHANGE
             [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC SM2_MONTJADD_ALT_EXEC (1--95)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (1--82) (1--82) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s78; sum_s79; sum_s80; sum_s81; word(bitval carry_s81)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (85--89) (83--95) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_sm2 then &t:real else &t - &p_sm2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s89 <=> t < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_SM2_TAC =
  ARM_MACRO_SIM_ABBREV_TAC sm2_montjadd_alt_mc 117 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = b
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x1e84) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) sm2_montjadd_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = read X17 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              b)
             (\s. read PC s = pcout /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                        X13; X14] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC SM2_MONTJADD_ALT_EXEC (1--117)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (1--104) (1--104) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s100; sum_s101; sum_s102; sum_s103;
           word(bitval carry_s103)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a * b) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (107--111) (105--117) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_sm2 then &t:real else &t - &p_sm2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s111 <=> t < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_SM2_TAC =
  ARM_MACRO_SIM_ABBREV_TAC sm2_montjadd_alt_mc 17 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x1e84) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) sm2_montjadd_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = read X17 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < p_sm2 /\ n < p_sm2
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 4)) s) = (&m - &n) rem &p_sm2))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
           MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (1--8) (1--8) THEN

  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ARM_STEPS_TAC SM2_MONTJADD_ALT_EXEC [9] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (10--17) (10--17) THEN

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

  CONJ_TAC THENL [REWRITE_TAC[p_sm2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_sm2`; `n < p_sm2`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_sm2] THEN REAL_ARITH_TAC;
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
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_sm2] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of amontsqr.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_AMONTSQR_SM2_TAC =
  ARM_MACRO_SIM_ABBREV_TAC sm2_montjadd_alt_mc 90 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = a
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x1e84) (word_add (read p3 t) (word n3),32)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) sm2_montjadd_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X15 s = read X15 t /\
              read X16 s = read X16 t /\
              read X17 s = read X17 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s =
              a)
         (\s. read PC s = pcout /\
              read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
              < 2 EXP 256 /\
              (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
               inverse_mod p_sm2 (2 EXP 256) * a EXP 2) (mod p_sm2))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (1--82) (1--82) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s78; sum_s79; sum_s80; sum_s81; word(bitval carry_s81)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 256 * t <= (2 EXP 256 - 1) EXP 2 + (2 EXP 256 - 1) * p
        ==> t < 2 EXP 256 + p`) THEN
      REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC SM2_MONTJADD_ALT_EXEC (85--89) (83--90) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == ab) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * ab) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `carry_s81 <=> 2 EXP 256 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
    ABBREV_TAC `b <=> 2 EXP 256 <= t`] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval b` THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
   [EXPAND_TAC "b" THEN UNDISCH_TAC `t < 2 EXP 256 + p_sm2` THEN
    REWRITE_TAC[bitval; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES; p_sm2] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_sm2 ==> x < p_sm2 /\ &x = &a rem &p_sm2`,
  REWRITE_TAC[INT_OF_NUM_REM; p_sm2] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_sm2 ==> x < p_sm2 /\ &x = a rem &p_sm2`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_sm2] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_sm2 = (&i * x rem &p_sm2 * y rem &p_sm2) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_sm2 = (&(NUMERAL n) * &x rem &p_sm2) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_sm2 (2 EXP 256)) *
    (&2 pow 256 * x) rem &p_sm2 * (&2 pow 256 * y) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * x * y) rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_sm2] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 256 * x) rem &p_sm2 + (&2 pow 256 * y) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * (x + y)) rem &p_sm2 /\
   ((&2 pow 256 * x) rem &p_sm2 - (&2 pow 256 * y) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * (x - y)) rem &p_sm2 /\
   (&(NUMERAL n) * (&2 pow 256 * x) rem &p_sm2) rem &p_sm2 =
   (&2 pow 256 * (&(NUMERAL n) * x)) rem &p_sm2`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_sm2 (2 EXP 256)) * (&2 pow 256 * x) rem &p_sm2) rem &p_sm2 =
   x rem &p_sm2`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_sm2
         ==> x =
             (2 EXP 256 * (inverse_mod p_sm2 (2 EXP 256) * x) MOD p_sm2) MOD
             p_sm2`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_jacobian_sm2_add = prove
 (`!P1 P2 x1 y1 z1 x2 y2 z2 x3 y3 z3.
        ~(weierstrass_of_jacobian (integer_mod_ring p_sm2)
           (x1 rem &p_sm2,y1 rem &p_sm2,z1 rem &p_sm2) =
          weierstrass_of_jacobian (integer_mod_ring p_sm2)
           (x2 rem &p_sm2,y2 rem &p_sm2,z2 rem &p_sm2)) /\
        jacobian_add_unexceptional ccsm2
         (x1 rem &p_sm2,y1 rem &p_sm2,z1 rem &p_sm2)
         (x2 rem &p_sm2,y2 rem &p_sm2,z2 rem &p_sm2) =
        (x3 rem &p_sm2,y3 rem &p_sm2,z3 rem &p_sm2)
        ==> weierstrass_of_jacobian (integer_mod_ring p_sm2)
                (x1 rem &p_sm2,y1 rem &p_sm2,z1 rem &p_sm2) = P1 /\
            weierstrass_of_jacobian (integer_mod_ring p_sm2)
                (x2 rem &p_sm2,y2 rem &p_sm2,z2 rem &p_sm2) = P2
            ==> weierstrass_of_jacobian (integer_mod_ring p_sm2)
                  (x3 rem &p_sm2,y3 rem &p_sm2,z3 rem &p_sm2) =
                group_mul sm2_group P1 P2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[ccsm2; SM2_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    W(MP_TAC o PART_MATCH (rand o rand) WEIERSTRASS_OF_JACOBIAN_EQ o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_PSM2] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_sm2; b_sm2] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_sm2 = new_definition
 `represents_sm2 P (x,y,z) <=>
        x < p_sm2 /\ y < p_sm2 /\ z < p_sm2 /\
        weierstrass_of_jacobian (integer_mod_ring p_sm2)
         (tripled (montgomery_decode (256,p_sm2)) (x,y,z)) = P`;;

let SM2_MONTJADD_ALT_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,224))
            [(word pc,0x1e84); (p1,96); (p2,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0x1e84)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) sm2_montjadd_alt_mc /\
                  read PC s = word(pc + 0x4) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read PC s = word (pc + 0x1e7c) /\
                  !P1 P2. represents_sm2 P1 t1 /\ represents_sm2 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_sm2 (group_mul sm2_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,224)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`; `p2:int64`;
    `x2:num`; `y2:num`; `z2:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_AMONTSQR_SM2_TAC 3 ["z1sq";"z_1"] THEN
  LOCAL_AMONTSQR_SM2_TAC 0 ["z2sq";"z_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y1a";"z_2";"y_1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y2a";"z_1";"y_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["x2a";"z1sq";"x_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["x1a";"z2sq";"x_1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y2a";"z1sq";"y2a"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["y1a";"z2sq";"y1a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["xd";"x2a";"x1a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["yd";"y2a";"y1a"] THEN
  LOCAL_AMONTSQR_SM2_TAC 0 ["zz";"xd"] THEN
  LOCAL_MONTSQR_SM2_TAC 0 ["ww";"yd"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["zzx1";"zz";"x1a"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["zzx2";"zz";"x2a"] THEN
  LOCAL_SUB_SM2_TAC 0 ["resx";"ww";"zzx1"] THEN
  LOCAL_SUB_SM2_TAC 0 ["t1";"zzx2";"zzx1"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["xd";"xd";"z_1"] THEN
  LOCAL_SUB_SM2_TAC 0 ["resx";"resx";"zzx2"] THEN
  LOCAL_SUB_SM2_TAC 0 ["t2";"zzx1";"resx"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["t1";"t1";"y1a"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["resz";"xd";"z_2"] THEN
  LOCAL_MONTMUL_SM2_TAC 0 ["t2";"yd";"t2"] THEN
  LOCAL_SUB_SM2_TAC 0 ["resy";"t2";"t1"] THEN

  BIGNUM_LDIGITIZE_TAC "x1_"
   `read (memory :> bytes (p1,8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "y1_"
   `read (memory :> bytes (word_add p1 (word 32),8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "z1_"
   `read (memory :> bytes (word_add p1 (word 64),8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "x2_"
   `read (memory :> bytes (p2,8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "y2_"
   `read (memory :> bytes (word_add p2 (word 32),8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "z2_"
   `read (memory :> bytes (word_add p2 (word 64),8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "resx_"
   `read (memory :> bytes (stackpointer,8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "resy_"
   `read (memory :> bytes (word_add stackpointer (word 128),8 * 4)) s26` THEN
  BIGNUM_LDIGITIZE_TAC "resz_"
   `read (memory :> bytes (word_add stackpointer (word 160),8 * 4)) s26` THEN
  ARM_STEPS_TAC SM2_MONTJADD_ALT_EXEC (27--85) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s85" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  MAP_EVERY X_GEN_TAC [`P1:(int#int)option`; `P2:(int#int)option`] THEN
  REWRITE_TAC[represents_sm2; tripled] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_sm2] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_sm2]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN

  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; INT_OF_NUM_EQ; WORD_OR_EQ_0] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MP_TAC(GEN_ALL(SPEC `[x0:int64;x1;x2;x3]` BIGNUM_OF_WORDLIST_EQ_0)) THEN
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
    REWRITE_TAC[SM2_GROUP; weierstrass_add];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P1" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[SM2_GROUP; weierstrass_add];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P2" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO] THEN
    REWRITE_TAC[weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[SM2_GROUP; weierstrass_add];
    ALL_TAC] THEN

  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma)
   [`z2:num`; `y2:num`; `x2:num`; `z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_sm2 (2 EXP 256) * x1`;
    `y1d = inverse_mod p_sm2 (2 EXP 256) * y1`;
    `z1d = inverse_mod p_sm2 (2 EXP 256) * z1`;
    `x2d = inverse_mod p_sm2 (2 EXP 256) * x2`;
    `y2d = inverse_mod p_sm2 (2 EXP 256) * y2`;
    `z2d = inverse_mod p_sm2 (2 EXP 256) * z2`] THEN
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
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl))) THEN
  REWRITE_TAC[IMP_IMP] THEN
  SUBGOAL_THEN `~(&z1d rem &p_sm2 = &0) /\ ~(&z2d rem &p_sm2 = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `~(&z1:int = &0)`; UNDISCH_TAC `~(&z2:int = &0)`] THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    REWRITE_TAC[INT_REM_EQ_0] THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_sm2_add THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM]) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "P2" THEN REWRITE_TAC[weierstrass_of_jacobian] THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; OPTION_DISTINCT];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[jacobian_add_unexceptional; ccsm2;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let SM2_MONTJADD_ALT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 p2 t2 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 224),224))
            [(word pc,0x1e84); (p1,96); (p2,96); (p3,96)] /\
        nonoverlapping (p3,96) (word pc,0x1e84)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) sm2_montjadd_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1; p2] s /\
                  bignum_triple_from_memory (p1,4) s = t1 /\
                  bignum_triple_from_memory (p2,4) s = t2)
             (\s. read PC s = returnaddress /\
                  !P1 P2. represents_sm2 P1 t1 /\ represents_sm2 P2 t2 /\
                          (P1 = P2 ==> P2 = NONE)
                          ==> represents_sm2 (group_mul sm2_group P1 P2)
                               (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(word_sub stackpointer (word 224),224)])`,
  ARM_ADD_RETURN_STACK_TAC SM2_MONTJADD_ALT_EXEC
   SM2_MONTJADD_ALT_CORRECT `[]` 224);;
