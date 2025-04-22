(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Montgomery-Jacobian coordinates for NIST P-384 curve.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp384.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/p384/p384_montjdouble_alt.o";;
 ****)

let p384_montjdouble_alt_mc = define_assert_from_elf
  "p384_montjdouble_alt_mc" "arm/p384/p384_montjdouble_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10543ff;       (* arm_SUB SP SP (rvalue (word 336)) *)
  0xaa0003f7;       (* arm_MOV X23 X0 *)
  0xaa0103f8;       (* arm_MOV X24 X1 *)
  0xa9460f02;       (* arm_LDP X2 X3 X24 (Immediate_Offset (iword (&96))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9471704;       (* arm_LDP X4 X5 X24 (Immediate_Offset (iword (&112))) *)
  0x9b047c48;       (* arm_MUL X8 X2 X4 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9b047c68;       (* arm_MUL X8 X3 X4 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b057c68;       (* arm_MUL X8 X3 X5 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0xa9481f06;       (* arm_LDP X6 X7 X24 (Immediate_Offset (iword (&128))) *)
  0x9b077c4d;       (* arm_MUL X13 X2 X7 *)
  0x9b067c68;       (* arm_MUL X8 X3 X6 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc77c4e;       (* arm_UMULH X14 X2 X7 *)
  0x9b077c68;       (* arm_MUL X8 X3 X7 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b067caf;       (* arm_MUL X15 X5 X6 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0x9bc47c68;       (* arm_UMULH X8 X3 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc67c68;       (* arm_UMULH X8 X3 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc77c68;       (* arm_UMULH X8 X3 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b067c48;       (* arm_MUL X8 X2 X6 *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0x9b057c88;       (* arm_MUL X8 X4 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b067c88;       (* arm_MUL X8 X4 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b077c88;       (* arm_MUL X8 X4 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b077ca8;       (* arm_MUL X8 X5 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9b077cd1;       (* arm_MUL X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc77cd3;       (* arm_UMULH X19 X6 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9bc67c48;       (* arm_UMULH X8 X2 X6 *)
  0xab0801ad;       (* arm_ADDS X13 X13 X8 *)
  0x9bc57c88;       (* arm_UMULH X8 X4 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc67c88;       (* arm_UMULH X8 X4 X6 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9bc77c88;       (* arm_UMULH X8 X4 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc77ca8;       (* arm_UMULH X8 X5 X7 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc27c48;       (* arm_UMULH X8 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9b037c68;       (* arm_MUL X8 X3 X3 *)
  0xba08014a;       (* arm_ADCS X10 X10 X8 *)
  0x9bc37c68;       (* arm_UMULH X8 X3 X3 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9b047c88;       (* arm_MUL X8 X4 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc57ca8;       (* arm_UMULH X8 X5 X5 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b067cc8;       (* arm_MUL X8 X6 X6 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc67cc8;       (* arm_UMULH X8 X6 X6 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0xba080273;       (* arm_ADCS X19 X19 X8 *)
  0x9bc77ce8;       (* arm_UMULH X8 X7 X7 *)
  0x9a080294;       (* arm_ADC X20 X20 X8 *)
  0xd3607c45;       (* arm_LSL X5 X2 32 *)
  0x8b0200a2;       (* arm_ADD X2 X5 X2 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc27ca5;       (* arm_UMULH X5 X5 X2 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b027c83;       (* arm_MUL X3 X4 X2 *)
  0x9bc27c84;       (* arm_UMULH X4 X4 X2 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050129;       (* arm_SUBS X9 X9 X5 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xd3607d25;       (* arm_LSL X5 X9 32 *)
  0x8b0900a9;       (* arm_ADD X9 X5 X9 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc97ca5;       (* arm_UMULH X5 X5 X9 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b097c83;       (* arm_MUL X3 X4 X9 *)
  0x9bc97c84;       (* arm_UMULH X4 X4 X9 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d45;       (* arm_LSL X5 X10 32 *)
  0x8b0a00aa;       (* arm_ADD X10 X5 X10 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0a7c83;       (* arm_MUL X3 X4 X10 *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05016b;       (* arm_SUBS X11 X11 X5 *)
  0xfa04018c;       (* arm_SBCS X12 X12 X4 *)
  0xfa0301ad;       (* arm_SBCS X13 X13 X3 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xd3607d65;       (* arm_LSL X5 X11 32 *)
  0x8b0b00ab;       (* arm_ADD X11 X5 X11 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcb7ca5;       (* arm_UMULH X5 X5 X11 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0b7c83;       (* arm_MUL X3 X4 X11 *)
  0x9bcb7c84;       (* arm_UMULH X4 X4 X11 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05018c;       (* arm_SUBS X12 X12 X5 *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa030042;       (* arm_SBCS X2 X2 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xd3607d85;       (* arm_LSL X5 X12 32 *)
  0x8b0c00ac;       (* arm_ADD X12 X5 X12 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ca5;       (* arm_UMULH X5 X5 X12 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0c7c83;       (* arm_MUL X3 X4 X12 *)
  0x9bcc7c84;       (* arm_UMULH X4 X4 X12 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb0501ad;       (* arm_SUBS X13 X13 X5 *)
  0xfa040042;       (* arm_SBCS X2 X2 X4 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da5;       (* arm_LSL X5 X13 32 *)
  0x8b0d00ad;       (* arm_ADD X13 X5 X13 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ca5;       (* arm_UMULH X5 X5 X13 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0d7c83;       (* arm_MUL X3 X4 X13 *)
  0x9bcd7c84;       (* arm_UMULH X4 X4 X13 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0d0084;       (* arm_ADCS X4 X4 X13 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050042;       (* arm_SUBS X2 X2 X5 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xab0e0042;       (* arm_ADDS X2 X2 X14 *)
  0xba0f0129;       (* arm_ADCS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xb26083e8;       (* arm_MOV X8 (rvalue (word 18446744069414584321)) *)
  0xab08004e;       (* arm_ADDS X14 X2 X8 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0xba08012f;       (* arm_ADCS X15 X9 X8 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xba080150;       (* arm_ADCS X16 X10 X8 *)
  0xba1f0171;       (* arm_ADCS X17 X11 XZR *)
  0xba1f0193;       (* arm_ADCS X19 X12 XZR *)
  0xba1f01b4;       (* arm_ADCS X20 X13 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a8e0042;       (* arm_CSEL X2 X2 X14 Condition_EQ *)
  0x9a8f0129;       (* arm_CSEL X9 X9 X15 Condition_EQ *)
  0x9a90014a;       (* arm_CSEL X10 X10 X16 Condition_EQ *)
  0x9a91016b;       (* arm_CSEL X11 X11 X17 Condition_EQ *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0xa90027e2;       (* arm_STP X2 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa90237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&32))) *)
  0xa9430f02;       (* arm_LDP X2 X3 X24 (Immediate_Offset (iword (&48))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9441704;       (* arm_LDP X4 X5 X24 (Immediate_Offset (iword (&64))) *)
  0x9b047c48;       (* arm_MUL X8 X2 X4 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9b047c68;       (* arm_MUL X8 X3 X4 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b057c68;       (* arm_MUL X8 X3 X5 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0xa9451f06;       (* arm_LDP X6 X7 X24 (Immediate_Offset (iword (&80))) *)
  0x9b077c4d;       (* arm_MUL X13 X2 X7 *)
  0x9b067c68;       (* arm_MUL X8 X3 X6 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc77c4e;       (* arm_UMULH X14 X2 X7 *)
  0x9b077c68;       (* arm_MUL X8 X3 X7 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b067caf;       (* arm_MUL X15 X5 X6 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0x9bc47c68;       (* arm_UMULH X8 X3 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc67c68;       (* arm_UMULH X8 X3 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc77c68;       (* arm_UMULH X8 X3 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b067c48;       (* arm_MUL X8 X2 X6 *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0x9b057c88;       (* arm_MUL X8 X4 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b067c88;       (* arm_MUL X8 X4 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b077c88;       (* arm_MUL X8 X4 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b077ca8;       (* arm_MUL X8 X5 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9b077cd1;       (* arm_MUL X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc77cd3;       (* arm_UMULH X19 X6 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9bc67c48;       (* arm_UMULH X8 X2 X6 *)
  0xab0801ad;       (* arm_ADDS X13 X13 X8 *)
  0x9bc57c88;       (* arm_UMULH X8 X4 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc67c88;       (* arm_UMULH X8 X4 X6 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9bc77c88;       (* arm_UMULH X8 X4 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc77ca8;       (* arm_UMULH X8 X5 X7 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc27c48;       (* arm_UMULH X8 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9b037c68;       (* arm_MUL X8 X3 X3 *)
  0xba08014a;       (* arm_ADCS X10 X10 X8 *)
  0x9bc37c68;       (* arm_UMULH X8 X3 X3 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9b047c88;       (* arm_MUL X8 X4 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc57ca8;       (* arm_UMULH X8 X5 X5 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b067cc8;       (* arm_MUL X8 X6 X6 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc67cc8;       (* arm_UMULH X8 X6 X6 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0xba080273;       (* arm_ADCS X19 X19 X8 *)
  0x9bc77ce8;       (* arm_UMULH X8 X7 X7 *)
  0x9a080294;       (* arm_ADC X20 X20 X8 *)
  0xd3607c45;       (* arm_LSL X5 X2 32 *)
  0x8b0200a2;       (* arm_ADD X2 X5 X2 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc27ca5;       (* arm_UMULH X5 X5 X2 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b027c83;       (* arm_MUL X3 X4 X2 *)
  0x9bc27c84;       (* arm_UMULH X4 X4 X2 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050129;       (* arm_SUBS X9 X9 X5 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xd3607d25;       (* arm_LSL X5 X9 32 *)
  0x8b0900a9;       (* arm_ADD X9 X5 X9 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc97ca5;       (* arm_UMULH X5 X5 X9 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b097c83;       (* arm_MUL X3 X4 X9 *)
  0x9bc97c84;       (* arm_UMULH X4 X4 X9 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d45;       (* arm_LSL X5 X10 32 *)
  0x8b0a00aa;       (* arm_ADD X10 X5 X10 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0a7c83;       (* arm_MUL X3 X4 X10 *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05016b;       (* arm_SUBS X11 X11 X5 *)
  0xfa04018c;       (* arm_SBCS X12 X12 X4 *)
  0xfa0301ad;       (* arm_SBCS X13 X13 X3 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xd3607d65;       (* arm_LSL X5 X11 32 *)
  0x8b0b00ab;       (* arm_ADD X11 X5 X11 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcb7ca5;       (* arm_UMULH X5 X5 X11 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0b7c83;       (* arm_MUL X3 X4 X11 *)
  0x9bcb7c84;       (* arm_UMULH X4 X4 X11 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05018c;       (* arm_SUBS X12 X12 X5 *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa030042;       (* arm_SBCS X2 X2 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xd3607d85;       (* arm_LSL X5 X12 32 *)
  0x8b0c00ac;       (* arm_ADD X12 X5 X12 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ca5;       (* arm_UMULH X5 X5 X12 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0c7c83;       (* arm_MUL X3 X4 X12 *)
  0x9bcc7c84;       (* arm_UMULH X4 X4 X12 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb0501ad;       (* arm_SUBS X13 X13 X5 *)
  0xfa040042;       (* arm_SBCS X2 X2 X4 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da5;       (* arm_LSL X5 X13 32 *)
  0x8b0d00ad;       (* arm_ADD X13 X5 X13 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ca5;       (* arm_UMULH X5 X5 X13 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0d7c83;       (* arm_MUL X3 X4 X13 *)
  0x9bcd7c84;       (* arm_UMULH X4 X4 X13 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0d0084;       (* arm_ADCS X4 X4 X13 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050042;       (* arm_SUBS X2 X2 X5 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xab0e0042;       (* arm_ADDS X2 X2 X14 *)
  0xba0f0129;       (* arm_ADCS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xb26083e8;       (* arm_MOV X8 (rvalue (word 18446744069414584321)) *)
  0xab08004e;       (* arm_ADDS X14 X2 X8 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0xba08012f;       (* arm_ADCS X15 X9 X8 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xba080150;       (* arm_ADCS X16 X10 X8 *)
  0xba1f0171;       (* arm_ADCS X17 X11 XZR *)
  0xba1f0193;       (* arm_ADCS X19 X12 XZR *)
  0xba1f01b4;       (* arm_ADCS X20 X13 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a8e0042;       (* arm_CSEL X2 X2 X14 Condition_EQ *)
  0x9a8f0129;       (* arm_CSEL X9 X9 X15 Condition_EQ *)
  0x9a90014a;       (* arm_CSEL X10 X10 X16 Condition_EQ *)
  0x9a91016b;       (* arm_CSEL X11 X11 X17 Condition_EQ *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0xa90327e2;       (* arm_STP X2 X9 SP (Immediate_Offset (iword (&48))) *)
  0xa9042fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&64))) *)
  0xa90537ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&80))) *)
  0xa9401b05;       (* arm_LDP X5 X6 X24 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xda9f33e3;       (* arm_CSETM X3 Condition_CS *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xfa0400c6;       (* arm_SBCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xda03014a;       (* arm_SBC X10 X10 X3 *)
  0xa90f1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa91023e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xa9112be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0xa9401b05;       (* arm_LDP X5 X6 X24 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9422b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9a03014a;       (* arm_ADC X10 X10 X3 *)
  0xa90c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa90e2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&224))) *)
  0xa94f13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&240))) *)
  0xa94c1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0x9b057c6c;       (* arm_MUL X12 X3 X5 *)
  0x9bc57c6d;       (* arm_UMULH X13 X3 X5 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94d23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9bc77c6f;       (* arm_UMULH X15 X3 X7 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c70;       (* arm_UMULH X16 X3 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0xa94e2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&224))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c71;       (* arm_UMULH X17 X3 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c73;       (* arm_UMULH X19 X3 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0294;       (* arm_ADC X20 X20 X11 *)
  0xa95013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&256))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9a9f37f5;       (* arm_CSET X21 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b02d6;       (* arm_ADC X22 X22 X11 *)
  0xa95113e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&272))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b0042;       (* arm_ADC X2 X2 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9a9f37e1;       (* arm_CSET X1 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0273;       (* arm_ADDS X19 X19 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xd3607d87;       (* arm_LSL X7 X12 32 *)
  0x8b0c00ec;       (* arm_ADD X12 X7 X12 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ce7;       (* arm_UMULH X7 X7 X12 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0c7cc5;       (* arm_MUL X5 X6 X12 *)
  0x9bcc7cc6;       (* arm_UMULH X6 X6 X12 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ad;       (* arm_SUBS X13 X13 X7 *)
  0xfa0601ce;       (* arm_SBCS X14 X14 X6 *)
  0xfa0501ef;       (* arm_SBCS X15 X15 X5 *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da7;       (* arm_LSL X7 X13 32 *)
  0x8b0d00ed;       (* arm_ADD X13 X7 X13 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ce7;       (* arm_UMULH X7 X7 X13 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0d7cc5;       (* arm_MUL X5 X6 X13 *)
  0x9bcd7cc6;       (* arm_UMULH X6 X6 X13 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ce;       (* arm_SUBS X14 X14 X7 *)
  0xfa0601ef;       (* arm_SBCS X15 X15 X6 *)
  0xfa050210;       (* arm_SBCS X16 X16 X5 *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xd3607dc7;       (* arm_LSL X7 X14 32 *)
  0x8b0e00ee;       (* arm_ADD X14 X7 X14 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bce7ce7;       (* arm_UMULH X7 X7 X14 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0e7cc5;       (* arm_MUL X5 X6 X14 *)
  0x9bce7cc6;       (* arm_UMULH X6 X6 X14 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ef;       (* arm_SUBS X15 X15 X7 *)
  0xfa060210;       (* arm_SBCS X16 X16 X6 *)
  0xfa050231;       (* arm_SBCS X17 X17 X5 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f01ce;       (* arm_SBC X14 X14 XZR *)
  0xd3607de7;       (* arm_LSL X7 X15 32 *)
  0x8b0f00ef;       (* arm_ADD X15 X7 X15 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcf7ce7;       (* arm_UMULH X7 X7 X15 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0f7cc5;       (* arm_MUL X5 X6 X15 *)
  0x9bcf7cc6;       (* arm_UMULH X6 X6 X15 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0f00c6;       (* arm_ADCS X6 X6 X15 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070210;       (* arm_SUBS X16 X16 X7 *)
  0xfa060231;       (* arm_SBCS X17 X17 X6 *)
  0xfa05018c;       (* arm_SBCS X12 X12 X5 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e07;       (* arm_LSL X7 X16 32 *)
  0x8b1000f0;       (* arm_ADD X16 X7 X16 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd07ce7;       (* arm_UMULH X7 X7 X16 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b107cc5;       (* arm_MUL X5 X6 X16 *)
  0x9bd07cc6;       (* arm_UMULH X6 X6 X16 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070231;       (* arm_SUBS X17 X17 X7 *)
  0xfa06018c;       (* arm_SBCS X12 X12 X6 *)
  0xfa0501ad;       (* arm_SBCS X13 X13 X5 *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e27;       (* arm_LSL X7 X17 32 *)
  0x8b1100f1;       (* arm_ADD X17 X7 X17 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd17ce7;       (* arm_UMULH X7 X7 X17 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b117cc5;       (* arm_MUL X5 X6 X17 *)
  0x9bd17cc6;       (* arm_UMULH X6 X6 X17 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1100c6;       (* arm_ADCS X6 X6 X17 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa0601ad;       (* arm_SBCS X13 X13 X6 *)
  0xfa0501ce;       (* arm_SBCS X14 X14 X5 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xab13018c;       (* arm_ADDS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xb26083eb;       (* arm_MOV X11 (rvalue (word 18446744069414584321)) *)
  0xab0b0193;       (* arm_ADDS X19 X12 X11 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xba0b01b4;       (* arm_ADCS X20 X13 X11 *)
  0xd280002b;       (* arm_MOV X11 (rvalue (word 1)) *)
  0xba0b01d5;       (* arm_ADCS X21 X14 X11 *)
  0xba1f01f6;       (* arm_ADCS X22 X15 XZR *)
  0xba1f0202;       (* arm_ADCS X2 X16 XZR *)
  0xba1f0221;       (* arm_ADCS X1 X17 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0x9a9501ce;       (* arm_CSEL X14 X14 X21 Condition_EQ *)
  0x9a9601ef;       (* arm_CSEL X15 X15 X22 Condition_EQ *)
  0x9a820210;       (* arm_CSEL X16 X16 X2 Condition_EQ *)
  0x9a810231;       (* arm_CSEL X17 X17 X1 Condition_EQ *)
  0xa90637ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&96))) *)
  0xa9073fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&112))) *)
  0xa90847f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&128))) *)
  0xa9431b05;       (* arm_LDP X5 X6 X24 (Immediate_Offset (iword (&48))) *)
  0xa9460f04;       (* arm_LDP X4 X3 X24 (Immediate_Offset (iword (&96))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9442307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&64))) *)
  0xa9470f04;       (* arm_LDP X4 X3 X24 (Immediate_Offset (iword (&112))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9452b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&80))) *)
  0xa9480f04;       (* arm_LDP X4 X3 X24 (Immediate_Offset (iword (&128))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0xeb0400bf;       (* arm_CMP X5 X4 *)
  0xb2607fe4;       (* arm_MOV X4 (rvalue (word 18446744069414584320)) *)
  0xfa0400df;       (* arm_SBCS XZR X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0xfa0400ff;       (* arm_SBCS XZR X7 X4 *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0xba1f015f;       (* arm_ADCS XZR X10 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xfa0400c6;       (* arm_SBCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xda03014a;       (* arm_SBC X10 X10 X3 *)
  0xa90f1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa91023e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xa9112be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0xa9460fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&96))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94717e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&112))) *)
  0x9b047c48;       (* arm_MUL X8 X2 X4 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9b047c68;       (* arm_MUL X8 X3 X4 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b057c68;       (* arm_MUL X8 X3 X5 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0xa9481fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c4d;       (* arm_MUL X13 X2 X7 *)
  0x9b067c68;       (* arm_MUL X8 X3 X6 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc77c4e;       (* arm_UMULH X14 X2 X7 *)
  0x9b077c68;       (* arm_MUL X8 X3 X7 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b067caf;       (* arm_MUL X15 X5 X6 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0x9bc47c68;       (* arm_UMULH X8 X3 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc67c68;       (* arm_UMULH X8 X3 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc77c68;       (* arm_UMULH X8 X3 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b067c48;       (* arm_MUL X8 X2 X6 *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0x9b057c88;       (* arm_MUL X8 X4 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b067c88;       (* arm_MUL X8 X4 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b077c88;       (* arm_MUL X8 X4 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b077ca8;       (* arm_MUL X8 X5 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9b077cd1;       (* arm_MUL X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc77cd3;       (* arm_UMULH X19 X6 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9bc67c48;       (* arm_UMULH X8 X2 X6 *)
  0xab0801ad;       (* arm_ADDS X13 X13 X8 *)
  0x9bc57c88;       (* arm_UMULH X8 X4 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc67c88;       (* arm_UMULH X8 X4 X6 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9bc77c88;       (* arm_UMULH X8 X4 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc77ca8;       (* arm_UMULH X8 X5 X7 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc27c48;       (* arm_UMULH X8 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9b037c68;       (* arm_MUL X8 X3 X3 *)
  0xba08014a;       (* arm_ADCS X10 X10 X8 *)
  0x9bc37c68;       (* arm_UMULH X8 X3 X3 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9b047c88;       (* arm_MUL X8 X4 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc57ca8;       (* arm_UMULH X8 X5 X5 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b067cc8;       (* arm_MUL X8 X6 X6 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc67cc8;       (* arm_UMULH X8 X6 X6 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0xba080273;       (* arm_ADCS X19 X19 X8 *)
  0x9bc77ce8;       (* arm_UMULH X8 X7 X7 *)
  0x9a080294;       (* arm_ADC X20 X20 X8 *)
  0xd3607c45;       (* arm_LSL X5 X2 32 *)
  0x8b0200a2;       (* arm_ADD X2 X5 X2 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc27ca5;       (* arm_UMULH X5 X5 X2 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b027c83;       (* arm_MUL X3 X4 X2 *)
  0x9bc27c84;       (* arm_UMULH X4 X4 X2 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050129;       (* arm_SUBS X9 X9 X5 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xd3607d25;       (* arm_LSL X5 X9 32 *)
  0x8b0900a9;       (* arm_ADD X9 X5 X9 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc97ca5;       (* arm_UMULH X5 X5 X9 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b097c83;       (* arm_MUL X3 X4 X9 *)
  0x9bc97c84;       (* arm_UMULH X4 X4 X9 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d45;       (* arm_LSL X5 X10 32 *)
  0x8b0a00aa;       (* arm_ADD X10 X5 X10 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0a7c83;       (* arm_MUL X3 X4 X10 *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05016b;       (* arm_SUBS X11 X11 X5 *)
  0xfa04018c;       (* arm_SBCS X12 X12 X4 *)
  0xfa0301ad;       (* arm_SBCS X13 X13 X3 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xd3607d65;       (* arm_LSL X5 X11 32 *)
  0x8b0b00ab;       (* arm_ADD X11 X5 X11 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcb7ca5;       (* arm_UMULH X5 X5 X11 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0b7c83;       (* arm_MUL X3 X4 X11 *)
  0x9bcb7c84;       (* arm_UMULH X4 X4 X11 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05018c;       (* arm_SUBS X12 X12 X5 *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa030042;       (* arm_SBCS X2 X2 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xd3607d85;       (* arm_LSL X5 X12 32 *)
  0x8b0c00ac;       (* arm_ADD X12 X5 X12 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ca5;       (* arm_UMULH X5 X5 X12 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0c7c83;       (* arm_MUL X3 X4 X12 *)
  0x9bcc7c84;       (* arm_UMULH X4 X4 X12 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb0501ad;       (* arm_SUBS X13 X13 X5 *)
  0xfa040042;       (* arm_SBCS X2 X2 X4 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da5;       (* arm_LSL X5 X13 32 *)
  0x8b0d00ad;       (* arm_ADD X13 X5 X13 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ca5;       (* arm_UMULH X5 X5 X13 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0d7c83;       (* arm_MUL X3 X4 X13 *)
  0x9bcd7c84;       (* arm_UMULH X4 X4 X13 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0d0084;       (* arm_ADCS X4 X4 X13 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050042;       (* arm_SUBS X2 X2 X5 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xab0e0042;       (* arm_ADDS X2 X2 X14 *)
  0xba0f0129;       (* arm_ADCS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xb26083e8;       (* arm_MOV X8 (rvalue (word 18446744069414584321)) *)
  0xab08004e;       (* arm_ADDS X14 X2 X8 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0xba08012f;       (* arm_ADCS X15 X9 X8 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xba080150;       (* arm_ADCS X16 X10 X8 *)
  0xba1f0171;       (* arm_ADCS X17 X11 XZR *)
  0xba1f0193;       (* arm_ADCS X19 X12 XZR *)
  0xba1f01b4;       (* arm_ADCS X20 X13 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a8e0042;       (* arm_CSEL X2 X2 X14 Condition_EQ *)
  0x9a8f0129;       (* arm_CSEL X9 X9 X15 Condition_EQ *)
  0x9a90014a;       (* arm_CSEL X10 X10 X16 Condition_EQ *)
  0x9a91016b;       (* arm_CSEL X11 X11 X17 Condition_EQ *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0xa91227e2;       (* arm_STP X2 X9 SP (Immediate_Offset (iword (&288))) *)
  0xa9132fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&304))) *)
  0xa91437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&320))) *)
  0xa9401303;       (* arm_LDP X3 X4 X24 (Immediate_Offset (iword (&0))) *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0x9b057c6c;       (* arm_MUL X12 X3 X5 *)
  0x9bc57c6d;       (* arm_UMULH X13 X3 X5 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9bc77c6f;       (* arm_UMULH X15 X3 X7 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c70;       (* arm_UMULH X16 X3 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0xa9452be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c71;       (* arm_UMULH X17 X3 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c73;       (* arm_UMULH X19 X3 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0294;       (* arm_ADC X20 X20 X11 *)
  0xa9411303;       (* arm_LDP X3 X4 X24 (Immediate_Offset (iword (&16))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9a9f37f5;       (* arm_CSET X21 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b02d6;       (* arm_ADC X22 X22 X11 *)
  0xa9421303;       (* arm_LDP X3 X4 X24 (Immediate_Offset (iword (&32))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b0042;       (* arm_ADC X2 X2 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9a9f37e1;       (* arm_CSET X1 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0273;       (* arm_ADDS X19 X19 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xd3607d87;       (* arm_LSL X7 X12 32 *)
  0x8b0c00ec;       (* arm_ADD X12 X7 X12 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ce7;       (* arm_UMULH X7 X7 X12 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0c7cc5;       (* arm_MUL X5 X6 X12 *)
  0x9bcc7cc6;       (* arm_UMULH X6 X6 X12 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ad;       (* arm_SUBS X13 X13 X7 *)
  0xfa0601ce;       (* arm_SBCS X14 X14 X6 *)
  0xfa0501ef;       (* arm_SBCS X15 X15 X5 *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da7;       (* arm_LSL X7 X13 32 *)
  0x8b0d00ed;       (* arm_ADD X13 X7 X13 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ce7;       (* arm_UMULH X7 X7 X13 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0d7cc5;       (* arm_MUL X5 X6 X13 *)
  0x9bcd7cc6;       (* arm_UMULH X6 X6 X13 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ce;       (* arm_SUBS X14 X14 X7 *)
  0xfa0601ef;       (* arm_SBCS X15 X15 X6 *)
  0xfa050210;       (* arm_SBCS X16 X16 X5 *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xd3607dc7;       (* arm_LSL X7 X14 32 *)
  0x8b0e00ee;       (* arm_ADD X14 X7 X14 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bce7ce7;       (* arm_UMULH X7 X7 X14 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0e7cc5;       (* arm_MUL X5 X6 X14 *)
  0x9bce7cc6;       (* arm_UMULH X6 X6 X14 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ef;       (* arm_SUBS X15 X15 X7 *)
  0xfa060210;       (* arm_SBCS X16 X16 X6 *)
  0xfa050231;       (* arm_SBCS X17 X17 X5 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f01ce;       (* arm_SBC X14 X14 XZR *)
  0xd3607de7;       (* arm_LSL X7 X15 32 *)
  0x8b0f00ef;       (* arm_ADD X15 X7 X15 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcf7ce7;       (* arm_UMULH X7 X7 X15 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0f7cc5;       (* arm_MUL X5 X6 X15 *)
  0x9bcf7cc6;       (* arm_UMULH X6 X6 X15 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0f00c6;       (* arm_ADCS X6 X6 X15 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070210;       (* arm_SUBS X16 X16 X7 *)
  0xfa060231;       (* arm_SBCS X17 X17 X6 *)
  0xfa05018c;       (* arm_SBCS X12 X12 X5 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e07;       (* arm_LSL X7 X16 32 *)
  0x8b1000f0;       (* arm_ADD X16 X7 X16 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd07ce7;       (* arm_UMULH X7 X7 X16 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b107cc5;       (* arm_MUL X5 X6 X16 *)
  0x9bd07cc6;       (* arm_UMULH X6 X6 X16 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070231;       (* arm_SUBS X17 X17 X7 *)
  0xfa06018c;       (* arm_SBCS X12 X12 X6 *)
  0xfa0501ad;       (* arm_SBCS X13 X13 X5 *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e27;       (* arm_LSL X7 X17 32 *)
  0x8b1100f1;       (* arm_ADD X17 X7 X17 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd17ce7;       (* arm_UMULH X7 X7 X17 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b117cc5;       (* arm_MUL X5 X6 X17 *)
  0x9bd17cc6;       (* arm_UMULH X6 X6 X17 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1100c6;       (* arm_ADCS X6 X6 X17 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa0601ad;       (* arm_SBCS X13 X13 X6 *)
  0xfa0501ce;       (* arm_SBCS X14 X14 X5 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xab13018c;       (* arm_ADDS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xb26083eb;       (* arm_MOV X11 (rvalue (word 18446744069414584321)) *)
  0xab0b0193;       (* arm_ADDS X19 X12 X11 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xba0b01b4;       (* arm_ADCS X20 X13 X11 *)
  0xd280002b;       (* arm_MOV X11 (rvalue (word 1)) *)
  0xba0b01d5;       (* arm_ADCS X21 X14 X11 *)
  0xba1f01f6;       (* arm_ADCS X22 X15 XZR *)
  0xba1f0202;       (* arm_ADCS X2 X16 XZR *)
  0xba1f0221;       (* arm_ADCS X1 X17 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0x9a9501ce;       (* arm_CSEL X14 X14 X21 Condition_EQ *)
  0x9a9601ef;       (* arm_CSEL X15 X15 X22 Condition_EQ *)
  0x9a820210;       (* arm_CSEL X16 X16 X2 Condition_EQ *)
  0x9a810231;       (* arm_CSEL X17 X17 X1 Condition_EQ *)
  0xa90937ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&144))) *)
  0xa90a3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&160))) *)
  0xa90b47f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&176))) *)
  0xa94f0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&240))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95017e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&256))) *)
  0x9b047c48;       (* arm_MUL X8 X2 X4 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9b047c68;       (* arm_MUL X8 X3 X4 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b057c68;       (* arm_MUL X8 X3 X5 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0xa9511fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&272))) *)
  0x9b077c4d;       (* arm_MUL X13 X2 X7 *)
  0x9b067c68;       (* arm_MUL X8 X3 X6 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc77c4e;       (* arm_UMULH X14 X2 X7 *)
  0x9b077c68;       (* arm_MUL X8 X3 X7 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b067caf;       (* arm_MUL X15 X5 X6 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0x9bc47c68;       (* arm_UMULH X8 X3 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc67c68;       (* arm_UMULH X8 X3 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc77c68;       (* arm_UMULH X8 X3 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b067c48;       (* arm_MUL X8 X2 X6 *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0x9b057c88;       (* arm_MUL X8 X4 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b067c88;       (* arm_MUL X8 X4 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b077c88;       (* arm_MUL X8 X4 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b077ca8;       (* arm_MUL X8 X5 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9b077cd1;       (* arm_MUL X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc77cd3;       (* arm_UMULH X19 X6 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9bc67c48;       (* arm_UMULH X8 X2 X6 *)
  0xab0801ad;       (* arm_ADDS X13 X13 X8 *)
  0x9bc57c88;       (* arm_UMULH X8 X4 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc67c88;       (* arm_UMULH X8 X4 X6 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9bc77c88;       (* arm_UMULH X8 X4 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc77ca8;       (* arm_UMULH X8 X5 X7 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc27c48;       (* arm_UMULH X8 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9b037c68;       (* arm_MUL X8 X3 X3 *)
  0xba08014a;       (* arm_ADCS X10 X10 X8 *)
  0x9bc37c68;       (* arm_UMULH X8 X3 X3 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9b047c88;       (* arm_MUL X8 X4 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc57ca8;       (* arm_UMULH X8 X5 X5 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b067cc8;       (* arm_MUL X8 X6 X6 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc67cc8;       (* arm_UMULH X8 X6 X6 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0xba080273;       (* arm_ADCS X19 X19 X8 *)
  0x9bc77ce8;       (* arm_UMULH X8 X7 X7 *)
  0x9a080294;       (* arm_ADC X20 X20 X8 *)
  0xd3607c45;       (* arm_LSL X5 X2 32 *)
  0x8b0200a2;       (* arm_ADD X2 X5 X2 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc27ca5;       (* arm_UMULH X5 X5 X2 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b027c83;       (* arm_MUL X3 X4 X2 *)
  0x9bc27c84;       (* arm_UMULH X4 X4 X2 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050129;       (* arm_SUBS X9 X9 X5 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xd3607d25;       (* arm_LSL X5 X9 32 *)
  0x8b0900a9;       (* arm_ADD X9 X5 X9 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc97ca5;       (* arm_UMULH X5 X5 X9 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b097c83;       (* arm_MUL X3 X4 X9 *)
  0x9bc97c84;       (* arm_UMULH X4 X4 X9 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d45;       (* arm_LSL X5 X10 32 *)
  0x8b0a00aa;       (* arm_ADD X10 X5 X10 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0a7c83;       (* arm_MUL X3 X4 X10 *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05016b;       (* arm_SUBS X11 X11 X5 *)
  0xfa04018c;       (* arm_SBCS X12 X12 X4 *)
  0xfa0301ad;       (* arm_SBCS X13 X13 X3 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xd3607d65;       (* arm_LSL X5 X11 32 *)
  0x8b0b00ab;       (* arm_ADD X11 X5 X11 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcb7ca5;       (* arm_UMULH X5 X5 X11 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0b7c83;       (* arm_MUL X3 X4 X11 *)
  0x9bcb7c84;       (* arm_UMULH X4 X4 X11 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05018c;       (* arm_SUBS X12 X12 X5 *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa030042;       (* arm_SBCS X2 X2 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xd3607d85;       (* arm_LSL X5 X12 32 *)
  0x8b0c00ac;       (* arm_ADD X12 X5 X12 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ca5;       (* arm_UMULH X5 X5 X12 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0c7c83;       (* arm_MUL X3 X4 X12 *)
  0x9bcc7c84;       (* arm_UMULH X4 X4 X12 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb0501ad;       (* arm_SUBS X13 X13 X5 *)
  0xfa040042;       (* arm_SBCS X2 X2 X4 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da5;       (* arm_LSL X5 X13 32 *)
  0x8b0d00ad;       (* arm_ADD X13 X5 X13 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ca5;       (* arm_UMULH X5 X5 X13 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0d7c83;       (* arm_MUL X3 X4 X13 *)
  0x9bcd7c84;       (* arm_UMULH X4 X4 X13 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0d0084;       (* arm_ADCS X4 X4 X13 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050042;       (* arm_SUBS X2 X2 X5 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xab0e0042;       (* arm_ADDS X2 X2 X14 *)
  0xba0f0129;       (* arm_ADCS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xb26083e8;       (* arm_MOV X8 (rvalue (word 18446744069414584321)) *)
  0xab08004e;       (* arm_ADDS X14 X2 X8 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0xba08012f;       (* arm_ADCS X15 X9 X8 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xba080150;       (* arm_ADCS X16 X10 X8 *)
  0xba1f0171;       (* arm_ADCS X17 X11 XZR *)
  0xba1f0193;       (* arm_ADCS X19 X12 XZR *)
  0xba1f01b4;       (* arm_ADCS X20 X13 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a8e0042;       (* arm_CSEL X2 X2 X14 Condition_EQ *)
  0x9a8f0129;       (* arm_CSEL X9 X9 X15 Condition_EQ *)
  0x9a90014a;       (* arm_CSEL X10 X10 X16 Condition_EQ *)
  0x9a91016b;       (* arm_CSEL X11 X11 X17 Condition_EQ *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0xa90c27e2;       (* arm_STP X2 X9 SP (Immediate_Offset (iword (&192))) *)
  0xa90d2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&208))) *)
  0xa90e37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&224))) *)
  0xa95207e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0xeb0000c6;       (* arm_SUBS X6 X6 X0 *)
  0xb2607fe7;       (* arm_MOV X7 (rvalue (word 18446744069414584320)) *)
  0xfa0100e7;       (* arm_SBCS X7 X7 X1 *)
  0xa95307e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&304))) *)
  0x92800028;       (* arm_MOVN X8 (word 1) 0 *)
  0xfa000108;       (* arm_SBCS X8 X8 X0 *)
  0x9280000d;       (* arm_MOVN X13 (word 0) 0 *)
  0xfa0101a9;       (* arm_SBCS X9 X13 X1 *)
  0xa95407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&320))) *)
  0xfa0001aa;       (* arm_SBCS X10 X13 X0 *)
  0xda0101ab;       (* arm_SBC X11 X13 X1 *)
  0xd280012c;       (* arm_MOV X12 (rvalue (word 9)) *)
  0x9b067d80;       (* arm_MUL X0 X12 X6 *)
  0x9b077d81;       (* arm_MUL X1 X12 X7 *)
  0x9b087d82;       (* arm_MUL X2 X12 X8 *)
  0x9b097d83;       (* arm_MUL X3 X12 X9 *)
  0x9b0a7d84;       (* arm_MUL X4 X12 X10 *)
  0x9b0b7d85;       (* arm_MUL X5 X12 X11 *)
  0x9bc67d86;       (* arm_UMULH X6 X12 X6 *)
  0x9bc77d87;       (* arm_UMULH X7 X12 X7 *)
  0x9bc87d88;       (* arm_UMULH X8 X12 X8 *)
  0x9bc97d89;       (* arm_UMULH X9 X12 X9 *)
  0x9bca7d8a;       (* arm_UMULH X10 X12 X10 *)
  0x9bcb7d8c;       (* arm_UMULH X12 X12 X11 *)
  0xab060021;       (* arm_ADDS X1 X1 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0x9a060186;       (* arm_ADC X6 X12 X6 *)
  0xa94927e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&144))) *)
  0xa94a2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&160))) *)
  0xa94b37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&176))) *)
  0xd280018e;       (* arm_MOV X14 (rvalue (word 12)) *)
  0x9b087dcf;       (* arm_MUL X15 X14 X8 *)
  0x9bc87dc8;       (* arm_UMULH X8 X14 X8 *)
  0xab0f0000;       (* arm_ADDS X0 X0 X15 *)
  0x9b097dcf;       (* arm_MUL X15 X14 X9 *)
  0x9bc97dc9;       (* arm_UMULH X9 X14 X9 *)
  0xba0f0021;       (* arm_ADCS X1 X1 X15 *)
  0x9b0a7dcf;       (* arm_MUL X15 X14 X10 *)
  0x9bca7dca;       (* arm_UMULH X10 X14 X10 *)
  0xba0f0042;       (* arm_ADCS X2 X2 X15 *)
  0x9b0b7dcf;       (* arm_MUL X15 X14 X11 *)
  0x9bcb7dcb;       (* arm_UMULH X11 X14 X11 *)
  0xba0f0063;       (* arm_ADCS X3 X3 X15 *)
  0x9b0c7dcf;       (* arm_MUL X15 X14 X12 *)
  0x9bcc7dcc;       (* arm_UMULH X12 X14 X12 *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0x9b0d7dcf;       (* arm_MUL X15 X14 X13 *)
  0x9bcd7dcd;       (* arm_UMULH X13 X14 X13 *)
  0xba0f00a5;       (* arm_ADCS X5 X5 X15 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab080021;       (* arm_ADDS X1 X1 X8 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0xba0c00a5;       (* arm_ADCS X5 X5 X12 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0xd3607cc7;       (* arm_LSL X7 X6 32 *)
  0xeb0700c8;       (* arm_SUBS X8 X6 X7 *)
  0xda1f00e7;       (* arm_SBC X7 X7 XZR *)
  0xab080000;       (* arm_ADDS X0 X0 X8 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xda9f23e6;       (* arm_CSETM X6 Condition_CC *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0xca0600e7;       (* arm_EOR X7 X7 X6 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0x92800027;       (* arm_MOVN X7 (word 1) 0 *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0x9a0600a5;       (* arm_ADC X5 X5 X6 *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa9130fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&304))) *)
  0xa91417e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&320))) *)
  0xa94c1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94d23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa94e2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&224))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9a03014a;       (* arm_ADC X10 X10 X3 *)
  0xa90f1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa91023e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xa9112be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0xa9430fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94417e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&64))) *)
  0x9b047c48;       (* arm_MUL X8 X2 X4 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9b047c68;       (* arm_MUL X8 X3 X4 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b057c68;       (* arm_MUL X8 X3 X5 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0xa9451fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&80))) *)
  0x9b077c4d;       (* arm_MUL X13 X2 X7 *)
  0x9b067c68;       (* arm_MUL X8 X3 X6 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc77c4e;       (* arm_UMULH X14 X2 X7 *)
  0x9b077c68;       (* arm_MUL X8 X3 X7 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b067caf;       (* arm_MUL X15 X5 X6 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0x9bc47c68;       (* arm_UMULH X8 X3 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc67c68;       (* arm_UMULH X8 X3 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc77c68;       (* arm_UMULH X8 X3 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b067c48;       (* arm_MUL X8 X2 X6 *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0x9b057c88;       (* arm_MUL X8 X4 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b067c88;       (* arm_MUL X8 X4 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b077c88;       (* arm_MUL X8 X4 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b077ca8;       (* arm_MUL X8 X5 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9b077cd1;       (* arm_MUL X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc77cd3;       (* arm_UMULH X19 X6 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9bc67c48;       (* arm_UMULH X8 X2 X6 *)
  0xab0801ad;       (* arm_ADDS X13 X13 X8 *)
  0x9bc57c88;       (* arm_UMULH X8 X4 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc67c88;       (* arm_UMULH X8 X4 X6 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9bc77c88;       (* arm_UMULH X8 X4 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc77ca8;       (* arm_UMULH X8 X5 X7 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc27c48;       (* arm_UMULH X8 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9b037c68;       (* arm_MUL X8 X3 X3 *)
  0xba08014a;       (* arm_ADCS X10 X10 X8 *)
  0x9bc37c68;       (* arm_UMULH X8 X3 X3 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9b047c88;       (* arm_MUL X8 X4 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc57ca8;       (* arm_UMULH X8 X5 X5 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b067cc8;       (* arm_MUL X8 X6 X6 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc67cc8;       (* arm_UMULH X8 X6 X6 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0xba080273;       (* arm_ADCS X19 X19 X8 *)
  0x9bc77ce8;       (* arm_UMULH X8 X7 X7 *)
  0x9a080294;       (* arm_ADC X20 X20 X8 *)
  0xd3607c45;       (* arm_LSL X5 X2 32 *)
  0x8b0200a2;       (* arm_ADD X2 X5 X2 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc27ca5;       (* arm_UMULH X5 X5 X2 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b027c83;       (* arm_MUL X3 X4 X2 *)
  0x9bc27c84;       (* arm_UMULH X4 X4 X2 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050129;       (* arm_SUBS X9 X9 X5 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xd3607d25;       (* arm_LSL X5 X9 32 *)
  0x8b0900a9;       (* arm_ADD X9 X5 X9 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc97ca5;       (* arm_UMULH X5 X5 X9 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b097c83;       (* arm_MUL X3 X4 X9 *)
  0x9bc97c84;       (* arm_UMULH X4 X4 X9 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d45;       (* arm_LSL X5 X10 32 *)
  0x8b0a00aa;       (* arm_ADD X10 X5 X10 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0a7c83;       (* arm_MUL X3 X4 X10 *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05016b;       (* arm_SUBS X11 X11 X5 *)
  0xfa04018c;       (* arm_SBCS X12 X12 X4 *)
  0xfa0301ad;       (* arm_SBCS X13 X13 X3 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xd3607d65;       (* arm_LSL X5 X11 32 *)
  0x8b0b00ab;       (* arm_ADD X11 X5 X11 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcb7ca5;       (* arm_UMULH X5 X5 X11 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0b7c83;       (* arm_MUL X3 X4 X11 *)
  0x9bcb7c84;       (* arm_UMULH X4 X4 X11 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05018c;       (* arm_SUBS X12 X12 X5 *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa030042;       (* arm_SBCS X2 X2 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xd3607d85;       (* arm_LSL X5 X12 32 *)
  0x8b0c00ac;       (* arm_ADD X12 X5 X12 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ca5;       (* arm_UMULH X5 X5 X12 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0c7c83;       (* arm_MUL X3 X4 X12 *)
  0x9bcc7c84;       (* arm_UMULH X4 X4 X12 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb0501ad;       (* arm_SUBS X13 X13 X5 *)
  0xfa040042;       (* arm_SBCS X2 X2 X4 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da5;       (* arm_LSL X5 X13 32 *)
  0x8b0d00ad;       (* arm_ADD X13 X5 X13 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ca5;       (* arm_UMULH X5 X5 X13 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0d7c83;       (* arm_MUL X3 X4 X13 *)
  0x9bcd7c84;       (* arm_UMULH X4 X4 X13 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0d0084;       (* arm_ADCS X4 X4 X13 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050042;       (* arm_SUBS X2 X2 X5 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xab0e0042;       (* arm_ADDS X2 X2 X14 *)
  0xba0f0129;       (* arm_ADCS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xb26083e8;       (* arm_MOV X8 (rvalue (word 18446744069414584321)) *)
  0xab08004e;       (* arm_ADDS X14 X2 X8 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0xba08012f;       (* arm_ADCS X15 X9 X8 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xba080150;       (* arm_ADCS X16 X10 X8 *)
  0xba1f0171;       (* arm_ADCS X17 X11 XZR *)
  0xba1f0193;       (* arm_ADCS X19 X12 XZR *)
  0xba1f01b4;       (* arm_ADCS X20 X13 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a8e0042;       (* arm_CSEL X2 X2 X14 Condition_EQ *)
  0x9a8f0129;       (* arm_CSEL X9 X9 X15 Condition_EQ *)
  0x9a90014a;       (* arm_CSEL X10 X10 X16 Condition_EQ *)
  0x9a91016b;       (* arm_CSEL X11 X11 X17 Condition_EQ *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0xa90c27e2;       (* arm_STP X2 X9 SP (Immediate_Offset (iword (&192))) *)
  0xa90d2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&208))) *)
  0xa90e37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&224))) *)
  0xa94f1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xa9440fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&64))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9512be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0xa9450fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&80))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xca030084;       (* arm_EOR X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0x92800024;       (* arm_MOVN X4 (word 1) 0 *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x9a03014a;       (* arm_ADC X10 X10 X3 *)
  0xa9061ae5;       (* arm_STP X5 X6 X23 (Immediate_Offset (iword (&96))) *)
  0xa90722e7;       (* arm_STP X7 X8 X23 (Immediate_Offset (iword (&112))) *)
  0xa9082ae9;       (* arm_STP X9 X10 X23 (Immediate_Offset (iword (&128))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa9461be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&96))) *)
  0x9b057c6c;       (* arm_MUL X12 X3 X5 *)
  0x9bc57c6d;       (* arm_UMULH X13 X3 X5 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94723e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9bc77c6f;       (* arm_UMULH X15 X3 X7 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c70;       (* arm_UMULH X16 X3 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0xa9482be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&128))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c71;       (* arm_UMULH X17 X3 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c73;       (* arm_UMULH X19 X3 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0294;       (* arm_ADC X20 X20 X11 *)
  0xa95313e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&304))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9a9f37f5;       (* arm_CSET X21 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b02d6;       (* arm_ADC X22 X22 X11 *)
  0xa95413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&320))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b0042;       (* arm_ADC X2 X2 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9a9f37e1;       (* arm_CSET X1 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0273;       (* arm_ADDS X19 X19 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xd3607d87;       (* arm_LSL X7 X12 32 *)
  0x8b0c00ec;       (* arm_ADD X12 X7 X12 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ce7;       (* arm_UMULH X7 X7 X12 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0c7cc5;       (* arm_MUL X5 X6 X12 *)
  0x9bcc7cc6;       (* arm_UMULH X6 X6 X12 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ad;       (* arm_SUBS X13 X13 X7 *)
  0xfa0601ce;       (* arm_SBCS X14 X14 X6 *)
  0xfa0501ef;       (* arm_SBCS X15 X15 X5 *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da7;       (* arm_LSL X7 X13 32 *)
  0x8b0d00ed;       (* arm_ADD X13 X7 X13 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ce7;       (* arm_UMULH X7 X7 X13 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0d7cc5;       (* arm_MUL X5 X6 X13 *)
  0x9bcd7cc6;       (* arm_UMULH X6 X6 X13 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ce;       (* arm_SUBS X14 X14 X7 *)
  0xfa0601ef;       (* arm_SBCS X15 X15 X6 *)
  0xfa050210;       (* arm_SBCS X16 X16 X5 *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xd3607dc7;       (* arm_LSL X7 X14 32 *)
  0x8b0e00ee;       (* arm_ADD X14 X7 X14 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bce7ce7;       (* arm_UMULH X7 X7 X14 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0e7cc5;       (* arm_MUL X5 X6 X14 *)
  0x9bce7cc6;       (* arm_UMULH X6 X6 X14 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ef;       (* arm_SUBS X15 X15 X7 *)
  0xfa060210;       (* arm_SBCS X16 X16 X6 *)
  0xfa050231;       (* arm_SBCS X17 X17 X5 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f01ce;       (* arm_SBC X14 X14 XZR *)
  0xd3607de7;       (* arm_LSL X7 X15 32 *)
  0x8b0f00ef;       (* arm_ADD X15 X7 X15 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcf7ce7;       (* arm_UMULH X7 X7 X15 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0f7cc5;       (* arm_MUL X5 X6 X15 *)
  0x9bcf7cc6;       (* arm_UMULH X6 X6 X15 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0f00c6;       (* arm_ADCS X6 X6 X15 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070210;       (* arm_SUBS X16 X16 X7 *)
  0xfa060231;       (* arm_SBCS X17 X17 X6 *)
  0xfa05018c;       (* arm_SBCS X12 X12 X5 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e07;       (* arm_LSL X7 X16 32 *)
  0x8b1000f0;       (* arm_ADD X16 X7 X16 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd07ce7;       (* arm_UMULH X7 X7 X16 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b107cc5;       (* arm_MUL X5 X6 X16 *)
  0x9bd07cc6;       (* arm_UMULH X6 X6 X16 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070231;       (* arm_SUBS X17 X17 X7 *)
  0xfa06018c;       (* arm_SBCS X12 X12 X6 *)
  0xfa0501ad;       (* arm_SBCS X13 X13 X5 *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e27;       (* arm_LSL X7 X17 32 *)
  0x8b1100f1;       (* arm_ADD X17 X7 X17 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd17ce7;       (* arm_UMULH X7 X7 X17 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b117cc5;       (* arm_MUL X5 X6 X17 *)
  0x9bd17cc6;       (* arm_UMULH X6 X6 X17 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1100c6;       (* arm_ADCS X6 X6 X17 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa0601ad;       (* arm_SBCS X13 X13 X6 *)
  0xfa0501ce;       (* arm_SBCS X14 X14 X5 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xab13018c;       (* arm_ADDS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xb26083eb;       (* arm_MOV X11 (rvalue (word 18446744069414584321)) *)
  0xab0b0193;       (* arm_ADDS X19 X12 X11 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xba0b01b4;       (* arm_ADCS X20 X13 X11 *)
  0xd280002b;       (* arm_MOV X11 (rvalue (word 1)) *)
  0xba0b01d5;       (* arm_ADCS X21 X14 X11 *)
  0xba1f01f6;       (* arm_ADCS X22 X15 XZR *)
  0xba1f0202;       (* arm_ADCS X2 X16 XZR *)
  0xba1f0221;       (* arm_ADCS X1 X17 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0x9a9501ce;       (* arm_CSEL X14 X14 X21 Condition_EQ *)
  0x9a9601ef;       (* arm_CSEL X15 X15 X22 Condition_EQ *)
  0x9a820210;       (* arm_CSEL X16 X16 X2 Condition_EQ *)
  0x9a810231;       (* arm_CSEL X17 X17 X1 Condition_EQ *)
  0xa90f37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&240))) *)
  0xa9103fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&256))) *)
  0xa91147f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&272))) *)
  0xa9490be1;       (* arm_LDP X1 X2 SP (Immediate_Offset (iword (&144))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xd37ef420;       (* arm_LSL X0 X1 2 *)
  0xa95223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&288))) *)
  0xeb070000;       (* arm_SUBS X0 X0 X7 *)
  0x93c1f841;       (* arm_EXTR X1 X2 X1 62 *)
  0xfa080021;       (* arm_SBCS X1 X1 X8 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0x93c2f862;       (* arm_EXTR X2 X3 X2 62 *)
  0xfa070042;       (* arm_SBCS X2 X2 X7 *)
  0x93c3f883;       (* arm_EXTR X3 X4 X3 62 *)
  0xfa080063;       (* arm_SBCS X3 X3 X8 *)
  0x93c4f8a4;       (* arm_EXTR X4 X5 X4 62 *)
  0xa95423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&320))) *)
  0xfa070084;       (* arm_SBCS X4 X4 X7 *)
  0x93c5f8c5;       (* arm_EXTR X5 X6 X5 62 *)
  0xfa0800a5;       (* arm_SBCS X5 X5 X8 *)
  0xd37efcc6;       (* arm_LSR X6 X6 62 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xd3607cc7;       (* arm_LSL X7 X6 32 *)
  0xeb0700c8;       (* arm_SUBS X8 X6 X7 *)
  0xda1f00e7;       (* arm_SBC X7 X7 XZR *)
  0xab080000;       (* arm_ADDS X0 X0 X8 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xda9f23e8;       (* arm_CSETM X8 Condition_CC *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xab090000;       (* arm_ADDS X0 X0 X9 *)
  0xca080129;       (* arm_EOR X9 X9 X8 *)
  0xba090021;       (* arm_ADCS X1 X1 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0x9a0800a5;       (* arm_ADC X5 X5 X8 *)
  0xa90006e0;       (* arm_STP X0 X1 X23 (Immediate_Offset (iword (&0))) *)
  0xa9010ee2;       (* arm_STP X2 X3 X23 (Immediate_Offset (iword (&16))) *)
  0xa90216e4;       (* arm_STP X4 X5 X23 (Immediate_Offset (iword (&32))) *)
  0xa94c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0xeb0000c6;       (* arm_SUBS X6 X6 X0 *)
  0xb2607fe7;       (* arm_MOV X7 (rvalue (word 18446744069414584320)) *)
  0xfa0100e7;       (* arm_SBCS X7 X7 X1 *)
  0xa94d07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&208))) *)
  0x92800028;       (* arm_MOVN X8 (word 1) 0 *)
  0xfa000108;       (* arm_SBCS X8 X8 X0 *)
  0x9280000d;       (* arm_MOVN X13 (word 0) 0 *)
  0xfa0101a9;       (* arm_SBCS X9 X13 X1 *)
  0xa94e07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&224))) *)
  0xfa0001aa;       (* arm_SBCS X10 X13 X0 *)
  0xda0101ab;       (* arm_SBC X11 X13 X1 *)
  0xd37df0c0;       (* arm_LSL X0 X6 3 *)
  0x93c6f4e1;       (* arm_EXTR X1 X7 X6 61 *)
  0x93c7f502;       (* arm_EXTR X2 X8 X7 61 *)
  0x93c8f523;       (* arm_EXTR X3 X9 X8 61 *)
  0x93c9f544;       (* arm_EXTR X4 X10 X9 61 *)
  0x93caf565;       (* arm_EXTR X5 X11 X10 61 *)
  0xd37dfd66;       (* arm_LSR X6 X11 61 *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xa94f27e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&240))) *)
  0xa9502fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&256))) *)
  0xa95137ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&272))) *)
  0xd280006e;       (* arm_MOV X14 (rvalue (word 3)) *)
  0x9b087dcf;       (* arm_MUL X15 X14 X8 *)
  0x9bc87dc8;       (* arm_UMULH X8 X14 X8 *)
  0xab0f0000;       (* arm_ADDS X0 X0 X15 *)
  0x9b097dcf;       (* arm_MUL X15 X14 X9 *)
  0x9bc97dc9;       (* arm_UMULH X9 X14 X9 *)
  0xba0f0021;       (* arm_ADCS X1 X1 X15 *)
  0x9b0a7dcf;       (* arm_MUL X15 X14 X10 *)
  0x9bca7dca;       (* arm_UMULH X10 X14 X10 *)
  0xba0f0042;       (* arm_ADCS X2 X2 X15 *)
  0x9b0b7dcf;       (* arm_MUL X15 X14 X11 *)
  0x9bcb7dcb;       (* arm_UMULH X11 X14 X11 *)
  0xba0f0063;       (* arm_ADCS X3 X3 X15 *)
  0x9b0c7dcf;       (* arm_MUL X15 X14 X12 *)
  0x9bcc7dcc;       (* arm_UMULH X12 X14 X12 *)
  0xba0f0084;       (* arm_ADCS X4 X4 X15 *)
  0x9b0d7dcf;       (* arm_MUL X15 X14 X13 *)
  0x9bcd7dcd;       (* arm_UMULH X13 X14 X13 *)
  0xba0f00a5;       (* arm_ADCS X5 X5 X15 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab080021;       (* arm_ADDS X1 X1 X8 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0xba0c00a5;       (* arm_ADCS X5 X5 X12 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0xd3607cc7;       (* arm_LSL X7 X6 32 *)
  0xeb0700c8;       (* arm_SUBS X8 X6 X7 *)
  0xda1f00e7;       (* arm_SBC X7 X7 XZR *)
  0xab080000;       (* arm_ADDS X0 X0 X8 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xda9f23e6;       (* arm_CSETM X6 Condition_CC *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0xca0600e7;       (* arm_EOR X7 X7 X6 *)
  0xba070021;       (* arm_ADCS X1 X1 X7 *)
  0x92800027;       (* arm_MOVN X7 (word 1) 0 *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0x9a0600a5;       (* arm_ADC X5 X5 X6 *)
  0xa90306e0;       (* arm_STP X0 X1 X23 (Immediate_Offset (iword (&48))) *)
  0xa9040ee2;       (* arm_STP X2 X3 X23 (Immediate_Offset (iword (&64))) *)
  0xa90516e4;       (* arm_STP X4 X5 X23 (Immediate_Offset (iword (&80))) *)
  0x910543ff;       (* arm_ADD SP SP (rvalue (word 336)) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P384_MONTJDOUBLE_ALT_EXEC = ARM_MK_EXEC_RULE p384_montjdouble_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

let p384shortishredlemma = prove
 (`!n. n <= 24 * (p_384 - 1)
       ==> let q = n DIV 2 EXP 384 + 1 in
           q < 25 /\
           q < 2 EXP 64 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let FORALL_INT_CASES' = prove
 (`!P. (!x:int. P x) <=> (!n. P(&n)) /\ (!n. ~(n = 0) ==> P(-- &n))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FORALL_INT_CASES] THEN
  MESON_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ]);;

let p384shortintredlemma = prove
 (`!n. --(&p_384) <= n /\ n <= &5 * &p_384
       ==> let q = (&2 pow 384 + n) div &2 pow 384 in
           &0 <= q /\ q < &25 /\
           q < &2 pow 64 /\
           q * &p_384 <= n + &p_384 /\
           n < q * &p_384 + &p_384`,
  ONCE_REWRITE_TAC[INT_ARITH `&2 pow 384 + n:int = &1 * &2 pow 384 + n`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[FORALL_INT_CASES'; INT_DIV_LNEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_LE_NEG2; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `n < 2 EXP 384` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= p_384` THEN REWRITE_TAC[p_384] THEN ARITH_TAC;
    ASM_SIMP_TAC[DIV_LT; MOD_LT]] THEN
  UNDISCH_TAC `n <= p_384` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[p_384] THEN INT_ARITH_TAC);;

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &18446744069414584321 *
        &(val(word_add (word_shl x 32) x:int64))
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &18446744069414584321 *
            &(val(word_add (word_shl x 32) x:int64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`] THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> (a * (b * x)  == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let lvs =
 ["x_1",[`X24`; `0`];
  "y_1",[`X24`; `48`];
  "z_1",[`X24`; `96`];
  "x_3",[`X23`; `0`];
  "y_3",[`X23`; `48`];
  "z_3",[`X23`; `96`];
  "z2",[`SP`; `0`];
  "y2",[`SP`; `48`];
  "x2p",[`SP`; `96`];
  "xy2",[`SP`; `144`];
  "y4",[`SP`; `192`];
  "t2",[`SP`; `192`];
  "dx2",[`SP`; `240`];
  "t1",[`SP`; `240`];
  "d",[`SP`; `288`];
  "x4p",[`SP`; `288`]];;

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Instances of montsqr.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTSQR_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 215 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = a
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              a)
             (\s. read PC s = pcout /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 6)) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                       X11; X12; X13; X14; X15; X16; X17; X19; X20] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--215)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Main squaring block ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--93) (1--93) THEN

  (*** Main Montgomery reduction block ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   (allpairs (fun i j -> 16 * i + j) (0--5)
             [97;99;101;102;104;105;106;107;108;109] @
    (190--196))
   (94--196) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Key properties of pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s190; sum_s191; sum_s192; sum_s193; sum_s194; sum_s195;
          word(bitval carry_s195)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

 (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   [198;200;202;203;204;205;206] (197--215) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`384`; `if t < p_384 then &t:real else &t - &p_384`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN
   `val(word_add (word(bitval carry_s195))
                 (word(bitval carry_s205)):int64) = 0 <=>
    t < p_384`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s195:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 271 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = b
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              b)
             (\s. read PC s = pcout /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--271)] THEN
  ENSURES_INIT_TAC "s0" THEN

  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Main multiplication block ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--149) (1--149) THEN

  (*** Main Montgomery reduction block ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   (allpairs (fun i j -> 16 * i + j) (0--5)
             [153;155;157;158;160;161;162;163;164;165] @
    (246--252))
   (150--252) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Key properties of pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s246; sum_s247; sum_s248; sum_s249; sum_s250; sum_s251;
          word(bitval carry_s251)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a * b) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

 (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   [254;256;258;259;260;261;262] (253--271) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`384`; `if t < p_384 then &t:real else &t - &p_384`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN
   `val(word_add (word(bitval carry_s251))
                 (word(bitval carry_s261)):int64) = 0 <=>
    t < p_384`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s251:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 27 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < p_384 /\ n < p_384
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s) = (&m - &n) rem &p_384))
            (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--12) (1--12) THEN

  SUBGOAL_THEN `carry_s12 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `384` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ARM_STEPS_TAC P384_MONTJDOUBLE_ALT_EXEC [13] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (14--27) (14--27) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s27" THEN

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
  EXISTS_TAC `(&2:real) pow 384` THEN

  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_384`; `n < p_384`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    ASM_CASES_TAC `&m:real < &n` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; STRIP_TAC] THEN

  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of weakadd                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKADD_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 27 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read PC s = pcout /\
                  (m + n < 2 EXP 384 + p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s < 2 EXP 384 /\
                       (&(read(memory :> bytes(word_add (read p3 t) (word n3),
                               8 * 6)) s):int == &m + &n) (mod &p_384)))
            (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--12) (1--12) THEN
  SUBGOAL_THEN `carry_s12 <=> 2 EXP 384 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC P384_MONTJDOUBLE_ALT_EXEC [13] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (14--27) (14--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!x. (x < 2 EXP 384 /\ P x) /\ y = x ==> y < 2 EXP 384 /\ P y`) THEN
  EXISTS_TAC `if m + n < 2 EXP 384 then m + n else (m + n) - p_384` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `m + n < 2 EXP 384 + p_384` THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_CONG_REFL] THEN
    MATCH_MP_TAC(INTEGER_RULE `y - p:int = x ==> (x == y) (mod p)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC INT_OF_NUM_SUB THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 384`)]) THEN
  ABBREV_TAC `b <=> 2 EXP 384 <= m + n` THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCARD_STATE_TAC "s27" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; COND_SWAP] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `m + n < 2 EXP 384 + p_384` THEN
    EXPAND_TAC "b" THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `&(if b then (m + n) - p_384 else m + n):real =
    if b then (&m + &n) - &p_384 else &m + &n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    UNDISCH_TAC `b:bool` THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 38 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
         (\s. read PC s = pcout /\
              (m < p_384 /\ n < p_384
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 6)) s = (m + n) MOD p_384))
         (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
          MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--13) (1--13) THEN

  SUBGOAL_THEN
   `2 EXP 384 * bitval carry_s12 +
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8; sum_s11; sum_s12] =
    m + n`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (14--22) (14--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN

  SUBGOAL_THEN
   `carry_s22 <=>
    p_384 <=
    bignum_of_wordlist [sum_s3; sum_s4; sum_s7; sum_s8; sum_s11; sum_s12]`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_384;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  ARM_STEPS_TAC P384_MONTJDOUBLE_ALT_EXEC [23;24] THEN

  FIRST_X_ASSUM(MP_TAC o
    SPEC `word_neg(word(bitval(p_384 <= m + n))):int64` o
    MATCH_MP (MESON[] `read X3 s = z ==> !a. z = a ==> read X3 s = a`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; ADD_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[BITVAL_BOUND; MOD_LT; ADD_EQ_0; BITVAL_EQ_0;
             ARITH_RULE `a <= 1 /\ b <= 1 ==> a + b <  2 EXP 64`] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 5 RAND_CONV) [SYM th]) THEN
    BOOL_CASES_TAC `carry_s12:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; COND_SWAP; MULT_CLAUSES;
                ADD_CLAUSES; WORD_MASK] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (25--38) (25--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s38" THEN

  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_384`; `n < p_384`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[p_384] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ]
   `a:num = m + n ==> &m + &n = &a`)) THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[WORD_AND_MASK] THEN REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REWRITE_TAC[WORD_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; p_384] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 86 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_384
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s) = (&12 * &m - &9 * &n) rem &p_384))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--86)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_384 =
    (&12 * &m + &9 * (&p_384 - &n)) rem &p_384`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--13) (1--13) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
           [sum_s3; sum_s5; sum_s8; sum_s10; sum_s12; sum_s13]` THEN
  SUBGOAL_THEN `p_384 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `12 * m + 9 * n'` p384shortishredlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_384] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `x DIV 2 EXP 384 + 1 = (2 EXP 384 + x) DIV 2 EXP 384`]) THEN

  (*** Main sum of products computation +1 ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (14--62) (14--62) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s40; sum_s57; sum_s58; sum_s59; sum_s60; sum_s61; sum_s62]` THEN
  SUBGOAL_THEN `2 EXP 384 + 12 * m + 9 * n'= ca` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
       SUBST_ALL_TAC th THEN ASSUME_TAC th THEN DISCH_TAC) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s62` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s46:int64` o concl))) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 384 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
    [64;65;66;67;68;69;70;71; 75;77;80;81;82;83]
    (63--86) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `384`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Explicitly observe that the small quotient mul works ***)

  SUBGOAL_THEN `&(val (word_shl q 32)):real = &2 pow 32 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_SHL; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `12 * m + 9 * n' < val(q:int64) * p_384 <=> ~carry_s71`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 384 + a < b + 2 EXP 384`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
     `&(12 * m + 9 * n'):real =
      (&2 pow 384 + &(12 * m + 9 * n')) - &2 pow 384`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s71:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub41_p384 (actually there is only one).                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 44 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
         (\s. read PC s = pcout /\
              (n <= p_384
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                          8 * 6)) s) = (&4 * &m - &n) rem &p_384))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9] ,,
          MAYCHANGE
            [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n <= p_384 assumption ***)

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--44)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Instantiate the (integer) quotient approximation lemma ***)

  MP_TAC(SPEC `&4 * &m - &n:int` p384shortintredlemma) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      INT_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[p_384] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Main shift-subtract block ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC [6;8;11;13;16;18;20] (1--20) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s6; sum_s8; sum_s11; sum_s13; sum_s16; sum_s18; sum_s20]` THEN
  SUBGOAL_THEN `&2 pow 384 + &4 * &m - &n:int = &ca`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_pow_th;
                int_mul_th; int_of_num_th] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&4 * &m:real =
      &(bignum_of_wordlist
         [word_shl m_0 2;
          word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
          word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
          word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
          word_subword ((word_join:int64->int64->int128) m_4 m_3) (62,64);
          word_subword ((word_join:int64->int64->int128) m_5 m_4) (62,64);
          word_ushr m_5 62])`
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s20` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s20:int64` o concl))) THEN
  SUBGOAL_THEN `&ca div &2 pow 384 = &(val(q:int64))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV] THEN
    EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
    [22;23;24;25;26;27;28;29; 33;35;38;39;40;41]
    (21--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED_MOD THEN
  MAP_EVERY EXISTS_TAC [`&(val(q:int64)):int`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; p_384] THEN BOUNDER_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `&4 * m - n:int = (&2 pow 384 + &4 * m - n) - &2 pow 384`] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Explicitly observe that the small quotient mul works ***)

  SUBGOAL_THEN `&(val (word_shl q 32)):real = &2 pow 32 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_SHL; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN
    `(&ca - &2 pow 384):int < &(val(q:int64)) * &p_384 <=> ~carry_s29`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_LT_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_RULE
     `(a:int == b + c - p) (mod p) <=> (a == b + c) (mod p)`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "ca" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s29:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instance of cmsub38 (there is only one).                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_alt_mc 74 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2324) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X23 s = read X23 t /\
              read X24 s = read X24 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) s =
              n)
             (\s. read PC s = pcout /\
                  (n <= p_384
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 6)) s) = (&3 * &m - &8 * &n) rem &p_384))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_ALT_EXEC (1--74)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 * &n) rem &p_384 =
    (&3 * &m + &8 * (&p_384 - &n)) rem &p_384`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** Initial negation of n ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC (1--13) (1--13) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
           [sum_s3; sum_s5; sum_s8; sum_s10; sum_s12; sum_s13]` THEN
  SUBGOAL_THEN `p_384 - n = n'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
     [UNDISCH_TAC `n <= p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `3 * m + 8 * n'` p384shortishredlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN REWRITE_TAC[p_384] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `x DIV 2 EXP 384 + 1 = (2 EXP 384 + x) DIV 2 EXP 384`]) THEN

  (*** Main sum of products computation +1 ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   [21; 26; 28; 29; 31; 32; 34; 35; 37; 38;
    40; 41; 43; 44; 45; 46; 47; 48; 49; 50]
   (14--50) THEN
  ABBREV_TAC `ca = bignum_of_wordlist
   [sum_s28; sum_s45; sum_s46; sum_s47; sum_s48; sum_s49; sum_s50]` THEN
  SUBGOAL_THEN `2 EXP 384 + 3 * m + 8 * n'= ca` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "n'"; "ca"] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&8 * &n':real =
      &(bignum_of_wordlist
      [word_shl sum_s3 3;
       word_subword ((word_join:int64->int64->int128) sum_s5 sum_s3) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s8 sum_s5) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s10 sum_s8) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s12 sum_s10) (61,64);
       word_subword ((word_join:int64->int64->int128) sum_s13 sum_s12) (61,64);
       word_ushr sum_s13 61])`
    SUBST1_TAC THENL
     [EXPAND_TAC "n'" THEN
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
      MAP_EVERY EXPAND_TAC ["m"; "ca"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN REAL_INTEGER_TAC];
      DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
        SUBST_ALL_TAC th THEN ASSUME_TAC th THEN DISCH_TAC) THEN
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s50` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s50:int64` o concl))) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 384 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_ALT_EXEC
   [52; 53; 54; 55; 56; 57; 58; 59;  63; 65; 68; 69; 70; 71]
   (51--74) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `384`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Explicitly observe that the small quotient mul works ***)

  SUBGOAL_THEN `&(val (word_shl q 32)):real = &2 pow 32 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_SHL; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `3 * m + 8 * n' < val(q:int64) * p_384 <=> ~carry_s59`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 384 + a < b + 2 EXP 384`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
     `&(3 * m + 8 * n'):real =
      (&2 pow 384 + &(3 * m + 8 * n')) - &2 pow 384`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s59:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_384 ==> x < p_384 /\ &x = &a rem &p_384`,
  REWRITE_TAC[INT_OF_NUM_REM; p_384] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_384 ==> x < p_384 /\ &x = a rem &p_384`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_384] THEN INT_ARITH_TAC);;

let lemont = prove
 (`(&i * x * y) rem &p_384 = (&i * x rem &p_384 * y rem &p_384) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let demont = prove
 (`(&(NUMERAL n) * &x) rem &p_384 = (&(NUMERAL n) * &x rem &p_384) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let pumont = prove
 (`(&(inverse_mod p_384 (2 EXP 384)) *
    (&2 pow 384 * x) rem &p_384 * (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * x * y) rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * t:int == &1) (mod p)
    ==> (i * (t * x) * (t * y) == t * x * y) (mod p)`) THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2; p_384] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let dismont = prove
 (`((&2 pow 384 * x) rem &p_384 + (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * (x + y)) rem &p_384 /\
   ((&2 pow 384 * x) rem &p_384 - (&2 pow 384 * y) rem &p_384) rem &p_384 =
   (&2 pow 384 * (x - y)) rem &p_384 /\
  (&(NUMERAL n) * (&2 pow 384 * x) rem &p_384) rem &p_384 =
   (&2 pow 384 * (&(NUMERAL n) * x)) rem &p_384`,
  REPEAT CONJ_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let unmont = prove
 (`(&(inverse_mod p_384 (2 EXP 384)) * (&2 pow 384 * x) rem &p_384) rem &p_384 =
   x rem &p_384`,
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * e:int == &1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let unreplemma = prove
 (`!x. x < p_384
         ==> x =
             (2 EXP 384 * (inverse_mod p_384 (2 EXP 384) * x) MOD p_384) MOD
             p_384`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(i * e == 1) (mod p) ==> (i * e * x == x) (mod p)`) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV);;

let weierstrass_of_jacobian_p384_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp384
         (x1 rem &p_384,y1 rem &p_384,z1 rem &p_384) =
        (x3 rem &p_384,y3 rem &p_384,z3 rem &p_384)
       ==> weierstrass_of_jacobian (integer_mod_ring p_384)
                (x1 rem &p_384,y1 rem &p_384,z1 rem &p_384) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_384)
                  (x3 rem &p_384,y3 rem &p_384,z3 rem &p_384) =
                group_mul p384_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp384; P384_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P384] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_384; b_384] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p384 = new_definition
 `represents_p384 P (x,y,z) <=>
        x < p_384 /\ y < p_384 /\ z < p_384 /\
        weierstrass_of_jacobian (integer_mod_ring p_384)
         (tripled (montgomery_decode (384,p_384)) (x,y,z)) = P`;;

let P384_MONTJDOUBLE_ALT_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,336))
            [(word pc,0x2324); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc,0x2324)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
                  read PC s = word(pc + 0x10) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read PC s = word (pc + 0x2310) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(stackpointer,336)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x1:num`; `y1:num`; `z1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_MONTSQR_P384_TAC 2 ["z2";"z_1"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["y2";"y_1"] THEN
  LOCAL_WEAKADD_P384_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_SUB_P384_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P384_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["t2";"t1"] THEN
  LOCAL_CMSUBC9_P384_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P384_TAC 0 ["t1";"t2";"z2"] THEN
  LOCAL_MONTSQR_P384_TAC 0 ["y4";"y2"] THEN
  LOCAL_SUB_P384_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_MONTMUL_P384_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_CMSUB41_P384_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P384_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s18" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p384; tripled] THEN
  REWRITE_TAC[montgomery_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_384] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_384]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o C SPEC unreplemma) [`z1:num`; `y1:num`; `x1:num`] THEN
  MAP_EVERY (fun t -> ABBREV_TAC t THEN POP_ASSUM(K ALL_TAC))
   [`x1d = inverse_mod p_384 (2 EXP 384) * x1`;
    `y1d = inverse_mod p_384 (2 EXP 384) * y1`;
    `z1d = inverse_mod p_384 (2 EXP 384) * z1`] THEN
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
  MATCH_MP_TAC weierstrass_of_jacobian_p384_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp384;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let P384_MONTJDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 384),384))
            [(word pc,0x2324); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc,0x2324)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read PC s = returnaddress /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,144);
                      memory :> bytes(word_sub stackpointer (word 384),384)])`,
  ARM_ADD_RETURN_STACK_TAC P384_MONTJDOUBLE_ALT_EXEC
   P384_MONTJDOUBLE_ALT_CORRECT
    `[X19; X20; X21; X22; X23; X24]` 384);;
