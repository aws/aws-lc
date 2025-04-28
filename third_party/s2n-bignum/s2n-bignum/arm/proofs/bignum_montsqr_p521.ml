(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_521.                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(**** print_literal_from_elf "arm/p521/unopt/bignum_montsqr_p521_base.o";;
 ****)

let bignum_montsqr_p521_unopt_mc = define_assert_from_elf "bignum_montsqr_p521_unopt_mc"
    "arm/p521/unopt/bignum_montsqr_p521_base.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9b097cf1;       (* arm_MUL X17 X7 X9 *)
  0x9bc87cd6;       (* arm_UMULH X22 X6 X8 *)
  0xeb0700d7;       (* arm_SUBS X23 X6 X7 *)
  0xda9726f7;       (* arm_CNEG X23 X23 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb08012a;       (* arm_SUBS X10 X9 X8 *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0x9b0a7ef0;       (* arm_MUL X16 X23 X10 *)
  0x9bca7eea;       (* arm_UMULH X10 X23 X10 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b0210;       (* arm_EOR X16 X16 X11 *)
  0xca0b014a;       (* arm_EOR X10 X10 X11 *)
  0xab16018d;       (* arm_ADDS X13 X12 X22 *)
  0x9a1f02d6;       (* arm_ADC X22 X22 XZR *)
  0x9bc97cf7;       (* arm_UMULH X23 X7 X9 *)
  0xab1101ad;       (* arm_ADDS X13 X13 X17 *)
  0xba1702d6;       (* arm_ADCS X22 X22 X23 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9a0b02f7;       (* arm_ADC X23 X23 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0x9b077cf0;       (* arm_MUL X16 X7 X7 *)
  0x9b077cd5;       (* arm_MUL X21 X6 X7 *)
  0x9bc67ccb;       (* arm_UMULH X11 X6 X6 *)
  0x9bc77cf1;       (* arm_UMULH X17 X7 X7 *)
  0x9bc77cd4;       (* arm_UMULH X20 X6 X7 *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1f02d6;       (* arm_ADCS X22 X22 XZR *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b087d0e;       (* arm_MUL X14 X8 X8 *)
  0x9b097d30;       (* arm_MUL X16 X9 X9 *)
  0x9b097d15;       (* arm_MUL X21 X8 X9 *)
  0x9bc87d0f;       (* arm_UMULH X15 X8 X8 *)
  0x9bc97d31;       (* arm_UMULH X17 X9 X9 *)
  0x9bc97d14;       (* arm_UMULH X20 X8 X9 *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1601ce;       (* arm_ADDS X14 X14 X22 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xf9402033;       (* arm_LDR X19 X1 (Immediate_Offset (word 64)) *)
  0x8b130277;       (* arm_ADD X23 X19 X19 *)
  0x9b137e73;       (* arm_MUL X19 X19 X19 *)
  0x9240cc55;       (* arm_AND X21 X2 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0x93c2d074;       (* arm_EXTR X20 X3 X2 (rvalue (word 52)) *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 (rvalue (word 52)) *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 (rvalue (word 12)) *)
  0x93d53296;       (* arm_EXTR X22 X20 X21 (rvalue (word 12)) *)
  0xab16014a;       (* arm_ADDS X10 X10 X22 *)
  0x93c3a095;       (* arm_EXTR X21 X4 X3 (rvalue (word 40)) *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 (rvalue (word 52)) *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd374ce94;       (* arm_LSL X20 X20 (rvalue (word 12)) *)
  0x93d462b6;       (* arm_EXTR X22 X21 X20 (rvalue (word 24)) *)
  0xba16016b;       (* arm_ADCS X11 X11 X22 *)
  0x93c470b4;       (* arm_EXTR X20 X5 X4 (rvalue (word 28)) *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 (rvalue (word 52)) *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 (rvalue (word 12)) *)
  0x93d59296;       (* arm_EXTR X22 X20 X21 (rvalue (word 36)) *)
  0xba16018c;       (* arm_ADCS X12 X12 X22 *)
  0x93c540d5;       (* arm_EXTR X21 X6 X5 (rvalue (word 16)) *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 (rvalue (word 52)) *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd374ce94;       (* arm_LSL X20 X20 (rvalue (word 12)) *)
  0x93d4c2b6;       (* arm_EXTR X22 X21 X20 (rvalue (word 48)) *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xd344fcd4;       (* arm_LSR X20 X6 (rvalue (word 4)) *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 (rvalue (word 52)) *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 (rvalue (word 12)) *)
  0x93d5f298;       (* arm_EXTR X24 X20 X21 (rvalue (word 60)) *)
  0x93c6e0f5;       (* arm_EXTR X21 X7 X6 (rvalue (word 56)) *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 (rvalue (word 52)) *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd378df18;       (* arm_LSL X24 X24 (rvalue (word 8)) *)
  0x93d822b6;       (* arm_EXTR X22 X21 X24 (rvalue (word 8)) *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0x93c7b114;       (* arm_EXTR X20 X8 X7 (rvalue (word 44)) *)
  0x9240ce94;       (* arm_AND X20 X20 (rvalue (word 4503599627370495)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 (rvalue (word 52)) *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 (rvalue (word 12)) *)
  0x93d55296;       (* arm_EXTR X22 X20 X21 (rvalue (word 20)) *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0x93c88135;       (* arm_EXTR X21 X9 X8 (rvalue (word 32)) *)
  0x9240ceb5;       (* arm_AND X21 X21 (rvalue (word 4503599627370495)) *)
  0x9b157ef5;       (* arm_MUL X21 X23 X21 *)
  0xd374fe96;       (* arm_LSR X22 X20 (rvalue (word 52)) *)
  0x8b1602b5;       (* arm_ADD X21 X21 X22 *)
  0xd374ce94;       (* arm_LSL X20 X20 (rvalue (word 12)) *)
  0x93d482b6;       (* arm_EXTR X22 X21 X20 (rvalue (word 32)) *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xd354fd34;       (* arm_LSR X20 X9 (rvalue (word 20)) *)
  0x9b147ef4;       (* arm_MUL X20 X23 X20 *)
  0xd374feb6;       (* arm_LSR X22 X21 (rvalue (word 52)) *)
  0x8b160294;       (* arm_ADD X20 X20 X22 *)
  0xd374ceb5;       (* arm_LSL X21 X21 (rvalue (word 12)) *)
  0x93d5b296;       (* arm_EXTR X22 X20 X21 (rvalue (word 44)) *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xd36cfe94;       (* arm_LSR X20 X20 (rvalue (word 44)) *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0x93ca2575;       (* arm_EXTR X21 X11 X10 (rvalue (word 9)) *)
  0x93cb2594;       (* arm_EXTR X20 X12 X11 (rvalue (word 9)) *)
  0xa9005015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0x93cc25b5;       (* arm_EXTR X21 X13 X12 (rvalue (word 9)) *)
  0x93cd25d4;       (* arm_EXTR X20 X14 X13 (rvalue (word 9)) *)
  0xa9015015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0x93ce25f5;       (* arm_EXTR X21 X15 X14 (rvalue (word 9)) *)
  0x93cf2614;       (* arm_EXTR X20 X16 X15 (rvalue (word 9)) *)
  0xa9025015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0x93d02635;       (* arm_EXTR X21 X17 X16 (rvalue (word 9)) *)
  0x93d12674;       (* arm_EXTR X20 X19 X17 (rvalue (word 9)) *)
  0xa9035015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0x92402156;       (* arm_AND X22 X10 (rvalue (word 511)) *)
  0xd349fe73;       (* arm_LSR X19 X19 (rvalue (word 9)) *)
  0x8b1302d6;       (* arm_ADD X22 X22 X19 *)
  0xf9002016;       (* arm_STR X22 X0 (Immediate_Offset (word 64)) *)
  0x9b047c4c;       (* arm_MUL X12 X2 X4 *)
  0x9b057c71;       (* arm_MUL X17 X3 X5 *)
  0x9bc47c56;       (* arm_UMULH X22 X2 X4 *)
  0xeb030057;       (* arm_SUBS X23 X2 X3 *)
  0xda9726f7;       (* arm_CNEG X23 X23 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb0400aa;       (* arm_SUBS X10 X5 X4 *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0x9b0a7ef0;       (* arm_MUL X16 X23 X10 *)
  0x9bca7eea;       (* arm_UMULH X10 X23 X10 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b0210;       (* arm_EOR X16 X16 X11 *)
  0xca0b014a;       (* arm_EOR X10 X10 X11 *)
  0xab16018d;       (* arm_ADDS X13 X12 X22 *)
  0x9a1f02d6;       (* arm_ADC X22 X22 XZR *)
  0x9bc57c77;       (* arm_UMULH X23 X3 X5 *)
  0xab1101ad;       (* arm_ADDS X13 X13 X17 *)
  0xba1702d6;       (* arm_ADCS X22 X22 X23 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9a0b02f7;       (* arm_ADC X23 X23 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0x9b027c4a;       (* arm_MUL X10 X2 X2 *)
  0x9b037c70;       (* arm_MUL X16 X3 X3 *)
  0x9b037c55;       (* arm_MUL X21 X2 X3 *)
  0x9bc27c4b;       (* arm_UMULH X11 X2 X2 *)
  0x9bc37c71;       (* arm_UMULH X17 X3 X3 *)
  0x9bc37c54;       (* arm_UMULH X20 X2 X3 *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab15016b;       (* arm_ADDS X11 X11 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xba1f02d6;       (* arm_ADCS X22 X22 XZR *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c8e;       (* arm_MUL X14 X4 X4 *)
  0x9b057cb0;       (* arm_MUL X16 X5 X5 *)
  0x9b057c95;       (* arm_MUL X21 X4 X5 *)
  0x9bc47c8f;       (* arm_UMULH X15 X4 X4 *)
  0x9bc57cb1;       (* arm_UMULH X17 X5 X5 *)
  0x9bc57c94;       (* arm_UMULH X20 X4 X5 *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab1601ce;       (* arm_ADDS X14 X14 X22 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xa9405015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0xab0a02b5;       (* arm_ADDS X21 X21 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0xa9005015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0xa9415015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xa9015015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0xa9425015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xba0f0294;       (* arm_ADCS X20 X20 X15 *)
  0xa9025015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0xa9435015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0xba1002b5;       (* arm_ADCS X21 X21 X16 *)
  0xba110294;       (* arm_ADCS X20 X20 X17 *)
  0xa9035015;       (* arm_STP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0xf9402016;       (* arm_LDR X22 X0 (Immediate_Offset (word 64)) *)
  0x9a1f02d6;       (* arm_ADC X22 X22 XZR *)
  0xf9002016;       (* arm_STR X22 X0 (Immediate_Offset (word 64)) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9b087c8f;       (* arm_MUL X15 X4 X8 *)
  0x9b097cb0;       (* arm_MUL X16 X5 X9 *)
  0x9bc67c51;       (* arm_UMULH X17 X2 X6 *)
  0xab1101ce;       (* arm_ADDS X14 X14 X17 *)
  0x9bc77c71;       (* arm_UMULH X17 X3 X7 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0x9bc87c91;       (* arm_UMULH X17 X4 X8 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc97cb1;       (* arm_UMULH X17 X5 X9 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab0a01cb;       (* arm_ADDS X11 X14 X10 *)
  0xba0e01ee;       (* arm_ADCS X14 X15 X14 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xab0a01cc;       (* arm_ADDS X12 X14 X10 *)
  0xba0b01ed;       (* arm_ADCS X13 X15 X11 *)
  0xba0e020e;       (* arm_ADCS X14 X16 X14 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba1003f0;       (* arm_ADCS X16 XZR X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xeb050096;       (* arm_SUBS X22 X4 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb080134;       (* arm_SUBS X20 X9 X8 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb030056;       (* arm_SUBS X22 X2 X3 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb0600f4;       (* arm_SUBS X20 X7 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba14018c;       (* arm_ADCS X12 X12 X20 *)
  0xba1301ad;       (* arm_ADCS X13 X13 X19 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050076;       (* arm_SUBS X22 X3 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070134;       (* arm_SUBS X20 X9 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040056;       (* arm_SUBS X22 X2 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060114;       (* arm_SUBS X20 X8 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15018c;       (* arm_ADCS X12 X12 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050056;       (* arm_SUBS X22 X2 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060134;       (* arm_SUBS X20 X9 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040076;       (* arm_SUBS X22 X3 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070114;       (* arm_SUBS X20 X8 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xa9405015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&0))) *)
  0x93ce21e2;       (* arm_EXTR X2 X15 X14 (rvalue (word 8)) *)
  0xab150042;       (* arm_ADDS X2 X2 X21 *)
  0x93cf2203;       (* arm_EXTR X3 X16 X15 (rvalue (word 8)) *)
  0xba140063;       (* arm_ADCS X3 X3 X20 *)
  0xa9415015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&16))) *)
  0x93d02224;       (* arm_EXTR X4 X17 X16 (rvalue (word 8)) *)
  0xba150084;       (* arm_ADCS X4 X4 X21 *)
  0x8a040076;       (* arm_AND X22 X3 X4 *)
  0xd348fe25;       (* arm_LSR X5 X17 (rvalue (word 8)) *)
  0xba1400a5;       (* arm_ADCS X5 X5 X20 *)
  0x8a0502d6;       (* arm_AND X22 X22 X5 *)
  0xa9425015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&32))) *)
  0xd37ff946;       (* arm_LSL X6 X10 (rvalue (word 1)) *)
  0xba1500c6;       (* arm_ADCS X6 X6 X21 *)
  0x8a0602d6;       (* arm_AND X22 X22 X6 *)
  0x93cafd67;       (* arm_EXTR X7 X11 X10 (rvalue (word 63)) *)
  0xba1400e7;       (* arm_ADCS X7 X7 X20 *)
  0x8a0702d6;       (* arm_AND X22 X22 X7 *)
  0xa9435015;       (* arm_LDP X21 X20 X0 (Immediate_Offset (iword (&48))) *)
  0x93cbfd88;       (* arm_EXTR X8 X12 X11 (rvalue (word 63)) *)
  0xba150108;       (* arm_ADCS X8 X8 X21 *)
  0x8a0802d6;       (* arm_AND X22 X22 X8 *)
  0x93ccfda9;       (* arm_EXTR X9 X13 X12 (rvalue (word 63)) *)
  0xba140129;       (* arm_ADCS X9 X9 X20 *)
  0x8a0902d6;       (* arm_AND X22 X22 X9 *)
  0xf9402015;       (* arm_LDR X21 X0 (Immediate_Offset (word 64)) *)
  0x93cdfdca;       (* arm_EXTR X10 X14 X13 (rvalue (word 63)) *)
  0x9240214a;       (* arm_AND X10 X10 (rvalue (word 511)) *)
  0x9a0a02aa;       (* arm_ADC X10 X21 X10 *)
  0xd349fd54;       (* arm_LSR X20 X10 (rvalue (word 9)) *)
  0xb277d94a;       (* arm_ORR X10 X10 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba14005f;       (* arm_ADCS XZR X2 X20 *)
  0xba1f02df;       (* arm_ADCS XZR X22 XZR *)
  0xba1f015f;       (* arm_ADCS XZR X10 XZR *)
  0xba140042;       (* arm_ADCS X2 X2 X20 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9240214a;       (* arm_AND X10 X10 (rvalue (word 511)) *)
  0xd377d853;       (* arm_LSL X19 X2 (rvalue (word 9)) *)
  0x93c2dc62;       (* arm_EXTR X2 X3 X2 (rvalue (word 55)) *)
  0x93c3dc83;       (* arm_EXTR X3 X4 X3 (rvalue (word 55)) *)
  0x93c4dca4;       (* arm_EXTR X4 X5 X4 (rvalue (word 55)) *)
  0x93c5dcc5;       (* arm_EXTR X5 X6 X5 (rvalue (word 55)) *)
  0xaa13014a;       (* arm_ORR X10 X10 X19 *)
  0x93c6dce6;       (* arm_EXTR X6 X7 X6 (rvalue (word 55)) *)
  0x93c7dd07;       (* arm_EXTR X7 X8 X7 (rvalue (word 55)) *)
  0x93c8dd28;       (* arm_EXTR X8 X9 X8 (rvalue (word 55)) *)
  0x93c9dd49;       (* arm_EXTR X9 X10 X9 (rvalue (word 55)) *)
  0xd377fd4a;       (* arm_LSR X10 X10 (rvalue (word 55)) *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200a;       (* arm_STR X10 X0 (Immediate_Offset (word 64)) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_P521_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_p521_unopt_mc;;

(* bignum_montsqr_p521_unopt_mc without callee-save register spills + ret. *)
let bignum_montsqr_p521_unopt_core_mc_def,
    bignum_montsqr_p521_unopt_core_mc,
    BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p521_unopt_core_mc"
    bignum_montsqr_p521_unopt_mc
    (`12`,`LENGTH bignum_montsqr_p521_unopt_mc - 28`)
    (fst BIGNUM_MONTSQR_P521_UNOPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_521_AS_WORDLIST = prove
 (`p_521 =
   bignum_of_wordlist
    [word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word(0x1FF)]`,
  REWRITE_TAC[p_521; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_EQ_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] = p_521 <=>
   (!i. i < 64
        ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
            bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
   (!i. i < 9 ==> bit i n8) /\ (!i. i < 64 ==> 9 <= i ==> ~bit i n8)`,
  REWRITE_TAC[P_521_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let BIGNUM_FROM_MEMORY_LE_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] <= p_521 <=>
   !i. i < 64 ==> 9 <= i ==> ~bit i n8`,
  SIMP_TAC[P_521; ARITH_RULE `p_521 = 2 EXP 521 - 1 ==>
    (n <= p_521 <=> n DIV 2 EXP (8 * 64) < 2 EXP 9)`] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `8`; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV; EXP; DIV_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; GSYM UPPER_BITS_ZERO] THEN
  MP_TAC(ISPEC `n8:int64` BIT_TRIVIAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MESON_TAC[NOT_LE]);;

let BIGNUM_FROM_MEMORY_LT_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] < p_521 <=>
   (!i. i < 64 ==> 9 <= i ==> ~bit i n8) /\
   ~((!i. i < 64
          ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
              bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
     (!i. i < 9 ==> bit i n8))`,
  GEN_REWRITE_TAC LAND_CONV [LT_LE] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_P521; BIGNUM_FROM_MEMORY_LE_P521] THEN
  MESON_TAC[]);;

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

let BIGNUM_MONTSQR_P521_UNOPT_CORE_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p521_unopt_core_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_unopt_core_mc /\
                  read PC s = word(pc) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p521_unopt_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                      X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC (1--423)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** The 4x4 squaring of the top "half" ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
   [5; 6; 13; 18; 19; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31;
    32; 33; 34; 35; 36; 37; 41; 42; 43; 44; 45; 46; 47; 48; 49;
    50; 51; 52; 53; 54; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67]
   (1--67) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_4; n_5; n_6; n_7] EXP 2 =
    bignum_of_wordlist
      [mullo_s35; sum_s44; sum_s47; sum_s48; sum_s64; sum_s65; sum_s66;
       sum_s67]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN FIRST_ASSUM
     (MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The complicated augmentation with the little word contribution ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
   [70; 80; 88; 96; 104; 119; 127; 135; 142; 144]
   (68--144) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_4; n_5; n_6; n_7; n_8] EXP 2 +
    2 * val n_8 * bignum_of_wordlist[n_0; n_1; n_2; n_3] =
    bignum_of_wordlist[sum_s80; sum_s88; sum_s96; sum_s104;
                       sum_s119; sum_s127; sum_s135; sum_s142; sum_s144]`
  ASSUME_TAC THENL
   [REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; ARITH_RULE
     `(l + 2 EXP 256 * h) EXP 2 =
      2 EXP 512 * h EXP 2 + 2 EXP 256 * (2 * h) * l + l EXP 2`] THEN
    REWRITE_TAC[ARITH_RULE
     `(x + 2 EXP 256 * (2 * c) * h + y) + 2 * c * l =
      x + y + 2 * c * (l + 2 EXP 256 * h)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      MATCH_MP_TAC(ARITH_RULE
       `c2 < 2 EXP 9 EXP 2 /\ x < 2 EXP 512 /\ c * y <= 2 EXP 9 * 2 EXP 512
        ==> 2 EXP 512 * c2 + x + 2 * c * y < 2 EXP 576`) THEN
      ASM_REWRITE_TAC[EXP_MONO_LT; ARITH_EQ] THEN CONJ_TAC THENL
       [ALL_TAC; MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE]] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `(x + 2 EXP 256 * (2 * c) * h + y) + 2 * c * l =
      x + y + 2 * c * (l + 2 EXP 256 * h)`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(4,4))] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 52 - 1`)) THEN
    REWRITE_TAC[WORD_RULE
     `word(val(word_add (x:int64) x) * val(y:int64)):int64 =
      word(2 * val x * val y)`] THEN
    MAP_EVERY ABBREV_TAC
     [`d0:int64 = word_and n_0 (word (2 EXP 52 - 1))`;
      `d1:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_1 n_0) (52,64))
                           (word (2 EXP 52 - 1))`;
      `d2:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_2 n_1) (40,64))
                           (word (2 EXP 52 - 1))`;
      `d3:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_3 n_2) (28,64))
                           (word (2 EXP 52 - 1))`;
      `d4:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_4 n_3) (16,64))
                           (word (2 EXP 52 - 1))`;
      `d5:int64 = word_and (word_ushr n_4 4) (word (2 EXP 52 - 1))`;
      `d6:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_5 n_4) (56,64))
                           (word (2 EXP 52 - 1))`;
      `d7:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_6 n_5) (44,64))
                           (word (2 EXP 52 - 1))`;
      `d8:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) n_7 n_6) (32,64))
                           (word (2 EXP 52 - 1))`;
      `d9:int64 = word_ushr n_7 20`;
      `e0:int64 = word(2 * val(n_8:int64) * val(d0:int64))`;
      `e1:int64 =
       word_add(word(2 * val(n_8:int64) * val(d1:int64))) (word_ushr e0 52)`;
      `e2:int64 =
       word_add(word(2 * val(n_8:int64) * val(d2:int64))) (word_ushr e1 52)`;
      `e3:int64 =
       word_add(word(2 * val(n_8:int64) * val(d3:int64))) (word_ushr e2 52)`;
      `e4:int64 =
       word_add(word(2 * val(n_8:int64) * val(d4:int64))) (word_ushr e3 52)`;
      `e5:int64 =
       word_add(word(2 * val(n_8:int64) * val(d5:int64))) (word_ushr e4 52)`;
      `e6:int64 =
       word_add(word(2 * val(n_8:int64) * val(d6:int64))) (word_ushr e5 52)`;
      `e7:int64 =
       word_add(word(2 * val(n_8:int64) * val(d7:int64))) (word_ushr e6 52)`;
      `e8:int64 =
       word_add(word(2 * val(n_8:int64) * val(d8:int64))) (word_ushr e7 52)`;
      `e9:int64 =
       word_add(word(2 * val(n_8:int64) * val(d9:int64))) (word_ushr e8 52)`;
      `f0:int64 = word_subword
       ((word_join:int64->int64->int128) e1 (word_shl e0 12)) (12,64)`;
      `f1:int64 = word_subword
       ((word_join:int64->int64->int128) e2 (word_shl e1 12)) (24,64)`;
      `f2:int64 = word_subword
       ((word_join:int64->int64->int128) e3 (word_shl e2 12)) (36,64)`;
      `f3:int64 = word_subword
       ((word_join:int64->int64->int128) e4 (word_shl e3 12)) (48,64)`;
      `f4:int64 = word_subword
        ((word_join:int64->int64->int128) e6
        (word_shl (word_subword ((word_join:int64->int64->int128) e5
              (word_shl e4 12)) (60,64)) 8)) (8,64)`;
      `f5:int64 = word_subword
       ((word_join:int64->int64->int128) e7 (word_shl e6 12)) (20,64)`;
      `f6:int64 = word_subword
        ((word_join:int64->int64->int128) e8 (word_shl e7 12)) (32,64)`;
      `f7:int64 = word_subword
        ((word_join:int64->int64->int128) e9 (word_shl e8 12)) (44,64)`;
      `f8:int64 = word_ushr e9 44`] THEN
    SUBGOAL_THEN
     `2 * val(n_8:int64) *
      bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7] =
      bignum_of_wordlist[f0;f1;f2;f3;f4;f5;f6;f7;f8]`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7] =
        ITLIST (\(h:int64) t. val h + 2 EXP 52 * t)
               [d0;d1;d2;d3;d4;d5;d6;d7;d8;d9] 0 /\
        bignum_of_wordlist[f0; f1; f2; f3; f4; f5; f6; f7; f8] =
        2 EXP 520 * val(e9:int64) DIV 2 EXP 52 +
        ITLIST (\(h:int64) t. val h MOD 2 EXP 52 + 2 EXP 52 * t)
               [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9] 0`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[ITLIST; ADD_CLAUSES; MULT_CLAUSES; bignum_of_wordlist] THEN
        REWRITE_TAC[GSYM VAL_WORD_USHR; GSYM VAL_WORD_AND_MASK_WORD] THEN
        CONJ_TAC THENL
         [MAP_EVERY EXPAND_TAC
           ["d0"; "d1"; "d2"; "d3"; "d4"; "d5"; "d6"; "d7"; "d8"; "d9"];
          MAP_EVERY EXPAND_TAC
           ["f0"; "f1"; "f2"; "f3"; "f4"; "f5"; "f6"; "f7"; "f8"]] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
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
        CONV_TAC NUM_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `2 * val(n_8:int64) * val(d0:int64) = val (e0:int64) /\
        2 * val n_8 * val(d1:int64) + val e0 DIV 2 EXP 52 = val(e1:int64) /\
        2 * val n_8 * val(d2:int64) + val e1 DIV 2 EXP 52 = val(e2:int64) /\
        2 * val n_8 * val(d3:int64) + val e2 DIV 2 EXP 52 = val(e3:int64) /\
        2 * val n_8 * val(d4:int64) + val e3 DIV 2 EXP 52 = val(e4:int64) /\
        2 * val n_8 * val(d5:int64) + val e4 DIV 2 EXP 52 = val(e5:int64) /\
        2 * val n_8 * val(d6:int64) + val e5 DIV 2 EXP 52 = val(e6:int64) /\
        2 * val n_8 * val(d7:int64) + val e6 DIV 2 EXP 52 = val(e7:int64) /\
        2 * val n_8 * val(d8:int64) + val e7 DIV 2 EXP 52 = val(e8:int64) /\
        2 * val n_8 * val(d9:int64) + val e8 DIV 2 EXP 52 = val(e9:int64)`
      MP_TAC THENL [ALL_TAC; REWRITE_TAC[ITLIST] THEN ARITH_TAC] THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; VAL_WORD_USHR; DIMINDEX_64] THEN
      CONV_TAC SYM_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
      MATCH_MP_TAC MOD_LT THEN
      (MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 /\ e < 2 EXP 64
         ==> 2 * n * d + e DIV 2 EXP 52 < 2 EXP 64`) ORELSE
       MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 ==> 2 * n * d < 2 EXP 64`)) THEN
      REWRITE_TAC[VAL_BOUND_64] THEN MATCH_MP_TAC LE_MULT2 THEN
      CONJ_TAC THEN MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC
       ["d0"; "d1"; "d2"; "d3"; "d4"; "d5"; "d6"; "d7"; "d8"; "d9"] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN TRY ARITH_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR] THEN MATCH_MP_TAC
       (ARITH_RULE `n < 2 EXP 64 ==> n DIV 2 EXP 20 < 2 EXP 52`) THEN
      MATCH_ACCEPT_TAC VAL_BOUND_64;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o rev o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Rotation of the high portion ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC (145--160) THEN
  ABBREV_TAC
   `htop:int64 =
    word_add (word_and sum_s80 (word 511)) (word_ushr sum_s144 9)` THEN
  SUBGOAL_THEN `val(htop:int64) < 2 EXP 56` ASSUME_TAC THENL
   [EXPAND_TAC "htop" THEN REWRITE_TAC[VAL_WORD_ADD] THEN
    W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
    REWRITE_TAC[DIMINDEX_64; SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD] THEN
    MP_TAC(ISPEC `sum_s144:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `h = bignum_of_wordlist
    [word_subword ((word_join:int64->int64->int128) sum_s88 sum_s80) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s96 sum_s88) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s104 sum_s96) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s119 sum_s104) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s127 sum_s119) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s135 sum_s127) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s142 sum_s135) (9,64);
     word_subword ((word_join:int64->int64->int128) sum_s144 sum_s142) (9,64);
     htop]` THEN

  SUBGOAL_THEN
   `(inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521 =
    (inverse_mod p_521 (2 EXP 576) *
     (2 EXP 257 * bignum_of_wordlist[n_0;n_1;n_2;n_3] *
                  bignum_of_wordlist[n_4;n_5;n_6;n_7] +
      bignum_of_wordlist[n_0;n_1;n_2;n_3] EXP 2 + h)) MOD p_521`
  SUBST1_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,5)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[ARITH_RULE
     `(l + 2 EXP 256 * (h + 2 EXP 256 * c)) EXP 2 =
      2 EXP 257 * l * h + l EXP 2 +
      2 EXP 512 * ((h + 2 EXP 256 * c) EXP 2 + 2 * c * l)`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1))] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC CONG_LMUL THEN
    REWRITE_TAC[CONG_ADD_LCANCEL_EQ] THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    SUBGOAL_THEN
    `val(htop:int64) =
     val(word_and sum_s80 (word 511):int64) + val(word_ushr sum_s144 9:int64)`
    SUBST1_TAC THENL
     [EXPAND_TAC "htop" THEN
      REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD] THEN
      MP_TAC(ISPEC `sum_s144:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
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
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Squaring of the lower "half" ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
   [161; 162; 169; 174; 175; 177; 178; 179; 180; 181; 183; 184; 185; 186; 187;
    188; 189; 190; 191; 192; 193; 197; 198; 199; 200; 201; 202; 203; 204; 205;
    206; 207; 208; 209; 210; 214; 215; 216; 217; 218; 219; 220; 221; 222; 223]
   (161--223) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_0; n_1; n_2; n_3] EXP 2 =
    bignum_of_wordlist
     [mullo_s191; sum_s200; sum_s203; sum_s204;
      sum_s220; sum_s221; sum_s222; sum_s223]`
  SUBST1_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN FIRST_ASSUM
     (MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Addition of low and rotated high parts ***)

  SUBGOAL_THEN `h < 2 EXP 568` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP (64 * 8) /\ h < 2 EXP 56
      ==> l + 2 EXP 512 * h < 2 EXP 568`) THEN
    ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `hl = bignum_of_wordlist
         [mullo_s191; sum_s200; sum_s203; sum_s204; sum_s220; sum_s221;
          sum_s222; sum_s223] + h` THEN
  SUBGOAL_THEN `hl < 2 EXP 569` ASSUME_TAC THENL
   [EXPAND_TAC "hl" THEN MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP (64 * 8) /\ h < 2 EXP 568 ==> l + h < 2 EXP 569`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
   [225; 226; 229; 230; 233; 234; 237; 238; 241] (224--242) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s225;sum_s226;sum_s229;sum_s230;
      sum_s233;sum_s234;sum_s237;sum_s238;sum_s241] = hl`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; INTEGER_CLOSED; LE_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `hl < 2 EXP 569 ==> hl < 2 EXP 576`] THEN
    MAP_EVERY EXPAND_TAC ["hl"; "h"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    FIRST_X_ASSUM(K ALL_TAC o check ((=) `hl:num` o rand o concl)) THEN
    DISCH_TAC] THEN

  (*** The cross-multiplication ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
   [243; 244; 245; 246; 248; 250; 252; 254; 255; 256; 257; 258;
    259; 260; 261; 262; 263; 264; 265; 271; 276; 278; 279; 285;
    290; 292; 293; 294; 295; 296; 297; 303; 308; 310; 311; 312;
    318; 323; 325; 326; 327; 328; 329; 335; 340; 342; 343; 344;
    345; 351; 356; 358; 359; 360; 361]
   (243--361) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist[n_0;n_1;n_2;n_3] *
    bignum_of_wordlist[n_4;n_5;n_6;n_7] =
    bignum_of_wordlist
     [mullo_s243; sum_s290; sum_s323; sum_s356;
      sum_s358; sum_s359; sum_s360; sum_s361]`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT]) THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN FIRST_ASSUM
     (MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Addition of the rotated cross-product to the running total ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
   [364; 366; 369; 372; 376; 379; 383; 386; 391] (362--391) THEN
  MAP_EVERY ABBREV_TAC
  [`m0:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s359 sum_s358) (8,64)`;
  `m1:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s360 sum_s359) (8,64)`;
  `m2:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s361 sum_s360) (8,64)`;
  `m3:int64 = word_ushr sum_s361 8`;
  `m4:int64 = word_shl mullo_s243 1`;
  `m5:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s290 mullo_s243) (63,64)`;
  `m6:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s323 sum_s290) (63,64)`;
  `m7:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s356 sum_s323) (63,64)`;
  `m8:int64 = word_and
     (word_subword ((word_join:int64->int64->int128) sum_s358 sum_s356)
     (63,64)) (word 511)`] THEN

  SUBGOAL_THEN
   `(inverse_mod p_521 (2 EXP 576) *
     (2 EXP 257 * bignum_of_wordlist
         [mullo_s243; sum_s290; sum_s323; sum_s356;
          sum_s358; sum_s359; sum_s360; sum_s361] + hl)) MOD p_521 =
    (inverse_mod p_521 (2 EXP 576) *
      (bignum_of_wordlist[m0;m1;m2;m3;m4;m5;m6;m7;m8] + hl)) MOD p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC CONG_LMUL THEN
    REWRITE_TAC[CONG_ADD_RCANCEL_EQ] THEN MAP_EVERY EXPAND_TAC
     ["m0"; "m1"; "m2"; "m3"; "m4"; "m5"; "m6"; "m7"; "m8"] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
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
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `m = bignum_of_wordlist
         [sum_s364; sum_s366; sum_s369; sum_s372; sum_s376;
          sum_s379; sum_s383; sum_s386; sum_s391]` THEN
  SUBGOAL_THEN `m < 2 EXP 576` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [m0; m1; m2; m3; m4; m5; m6; m7; m8] + hl = m`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      MATCH_MP_TAC(ARITH_RULE
       `l < 2 EXP (64 * 8) /\ hl < 2 EXP 569 /\ h < 2 EXP 56
        ==> (l + 2 EXP 512 * h) + hl < 2 EXP 576`) THEN
      ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        EXPAND_TAC "m8" THEN
        REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
        REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED; LE_0; REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["hl"; "m"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN
   `(inverse_mod p_521 (2 EXP 576) * m) MOD p_521 =
    (inverse_mod p_521 (2 EXP 576) *
      (m DIV 2 EXP 521 + m MOD 2 EXP 521)) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC BINOP_CONV [GSYM MOD_MULT_MOD2] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `m = 2 EXP 521 * m DIV 2 EXP 521 + m MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m DIV 2 EXP 521 < 2 EXP 64 /\ m MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `m < 2 EXP 576` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC (392--394) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `h:num` o concl))) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s391 9`;
    `d:int64 = word_or sum_s391 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s366 (word_and sum_s369 (word_and sum_s372
      (word_and sum_s376 (word_and sum_s379
         (word_and sum_s383 sum_s386)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC (395--397) (395--397) THEN
  SUBGOAL_THEN
   `carry_s397 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s364:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC (398--406) (398--423) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Deal with the final Montgomery tweak first ***)

  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s398; sum_s399; sum_s400; sum_s401;
      sum_s402; sum_s403; sum_s404; sum_s405;
      word_and sum_s406 (word 511)] =
    (m DIV 2 EXP 521 + m MOD 2 EXP 521) MOD p_521`
  MP_TAC THENL
   [ALL_TAC;
    CONV_TAC(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(BINOP_CONV SYM_CONV) THEN REWRITE_TAC[MOD_UNIQUE] THEN
    REWRITE_TAC[p_521] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN
    REWRITE_TAC[GSYM p_521] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_LT_P521] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_SHL;
               BIT_WORD_JOIN; BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128] THEN
      CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
      GEN_REWRITE_TAC I [CONTRAPOS_THM] THEN
      CONV_TAC(BINOP_CONV CONJ_CANON_CONV) THEN
      DISCH_THEN ACCEPT_TAC;
      MATCH_MP_TAC(NUMBER_RULE
       `!a. (a * i == 1) (mod p) /\ (a * q == n) (mod p)
            ==> (x == n) (mod p) ==> (i * x == q) (mod p)`) THEN
      EXISTS_TAC `2 EXP 576` THEN
      REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2; p_521] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
      REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_SHL;
               BIT_WORD_JOIN; BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      CONV_TAC(DEPTH_CONV
       (NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC]] THEN

  (*** Evaluate d and un-condense the inequality ***)

  DISCARD_STATE_TAC "s423" THEN
  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s391:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s391:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s364; sum_s366; sum_s369; sum_s372; sum_s376;
      sum_s379; sum_s383; sum_s386] =
    m MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= m MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s397`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s397" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s366; sum_s369; sum_s372; sum_s376; sum_s379; sum_s383; sum_s386] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s364:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < m ==> (a < m - 1 <=> ~(a = m - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s391:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s391:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s364:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = m DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    MATCH_MP_TAC(ARITH_RULE
     `m DIV 2 EXP 512 = x ==> x DIV 2 EXP 9 = m DIV 2 EXP 521`) THEN
    EXPAND_TAC "m" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= m MOD 2 EXP 521 + m DIV 2 EXP 521 + 1 <=>
    p_521 <= m DIV 2 EXP 521 + m MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if m DIV 2 EXP 521 + m MOD 2 EXP 521 < p_521
     then &(m DIV 2 EXP 521 + m MOD 2 EXP 521)
     else &(m DIV 2 EXP 521 + m MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `m < 2 EXP 576` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_P521_UNOPT_CORRECT = time prove
   (`!z x n pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p521_unopt_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_unopt_mc /\
                  read PC s = word(pc + 12) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 12 + LENGTH bignum_montsqr_p521_unopt_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                      X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_CORRECT
    bignum_montsqr_p521_unopt_core_mc_def
    [fst BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC;fst BIGNUM_MONTSQR_P521_UNOPT_EXEC]);;


(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-scheduled program
******************************************************************************)

(* This is the intermediate program that is equivalent to both
   bignum_montsqr_p521_base and bignum_montsqr_p521. This is a vectorized
   version of bignum_montsqr_p521_base but instructions are unscheduled. *)

let bignum_montsqr_p521_interm1_ops:int list = [
  0xa9402030; (* ldp    x16, x8, [x1] *)
  0x3dc00032; (* ldr    q18, [x1] *)
  0x3dc00025; (* ldr    q5, [x1] *)
  0x3dc00034; (* ldr    q20, [x1] *)
  0xa9413431; (* ldp    x17, x13, [x1, #16] *)
  0x3dc00431; (* ldr    q17, [x1, #16] *)
  0x3dc00421; (* ldr    q1, [x1, #16] *)
  0x3dc0043c; (* ldr    q28, [x1, #16] *)
  0xa9423c29; (* ldp    x9, x15, [x1, #32] *)
  0x3dc0003b; (* ldr    q27, [x1] *)
  0x3dc0083d; (* ldr    q29, [x1, #32] *)
  0xa9430837; (* ldp    x23, x2, [x1, #48] *)
  0x3dc00c26; (* ldr    q6, [x1, #48] *)
  0x3dc00c24; (* ldr    q4, [x1, #48] *)
  0x9b177d38; (* mul    x24, x9, x23 *)
  0x9b027deb; (* mul    x11, x15, x2 *)
  0x9bd77d34; (* umulh  x20, x9, x23 *)
  0xeb0f0124; (* subs   x4, x9, x15 *)
  0xda842496; (* cneg   x22, x4, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm  x12, cc  // cc = lo, ul, last *)
  0xeb170044; (* subs   x4, x2, x23 *)
  0xda842484; (* cneg   x4, x4, cc  // cc = lo, ul, last *)
  0x9b047ed3; (* mul    x19, x22, x4 *)
  0x9bc47ec4; (* umulh  x4, x22, x4 *)
  0xda8c2187; (* cinv   x7, x12, cc  // cc = lo, ul, last *)
  0xca07026e; (* eor    x14, x19, x7 *)
  0xca070096; (* eor    x22, x4, x7 *)
  0xab14030c; (* adds   x12, x24, x20 *)
  0x9a1f0293; (* adc    x19, x20, xzr *)
  0x9bc27de4; (* umulh  x4, x15, x2 *)
  0xab0b018c; (* adds   x12, x12, x11 *)
  0xba040273; (* adcs   x19, x19, x4 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab0b0273; (* adds   x19, x19, x11 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xba0e018c; (* adcs   x12, x12, x14 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0x9a070084; (* adc    x4, x4, x7 *)
  0xab18030b; (* adds   x11, x24, x24 *)
  0xba0c0194; (* adcs   x20, x12, x12 *)
  0xba13026a; (* adcs   x10, x19, x19 *)
  0xba040083; (* adcs   x3, x4, x4 *)
  0x9a1f03e5; (* adc    x5, xzr, xzr *)
  0x3dc0083e; (* ldr    q30, [x1, #32] *)
  0x2ebec3c0; (* umull  v0.2d, v30.2s, v30.2s *)
  0x6ebec3c2; (* umull2 v2.2d, v30.4s, v30.4s *)
  0x0ea12bd8; (* xtn    v24.2s, v30.2d *)
  0x4e9e5bde; (* uzp2   v30.4s, v30.4s, v30.4s *)
  0x2eb8c3de; (* umull  v30.2d, v30.2s, v24.2s *)
  0x4e083c07; (* mov    x7, v0.d[0] *)
  0x4e183c0e; (* mov    x14, v0.d[1] *)
  0x4e083c53; (* mov    x19, v2.d[0] *)
  0x4e183c56; (* mov    x22, v2.d[1] *)
  0x4e083fc4; (* mov    x4, v30.d[0] *)
  0x4e183fcc; (* mov    x12, v30.d[1] *)
  0xab0484f5; (* adds   x21, x7, x4, lsl #33 *)
  0xd35ffc84; (* lsr    x4, x4, #31 *)
  0x9a0401ce; (* adc    x14, x14, x4 *)
  0xab0c8673; (* adds   x19, x19, x12, lsl #33 *)
  0xd35ffd84; (* lsr    x4, x12, #31 *)
  0x9a0402d6; (* adc    x22, x22, x4 *)
  0x9b0f7d24; (* mul    x4, x9, x15 *)
  0x9bcf7d2c; (* umulh  x12, x9, x15 *)
  0xab0405d8; (* adds   x24, x14, x4, lsl #1 *)
  0x93c4fd84; (* extr   x4, x12, x4, #63 *)
  0xba040273; (* adcs   x19, x19, x4 *)
  0xd37ffd84; (* lsr    x4, x12, #63 *)
  0x9a0402c4; (* adc    x4, x22, x4 *)
  0xab13016b; (* adds   x11, x11, x19 *)
  0xba040294; (* adcs   x20, x20, x4 *)
  0xba1f014a; (* adcs   x10, x10, xzr *)
  0xba1f0063; (* adcs   x3, x3, xzr *)
  0x9a1f00a6; (* adc    x6, x5, xzr *)
  0x6f00e5e3; (* movi   v3.2d, #0xffffffff *)
  0x4e845890; (* uzp2   v16.4s, v4.4s, v4.4s *)
  0x0ea128d9; (* xtn    v25.2s, v6.2d *)
  0x0ea12897; (* xtn    v23.2s, v4.2d *)
  0x4ea0089e; (* rev64  v30.4s, v4.4s *)
  0x2eb7c338; (* umull  v24.2d, v25.2s, v23.2s *)
  0x2eb0c320; (* umull  v0.2d, v25.2s, v16.2s *)
  0x4e8658c2; (* uzp2   v2.4s, v6.4s, v6.4s *)
  0x4ea69fde; (* mul    v30.4s, v30.4s, v6.4s *)
  0x6f601700; (* usra   v0.2d, v24.2d, #32 *)
  0x2eb0c053; (* umull  v19.2d, v2.2s, v16.2s *)
  0x6ea02bde; (* uaddlp v30.2d, v30.4s *)
  0x4e231c18; (* and    v24.16b, v0.16b, v3.16b *)
  0x2eb78058; (* umlal  v24.2d, v2.2s, v23.2s *)
  0x4f6057de; (* shl    v30.2d, v30.2d, #32 *)
  0x6f601413; (* usra   v19.2d, v0.2d, #32 *)
  0x2eb7833e; (* umlal  v30.2d, v25.2s, v23.2s *)
  0x6f601713; (* usra   v19.2d, v24.2d, #32 *)
  0x4e083fc5; (* mov    x5, v30.d[0] *)
  0x4e183fc7; (* mov    x7, v30.d[1] *)
  0x9b027eee; (* mul    x14, x23, x2 *)
  0x4e083e73; (* mov    x19, v19.d[0] *)
  0x4e183e64; (* mov    x4, v19.d[1] *)
  0x9bc27ef6; (* umulh  x22, x23, x2 *)
  0xab0e026c; (* adds   x12, x19, x14 *)
  0xba1600f3; (* adcs   x19, x7, x22 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab0e018c; (* adds   x12, x12, x14 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab0a00a7; (* adds   x7, x5, x10 *)
  0xba030183; (* adcs   x3, x12, x3 *)
  0xba06026e; (* adcs   x14, x19, x6 *)
  0x9a1f008a; (* adc    x10, x4, xzr *)
  0xf9402024; (* ldr    x4, [x1, #64] *)
  0x8b040086; (* add    x6, x4, x4 *)
  0x9b047c85; (* mul    x5, x4, x4 *)
  0x9240ce04; (* and    x4, x16, #0xfffffffffffff *)
  0x9b047cd6; (* mul    x22, x6, x4 *)
  0x93d0d104; (* extr   x4, x8, x16, #52 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fec4; (* lsr    x4, x22, #52 *)
  0x8b04026c; (* add    x12, x19, x4 *)
  0xd374cec4; (* lsl    x4, x22, #12 *)
  0x93c43184; (* extr   x4, x12, x4, #12 *)
  0xab0402b5; (* adds   x21, x21, x4 *)
  0x93c8a224; (* extr   x4, x17, x8, #40 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fd84; (* lsr    x4, x12, #52 *)
  0x8b040276; (* add    x22, x19, x4 *)
  0xd374cd84; (* lsl    x4, x12, #12 *)
  0x93c462c4; (* extr   x4, x22, x4, #24 *)
  0xba040318; (* adcs   x24, x24, x4 *)
  0x93d171a4; (* extr   x4, x13, x17, #28 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fec4; (* lsr    x4, x22, #52 *)
  0x8b04026c; (* add    x12, x19, x4 *)
  0xd374cec4; (* lsl    x4, x22, #12 *)
  0x93c49184; (* extr   x4, x12, x4, #36 *)
  0xba04016b; (* adcs   x11, x11, x4 *)
  0x93cd4124; (* extr   x4, x9, x13, #16 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fd84; (* lsr    x4, x12, #52 *)
  0x8b040276; (* add    x22, x19, x4 *)
  0xd374cd84; (* lsl    x4, x12, #12 *)
  0x93c4c2c4; (* extr   x4, x22, x4, #48 *)
  0xba040294; (* adcs   x20, x20, x4 *)
  0xd344fd24; (* lsr    x4, x9, #4 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fec4; (* lsr    x4, x22, #52 *)
  0x8b04026c; (* add    x12, x19, x4 *)
  0xd374cec4; (* lsl    x4, x22, #12 *)
  0x93c4f196; (* extr   x22, x12, x4, #60 *)
  0x93c9e1e4; (* extr   x4, x15, x9, #56 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fd84; (* lsr    x4, x12, #52 *)
  0x8b04026c; (* add    x12, x19, x4 *)
  0xd378dec4; (* lsl    x4, x22, #8 *)
  0x93c42184; (* extr   x4, x12, x4, #8 *)
  0xba0400e7; (* adcs   x7, x7, x4 *)
  0x93cfb2e4; (* extr   x4, x23, x15, #44 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fd84; (* lsr    x4, x12, #52 *)
  0x8b040276; (* add    x22, x19, x4 *)
  0xd374cd84; (* lsl    x4, x12, #12 *)
  0x93c452c4; (* extr   x4, x22, x4, #20 *)
  0xba040061; (* adcs   x1, x3, x4 *)
  0x93d78044; (* extr   x4, x2, x23, #32 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fec4; (* lsr    x4, x22, #52 *)
  0x8b04026c; (* add    x12, x19, x4 *)
  0xd374cec4; (* lsl    x4, x22, #12 *)
  0x93c48184; (* extr   x4, x12, x4, #32 *)
  0xba0401ce; (* adcs   x14, x14, x4 *)
  0xd354fc44; (* lsr    x4, x2, #20 *)
  0x9b047cd3; (* mul    x19, x6, x4 *)
  0xd374fd84; (* lsr    x4, x12, #52 *)
  0x8b040273; (* add    x19, x19, x4 *)
  0xd374cd84; (* lsl    x4, x12, #12 *)
  0x93c4b264; (* extr   x4, x19, x4, #44 *)
  0xba040156; (* adcs   x22, x10, x4 *)
  0xd36cfe64; (* lsr    x4, x19, #44 *)
  0x9a0400ac; (* adc    x12, x5, x4 *)
  0x93d52713; (* extr   x19, x24, x21, #9 *)
  0x93d82564; (* extr   x4, x11, x24, #9 *)
  0xa9001013; (* stp    x19, x4, [x0] *)
  0x93cb2693; (* extr   x19, x20, x11, #9 *)
  0x93d424e4; (* extr   x4, x7, x20, #9 *)
  0xa9011013; (* stp    x19, x4, [x0, #16] *)
  0x93c72433; (* extr   x19, x1, x7, #9 *)
  0x93c125c4; (* extr   x4, x14, x1, #9 *)
  0xa9021013; (* stp    x19, x4, [x0, #32] *)
  0x93ce26d3; (* extr   x19, x22, x14, #9 *)
  0x93d62584; (* extr   x4, x12, x22, #9 *)
  0xa9031013; (* stp    x19, x4, [x0, #48] *)
  0x924022b3; (* and    x19, x21, #0x1ff *)
  0xd349fd84; (* lsr    x4, x12, #9 *)
  0x8b040264; (* add    x4, x19, x4 *)
  0xf9002004; (* str    x4, [x0, #64] *)
  0x4e921b82; (* uzp1   v2.4s, v28.4s, v18.4s *)
  0x4ea00b9e; (* rev64  v30.4s, v28.4s *)
  0x4e921a58; (* uzp1   v24.4s, v18.4s, v18.4s *)
  0x4eb29fde; (* mul    v30.4s, v30.4s, v18.4s *)
  0x6ea02bde; (* uaddlp v30.2d, v30.4s *)
  0x4f6057de; (* shl    v30.2d, v30.2d, #32 *)
  0x2ea2831e; (* umlal  v30.2d, v24.2s, v2.2s *)
  0x4e083fcb; (* mov    x11, v30.d[0] *)
  0x4e183fd4; (* mov    x20, v30.d[1] *)
  0x9bd17e07; (* umulh  x7, x16, x17 *)
  0xeb080204; (* subs   x4, x16, x8 *)
  0xda842496; (* cneg   x22, x4, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm  x12, cc  // cc = lo, ul, last *)
  0xeb1101a4; (* subs   x4, x13, x17 *)
  0xda842484; (* cneg   x4, x4, cc  // cc = lo, ul, last *)
  0x9b047ed3; (* mul    x19, x22, x4 *)
  0x9bc47ec4; (* umulh  x4, x22, x4 *)
  0xda8c2181; (* cinv   x1, x12, cc  // cc = lo, ul, last *)
  0xca01026e; (* eor    x14, x19, x1 *)
  0xca010096; (* eor    x22, x4, x1 *)
  0xab07016c; (* adds   x12, x11, x7 *)
  0x9a1f00f3; (* adc    x19, x7, xzr *)
  0x9bcd7d04; (* umulh  x4, x8, x13 *)
  0xab14018c; (* adds   x12, x12, x20 *)
  0xba040273; (* adcs   x19, x19, x4 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab140273; (* adds   x19, x19, x20 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xb100043f; (* cmn    x1, #0x1 *)
  0xba0e018c; (* adcs   x12, x12, x14 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0x9a010084; (* adc    x4, x4, x1 *)
  0xab0b0175; (* adds   x21, x11, x11 *)
  0xba0c0198; (* adcs   x24, x12, x12 *)
  0xba13026b; (* adcs   x11, x19, x19 *)
  0xba040094; (* adcs   x20, x4, x4 *)
  0x9a1f03e7; (* adc    x7, xzr, xzr *)
  0x6f00e5e3; (* movi   v3.2d, #0xffffffff *)
  0x4e945a90; (* uzp2   v16.4s, v20.4s, v20.4s *)
  0x0ea128b9; (* xtn    v25.2s, v5.2d *)
  0x0ea12a97; (* xtn    v23.2s, v20.2d *)
  0x4ea00a9e; (* rev64  v30.4s, v20.4s *)
  0x2eb7c338; (* umull  v24.2d, v25.2s, v23.2s *)
  0x2eb0c320; (* umull  v0.2d, v25.2s, v16.2s *)
  0x4e8558a2; (* uzp2   v2.4s, v5.4s, v5.4s *)
  0x4ea59fde; (* mul    v30.4s, v30.4s, v5.4s *)
  0x6f601700; (* usra   v0.2d, v24.2d, #32 *)
  0x2eb0c053; (* umull  v19.2d, v2.2s, v16.2s *)
  0x6ea02bde; (* uaddlp v30.2d, v30.4s *)
  0x4e231c18; (* and    v24.16b, v0.16b, v3.16b *)
  0x2eb78058; (* umlal  v24.2d, v2.2s, v23.2s *)
  0x4f6057de; (* shl    v30.2d, v30.2d, #32 *)
  0x6f601413; (* usra   v19.2d, v0.2d, #32 *)
  0x2eb7833e; (* umlal  v30.2d, v25.2s, v23.2s *)
  0x6f601713; (* usra   v19.2d, v24.2d, #32 *)
  0x4e083fca; (* mov    x10, v30.d[0] *)
  0x4e183fc1; (* mov    x1, v30.d[1] *)
  0x9b087e0e; (* mul    x14, x16, x8 *)
  0x4e083e73; (* mov    x19, v19.d[0] *)
  0x4e183e64; (* mov    x4, v19.d[1] *)
  0x9bc87e16; (* umulh  x22, x16, x8 *)
  0xab0e026c; (* adds   x12, x19, x14 *)
  0xba160033; (* adcs   x19, x1, x22 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab0e0183; (* adds   x3, x12, x14 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab1302a5; (* adds   x5, x21, x19 *)
  0xba040315; (* adcs   x21, x24, x4 *)
  0xba1f0178; (* adcs   x24, x11, xzr *)
  0xba1f028b; (* adcs   x11, x20, xzr *)
  0x9a1f00f4; (* adc    x20, x7, xzr *)
  0x6f00e5e3; (* movi   v3.2d, #0xffffffff *)
  0x4e815830; (* uzp2   v16.4s, v1.4s, v1.4s *)
  0x0ea12a39; (* xtn    v25.2s, v17.2d *)
  0x0ea12837; (* xtn    v23.2s, v1.2d *)
  0x4ea0083e; (* rev64  v30.4s, v1.4s *)
  0x2eb7c338; (* umull  v24.2d, v25.2s, v23.2s *)
  0x2eb0c320; (* umull  v0.2d, v25.2s, v16.2s *)
  0x4e915a22; (* uzp2   v2.4s, v17.4s, v17.4s *)
  0x4eb19fde; (* mul    v30.4s, v30.4s, v17.4s *)
  0x6f601700; (* usra   v0.2d, v24.2d, #32 *)
  0x2eb0c053; (* umull  v19.2d, v2.2s, v16.2s *)
  0x6ea02bde; (* uaddlp v30.2d, v30.4s *)
  0x4e231c18; (* and    v24.16b, v0.16b, v3.16b *)
  0x2eb78058; (* umlal  v24.2d, v2.2s, v23.2s *)
  0x4f6057de; (* shl    v30.2d, v30.2d, #32 *)
  0x6f601413; (* usra   v19.2d, v0.2d, #32 *)
  0x2eb7833e; (* umlal  v30.2d, v25.2s, v23.2s *)
  0x6f601713; (* usra   v19.2d, v24.2d, #32 *)
  0x4e083fc7; (* mov    x7, v30.d[0] *)
  0x4e183fc1; (* mov    x1, v30.d[1] *)
  0x9b0d7e2e; (* mul    x14, x17, x13 *)
  0x4e083e73; (* mov    x19, v19.d[0] *)
  0x4e183e64; (* mov    x4, v19.d[1] *)
  0x9bcd7e36; (* umulh  x22, x17, x13 *)
  0xab0e026c; (* adds   x12, x19, x14 *)
  0xba160033; (* adcs   x19, x1, x22 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab0e018c; (* adds   x12, x12, x14 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab1800e1; (* adds   x1, x7, x24 *)
  0xba0b018e; (* adcs   x14, x12, x11 *)
  0xba140276; (* adcs   x22, x19, x20 *)
  0x9a1f008c; (* adc    x12, x4, xzr *)
  0xa9401013; (* ldp    x19, x4, [x0] *)
  0xab0a0273; (* adds   x19, x19, x10 *)
  0xba030084; (* adcs   x4, x4, x3 *)
  0xa9001013; (* stp    x19, x4, [x0] *)
  0xa9411013; (* ldp    x19, x4, [x0, #16] *)
  0xba050273; (* adcs   x19, x19, x5 *)
  0xba150084; (* adcs   x4, x4, x21 *)
  0xa9011013; (* stp    x19, x4, [x0, #16] *)
  0xa9421013; (* ldp    x19, x4, [x0, #32] *)
  0xba010273; (* adcs   x19, x19, x1 *)
  0xba0e0084; (* adcs   x4, x4, x14 *)
  0xa9021013; (* stp    x19, x4, [x0, #32] *)
  0xa9431013; (* ldp    x19, x4, [x0, #48] *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0xba0c0084; (* adcs   x4, x4, x12 *)
  0xa9031013; (* stp    x19, x4, [x0, #48] *)
  0xf9402004; (* ldr    x4, [x0, #64] *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xf9002004; (* str    x4, [x0, #64] *)
  0x6f00e5e3; (* movi   v3.2d, #0xffffffff *)
  0x4e9d5ba2; (* uzp2   v2.4s, v29.4s, v29.4s *)
  0x0ea12b70; (* xtn    v16.2s, v27.2d *)
  0x0ea12bb9; (* xtn    v25.2s, v29.2d *)
  0x4ea00bbe; (* rev64  v30.4s, v29.4s *)
  0x2eb9c218; (* umull  v24.2d, v16.2s, v25.2s *)
  0x2ea2c217; (* umull  v23.2d, v16.2s, v2.2s *)
  0x4e9b5b60; (* uzp2   v0.4s, v27.4s, v27.4s *)
  0x4ebb9fde; (* mul    v30.4s, v30.4s, v27.4s *)
  0x6f601717; (* usra   v23.2d, v24.2d, #32 *)
  0x2ea2c002; (* umull  v2.2d, v0.2s, v2.2s *)
  0x6ea02bde; (* uaddlp v30.2d, v30.4s *)
  0x4e231ef8; (* and    v24.16b, v23.16b, v3.16b *)
  0x2eb98018; (* umlal  v24.2d, v0.2s, v25.2s *)
  0x4f6057de; (* shl    v30.2d, v30.2d, #32 *)
  0x6f6016e2; (* usra   v2.2d, v23.2d, #32 *)
  0x2eb9821e; (* umlal  v30.2d, v16.2s, v25.2s *)
  0x6f601702; (* usra   v2.2d, v24.2d, #32 *)
  0x4e083fc6; (* mov    x6, v30.d[0] *)
  0x4e183fd6; (* mov    x22, v30.d[1] *)
  0x9b177e2c; (* mul    x12, x17, x23 *)
  0x9b027db3; (* mul    x19, x13, x2 *)
  0x4e083c44; (* mov    x4, v2.d[0] *)
  0xab0402d6; (* adds   x22, x22, x4 *)
  0x4e183c44; (* mov    x4, v2.d[1] *)
  0xba04018c; (* adcs   x12, x12, x4 *)
  0x9bd77e24; (* umulh  x4, x17, x23 *)
  0xba040273; (* adcs   x19, x19, x4 *)
  0x9bc27da4; (* umulh  x4, x13, x2 *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0xab0602d5; (* adds   x21, x22, x6 *)
  0xba160196; (* adcs   x22, x12, x22 *)
  0xba0c026c; (* adcs   x12, x19, x12 *)
  0xba130093; (* adcs   x19, x4, x19 *)
  0x9a0403e4; (* adc    x4, xzr, x4 *)
  0xab0602d8; (* adds   x24, x22, x6 *)
  0xba15018b; (* adcs   x11, x12, x21 *)
  0xba160274; (* adcs   x20, x19, x22 *)
  0xba0c0081; (* adcs   x1, x4, x12 *)
  0xba1303ee; (* adcs   x14, xzr, x19 *)
  0x9a0403e7; (* adc    x7, xzr, x4 *)
  0xeb0d0224; (* subs   x4, x17, x13 *)
  0xda84248c; (* cneg   x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb170044; (* subs   x4, x2, x23 *)
  0xda842493; (* cneg   x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul    x4, x12, x19 *)
  0x9bd37d8c; (* umulh  x12, x12, x19 *)
  0xda9622d3; (* cinv   x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xca130084; (* eor    x4, x4, x19 *)
  0xba040021; (* adcs   x1, x1, x4 *)
  0xca130184; (* eor    x4, x12, x19 *)
  0xba0401ce; (* adcs   x14, x14, x4 *)
  0x9a1300e7; (* adc    x7, x7, x19 *)
  0xeb080204; (* subs   x4, x16, x8 *)
  0xda84248c; (* cneg   x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb0901e4; (* subs   x4, x15, x9 *)
  0xda842493; (* cneg   x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul    x4, x12, x19 *)
  0x9bd37d8c; (* umulh  x12, x12, x19 *)
  0xda9622d3; (* cinv   x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xca130084; (* eor    x4, x4, x19 *)
  0xba0402aa; (* adcs   x10, x21, x4 *)
  0xca130184; (* eor    x4, x12, x19 *)
  0xba040318; (* adcs   x24, x24, x4 *)
  0xba13016b; (* adcs   x11, x11, x19 *)
  0xba130294; (* adcs   x20, x20, x19 *)
  0xba130021; (* adcs   x1, x1, x19 *)
  0xba1301ce; (* adcs   x14, x14, x19 *)
  0x9a1300e7; (* adc    x7, x7, x19 *)
  0xeb0d0104; (* subs   x4, x8, x13 *)
  0xda84248c; (* cneg   x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb0f0044; (* subs   x4, x2, x15 *)
  0xda842493; (* cneg   x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul    x4, x12, x19 *)
  0x9bd37d8c; (* umulh  x12, x12, x19 *)
  0xda9622d3; (* cinv   x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xca130084; (* eor    x4, x4, x19 *)
  0xba040294; (* adcs   x20, x20, x4 *)
  0xca130184; (* eor    x4, x12, x19 *)
  0xba040021; (* adcs   x1, x1, x4 *)
  0xba1301ce; (* adcs   x14, x14, x19 *)
  0x9a1300e7; (* adc    x7, x7, x19 *)
  0xeb110204; (* subs   x4, x16, x17 *)
  0xda84248c; (* cneg   x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb0902e4; (* subs   x4, x23, x9 *)
  0xda842493; (* cneg   x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul    x4, x12, x19 *)
  0x9bd37d8c; (* umulh  x12, x12, x19 *)
  0xda9622d3; (* cinv   x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xca130084; (* eor    x4, x4, x19 *)
  0xba040318; (* adcs   x24, x24, x4 *)
  0xca130184; (* eor    x4, x12, x19 *)
  0xba04016b; (* adcs   x11, x11, x4 *)
  0xba130294; (* adcs   x20, x20, x19 *)
  0xba130021; (* adcs   x1, x1, x19 *)
  0xba1301ce; (* adcs   x14, x14, x19 *)
  0x9a1300e7; (* adc    x7, x7, x19 *)
  0xeb0d0204; (* subs   x4, x16, x13 *)
  0xda84248c; (* cneg   x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb090044; (* subs   x4, x2, x9 *)
  0xda842493; (* cneg   x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul    x4, x12, x19 *)
  0x9bd37d8c; (* umulh  x12, x12, x19 *)
  0xda9622d3; (* cinv   x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xca130084; (* eor    x4, x4, x19 *)
  0xba04016b; (* adcs   x11, x11, x4 *)
  0xca130184; (* eor    x4, x12, x19 *)
  0xba040294; (* adcs   x20, x20, x4 *)
  0xba130021; (* adcs   x1, x1, x19 *)
  0xba1301ce; (* adcs   x14, x14, x19 *)
  0x9a1300e7; (* adc    x7, x7, x19 *)
  0xeb110104; (* subs   x4, x8, x17 *)
  0xda84248c; (* cneg   x12, x4, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb0f02e4; (* subs   x4, x23, x15 *)
  0xda842493; (* cneg   x19, x4, cc  // cc = lo, ul, last *)
  0x9b137d84; (* mul    x4, x12, x19 *)
  0x9bd37d8c; (* umulh  x12, x12, x19 *)
  0xda9622d3; (* cinv   x19, x22, cc  // cc = lo, ul, last *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xca130084; (* eor    x4, x4, x19 *)
  0xba040163; (* adcs   x3, x11, x4 *)
  0xca130184; (* eor    x4, x12, x19 *)
  0xba040285; (* adcs   x5, x20, x4 *)
  0xba130021; (* adcs   x1, x1, x19 *)
  0xba1301ce; (* adcs   x14, x14, x19 *)
  0x9a1300f6; (* adc    x22, x7, x19 *)
  0xa9404c0c; (* ldp    x12, x19, [x0] *)
  0x93c52024; (* extr   x4, x1, x5, #8 *)
  0xab0c008b; (* adds   x11, x4, x12 *)
  0x93c121c4; (* extr   x4, x14, x1, #8 *)
  0xba130094; (* adcs   x20, x4, x19 *)
  0xa9413013; (* ldp    x19, x12, [x0, #16] *)
  0x93ce22c4; (* extr   x4, x22, x14, #8 *)
  0xba130087; (* adcs   x7, x4, x19 *)
  0x8a070293; (* and    x19, x20, x7 *)
  0xd348fec4; (* lsr    x4, x22, #8 *)
  0xba0c0081; (* adcs   x1, x4, x12 *)
  0x8a010276; (* and    x22, x19, x1 *)
  0xa9423013; (* ldp    x19, x12, [x0, #32] *)
  0xd37ff8c4; (* lsl    x4, x6, #1 *)
  0xba13008e; (* adcs   x14, x4, x19 *)
  0x8a0e02d3; (* and    x19, x22, x14 *)
  0x93c6fd44; (* extr   x4, x10, x6, #63 *)
  0xba0c0095; (* adcs   x21, x4, x12 *)
  0x8a150276; (* and    x22, x19, x21 *)
  0xa9433013; (* ldp    x19, x12, [x0, #48] *)
  0x93caff04; (* extr   x4, x24, x10, #63 *)
  0xba130082; (* adcs   x2, x4, x19 *)
  0x8a0202d3; (* and    x19, x22, x2 *)
  0x93d8fc64; (* extr   x4, x3, x24, #63 *)
  0xba0c0098; (* adcs   x24, x4, x12 *)
  0x8a18026c; (* and    x12, x19, x24 *)
  0xf9402013; (* ldr    x19, [x0, #64] *)
  0x93c3fca4; (* extr   x4, x5, x3, #63 *)
  0x92402084; (* and    x4, x4, #0x1ff *)
  0x9a040264; (* adc    x4, x19, x4 *)
  0xd349fc93; (* lsr    x19, x4, #9 *)
  0xb277d884; (* orr    x4, x4, #0xfffffffffffffe00 *)
  0xeb1f03ff; (* cmp    xzr, xzr *)
  0xba13017f; (* adcs   xzr, x11, x19 *)
  0xba1f019f; (* adcs   xzr, x12, xzr *)
  0xba1f009f; (* adcs   xzr, x4, xzr *)
  0xba13016b; (* adcs   x11, x11, x19 *)
  0xba1f0294; (* adcs   x20, x20, xzr *)
  0xba1f00e7; (* adcs   x7, x7, xzr *)
  0xba1f0021; (* adcs   x1, x1, xzr *)
  0xba1f01ce; (* adcs   x14, x14, xzr *)
  0xba1f02b6; (* adcs   x22, x21, xzr *)
  0xba1f004c; (* adcs   x12, x2, xzr *)
  0xba1f0318; (* adcs   x24, x24, xzr *)
  0x9a1f0084; (* adc    x4, x4, xzr *)
  0x92402093; (* and    x19, x4, #0x1ff *)
  0xd377d964; (* lsl    x4, x11, #9 *)
  0x93cbde8b; (* extr   x11, x20, x11, #55 *)
  0x93d4dcf4; (* extr   x20, x7, x20, #55 *)
  0x93c7dc27; (* extr   x7, x1, x7, #55 *)
  0x93c1ddc1; (* extr   x1, x14, x1, #55 *)
  0xaa040264; (* orr    x4, x19, x4 *)
  0x93cedece; (* extr   x14, x22, x14, #55 *)
  0x93d6dd96; (* extr   x22, x12, x22, #55 *)
  0x93ccdf0c; (* extr   x12, x24, x12, #55 *)
  0x93d8dc93; (* extr   x19, x4, x24, #55 *)
  0xd377fc84; (* lsr    x4, x4, #55 *)
  0xa900500b; (* stp    x11, x20, [x0] *)
  0xa9010407; (* stp    x7, x1, [x0, #16] *)
  0xa902580e; (* stp    x14, x22, [x0, #32] *)
  0xa9034c0c; (* stp    x12, x19, [x0, #48] *)
  0xf9002004; (* str    x4, [x0, #64] *)
];;

let bignum_montsqr_p521_interm1_core_mc =
  define_mc_from_intlist "bignum_montsqr_p521_interm1_core_mc" bignum_montsqr_p521_interm1_ops;;

let BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC =
  ARM_MK_EXEC_RULE bignum_montsqr_p521_interm1_core_mc;;

let montsqr_p521_eqin = new_definition
  `!s1 s1' x z.
    (montsqr_p521_eqin:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
    (C_ARGUMENTS [z; x] s1 /\
     C_ARGUMENTS [z; x] s1' /\
     ?a. bignum_from_memory (x,9) s1 = a /\
         bignum_from_memory (x,9) s1' = a)`;;

let montsqr_p521_eqout = new_definition
  `!s1 s1' z.
    (montsqr_p521_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,9) s1 = a /\
      bignum_from_memory (z,9) s1' = a)`;;

let actions1 = [
  ("equal", 0, 1, 0, 1); ("insert", 1, 1, 1, 4); ("equal", 1, 2, 4, 5);
  ("insert", 2, 2, 5, 8); ("equal", 2, 3, 8, 9); ("insert", 3, 3, 9, 11);
  ("equal", 3, 4, 11, 12); ("insert", 4, 4, 12, 14); ("equal", 4, 34, 14, 44);
  ("delete", 34, 46, 44, 44); ("insert", 46, 46, 44, 69)
];;
(* rewrite WORD_SQR128_DIGIT3;WORD_SQR128_DIGIT2;WORD_SQR128_DIGIT1;
           WORD_SQR128_DIGIT0 before actions2 *)
let actions2 = [
  ("equal", 46, 51, 69, 74); ("delete", 51, 53, 74, 74);
  ("insert", 53, 53, 74, 94); ("equal", 53, 54, 94, 95);
  ("delete", 54, 56, 95, 95); ("insert", 56, 56, 95, 97);
  ("equal", 56, 160, 97, 201); ("delete", 160, 162, 201, 201);
  ("insert", 162, 162, 201, 210); ("equal", 162, 190, 210, 238);
  ("delete", 190, 192, 238, 238); ("insert", 192, 192, 238, 258);
  ("equal", 192, 193, 258, 259); ("delete", 193, 195, 259, 259);
  ("insert", 195, 195, 259, 261); ("equal", 195, 207, 261, 273);
  ("delete", 207, 209, 273, 273); ("insert", 209, 209, 273, 293);
  ("equal", 209, 210, 293, 294); ("delete", 210, 212, 294, 294);
  ("insert", 212, 212, 294, 296); ("equal", 212, 242, 296, 326);
  ("delete", 242, 244, 326, 326); ("insert", 244, 244, 326, 346);
  ("equal", 244, 246, 346, 348); ("delete", 246, 247, 348, 348);
  ("insert", 247, 247, 348, 349); ("equal", 247, 248, 349, 350);
  ("delete", 248, 249, 350, 350); ("insert", 249, 249, 350, 351);
  ("equal", 249, 423, 351, 525)
];;

let actions1 = break_equal_loads actions1
    (snd BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC) 0x0;;

let actions2 = break_equal_loads actions2
    (snd BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC) 0x0;;


let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montsqr_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_montsqr_p521_interm1_core_mc)]`
    montsqr_p521_eqin
    montsqr_p521_eqout
    bignum_montsqr_p521_unopt_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_montsqr_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
                       WORD_SQR64_HI]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTSQR_P521_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC;
    fst BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC;bignum] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p521_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Start *)
  EQUIV_STEPS_TAC actions1
    BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC THEN

  RULE_ASSUM_TAC (REWRITE_RULE[WORD_SQR128_DIGIT3;
    WORD_SQR128_DIGIT2;WORD_SQR128_DIGIT1;WORD_SQR128_DIGIT0]) THEN

  EQUIV_STEPS_TAC actions2
    BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,9) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV;;



(******************************************************************************
  The second program equivalence between the core part of intermediate
  program and fully optimized program
******************************************************************************)

let bignum_montsqr_p521_mc =
  define_from_elf "bignum_montsqr_p521_mc"
    "arm/p521/bignum_montsqr_p521.o";;

let BIGNUM_MONTSQR_P521_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p521_mc;;

let bignum_montsqr_p521_core_mc_def,
    bignum_montsqr_p521_core_mc,
    BIGNUM_MONTSQR_P521_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p521_core_mc"
    bignum_montsqr_p521_mc
    (`12`,`LENGTH bignum_montsqr_p521_mc - 28`)
    (fst BIGNUM_MONTSQR_P521_EXEC);;

let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montsqr_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_montsqr_p521_core_mc)]`
    montsqr_p521_eqin
    montsqr_p521_eqout
    bignum_montsqr_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_montsqr_p521_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws. *)

let inst_map = [
  14;9;12;13;45;79;17;83;77;76;48;78;49;81;15;86;80;28;63;75;82;29;18;50;89;20;19;85;8;21;16;84;2;22;30;46;203;25;31;56;91;47;55;205;87;23;52;51;32;3;4;33;34;90;88;35;57;54;53;58;202;204;92;59;61;60;6;240;26;24;242;62;36;241;10;37;206;64;27;38;39;40;41;95;244;42;1;245;246;43;11;44;65;94;207;68;66;7;97;67;98;239;248;69;70;96;249;71;243;109;5;72;208;73;112;247;74;99;277;100;93;101;102;110;251;103;114;113;254;104;105;252;115;106;275;122;116;107;278;111;146;108;119;117;118;123;120;124;130;121;282;131;125;127;132;126;128;147;129;138;148;139;133;134;135;140;136;137;187;186;250;143;188;211;285;141;153;256;142;161;288;144;154;281;145;276;151;149;155;150;162;169;152;158;156;163;157;170;159;166;164;160;171;165;167;189;190;177;178;172;173;174;168;175;179;176;280;180;181;192;331;279;193;182;290;183;224;184;185;212;191;214;253;274;213;215;283;216;199;198;209;200;194;218;210;201;195;284;217;335;286;219;222;334;223;225;287;330;221;226;289;220;291;329;227;228;255;328;229;230;332;231;196;333;232;197;259;296;336;233;234;262;338;295;235;260;327;236;258;261;237;339;238;340;263;294;257;337;264;341;265;266;267;297;268;269;270;271;293;342;292;272;273;298;299;300;301;355;302;303;304;308;305;312;344;306;343;307;353;309;316;310;313;311;320;314;348;324;317;318;351;319;347;321;349;346;315;322;345;325;382;383;384;385;386;389;350;388;352;323;326;354;356;368;369;370;371;372;375;357;387;358;393;373;359;360;361;374;362;391;363;377;364;365;366;367;379;376;378;380;381;400;401;402;403;407;404;390;392;405;394;409;395;406;396;397;398;399;415;417;416;418;419;422;408;420;410;411;424;421;412;413;414;448;449;450;432;433;434;451;455;452;453;435;439;436;426;437;423;425;457;427;428;438;429;483;480;430;441;431;440;454;443;442;469;464;444;445;484;477;446;447;456;458;459;476;460;490;487;461;491;462;492;465;467;463;466;468;470;473;471;474;472;478;475;481;479;485;482;488;486;489;493;494;496;495;497;498;499;500;501;510;502;511;512;503;513;521;504;505;514;506;522;516;507;517;508;523;518;509;515;519;520;524;525];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTSQR_P521_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTSQR_P521_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p521_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MONTSQR_P521_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,9) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;



(******************************************************************************
  Use transitivity of two program equivalences to prove end-to-end
  correctness
******************************************************************************)

let equiv_goal = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montsqr_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_montsqr_p521_core_mc)]`
    montsqr_p521_eqin
    montsqr_p521_eqout
    bignum_montsqr_p521_unopt_core_mc
    `MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9)]`
    bignum_montsqr_p521_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9)]`;;

let montsqr_p521_eqout_TRANS = prove(
  `!s s2 s'
    z. montsqr_p521_eqout (s,s') z /\ montsqr_p521_eqout (s',s2) z
    ==> montsqr_p521_eqout (s,s2) z`,
  MESON_TAC[montsqr_p521_eqout]);;

let BIGNUM_MONTSQR_P521_CORE_EQUIV = time prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc:int64,LENGTH bignum_montsqr_p521_unopt_core_mc);
        (word pc3:int64,LENGTH bignum_montsqr_p521_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc3:int64,LENGTH bignum_montsqr_p521_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montsqr_p521_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montsqr_p521_interm1_core_mc))
        [x,8 * 9] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTSQR_P521_CORE_EXEC;
       GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTSQR_P521_CORE_EQUIV1,BIGNUM_MONTSQR_P521_CORE_EQUIV2)
    (montsqr_p521_eqin,montsqr_p521_eqin,montsqr_p521_eqin)
    montsqr_p521_eqout_TRANS
    (BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P521_INTERM1_CORE_EXEC,
     BIGNUM_MONTSQR_P521_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MONTSQR_P521_SUBROUTINE_CORRECT
          from BIGNUM_MONTSQR_P521_UNOPT_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTSQR_P384_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64,
        LENGTH (APPEND bignum_montsqr_p521_unopt_core_mc barrier_inst_bytes))
      (z:int64,8 * 9)`
    [`z:int64`;`x:int64`] bignum_montsqr_p521_unopt_core_mc
    `\s0. C_ARGUMENTS [z;x] s0`;;

let BIGNUM_MONTSQR_P521_EVENTUALLY_N_AT_PC = time prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montsqr_p521_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              fst BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC);;


let BIGNUM_MONTSQR_P521_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTSQR_P521_UNOPT_EXEC
    BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P521_UNOPT_CORE_CORRECT
    BIGNUM_MONTSQR_P521_EVENTUALLY_N_AT_PC;;

(* This theorem is a copy of BIGNUM_MONTSQR_P521_UNOPT_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - bignum_montsqr_p521_unopt_core_mc with bignum_montsqr_p521_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)

let BIGNUM_MONTSQR_P521_CORE_CORRECT = time prove
 (`!z x n pc2.
        nonoverlapping (word pc2,LENGTH bignum_montsqr_p521_core_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p521_core_mc /\
                  read PC s = word(pc2) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p521_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                      X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program. This is going to be used
     for preparing an initial state by 'overwriting' bignum_montsqr_p384_mc
     at pc. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p521_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 9) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p521_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 9) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P521_CORE_EQUIV BIGNUM_MONTSQR_P521_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P521_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P521_CORE_EXEC)
    (montsqr_p521_eqin,montsqr_p521_eqout));;


let BIGNUM_MONTSQR_P521_CORRECT = time prove
   (`!z x n pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p521_mc) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_mc /\
                  read PC s = word(pc + 12) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 12 + LENGTH bignum_montsqr_p521_core_mc) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
                      X14; X15; X16; X17; X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE MODIFIABLE_SIMD_REGS ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,

  ARM_SUB_LIST_OF_MC_TAC
    BIGNUM_MONTSQR_P521_CORE_CORRECT
    bignum_montsqr_p521_core_mc_def
    [fst BIGNUM_MONTSQR_P521_CORE_EXEC;
     fst BIGNUM_MONTSQR_P521_EXEC]);;

let BIGNUM_MONTSQR_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),48) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 9); (word_sub stackpointer (word 48),48)]
       [(word pc,LENGTH bignum_montsqr_p521_mc); (x,8 * 9)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = returnaddress /\
                (n < p_521
                 ==> bignum_from_memory (z,9) s =
                     (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)
    (REWRITE_RULE [fst BIGNUM_MONTSQR_P521_CORE_EXEC;
                   fst BIGNUM_MONTSQR_P521_EXEC]
     BIGNUM_MONTSQR_P521_CORRECT) in
  REWRITE_TAC[fst BIGNUM_MONTSQR_P521_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTSQR_P521_EXEC th
   `[X19;X20;X21;X22;X23;X24]` 48);;
