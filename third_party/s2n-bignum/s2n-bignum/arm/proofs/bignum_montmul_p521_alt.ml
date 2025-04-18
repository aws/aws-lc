(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication modulo p_521.                                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_montmul_p521_alt.o";;
 ****)

let bignum_montmul_p521_alt_mc =
  define_assert_from_elf "bignum_montmul_p521_alt_mc" "arm/p521/bignum_montmul_p521_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&0))) *)
  0x9b057c6f;       (* arm_MUL X15 X3 X5 *)
  0x9bc57c70;       (* arm_UMULH X16 X3 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xa9412047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0x9bc87c74;       (* arm_UMULH X20 X3 X8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xa9422849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&32))) *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0x9bc97c75;       (* arm_UMULH X21 X3 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0x9bca7c76;       (* arm_UMULH X22 X3 X10 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xa943304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&48))) *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0x9bcb7c77;       (* arm_UMULH X23 X3 X11 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xf940204d;       (* arm_LDR X13 X2 (Immediate_Offset (word 64)) *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0x9bcc7c78;       (* arm_UMULH X24 X3 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0x9bcd7c79;       (* arm_UMULH X25 X3 X13 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9a9f37fa;       (* arm_CSET X26 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e0231;       (* arm_ADDS X17 X17 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e035a;       (* arm_ADC X26 X26 X14 *)
  0xa90043ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&0))) *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0231;       (* arm_ADDS X17 X17 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9a9f37ef;       (* arm_CSET X15 Condition_CS *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bcd7c6e;       (* arm_UMULH X14 X3 X13 *)
  0x9a0e01ef;       (* arm_ADC X15 X15 X14 *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0210;       (* arm_ADC X16 X16 X14 *)
  0xa9014ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&16))) *)
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9a9f37f1;       (* arm_CSET X17 Condition_CS *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e02b5;       (* arm_ADDS X21 X21 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcd7c6e;       (* arm_UMULH X14 X3 X13 *)
  0x9a0e0231;       (* arm_ADC X17 X17 X14 *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e02b5;       (* arm_ADDS X21 X21 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9a9f37f3;       (* arm_CSET X19 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e02d6;       (* arm_ADDS X22 X22 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0273;       (* arm_ADC X19 X19 X14 *)
  0xa90257f4;       (* arm_STP X20 X21 SP (Immediate_Offset (iword (&32))) *)
  0xa9431023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&48))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e02d6;       (* arm_ADDS X22 X22 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e02f7;       (* arm_ADDS X23 X23 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bcd7c6e;       (* arm_UMULH X14 X3 X13 *)
  0x9a0e0294;       (* arm_ADC X20 X20 X14 *)
  0x9b057c8e;       (* arm_MUL X14 X4 X5 *)
  0xab0e02f7;       (* arm_ADDS X23 X23 X14 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b077c8e;       (* arm_MUL X14 X4 X7 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b097c8e;       (* arm_MUL X14 X4 X9 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0b7c8e;       (* arm_MUL X14 X4 X11 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b0d7c8e;       (* arm_MUL X14 X4 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9a9f37f5;       (* arm_CSET X21 Condition_CS *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xab0e0318;       (* arm_ADDS X24 X24 X14 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bc87c8e;       (* arm_UMULH X14 X4 X8 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e02b5;       (* arm_ADC X21 X21 X14 *)
  0xa9035ff6;       (* arm_STP X22 X23 SP (Immediate_Offset (iword (&48))) *)
  0xf9402023;       (* arm_LDR X3 X1 (Immediate_Offset (word 64)) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0318;       (* arm_ADDS X24 X24 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e0339;       (* arm_ADCS X25 X25 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0x9a0e02b5;       (* arm_ADC X21 X21 X14 *)
  0x9bc57c6e;       (* arm_UMULH X14 X3 X5 *)
  0xab0e0339;       (* arm_ADDS X25 X25 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e035a;       (* arm_ADCS X26 X26 X14 *)
  0x9bc77c6e;       (* arm_UMULH X14 X3 X7 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bc97c6e;       (* arm_UMULH X14 X3 X9 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x9bcb7c6e;       (* arm_UMULH X14 X3 X11 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0x9a0e02b5;       (* arm_ADC X21 X21 X14 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9401be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0x93d8272e;       (* arm_EXTR X14 X25 X24 9 *)
  0xba0e00a5;       (* arm_ADCS X5 X5 X14 *)
  0x93d9274e;       (* arm_EXTR X14 X26 X25 9 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0xa94123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0x93da25ee;       (* arm_EXTR X14 X15 X26 9 *)
  0xba0e00e7;       (* arm_ADCS X7 X7 X14 *)
  0x93cf260e;       (* arm_EXTR X14 X16 X15 9 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0xa9422be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&32))) *)
  0x93d0262e;       (* arm_EXTR X14 X17 X16 9 *)
  0xba0e0129;       (* arm_ADCS X9 X9 X14 *)
  0x93d1266e;       (* arm_EXTR X14 X19 X17 9 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xa94333eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&48))) *)
  0x93d3268e;       (* arm_EXTR X14 X20 X19 9 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x93d426ae;       (* arm_EXTR X14 X21 X20 9 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0xb277db0d;       (* arm_ORR X13 X24 (rvalue (word 18446744073709551104)) *)
  0xd349feae;       (* arm_LSR X14 X21 9 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xd377d8ae;       (* arm_LSL X14 X5 9 *)
  0x93c5dcc5;       (* arm_EXTR X5 X6 X5 55 *)
  0x93c6dce6;       (* arm_EXTR X6 X7 X6 55 *)
  0x93c7dd07;       (* arm_EXTR X7 X8 X7 55 *)
  0x93c8dd28;       (* arm_EXTR X8 X9 X8 55 *)
  0xaa0e01ad;       (* arm_ORR X13 X13 X14 *)
  0x93c9dd49;       (* arm_EXTR X9 X10 X9 55 *)
  0x93cadd6a;       (* arm_EXTR X10 X11 X10 55 *)
  0x93cbdd8b;       (* arm_EXTR X11 X12 X11 55 *)
  0x93ccddac;       (* arm_EXTR X12 X13 X12 55 *)
  0xd377fdad;       (* arm_LSR X13 X13 55 *)
  0xa9001805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0xa903300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200d;       (* arm_STR X13 X0 (Immediate_Offset (word 64)) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_P521_ALT_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p521_alt_mc;;

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

let BIGNUM_MONTMUL_P521_ALT_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,64))
            [(word pc,0x62c); (z,8 * 9); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,0x62c)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_alt_mc /\
                  read PC s = word(pc + 0x14) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + 0x614) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                         memory :> bytes(stackpointer,64)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC BIGNUM_MONTMUL_P521_ALT_EXEC (1--384)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `bignum_from_memory (y,9) s0` THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_ALT_EXEC (1--334) (1--334) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`h0 = read X24 s334`;
    `h1 = read X25 s334`;
    `h2 = read X26 s334`;
    `h3 = read X15 s334`;
    `h4 = read X16 s334`;
    `h5 = read X17 s334`;
    `h6 = read X19 s334`;
    `h7 = read X20 s334`;
    `h8 = read X21 s334`] THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_from_memory(stackpointer,8) s334 =
    a * b`
  ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[EXP_2; ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      MATCH_MP_TAC LT_MULT2 THEN
      MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the shift-and-add of high and lower parts ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_ALT_EXEC
   [338;340;343;345;348;350;353;355;358] (335--358) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (a * b) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (a * b) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  SUBGOAL_THEN `(a * b) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`a * b:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    REWRITE_TAC[MOD_MULT_MOD2]] THEN
  SUBGOAL_THEN
   `(a * b) DIV 2 EXP 521 =
    bignum_of_wordlist
     [word_subword (word_join (h1:int64) h0:int128) (9,64);
      word_subword (word_join (h2:int64) h1:int128) (9,64);
      word_subword (word_join (h3:int64) h2:int128) (9,64);
      word_subword (word_join (h4:int64) h3:int128) (9,64);
      word_subword (word_join (h5:int64) h4:int128) (9,64);
      word_subword (word_join (h6:int64) h5:int128) (9,64);
      word_subword (word_join (h7:int64) h6:int128) (9,64);
      word_subword (word_join (h8:int64) h7:int128) (9,64);
      word_ushr h8 9] /\
    (a * b) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist
     [mullo_s3; sum_s35; sum_s74; sum_s111;
      sum_s150; sum_s187; sum_s226;  sum_s263]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_USHR] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
      ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) ==> 2 EXP 512 * h MOD 2 EXP 9 + x < 2 EXP 521`) THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH]];
    ALL_TAC] THEN

  (*** The net comparison h + l >= p_521 ***)

  SUBGOAL_THEN
   `&(val (word_or h0 (word 18446744073709551104))):real =
    (&2 pow 64 - &2 pow 9) + &(val(word_and h0 (word 511):int64))`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s358 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The  correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_ALT_EXEC (359--367) (359--384) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s359; sum_s360; sum_s361; sum_s362;
      sum_s363; sum_s364; sum_s365; sum_s366;
      word_and sum_s367 (word 511)] =
    (h + l) MOD p_521`
  MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`521`;
      `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
    REPEAT CONJ_TAC THENL
     [BOUNDER_TAC[];
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[GSYM NOT_LT] THEN ABBREV_TAC `bb <=> h + l < p_521` THEN
      MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
      REWRITE_TAC[REAL_OF_NUM_MOD] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ASM_SIMP_TAC[MOD_CASES; ARITH_RULE
       `h < p /\ l <= p ==> h + l < 2 * p`] THEN
      SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB;
               COND_SWAP; GSYM NOT_LE] THEN
      MESON_TAC[]];
   ALL_TAC] THEN

  (*** The final rotation for the Montgomery ingredient ***)

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
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC]);;

let BIGNUM_MONTMUL_P521_ALT_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 9) (word pc,0x62c) /\
        ALL (nonoverlapping (word_sub stackpointer (word 128),128))
            [(word pc,0x62c); (x,8 * 9); (y,8 * 9); (z,8 * 9)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = returnaddress /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 128),128)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P521_ALT_EXEC BIGNUM_MONTMUL_P521_ALT_CORRECT
   `[X19;X20;X21;X22;X23;X24;X25;X26]` 128);;
