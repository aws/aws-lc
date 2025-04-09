(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Point doubling in Jacobian coordinates for NIST p521 curve.               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp521.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/p521/p521_jdouble_alt.o";;
 ****)

let p521_jdouble_alt_mc = define_assert_from_elf
  "p521_jdouble_alt_mc" "arm/p521/p521_jdouble_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf73fb;       (* arm_STP X27 X28 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10803ff;       (* arm_SUB SP SP (rvalue (word 512)) *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xaa0103fb;       (* arm_MOV X27 X1 *)
  0xa9490f62;       (* arm_LDP X2 X3 X27 (Immediate_Offset (iword (&144))) *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xa94a1764;       (* arm_LDP X4 X5 X27 (Immediate_Offset (iword (&160))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4d;       (* arm_UMULH X13 X2 X4 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xa94b1f66;       (* arm_LDP X6 X7 X27 (Immediate_Offset (iword (&176))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4e;       (* arm_UMULH X14 X2 X5 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0xa94c2768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&192))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c4f;       (* arm_UMULH X15 X2 X6 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c50;       (* arm_UMULH X16 X2 X7 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c51;       (* arm_UMULH X17 X2 X8 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c53;       (* arm_UMULH X19 X2 X9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a0294;       (* arm_ADC X20 X20 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd5;       (* arm_UMULH X21 X6 X7 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02d6;       (* arm_ADC X22 X22 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf7;       (* arm_UMULH X23 X7 X8 *)
  0xab0a02d6;       (* arm_ADDS X22 X22 X10 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0318;       (* arm_ADC X24 X24 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d19;       (* arm_UMULH X25 X8 X9 *)
  0xab0a0318;       (* arm_ADDS X24 X24 X10 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0xab0a016b;       (* arm_ADDS X11 X11 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a0000;       (* arm_ADC X0 X0 X10 *)
  0xf9406b61;       (* arm_LDR X1 X27 (Immediate_Offset (word 208)) *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x9b027c2a;       (* arm_MUL X10 X1 X2 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc27c2a;       (* arm_UMULH X10 X1 X2 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b047c2a;       (* arm_MUL X10 X1 X4 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc47c2a;       (* arm_UMULH X10 X1 X4 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b067c2a;       (* arm_MUL X10 X1 X6 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc67c2a;       (* arm_UMULH X10 X1 X6 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b087c2a;       (* arm_MUL X10 X1 X8 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc87c2a;       (* arm_UMULH X10 X1 X8 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0xd341fc24;       (* arm_LSR X4 X1 1 *)
  0x9b047c84;       (* arm_MUL X4 X4 X4 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b037c2a;       (* arm_MUL X10 X1 X3 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9bc37c2a;       (* arm_UMULH X10 X1 X3 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b057c2a;       (* arm_MUL X10 X1 X5 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc57c2a;       (* arm_UMULH X10 X1 X5 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b077c2a;       (* arm_MUL X10 X1 X7 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc77c2a;       (* arm_UMULH X10 X1 X7 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b097c2a;       (* arm_MUL X10 X1 X9 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0x9bc97c2a;       (* arm_UMULH X10 X1 X9 *)
  0x9a0a0084;       (* arm_ADC X4 X4 X10 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93d3268a;       (* arm_EXTR X10 X20 X19 9 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0x93d426aa;       (* arm_EXTR X10 X21 X20 9 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x93d526ca;       (* arm_EXTR X10 X22 X21 9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x93d626ea;       (* arm_EXTR X10 X23 X22 9 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x93d7270a;       (* arm_EXTR X10 X24 X23 9 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x93d8272a;       (* arm_EXTR X10 X25 X24 9 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x93d9240a;       (* arm_EXTR X10 X0 X25 9 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x93c0248a;       (* arm_EXTR X10 X4 X0 9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xb277da73;       (* arm_ORR X19 X19 (rvalue (word 18446744073709551104)) *)
  0xd349fc8a;       (* arm_LSR X10 X4 9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f0273;       (* arm_SBC X19 X19 XZR *)
  0x92402273;       (* arm_AND X19 X19 (rvalue (word 511)) *)
  0xa9002fe2;       (* arm_STP X2 X11 SP (Immediate_Offset (iword (&0))) *)
  0xa90137ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  0xa9023fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&32))) *)
  0xa90347f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&48))) *)
  0xf90023f3;       (* arm_STR X19 SP (Immediate_Offset (word 64)) *)
  0xa9448f62;       (* arm_LDP X2 X3 X27 (Immediate_Offset (iword (&72))) *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xa9459764;       (* arm_LDP X4 X5 X27 (Immediate_Offset (iword (&88))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4d;       (* arm_UMULH X13 X2 X4 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xa9469f66;       (* arm_LDP X6 X7 X27 (Immediate_Offset (iword (&104))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4e;       (* arm_UMULH X14 X2 X5 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0xa947a768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&120))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c4f;       (* arm_UMULH X15 X2 X6 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c50;       (* arm_UMULH X16 X2 X7 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c51;       (* arm_UMULH X17 X2 X8 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c53;       (* arm_UMULH X19 X2 X9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a0294;       (* arm_ADC X20 X20 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd5;       (* arm_UMULH X21 X6 X7 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02d6;       (* arm_ADC X22 X22 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf7;       (* arm_UMULH X23 X7 X8 *)
  0xab0a02d6;       (* arm_ADDS X22 X22 X10 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0318;       (* arm_ADC X24 X24 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d19;       (* arm_UMULH X25 X8 X9 *)
  0xab0a0318;       (* arm_ADDS X24 X24 X10 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0xab0a016b;       (* arm_ADDS X11 X11 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a0000;       (* arm_ADC X0 X0 X10 *)
  0xf9404761;       (* arm_LDR X1 X27 (Immediate_Offset (word 136)) *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x9b027c2a;       (* arm_MUL X10 X1 X2 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc27c2a;       (* arm_UMULH X10 X1 X2 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b047c2a;       (* arm_MUL X10 X1 X4 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc47c2a;       (* arm_UMULH X10 X1 X4 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b067c2a;       (* arm_MUL X10 X1 X6 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc67c2a;       (* arm_UMULH X10 X1 X6 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b087c2a;       (* arm_MUL X10 X1 X8 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc87c2a;       (* arm_UMULH X10 X1 X8 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0xd341fc24;       (* arm_LSR X4 X1 1 *)
  0x9b047c84;       (* arm_MUL X4 X4 X4 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b037c2a;       (* arm_MUL X10 X1 X3 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9bc37c2a;       (* arm_UMULH X10 X1 X3 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b057c2a;       (* arm_MUL X10 X1 X5 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc57c2a;       (* arm_UMULH X10 X1 X5 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b077c2a;       (* arm_MUL X10 X1 X7 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc77c2a;       (* arm_UMULH X10 X1 X7 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b097c2a;       (* arm_MUL X10 X1 X9 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0x9bc97c2a;       (* arm_UMULH X10 X1 X9 *)
  0x9a0a0084;       (* arm_ADC X4 X4 X10 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93d3268a;       (* arm_EXTR X10 X20 X19 9 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0x93d426aa;       (* arm_EXTR X10 X21 X20 9 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x93d526ca;       (* arm_EXTR X10 X22 X21 9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x93d626ea;       (* arm_EXTR X10 X23 X22 9 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x93d7270a;       (* arm_EXTR X10 X24 X23 9 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x93d8272a;       (* arm_EXTR X10 X25 X24 9 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x93d9240a;       (* arm_EXTR X10 X0 X25 9 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x93c0248a;       (* arm_EXTR X10 X4 X0 9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xb277da73;       (* arm_ORR X19 X19 (rvalue (word 18446744073709551104)) *)
  0xd349fc8a;       (* arm_LSR X10 X4 9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f0273;       (* arm_SBC X19 X19 XZR *)
  0x92402273;       (* arm_AND X19 X19 (rvalue (word 511)) *)
  0xa904afe2;       (* arm_STP X2 X11 SP (Immediate_Offset (iword (&72))) *)
  0xa905b7ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&88))) *)
  0xa906bfee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&104))) *)
  0xa907c7f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&120))) *)
  0xf90047f3;       (* arm_STR X19 SP (Immediate_Offset (word 136)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9401b65;       (* arm_LDP X5 X6 X27 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xba0400a5;       (* arm_ADCS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412367;       (* arm_LDP X7 X8 X27 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422b69;       (* arm_LDP X9 X10 X27 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xa943336b;       (* arm_LDP X11 X12 X27 (Immediate_Offset (iword (&48))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xba04016b;       (* arm_ADCS X11 X11 X4 *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf940236d;       (* arm_LDR X13 X27 (Immediate_Offset (word 64)) *)
  0xf94023e4;       (* arm_LDR X4 SP (Immediate_Offset (word 64)) *)
  0x9a0401ad;       (* arm_ADC X13 X13 X4 *)
  0xf10801a4;       (* arm_SUBS X4 X13 (rvalue (word 512)) *)
  0xda9f33e4;       (* arm_CSETM X4 Condition_CS *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x92770084;       (* arm_AND X4 X4 (rvalue (word 512)) *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda0401ad;       (* arm_SBC X13 X13 X4 *)
  0xa9169be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&360))) *)
  0xa917a3e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&376))) *)
  0xa918abe9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&392))) *)
  0xa919b3eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&408))) *)
  0xf900d7ed;       (* arm_STR X13 SP (Immediate_Offset (word 424)) *)
  0xa9401b65;       (* arm_LDP X5 X6 X27 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412367;       (* arm_LDP X7 X8 X27 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9422b69;       (* arm_LDP X9 X10 X27 (Immediate_Offset (iword (&32))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xa943336b;       (* arm_LDP X11 X12 X27 (Immediate_Offset (iword (&48))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf940236d;       (* arm_LDR X13 X27 (Immediate_Offset (word 64)) *)
  0xf94023e4;       (* arm_LDR X4 SP (Immediate_Offset (word 64)) *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa9121be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa91323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9142be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&320))) *)
  0xa91533eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&336))) *)
  0xf900b3ed;       (* arm_STR X13 SP (Immediate_Offset (word 352)) *)
  0xa95693e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&360))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0x9b057c6f;       (* arm_MUL X15 X3 X5 *)
  0x9bc57c70;       (* arm_UMULH X16 X3 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0x9bc87c74;       (* arm_UMULH X20 X3 X8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xa9542be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&320))) *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0x9bc97c75;       (* arm_UMULH X21 X3 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0x9bca7c76;       (* arm_UMULH X22 X3 X10 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xa95533eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&336))) *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0x9bcb7c77;       (* arm_UMULH X23 X3 X11 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xf940b3ed;       (* arm_LDR X13 SP (Immediate_Offset (word 352)) *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0x9bcc7c78;       (* arm_UMULH X24 X3 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0x9bcd7c61;       (* arm_UMULH X1 X3 X13 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0000;       (* arm_ADC X0 X0 X14 *)
  0xa90943ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&144))) *)
  0xa95793e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&376))) *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0210;       (* arm_ADC X16 X16 X14 *)
  0xa90a4ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&160))) *)
  0xa95893e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&392))) *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0273;       (* arm_ADC X19 X19 X14 *)
  0xa90b57f4;       (* arm_STP X20 X21 SP (Immediate_Offset (iword (&176))) *)
  0xa95993e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&408))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e02d6;       (* arm_ADDS X22 X22 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xa90c5ff6;       (* arm_STP X22 X23 SP (Immediate_Offset (iword (&192))) *)
  0xf940d7e3;       (* arm_LDR X3 SP (Immediate_Offset (word 424)) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0318;       (* arm_ADDS X24 X24 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xab0e0021;       (* arm_ADDS X1 X1 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0x93d8242e;       (* arm_EXTR X14 X1 X24 9 *)
  0xba0e00a5;       (* arm_ADCS X5 X5 X14 *)
  0x93c1240e;       (* arm_EXTR X14 X0 X1 9 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0x93c025ee;       (* arm_EXTR X14 X15 X0 9 *)
  0xba0e00e7;       (* arm_ADCS X7 X7 X14 *)
  0x93cf260e;       (* arm_EXTR X14 X16 X15 9 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0xa94b2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0x93d0262e;       (* arm_EXTR X14 X17 X16 9 *)
  0xba0e0129;       (* arm_ADCS X9 X9 X14 *)
  0x93d1266e;       (* arm_EXTR X14 X19 X17 9 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xa94c33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&192))) *)
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
  0xa9091be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa90a23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xf9006bed;       (* arm_STR X13 SP (Immediate_Offset (word 208)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9449b65;       (* arm_LDP X5 X6 X27 (Immediate_Offset (iword (&72))) *)
  0xa9490f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&144))) *)
  0xba0400a5;       (* arm_ADCS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa945a367;       (* arm_LDP X7 X8 X27 (Immediate_Offset (iword (&88))) *)
  0xa94a0f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&160))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa946ab69;       (* arm_LDP X9 X10 X27 (Immediate_Offset (iword (&104))) *)
  0xa94b0f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&176))) *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xa947b36b;       (* arm_LDP X11 X12 X27 (Immediate_Offset (iword (&120))) *)
  0xa94c0f64;       (* arm_LDP X4 X3 X27 (Immediate_Offset (iword (&192))) *)
  0xba04016b;       (* arm_ADCS X11 X11 X4 *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf940476d;       (* arm_LDR X13 X27 (Immediate_Offset (word 136)) *)
  0xf9406b64;       (* arm_LDR X4 X27 (Immediate_Offset (word 208)) *)
  0x9a0401ad;       (* arm_ADC X13 X13 X4 *)
  0xf10801a4;       (* arm_SUBS X4 X13 (rvalue (word 512)) *)
  0xda9f33e4;       (* arm_CSETM X4 Condition_CS *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x92770084;       (* arm_AND X4 X4 (rvalue (word 512)) *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda0401ad;       (* arm_SBC X13 X13 X4 *)
  0xa9169be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&360))) *)
  0xa917a3e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&376))) *)
  0xa918abe9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&392))) *)
  0xa919b3eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&408))) *)
  0xf900d7ed;       (* arm_STR X13 SP (Immediate_Offset (word 424)) *)
  0xa9490fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xa94a17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&160))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4d;       (* arm_UMULH X13 X2 X4 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xa94b1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&176))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4e;       (* arm_UMULH X14 X2 X5 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0xa94c27e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&192))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c4f;       (* arm_UMULH X15 X2 X6 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c50;       (* arm_UMULH X16 X2 X7 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c51;       (* arm_UMULH X17 X2 X8 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c53;       (* arm_UMULH X19 X2 X9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a0294;       (* arm_ADC X20 X20 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd5;       (* arm_UMULH X21 X6 X7 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02d6;       (* arm_ADC X22 X22 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf7;       (* arm_UMULH X23 X7 X8 *)
  0xab0a02d6;       (* arm_ADDS X22 X22 X10 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0318;       (* arm_ADC X24 X24 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d19;       (* arm_UMULH X25 X8 X9 *)
  0xab0a0318;       (* arm_ADDS X24 X24 X10 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0xab0a016b;       (* arm_ADDS X11 X11 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a0000;       (* arm_ADC X0 X0 X10 *)
  0xf9406be1;       (* arm_LDR X1 SP (Immediate_Offset (word 208)) *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x9b027c2a;       (* arm_MUL X10 X1 X2 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc27c2a;       (* arm_UMULH X10 X1 X2 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b047c2a;       (* arm_MUL X10 X1 X4 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc47c2a;       (* arm_UMULH X10 X1 X4 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b067c2a;       (* arm_MUL X10 X1 X6 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc67c2a;       (* arm_UMULH X10 X1 X6 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b087c2a;       (* arm_MUL X10 X1 X8 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc87c2a;       (* arm_UMULH X10 X1 X8 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0xd341fc24;       (* arm_LSR X4 X1 1 *)
  0x9b047c84;       (* arm_MUL X4 X4 X4 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b037c2a;       (* arm_MUL X10 X1 X3 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9bc37c2a;       (* arm_UMULH X10 X1 X3 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b057c2a;       (* arm_MUL X10 X1 X5 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc57c2a;       (* arm_UMULH X10 X1 X5 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b077c2a;       (* arm_MUL X10 X1 X7 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc77c2a;       (* arm_UMULH X10 X1 X7 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b097c2a;       (* arm_MUL X10 X1 X9 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0x9bc97c2a;       (* arm_UMULH X10 X1 X9 *)
  0x9a0a0084;       (* arm_ADC X4 X4 X10 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93d3268a;       (* arm_EXTR X10 X20 X19 9 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0x93d426aa;       (* arm_EXTR X10 X21 X20 9 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x93d526ca;       (* arm_EXTR X10 X22 X21 9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x93d626ea;       (* arm_EXTR X10 X23 X22 9 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x93d7270a;       (* arm_EXTR X10 X24 X23 9 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x93d8272a;       (* arm_EXTR X10 X25 X24 9 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x93d9240a;       (* arm_EXTR X10 X0 X25 9 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x93c0248a;       (* arm_EXTR X10 X4 X0 9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xb277da73;       (* arm_ORR X19 X19 (rvalue (word 18446744073709551104)) *)
  0xd349fc8a;       (* arm_LSR X10 X4 9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f0273;       (* arm_SBC X19 X19 XZR *)
  0x92402273;       (* arm_AND X19 X19 (rvalue (word 511)) *)
  0xa91b2fe2;       (* arm_STP X2 X11 SP (Immediate_Offset (iword (&432))) *)
  0xa91c37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&448))) *)
  0xa91d3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&464))) *)
  0xa91e47f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&480))) *)
  0xf900fbf3;       (* arm_STR X19 SP (Immediate_Offset (word 496)) *)
  0xa9401363;       (* arm_LDP X3 X4 X27 (Immediate_Offset (iword (&0))) *)
  0xa9449be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&72))) *)
  0x9b057c6f;       (* arm_MUL X15 X3 X5 *)
  0x9bc57c70;       (* arm_UMULH X16 X3 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xa945a3e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&88))) *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0x9bc87c74;       (* arm_UMULH X20 X3 X8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xa946abe9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&104))) *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0x9bc97c75;       (* arm_UMULH X21 X3 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0x9bca7c76;       (* arm_UMULH X22 X3 X10 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xa947b3eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&120))) *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0x9bcb7c77;       (* arm_UMULH X23 X3 X11 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xf94047ed;       (* arm_LDR X13 SP (Immediate_Offset (word 136)) *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0x9bcc7c78;       (* arm_UMULH X24 X3 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0x9bcd7c61;       (* arm_UMULH X1 X3 X13 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0000;       (* arm_ADC X0 X0 X14 *)
  0xa90dc3ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&216))) *)
  0xa9411363;       (* arm_LDP X3 X4 X27 (Immediate_Offset (iword (&16))) *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0210;       (* arm_ADC X16 X16 X14 *)
  0xa90ecff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&232))) *)
  0xa9421363;       (* arm_LDP X3 X4 X27 (Immediate_Offset (iword (&32))) *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0273;       (* arm_ADC X19 X19 X14 *)
  0xa90fd7f4;       (* arm_STP X20 X21 SP (Immediate_Offset (iword (&248))) *)
  0xa9431363;       (* arm_LDP X3 X4 X27 (Immediate_Offset (iword (&48))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e02d6;       (* arm_ADDS X22 X22 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xa910dff6;       (* arm_STP X22 X23 SP (Immediate_Offset (iword (&264))) *)
  0xf9402363;       (* arm_LDR X3 X27 (Immediate_Offset (word 64)) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0318;       (* arm_ADDS X24 X24 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xab0e0021;       (* arm_ADDS X1 X1 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xa94d9be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&216))) *)
  0x93d8242e;       (* arm_EXTR X14 X1 X24 9 *)
  0xab0e00a5;       (* arm_ADDS X5 X5 X14 *)
  0x93c1240e;       (* arm_EXTR X14 X0 X1 9 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0xa94ea3e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&232))) *)
  0x93c025ee;       (* arm_EXTR X14 X15 X0 9 *)
  0xba0e00e7;       (* arm_ADCS X7 X7 X14 *)
  0x93cf260e;       (* arm_EXTR X14 X16 X15 9 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0xa94fabe9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&248))) *)
  0x93d0262e;       (* arm_EXTR X14 X17 X16 9 *)
  0xba0e0129;       (* arm_ADCS X9 X9 X14 *)
  0x93d1266e;       (* arm_EXTR X14 X19 X17 9 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xa950b3eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&264))) *)
  0x93d3268e;       (* arm_EXTR X14 X20 X19 9 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x93d426ae;       (* arm_EXTR X14 X21 X20 9 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9240230d;       (* arm_AND X13 X24 (rvalue (word 511)) *)
  0xd349feae;       (* arm_LSR X14 X21 9 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xa90d9be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&216))) *)
  0xa90ea3e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&232))) *)
  0xa90fabe9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&248))) *)
  0xa910b3eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&264))) *)
  0xf9008fed;       (* arm_STR X13 SP (Immediate_Offset (word 280)) *)
  0xa9568fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&360))) *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xa95797e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&376))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4d;       (* arm_UMULH X13 X2 X4 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xa9589fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&392))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4e;       (* arm_UMULH X14 X2 X5 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0xa959a7e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&408))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c4f;       (* arm_UMULH X15 X2 X6 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c50;       (* arm_UMULH X16 X2 X7 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c51;       (* arm_UMULH X17 X2 X8 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c53;       (* arm_UMULH X19 X2 X9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a0294;       (* arm_ADC X20 X20 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd5;       (* arm_UMULH X21 X6 X7 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02d6;       (* arm_ADC X22 X22 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf7;       (* arm_UMULH X23 X7 X8 *)
  0xab0a02d6;       (* arm_ADDS X22 X22 X10 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0318;       (* arm_ADC X24 X24 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d19;       (* arm_UMULH X25 X8 X9 *)
  0xab0a0318;       (* arm_ADDS X24 X24 X10 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0xab0a016b;       (* arm_ADDS X11 X11 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a0000;       (* arm_ADC X0 X0 X10 *)
  0xf940d7e1;       (* arm_LDR X1 SP (Immediate_Offset (word 424)) *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x9b027c2a;       (* arm_MUL X10 X1 X2 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc27c2a;       (* arm_UMULH X10 X1 X2 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b047c2a;       (* arm_MUL X10 X1 X4 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc47c2a;       (* arm_UMULH X10 X1 X4 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b067c2a;       (* arm_MUL X10 X1 X6 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc67c2a;       (* arm_UMULH X10 X1 X6 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b087c2a;       (* arm_MUL X10 X1 X8 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc87c2a;       (* arm_UMULH X10 X1 X8 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0xd341fc24;       (* arm_LSR X4 X1 1 *)
  0x9b047c84;       (* arm_MUL X4 X4 X4 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b037c2a;       (* arm_MUL X10 X1 X3 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9bc37c2a;       (* arm_UMULH X10 X1 X3 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b057c2a;       (* arm_MUL X10 X1 X5 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc57c2a;       (* arm_UMULH X10 X1 X5 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b077c2a;       (* arm_MUL X10 X1 X7 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc77c2a;       (* arm_UMULH X10 X1 X7 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b097c2a;       (* arm_MUL X10 X1 X9 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0x9bc97c2a;       (* arm_UMULH X10 X1 X9 *)
  0x9a0a0084;       (* arm_ADC X4 X4 X10 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93d3268a;       (* arm_EXTR X10 X20 X19 9 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0x93d426aa;       (* arm_EXTR X10 X21 X20 9 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x93d526ca;       (* arm_EXTR X10 X22 X21 9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x93d626ea;       (* arm_EXTR X10 X23 X22 9 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x93d7270a;       (* arm_EXTR X10 X24 X23 9 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x93d8272a;       (* arm_EXTR X10 X25 X24 9 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x93d9240a;       (* arm_EXTR X10 X0 X25 9 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x93c0248a;       (* arm_EXTR X10 X4 X0 9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xb277da73;       (* arm_ORR X19 X19 (rvalue (word 18446744073709551104)) *)
  0xd349fc8a;       (* arm_LSR X10 X4 9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f0273;       (* arm_SBC X19 X19 XZR *)
  0x92402273;       (* arm_AND X19 X19 (rvalue (word 511)) *)
  0xa9122fe2;       (* arm_STP X2 X11 SP (Immediate_Offset (iword (&288))) *)
  0xa91337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&304))) *)
  0xa9143fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&320))) *)
  0xa91547f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&336))) *)
  0xf900b3f3;       (* arm_STR X19 SP (Immediate_Offset (word 352)) *)
  0xa94d9fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&216))) *)
  0xd2800181;       (* arm_MOV X1 (rvalue (word 12)) *)
  0x9b067c23;       (* arm_MUL X3 X1 X6 *)
  0x9b077c24;       (* arm_MUL X4 X1 X7 *)
  0x9bc67c26;       (* arm_UMULH X6 X1 X6 *)
  0xab060084;       (* arm_ADDS X4 X4 X6 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0xa94ea7e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&232))) *)
  0x9b087c25;       (* arm_MUL X5 X1 X8 *)
  0x9b097c26;       (* arm_MUL X6 X1 X9 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xa94fafea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&248))) *)
  0x9b0a7c27;       (* arm_MUL X7 X1 X10 *)
  0x9b0b7c28;       (* arm_MUL X8 X1 X11 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xba0900e7;       (* arm_ADCS X7 X7 X9 *)
  0x9bcb7c2b;       (* arm_UMULH X11 X1 X11 *)
  0xba0a0108;       (* arm_ADCS X8 X8 X10 *)
  0xa950b7ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&264))) *)
  0x9b0c7c29;       (* arm_MUL X9 X1 X12 *)
  0x9b0d7c2a;       (* arm_MUL X10 X1 X13 *)
  0x9bcc7c2c;       (* arm_UMULH X12 X1 X12 *)
  0xba0b0129;       (* arm_ADCS X9 X9 X11 *)
  0x9bcd7c2d;       (* arm_UMULH X13 X1 X13 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xf9408fee;       (* arm_LDR X14 SP (Immediate_Offset (word 280)) *)
  0x9b0e7c2b;       (* arm_MUL X11 X1 X14 *)
  0x9a0d016b;       (* arm_ADC X11 X11 X13 *)
  0xd2800121;       (* arm_MOV X1 (rvalue (word 9)) *)
  0xa95b57f4;       (* arm_LDP X20 X21 SP (Immediate_Offset (iword (&432))) *)
  0xaa3403f4;       (* arm_MVN X20 X20 *)
  0x9b147c20;       (* arm_MUL X0 X1 X20 *)
  0x9bd47c34;       (* arm_UMULH X20 X1 X20 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xaa3503f5;       (* arm_MVN X21 X21 *)
  0x9b157c20;       (* arm_MUL X0 X1 X21 *)
  0x9bd57c35;       (* arm_UMULH X21 X1 X21 *)
  0xba000084;       (* arm_ADCS X4 X4 X0 *)
  0xa95c5ff6;       (* arm_LDP X22 X23 SP (Immediate_Offset (iword (&448))) *)
  0xaa3603f6;       (* arm_MVN X22 X22 *)
  0x9b167c20;       (* arm_MUL X0 X1 X22 *)
  0x9bd67c36;       (* arm_UMULH X22 X1 X22 *)
  0xba0000a5;       (* arm_ADCS X5 X5 X0 *)
  0xaa3703f7;       (* arm_MVN X23 X23 *)
  0x9b177c20;       (* arm_MUL X0 X1 X23 *)
  0x9bd77c37;       (* arm_UMULH X23 X1 X23 *)
  0xba0000c6;       (* arm_ADCS X6 X6 X0 *)
  0xa95d4ff1;       (* arm_LDP X17 X19 SP (Immediate_Offset (iword (&464))) *)
  0xaa3103f1;       (* arm_MVN X17 X17 *)
  0x9b117c20;       (* arm_MUL X0 X1 X17 *)
  0x9bd17c31;       (* arm_UMULH X17 X1 X17 *)
  0xba0000e7;       (* arm_ADCS X7 X7 X0 *)
  0xaa3303f3;       (* arm_MVN X19 X19 *)
  0x9b137c20;       (* arm_MUL X0 X1 X19 *)
  0x9bd37c33;       (* arm_UMULH X19 X1 X19 *)
  0xba000108;       (* arm_ADCS X8 X8 X0 *)
  0xa95e43e2;       (* arm_LDP X2 X16 SP (Immediate_Offset (iword (&480))) *)
  0xaa2203e2;       (* arm_MVN X2 X2 *)
  0x9b027c20;       (* arm_MUL X0 X1 X2 *)
  0x9bc27c22;       (* arm_UMULH X2 X1 X2 *)
  0xba000129;       (* arm_ADCS X9 X9 X0 *)
  0xaa3003f0;       (* arm_MVN X16 X16 *)
  0x9b107c20;       (* arm_MUL X0 X1 X16 *)
  0x9bd07c30;       (* arm_UMULH X16 X1 X16 *)
  0xba00014a;       (* arm_ADCS X10 X10 X0 *)
  0xf940fbe0;       (* arm_LDR X0 SP (Immediate_Offset (word 496)) *)
  0xd2402000;       (* arm_EOR X0 X0 (rvalue (word 511)) *)
  0x9b007c20;       (* arm_MUL X0 X1 X0 *)
  0x9a00016b;       (* arm_ADC X11 X11 X0 *)
  0xab140084;       (* arm_ADDS X4 X4 X20 *)
  0xba1500a5;       (* arm_ADCS X5 X5 X21 *)
  0x8a05008f;       (* arm_AND X15 X4 X5 *)
  0xba1600c6;       (* arm_ADCS X6 X6 X22 *)
  0x8a0601ef;       (* arm_AND X15 X15 X6 *)
  0xba1700e7;       (* arm_ADCS X7 X7 X23 *)
  0x8a0701ef;       (* arm_AND X15 X15 X7 *)
  0xba110108;       (* arm_ADCS X8 X8 X17 *)
  0x8a0801ef;       (* arm_AND X15 X15 X8 *)
  0xba130129;       (* arm_ADCS X9 X9 X19 *)
  0x8a0901ef;       (* arm_AND X15 X15 X9 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0x9a10016b;       (* arm_ADC X11 X11 X16 *)
  0xd349fd6c;       (* arm_LSR X12 X11 9 *)
  0xb277d96b;       (* arm_ORR X11 X11 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba0c007f;       (* arm_ADCS XZR X3 X12 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xba0c0063;       (* arm_ADCS X3 X3 X12 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0x9240216b;       (* arm_AND X11 X11 (rvalue (word 511)) *)
  0xa91b13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&432))) *)
  0xa91c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&448))) *)
  0xa91d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&464))) *)
  0xa91e2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&480))) *)
  0xf900fbeb;       (* arm_STR X11 SP (Immediate_Offset (word 496)) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9542be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&320))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xa95533eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&336))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf940b3ed;       (* arm_LDR X13 SP (Immediate_Offset (word 352)) *)
  0xf94023e4;       (* arm_LDR X4 SP (Immediate_Offset (word 64)) *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa9169be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&360))) *)
  0xa917a3e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&376))) *)
  0xa918abe9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&392))) *)
  0xa919b3eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&408))) *)
  0xf900d7ed;       (* arm_STR X13 SP (Immediate_Offset (word 424)) *)
  0xa9448fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&72))) *)
  0x9b037c4b;       (* arm_MUL X11 X2 X3 *)
  0x9bc37c4c;       (* arm_UMULH X12 X2 X3 *)
  0xa94597e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&88))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4d;       (* arm_UMULH X13 X2 X4 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xa9469fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&104))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4e;       (* arm_UMULH X14 X2 X5 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0xa947a7e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&120))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c4f;       (* arm_UMULH X15 X2 X6 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c50;       (* arm_UMULH X16 X2 X7 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c51;       (* arm_UMULH X17 X2 X8 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c53;       (* arm_UMULH X19 X2 X9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a0294;       (* arm_ADC X20 X20 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd5;       (* arm_UMULH X21 X6 X7 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02d6;       (* arm_ADC X22 X22 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf7;       (* arm_UMULH X23 X7 X8 *)
  0xab0a02d6;       (* arm_ADDS X22 X22 X10 *)
  0x9a1f02f7;       (* arm_ADC X23 X23 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0318;       (* arm_ADC X24 X24 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d19;       (* arm_UMULH X25 X8 X9 *)
  0xab0a0318;       (* arm_ADDS X24 X24 X10 *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0xab0a016b;       (* arm_ADDS X11 X11 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a0000;       (* arm_ADC X0 X0 X10 *)
  0xf94047e1;       (* arm_LDR X1 SP (Immediate_Offset (word 136)) *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x9b027c2a;       (* arm_MUL X10 X1 X2 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9bc27c2a;       (* arm_UMULH X10 X1 X2 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b047c2a;       (* arm_MUL X10 X1 X4 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc47c2a;       (* arm_UMULH X10 X1 X4 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b067c2a;       (* arm_MUL X10 X1 X6 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc67c2a;       (* arm_UMULH X10 X1 X6 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b087c2a;       (* arm_MUL X10 X1 X8 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc87c2a;       (* arm_UMULH X10 X1 X8 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0xd341fc24;       (* arm_LSR X4 X1 1 *)
  0x9b047c84;       (* arm_MUL X4 X4 X4 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b037c2a;       (* arm_MUL X10 X1 X3 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9bc37c2a;       (* arm_UMULH X10 X1 X3 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b057c2a;       (* arm_MUL X10 X1 X5 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc57c2a;       (* arm_UMULH X10 X1 X5 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b077c2a;       (* arm_MUL X10 X1 X7 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc77c2a;       (* arm_UMULH X10 X1 X7 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b097c2a;       (* arm_MUL X10 X1 X9 *)
  0xba0a0000;       (* arm_ADCS X0 X0 X10 *)
  0x9bc97c2a;       (* arm_UMULH X10 X1 X9 *)
  0x9a0a0084;       (* arm_ADC X4 X4 X10 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93d3268a;       (* arm_EXTR X10 X20 X19 9 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0x93d426aa;       (* arm_EXTR X10 X21 X20 9 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x93d526ca;       (* arm_EXTR X10 X22 X21 9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x93d626ea;       (* arm_EXTR X10 X23 X22 9 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x93d7270a;       (* arm_EXTR X10 X24 X23 9 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x93d8272a;       (* arm_EXTR X10 X25 X24 9 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x93d9240a;       (* arm_EXTR X10 X0 X25 9 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x93c0248a;       (* arm_EXTR X10 X4 X0 9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0xb277da73;       (* arm_ORR X19 X19 (rvalue (word 18446744073709551104)) *)
  0xd349fc8a;       (* arm_LSR X10 X4 9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f0273;       (* arm_SBC X19 X19 XZR *)
  0x92402273;       (* arm_AND X19 X19 (rvalue (word 511)) *)
  0xa9122fe2;       (* arm_STP X2 X11 SP (Immediate_Offset (iword (&288))) *)
  0xa91337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&304))) *)
  0xa9143fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&320))) *)
  0xa91547f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&336))) *)
  0xf900b3f3;       (* arm_STR X19 SP (Immediate_Offset (word 352)) *)
  0xa9569be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&360))) *)
  0xa9448fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&72))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa957a3e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&376))) *)
  0xa9458fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&88))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa958abe9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&392))) *)
  0xa9468fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&104))) *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xa959b3eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&408))) *)
  0xa9478fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&120))) *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xf940d7ed;       (* arm_LDR X13 SP (Immediate_Offset (word 424)) *)
  0xf94047e4;       (* arm_LDR X4 SP (Immediate_Offset (word 136)) *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x924021ad;       (* arm_AND X13 X13 (rvalue (word 511)) *)
  0xa9091b45;       (* arm_STP X5 X6 X26 (Immediate_Offset (iword (&144))) *)
  0xa90a2347;       (* arm_STP X7 X8 X26 (Immediate_Offset (iword (&160))) *)
  0xa90b2b49;       (* arm_STP X9 X10 X26 (Immediate_Offset (iword (&176))) *)
  0xa90c334b;       (* arm_STP X11 X12 X26 (Immediate_Offset (iword (&192))) *)
  0xf9006b4d;       (* arm_STR X13 X26 (Immediate_Offset (word 208)) *)
  0xa95b13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&432))) *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0x9b057c6f;       (* arm_MUL X15 X3 X5 *)
  0x9bc57c70;       (* arm_UMULH X16 X3 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0x9bc87c74;       (* arm_UMULH X20 X3 X8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xa94b2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0x9bc97c75;       (* arm_UMULH X21 X3 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9b0a7c6e;       (* arm_MUL X14 X3 X10 *)
  0x9bca7c76;       (* arm_UMULH X22 X3 X10 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xa94c33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0x9bcb7c77;       (* arm_UMULH X23 X3 X11 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xf9406bed;       (* arm_LDR X13 SP (Immediate_Offset (word 208)) *)
  0x9b0c7c6e;       (* arm_MUL X14 X3 X12 *)
  0x9bcc7c78;       (* arm_UMULH X24 X3 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0x9bcd7c61;       (* arm_UMULH X1 X3 X13 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0000;       (* arm_ADC X0 X0 X14 *)
  0xa916c3ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&360))) *)
  0xa95c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&448))) *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0d7c6e;       (* arm_MUL X14 X3 X13 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcc7c6e;       (* arm_UMULH X14 X3 X12 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0c7c8e;       (* arm_MUL X14 X4 X12 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0210;       (* arm_ADC X16 X16 X14 *)
  0xa917cff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&376))) *)
  0xa95d13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&464))) *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0b7c6e;       (* arm_MUL X14 X3 X11 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bca7c6e;       (* arm_UMULH X14 X3 X10 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc97c8e;       (* arm_UMULH X14 X4 X9 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0e01ef;       (* arm_ADCS X15 X15 X14 *)
  0x9bcb7c8e;       (* arm_UMULH X14 X4 X11 *)
  0xba0e0210;       (* arm_ADCS X16 X16 X14 *)
  0x9bcc7c8e;       (* arm_UMULH X14 X4 X12 *)
  0xba0e0231;       (* arm_ADCS X17 X17 X14 *)
  0x9bcd7c8e;       (* arm_UMULH X14 X4 X13 *)
  0x9a0e0273;       (* arm_ADC X19 X19 X14 *)
  0xa918d7f4;       (* arm_STP X20 X21 SP (Immediate_Offset (iword (&392))) *)
  0xa95e13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&480))) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e02d6;       (* arm_ADDS X22 X22 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0318;       (* arm_ADCS X24 X24 X14 *)
  0x9b087c6e;       (* arm_MUL X14 X3 X8 *)
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b097c6e;       (* arm_MUL X14 X3 X9 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b087c8e;       (* arm_MUL X14 X4 X8 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9bc77c8e;       (* arm_UMULH X14 X4 X7 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xa919dff6;       (* arm_STP X22 X23 SP (Immediate_Offset (iword (&408))) *)
  0xf940fbe3;       (* arm_LDR X3 SP (Immediate_Offset (word 496)) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0xab0e0318;       (* arm_ADDS X24 X24 X14 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0xba0e0021;       (* arm_ADCS X1 X1 X14 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xab0e0021;       (* arm_ADDS X1 X1 X14 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xba0e0000;       (* arm_ADCS X0 X0 X14 *)
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
  0xa9569be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&360))) *)
  0x93d8242e;       (* arm_EXTR X14 X1 X24 9 *)
  0xab0e00a5;       (* arm_ADDS X5 X5 X14 *)
  0x93c1240e;       (* arm_EXTR X14 X0 X1 9 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0xa957a3e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&376))) *)
  0x93c025ee;       (* arm_EXTR X14 X15 X0 9 *)
  0xba0e00e7;       (* arm_ADCS X7 X7 X14 *)
  0x93cf260e;       (* arm_EXTR X14 X16 X15 9 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0xa958abe9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&392))) *)
  0x93d0262e;       (* arm_EXTR X14 X17 X16 9 *)
  0xba0e0129;       (* arm_ADCS X9 X9 X14 *)
  0x93d1266e;       (* arm_EXTR X14 X19 X17 9 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xa959b3eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&408))) *)
  0x93d3268e;       (* arm_EXTR X14 X20 X19 9 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0x93d426ae;       (* arm_EXTR X14 X21 X20 9 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9240230d;       (* arm_AND X13 X24 (rvalue (word 511)) *)
  0xd349feae;       (* arm_LSR X14 X21 9 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xa9169be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&360))) *)
  0xa917a3e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&376))) *)
  0xa918abe9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&392))) *)
  0xa919b3eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&408))) *)
  0xf900d7ed;       (* arm_STR X13 SP (Immediate_Offset (word 424)) *)
  0xa94d9fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&216))) *)
  0xd37ef4c3;       (* arm_LSL X3 X6 2 *)
  0x93c6f8e4;       (* arm_EXTR X4 X7 X6 62 *)
  0xa94ea7e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&232))) *)
  0x93c7f905;       (* arm_EXTR X5 X8 X7 62 *)
  0x93c8f926;       (* arm_EXTR X6 X9 X8 62 *)
  0xa94fafea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&248))) *)
  0x93c9f947;       (* arm_EXTR X7 X10 X9 62 *)
  0x93caf968;       (* arm_EXTR X8 X11 X10 62 *)
  0xa950b7ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&264))) *)
  0x93cbf989;       (* arm_EXTR X9 X12 X11 62 *)
  0x93ccf9aa;       (* arm_EXTR X10 X13 X12 62 *)
  0xf9408fee;       (* arm_LDR X14 SP (Immediate_Offset (word 280)) *)
  0x93cdf9cb;       (* arm_EXTR X11 X14 X13 62 *)
  0xa95b07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&432))) *)
  0xaa2003e0;       (* arm_MVN X0 X0 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xfa010084;       (* arm_SBCS X4 X4 X1 *)
  0xa95c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&448))) *)
  0xfa0000a5;       (* arm_SBCS X5 X5 X0 *)
  0x8a05008f;       (* arm_AND X15 X4 X5 *)
  0xfa0100c6;       (* arm_SBCS X6 X6 X1 *)
  0x8a0601ef;       (* arm_AND X15 X15 X6 *)
  0xa95d07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&464))) *)
  0xfa0000e7;       (* arm_SBCS X7 X7 X0 *)
  0x8a0701ef;       (* arm_AND X15 X15 X7 *)
  0xfa010108;       (* arm_SBCS X8 X8 X1 *)
  0x8a0801ef;       (* arm_AND X15 X15 X8 *)
  0xa95e07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&480))) *)
  0xfa000129;       (* arm_SBCS X9 X9 X0 *)
  0x8a0901ef;       (* arm_AND X15 X15 X9 *)
  0xfa01014a;       (* arm_SBCS X10 X10 X1 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xf940fbe0;       (* arm_LDR X0 SP (Immediate_Offset (word 496)) *)
  0xd2402000;       (* arm_EOR X0 X0 (rvalue (word 511)) *)
  0x9a00016b;       (* arm_ADC X11 X11 X0 *)
  0xd349fd6c;       (* arm_LSR X12 X11 9 *)
  0xb277d96b;       (* arm_ORR X11 X11 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba0c007f;       (* arm_ADCS XZR X3 X12 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xba0c0063;       (* arm_ADCS X3 X3 X12 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0x9240216b;       (* arm_AND X11 X11 (rvalue (word 511)) *)
  0xa9001343;       (* arm_STP X3 X4 X26 (Immediate_Offset (iword (&0))) *)
  0xa9011b45;       (* arm_STP X5 X6 X26 (Immediate_Offset (iword (&16))) *)
  0xa9022347;       (* arm_STP X7 X8 X26 (Immediate_Offset (iword (&32))) *)
  0xa9032b49;       (* arm_STP X9 X10 X26 (Immediate_Offset (iword (&48))) *)
  0xf900234b;       (* arm_STR X11 X26 (Immediate_Offset (word 64)) *)
  0xa9569fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&360))) *)
  0xd37ff8c3;       (* arm_LSL X3 X6 1 *)
  0xab060063;       (* arm_ADDS X3 X3 X6 *)
  0x93c6fce4;       (* arm_EXTR X4 X7 X6 63 *)
  0xba070084;       (* arm_ADCS X4 X4 X7 *)
  0xa957a7e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&376))) *)
  0x93c7fd05;       (* arm_EXTR X5 X8 X7 63 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x93c8fd26;       (* arm_EXTR X6 X9 X8 63 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0xa958afea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&392))) *)
  0x93c9fd47;       (* arm_EXTR X7 X10 X9 63 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0x93cafd68;       (* arm_EXTR X8 X11 X10 63 *)
  0xba0b0108;       (* arm_ADCS X8 X8 X11 *)
  0xa959b7ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&408))) *)
  0x93cbfd89;       (* arm_EXTR X9 X12 X11 63 *)
  0xba0c0129;       (* arm_ADCS X9 X9 X12 *)
  0x93ccfdaa;       (* arm_EXTR X10 X13 X12 63 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0xf940d7ee;       (* arm_LDR X14 SP (Immediate_Offset (word 424)) *)
  0x93cdfdcb;       (* arm_EXTR X11 X14 X13 63 *)
  0x9a0e016b;       (* arm_ADC X11 X11 X14 *)
  0xa95257f4;       (* arm_LDP X20 X21 SP (Immediate_Offset (iword (&288))) *)
  0xaa3403f4;       (* arm_MVN X20 X20 *)
  0xd37df280;       (* arm_LSL X0 X20 3 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xaa3503f5;       (* arm_MVN X21 X21 *)
  0x93d4f6a0;       (* arm_EXTR X0 X21 X20 61 *)
  0xba000084;       (* arm_ADCS X4 X4 X0 *)
  0xa9535ff6;       (* arm_LDP X22 X23 SP (Immediate_Offset (iword (&304))) *)
  0xaa3603f6;       (* arm_MVN X22 X22 *)
  0x93d5f6c0;       (* arm_EXTR X0 X22 X21 61 *)
  0xba0000a5;       (* arm_ADCS X5 X5 X0 *)
  0x8a05008f;       (* arm_AND X15 X4 X5 *)
  0xaa3703f7;       (* arm_MVN X23 X23 *)
  0x93d6f6e0;       (* arm_EXTR X0 X23 X22 61 *)
  0xba0000c6;       (* arm_ADCS X6 X6 X0 *)
  0x8a0601ef;       (* arm_AND X15 X15 X6 *)
  0xa95457f4;       (* arm_LDP X20 X21 SP (Immediate_Offset (iword (&320))) *)
  0xaa3403f4;       (* arm_MVN X20 X20 *)
  0x93d7f680;       (* arm_EXTR X0 X20 X23 61 *)
  0xba0000e7;       (* arm_ADCS X7 X7 X0 *)
  0x8a0701ef;       (* arm_AND X15 X15 X7 *)
  0xaa3503f5;       (* arm_MVN X21 X21 *)
  0x93d4f6a0;       (* arm_EXTR X0 X21 X20 61 *)
  0xba000108;       (* arm_ADCS X8 X8 X0 *)
  0x8a0801ef;       (* arm_AND X15 X15 X8 *)
  0xa9555ff6;       (* arm_LDP X22 X23 SP (Immediate_Offset (iword (&336))) *)
  0xaa3603f6;       (* arm_MVN X22 X22 *)
  0x93d5f6c0;       (* arm_EXTR X0 X22 X21 61 *)
  0xba000129;       (* arm_ADCS X9 X9 X0 *)
  0x8a0901ef;       (* arm_AND X15 X15 X9 *)
  0xaa3703f7;       (* arm_MVN X23 X23 *)
  0x93d6f6e0;       (* arm_EXTR X0 X23 X22 61 *)
  0xba00014a;       (* arm_ADCS X10 X10 X0 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xf940b3e0;       (* arm_LDR X0 SP (Immediate_Offset (word 352)) *)
  0xd2402000;       (* arm_EOR X0 X0 (rvalue (word 511)) *)
  0x93d7f400;       (* arm_EXTR X0 X0 X23 61 *)
  0x9a00016b;       (* arm_ADC X11 X11 X0 *)
  0xd349fd6c;       (* arm_LSR X12 X11 9 *)
  0xb277d96b;       (* arm_ORR X11 X11 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba0c007f;       (* arm_ADCS XZR X3 X12 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xba0c0063;       (* arm_ADCS X3 X3 X12 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0x9240216b;       (* arm_AND X11 X11 (rvalue (word 511)) *)
  0xa9049343;       (* arm_STP X3 X4 X26 (Immediate_Offset (iword (&72))) *)
  0xa9059b45;       (* arm_STP X5 X6 X26 (Immediate_Offset (iword (&88))) *)
  0xa906a347;       (* arm_STP X7 X8 X26 (Immediate_Offset (iword (&104))) *)
  0xa907ab49;       (* arm_STP X9 X10 X26 (Immediate_Offset (iword (&120))) *)
  0xf900474b;       (* arm_STR X11 X26 (Immediate_Offset (word 136)) *)
  0x910803ff;       (* arm_ADD SP SP (rvalue (word 512)) *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P521_JDOUBLE_ALT_EXEC = ARM_MK_EXEC_RULE p521_jdouble_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Common supporting definitions and lemmas for component proofs.            *)
(* ------------------------------------------------------------------------- *)

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

let lvs =
 ["x_1",[`X27`;`0`];
  "y_1",[`X27`;`72`];
  "z_1",[`X27`;`144`];
  "x_3",[`X26`;`0`];
  "y_3",[`X26`;`72`];
  "z_3",[`X26`;`144`];
  "z2",[`SP`;`0`];
  "y2",[`SP`;`72`];
  "x2p",[`SP`;`144`];
  "xy2",[`SP`;`216`];
  "y4",[`SP`;`288`];
  "t2",[`SP`;`288`];
  "dx2",[`SP`;`360`];
  "t1",[`SP`;`360`];
  "d",[`SP`;`432`];
  "x4p",[`SP`;`432`]];;

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 230 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              n)
         (\s. read PC s = pcout /\
              (n < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 9)) s = (n EXP 2) MOD p_521))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                     X11; X12; X13; X14; X15; X16; X17; X19; X20;
                     X21; X22; X23; X24; X25] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P521_JDOUBLE_ALT_EXEC (1--230)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** Simulate the initial squaring ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (1--195) (1--195) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`l0 = read X2 s195`;
    `l1 = read X11 s195`;
    `l2 = read X12 s195`;
    `l3 = read X13 s195`;
    `l4 = read X14 s195`;
    `l5 = read X15 s195`;
    `l6 = read X16 s195`;
    `l7 = read X17 s195`;
    `h0 = read X19 s195`;
    `h1 = read X20 s195`;
    `h2 = read X21 s195`;
    `h3 = read X22 s195`;
    `h4 = read X23 s195`;
    `h5 = read X24 s195`;
    `h6 = read X25 s195`;
    `h7 = read X0 s195`;
    `h8 = read X4 s195`]  THEN

  (*** Handle the two anomalous operations ***)

  UNDISCH_THEN
   `&2 pow 64 * &(bitval carry_s159) + &(val(sum_s159:int64)):real =
    &(val(n_8:int64)) + &(val n_8)`
  (MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
   MATCH_MP_TAC(ARITH_RULE `a < b ==> ~(b + s:num = a)`) THEN
   ASM BOUNDER_TAC[];
   REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
   DISCH_THEN SUBST_ALL_TAC] THEN

  UNDISCH_THEN
   `&2 pow 64 * &(val(mulhi_s176:int64)) + &(val(mullo_s176:int64)):real =
    &2 pow 63 * (&(val(n_8:int64)) + &(val n_8))`
    (MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 63 * (n + n) = 2 EXP 64 * n`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `e * h + l = e * x ==> e divides l /\ e * h + l = e * x`)) THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REWRITE_TAC[REWRITE_RULE[GSYM NOT_LE] VAL_BOUND_64] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 * x + 0 = 2 EXP 64 * y <=> x = y`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN

  (*** Show that the core squaring operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_of_wordlist[l0;l1;l2;l3;l4;l5;l6;l7] =
    n EXP 2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[EXP_2; ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      MATCH_MP_TAC LT_MULT2 THEN UNDISCH_TAC `n < p_521` THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the shift-and-add of high and lower parts ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC
   [198;200;202;204;206;208;210;212;215] (196--215) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (n EXP 2) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (n EXP 2) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n EXP 2) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`n EXP 2:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(n EXP 2) DIV 2 EXP 521 =
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
    (n EXP 2) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist [l0; l1; l2; l3; l4; l5; l6; l7]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
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
  SUBGOAL_THEN `carry_s215 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (216--224) (216--230) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
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
    SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; COND_SWAP; GSYM NOT_LE] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Instances of mul.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 373 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = b
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              b)
         (\s. read PC s = pcout /\
              (a < p_521 /\ b < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 9)) s = (a * b) MOD p_521))
         (MAYCHANGE [PC; X0; X1; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13; X14; X15; X16; X17; X19;
                     X20; X21; X22; X23; X24] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JDOUBLE_ALT_EXEC (1--373)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (1--334) (1--334) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`h0 = read X24 s334`;
    `h1 = read X1 s334`;
    `h2 = read X0 s334`;
    `h3 = read X15 s334`;
    `h4 = read X16 s334`;
    `h5 = read X17 s334`;
    `h6 = read X19 s334`;
    `h7 = read X20 s334`;
    `h8 = read X21 s334`] THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_of_wordlist
     [mullo_s3; sum_s35; sum_s74; sum_s111;
      sum_s150; sum_s187; sum_s226;  sum_s263] =
    a * b`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the shift-and-add of high and lower parts ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC
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
  SUBGOAL_THEN `(a * b) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`a * b:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (359--367) (359--373) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
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
    SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; COND_SWAP; GSYM NOT_LE] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Instances of add.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 37 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read PC s = pcout /\
              (m < p_521 /\ n < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 9)) s = (m + n) MOD p_521))
         (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the m < p_521 /\ n < p_521 assumption ***)

  ASM_CASES_TAC `m < p_521 /\ n < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JDOUBLE_ALT_EXEC (1--37)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial non-overflowing addition s = x + y + 1 ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC [4;5;8;9;12;13;16;17;20] (1--20) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s4;sum_s5;sum_s8;sum_s9;sum_s12;sum_s13;sum_s16;sum_s17;sum_s20] =
    m + n + 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[p_521] THEN REAL_ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The net comparison s >= 2^521 <=> x + y >= p_521 ***)

  ARM_STEPS_TAC P521_JDOUBLE_ALT_EXEC (21--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LT]) THEN
  SUBGOAL_THEN `512 <= val(sum_s20:int64) <=> p_521 <= m + n`
  SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS `512 <= (m + n + 1) DIV 2 EXP 512` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (23::(25--32)) (23--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 9`;
    `if p_521 <= m + n then &(m + n + 1) - &2 pow 521
     else &(m + n + 1) - &1:real`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `s = m + n + 1` THEN POP_ASSUM(K ALL_TAC) THEN EXPAND_TAC "s" THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 34 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
         (\s. read PC s = pcout /\
              (m < p_521 /\ n < p_521
               ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                     8 * 9)) s) = (&m - &n) rem &p_521))
         (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13] ,,
          MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** Initial subtraction x - y, comparison result ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC [3;4;7;8;11;12;15;16;19] (1--19) THEN

  SUBGOAL_THEN `carry_s19 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (20--28) (20--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Map things into the reals, doing case analysis over comparison ***)

  TRANS_TAC EQ_TRANS `if m < n then &m - &n + &p_521:int else &m - &n` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
   REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th];
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
   EXISTS_TAC `if m:num < n then --(&1):int else &0` THEN
   MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_521] THEN INT_ARITH_TAC] THEN

  (*** Hence show that we get the right result in 521 bits ***)

  CONV_TAC SYM_CONV THEN
  CONV_TAC(RAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`521`; `&0:real`] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of weakmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_WEAKMUL_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 362 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = b
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              a /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              b)
         (\s. read PC s = pcout /\
              (a < p_521 /\ b < p_521
               ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 9)) s < 2 * p_521 /\
                   (read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 9)) s == a * b) (mod p_521)))
         (MAYCHANGE [PC; X0; X1; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13; X14; X15; X16; X17; X19;
                     X20; X21; X22; X23; X24] ,,
          MAYCHANGE
           [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JDOUBLE_ALT_EXEC (1--362)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN

  (*** Simulate the initial multiplication ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (1--334) (1--334) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`h0 = read X24 s334`;
    `h1 = read X1 s334`;
    `h2 = read X0 s334`;
    `h3 = read X15 s334`;
    `h4 = read X16 s334`;
    `h5 = read X17 s334`;
    `h6 = read X19 s334`;
    `h7 = read X20 s334`;
    `h8 = read X21 s334`] THEN

  (*** Show that the core multiplication operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_of_wordlist
     [mullo_s3; sum_s35; sum_s74; sum_s111;
      sum_s150; sum_s187; sum_s226;  sum_s263] =
    a * b`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

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
  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN `(a * b) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`a * b:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
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

  (*** Now the simple addition of h + l as the result ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC
   [337; 339; 342; 344; 347; 349; 352; 354; 357] (335--362) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(MESON[]
   `x' < a /\ x = x' ==> x < a /\ x MOD p = x' MOD p`) THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`h < p_521`; `l <= p_521`] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    MAP_EVERY UNDISCH_TAC [`h < p_521`; `l <= p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
  REWRITE_TAC[REAL_OF_NUM_MOD] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instance (12,9) of cmsub (the only one used in this code).                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUBC9_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 107 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < 2 * p_521 /\ n <= p_521
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 9)) s) = (&12 * &m - &9 * &n) rem &p_521))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17;
                        X19; X20; X21; X22; X23] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JDOUBLE_ALT_EXEC (1--107)] THEN

  (*** Digitize and introduce the sign-flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
    [word_not n_0; word_not n_1; word_not n_2; word_not n_3; word_not n_4;
     word_not n_5; word_not n_6; word_not n_7; word_xor n_8 (word 0x1FF)]` THEN

  SUBGOAL_THEN `p_521 - n = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n + m:num = p ==> p - n = m`) THEN
    MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    SUBGOAL_THEN
     `&(val(word_xor (n_8:int64) (word 511))):real = &2 pow 9 - &1 - &(val n_8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_VAL_WORD_XOR];
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
      REAL_ARITH_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH
     `n':real = n ==> (n + c) - &2 * n' = c - n`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n <= p_521` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `n <= p ==> n DIV 2 EXP 512 <= p DIV 2 EXP 512`)) THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&12 * &m - &9 * &n) rem &p_521 =
    (&12 * &m + &9 * (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca = 12 * m + 9 * n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "n'"] THEN UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (1--86) (1--86) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s37; sum_s73; sum_s74; sum_s76;
      sum_s78; sum_s80; sum_s82; sum_s84; sum_s86] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "ca" THEN CONJ_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN EXPAND_TAC "n'" THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    UNDISCH_THEN `p_521 - n = n'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC P521_JDOUBLE_ALT_EXEC (87--89) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s86 9`;
    `d:int64 = word_or sum_s86 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s73 (word_and sum_s74 (word_and sum_s76
      (word_and sum_s78 (word_and sum_s80 (word_and sum_s82 sum_s84)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (90--92) (90--92) THEN
  SUBGOAL_THEN
   `carry_s92 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s37:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (93--101) (93--107) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s107" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s86:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s86:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s37; sum_s73; sum_s74; sum_s76; sum_s78; sum_s80; sum_s82; sum_s84] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s92`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s92" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s73; sum_s74; sum_s76; sum_s78; sum_s80; sum_s82; sum_s84] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s37:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s86:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s86:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s37:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of cmsub41 (there is only one).                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB41_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 57 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < 2 * p_521 /\ n <= p_521
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 9)) s) = (&4 * &m - &n) rem &p_521))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JDOUBLE_ALT_EXEC (1--57)] THEN

  (*** Digitize and introduce the sign-flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
    [word_not n_0; word_not n_1; word_not n_2; word_not n_3; word_not n_4;
     word_not n_5; word_not n_6; word_not n_7; word_xor n_8 (word 0x1FF)]` THEN

  SUBGOAL_THEN `p_521 - n = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n + m:num = p ==> p - n = m`) THEN
    MAP_EVERY EXPAND_TAC ["n"; "n'"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    SUBGOAL_THEN
     `&(val(word_xor (n_8:int64) (word 511))):real = &2 pow 9 - &1 - &(val n_8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_VAL_WORD_XOR];
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; p_521] THEN
      REAL_ARITH_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH
     `n':real = n ==> (n + c) - &2 * n' = c - n`) THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n <= p_521` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `n <= p ==> n DIV 2 EXP 512 <= p DIV 2 EXP 512`)) THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Now introduce the shifted version of m ***)

  ABBREV_TAC
   `m' = bignum_of_wordlist
     [word_shl m_0 2;
      word_subword ((word_join:int64->int64->int128) m_1 m_0) (62,64);
      word_subword ((word_join:int64->int64->int128) m_2 m_1) (62,64);
      word_subword ((word_join:int64->int64->int128) m_3 m_2) (62,64);
      word_subword ((word_join:int64->int64->int128) m_4 m_3) (62,64);
      word_subword ((word_join:int64->int64->int128) m_5 m_4) (62,64);
      word_subword ((word_join:int64->int64->int128) m_6 m_5) (62,64);
      word_subword ((word_join:int64->int64->int128) m_7 m_6) (62,64);
      word_subword ((word_join:int64->int64->int128) m_8 m_7) (62,64)]` THEN
  SUBGOAL_THEN `4 * m = m'` ASSUME_TAC THENL
   [SUBGOAL_THEN `m DIV 2 EXP 512 < 2 EXP 62` MP_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "m'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `62` th) THEN MP_TAC(SPEC `63` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN DISCH_TAC THEN
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
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&4 * &m - &n) rem &p_521 =
    (&4 * &m + (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca:num = m' + n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "m'"; "n'"] THEN
    UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC [17;18;20;22;25;27;30;32;36] (1--36) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s17; sum_s18; sum_s20; sum_s22;
      sum_s25; sum_s27; sum_s30; sum_s32; sum_s36] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED] THEN EXPAND_TAC "ca"] THEN
    UNDISCH_THEN `p_521 - n = n'` (K ALL_TAC) THEN
    UNDISCH_THEN `4 * m = m'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m'"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC P521_JDOUBLE_ALT_EXEC (37--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s36 9`;
    `d:int64 = word_or sum_s36 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s18 (word_and sum_s20 (word_and sum_s22
      (word_and sum_s25 (word_and sum_s27 (word_and sum_s30 sum_s32)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (40--42) (40--42) THEN
  SUBGOAL_THEN
   `carry_s42 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s17:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (43--51) (43--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s57" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s36:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s36:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s17; sum_s18; sum_s20; sum_s22; sum_s25; sum_s27; sum_s30; sum_s32] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s42`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s42" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s18; sum_s20; sum_s22; sum_s25; sum_s27; sum_s30; sum_s32] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s17:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s36:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s36:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s17:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances cmsub38 (there is only one).                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMSUB38_P521_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p521_jdouble_alt_mc 82 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x29f0) (word_add (read p3 t) (word n3),72) /\
    nonoverlapping (read X26 t,216) (stackpointer,512) /\
    nonoverlapping (read X27 t,216) (stackpointer,512)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X26 s = read X26 t /\
              read X27 s = read X27 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 9)) s =
              m /\
              read(memory :> bytes(word_add (read p2 t) (word n2),8 * 9)) s =
              n)
             (\s. read PC s = pcout /\
                  (m < 2 * p_521 /\ n <= p_521
                   ==> &(read(memory :> bytes(word_add (read p3 t) (word n3),
                            8 * 9)) s) = (&3 * &m - &8 *  &n) rem &p_521))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17;
                        X19; X20; X21; X22; X23] ,,
             MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 9)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the bound assumption for simplicity ***)

  ASM_CASES_TAC `m < 2 * p_521 /\ n <= p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC P521_JDOUBLE_ALT_EXEC (1--82)] THEN

  (*** Digitize and introduce the shifted and flipped version of n ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ABBREV_TAC
   `n' = bignum_of_wordlist
     [word_shl (word_not n_0) 3;
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_1) (word_not n_0)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_2) (word_not n_1)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_3) (word_not n_2)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_4) (word_not n_3)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_5) (word_not n_4)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_6) (word_not n_5)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_not n_7) (word_not n_6)) (61,64);
      word_subword ((word_join:int64->int64->int128)
                    (word_xor n_8 (word 0x1FF)) (word_not n_7)) (61,64)]` THEN
  SUBGOAL_THEN `8 * (p_521 - n) = n'` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `8 * n + m = 8 * p ==> 8 * (p - n) = m`) THEN
    SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
     [UNDISCH_TAC `n <= p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "n'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
     `(!i. P i) ==> (!i. i < 64 ==> P i)`)) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_SHL;
                BIT_WORD_NOT; BIT_WORD_XOR; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_521] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN

  (*** Now introduce the shifted version of m for 3 * m = 2 * m + m ***)

  ABBREV_TAC
   `m' = bignum_of_wordlist
     [word_shl m_0 1;
      word_subword ((word_join:int64->int64->int128) m_1 m_0) (63,64);
      word_subword ((word_join:int64->int64->int128) m_2 m_1) (63,64);
      word_subword ((word_join:int64->int64->int128) m_3 m_2) (63,64);
      word_subword ((word_join:int64->int64->int128) m_4 m_3) (63,64);
      word_subword ((word_join:int64->int64->int128) m_5 m_4) (63,64);
      word_subword ((word_join:int64->int64->int128) m_6 m_5) (63,64);
      word_subword ((word_join:int64->int64->int128) m_7 m_6) (63,64);
      word_subword ((word_join:int64->int64->int128) m_8 m_7) (63,64)]` THEN
  SUBGOAL_THEN `2 * m = m'` ASSUME_TAC THENL
   [SUBGOAL_THEN `m DIV 2 EXP 512 < 2 EXP 63` MP_TAC THENL
     [UNDISCH_TAC `m < 2 * p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM UPPER_BITS_ZERO]] THEN
    EXPAND_TAC "m'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `63`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
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
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&3 * &m - &8 *  &n) rem &p_521 =
    (&2 * &m + &m + &8 *  (&p_521 - &n)) rem &p_521`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; INT_OF_NUM_REM]] THEN

  (*** The basic multiply-add block = ca, then forget the components ***)

  ABBREV_TAC `ca = m' + m + n'` THEN
  SUBGOAL_THEN `ca < 2 EXP 527` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "m'"; "n'"] THEN
    UNDISCH_TAC `m < 2 * p_521` THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC
   [3;5;8;10;13;15;18;20;23;27;30;34;38;43;47;52;56;61] (1--61) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s27; sum_s30; sum_s34; sum_s38;
      sum_s43; sum_s47; sum_s52; sum_s56; sum_s61] = ca`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED] THEN EXPAND_TAC "ca"] THEN
    UNDISCH_THEN `8 * (p_521 - n) = n'` (K ALL_TAC) THEN
    UNDISCH_THEN `2 * m = m'` (K ALL_TAC) THEN
    MAP_EVERY EXPAND_TAC ["m"; "m'"; "n'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n':num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `ca MOD p_521 = (ca DIV 2 EXP 521 + ca MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `ca = 2 EXP 521 * ca DIV 2 EXP 521 + ca MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 521 < 2 EXP 64 /\ ca MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `ca < 2 EXP 527` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC P521_JDOUBLE_ALT_EXEC (62--64) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s61 9`;
    `d:int64 = word_or sum_s61 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s30 (word_and sum_s34 (word_and sum_s38
      (word_and sum_s43 (word_and sum_s47 (word_and sum_s52 sum_s56)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (65--67) (65--67) THEN
  SUBGOAL_THEN
   `carry_s67 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s27:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC P521_JDOUBLE_ALT_EXEC (68--76) (68--82) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s82" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s61:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s61:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s27; sum_s30; sum_s34; sum_s38; sum_s43; sum_s47; sum_s52; sum_s56] =
    ca MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s67`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s67" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s30; sum_s34; sum_s38; sum_s43; sum_s47; sum_s52; sum_s56] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s27:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s61:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s61:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s27:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = ca DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= ca MOD 2 EXP 521 + ca DIV 2 EXP 521 + 1 <=>
    p_521 <= ca DIV 2 EXP 521 + ca MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if ca DIV 2 EXP 521 + ca MOD 2 EXP 521 < p_521
     then &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521)
     else &(ca DIV 2 EXP 521 + ca MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ca < 2 EXP 527` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let unilemma0 = prove
 (`x = a MOD p_521 ==> x < p_521 /\ &x = &a rem &p_521`,
  REWRITE_TAC[INT_OF_NUM_REM; p_521] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_521 ==> x < p_521 /\ &x = a rem &p_521`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_521] THEN INT_ARITH_TAC);;

let weierstrass_of_jacobian_p521_double = prove
 (`!P1 P2 x1 y1 z1 x3 y3 z3.
        jacobian_double_unexceptional nistp521
         (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) =
        (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521)
       ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                (x1 rem &p_521,y1 rem &p_521,z1 rem &p_521) = P1
            ==> weierstrass_of_jacobian (integer_mod_ring p_521)
                  (x3 rem &p_521,y3 rem &p_521,z3 rem &p_521) =
                group_mul p521_group P1 P1`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[nistp521; P521_GROUP] THEN
  MATCH_MP_TAC WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P521] THEN
  ASM_REWRITE_TAC[jacobian_point; INTEGER_MOD_RING_CHAR;
                  INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[p_521; b_521] THEN CONV_TAC INT_REDUCE_CONV);;

let represents_p521 = new_definition
 `represents_p521 P (x,y,z) <=>
        x < p_521 /\ y < p_521 /\ z < p_521 /\
        weierstrass_of_jacobian (integer_mod_ring p_521)
         (tripled (modular_decode (576,p_521)) (x,y,z)) = P`;;

let P521_JDOUBLE_ALT_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,512))
            [(word pc,0x29f0); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x29f0)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
                  read PC s = word(pc + 0x18) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read PC s = word (pc + 0x29d4) /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X27] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(stackpointer,512)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `x:num`; `y:num`; `z:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SQR_P521_TAC 2 ["z2";"z_1"] THEN
  LOCAL_SQR_P521_TAC 0 ["y2";"y_1"] THEN
  LOCAL_ADD_P521_TAC 0 ["t1";"x_1";"z2"] THEN
  LOCAL_SUB_P521_TAC 0 ["t2";"x_1";"z2"] THEN
  LOCAL_MUL_P521_TAC 0 ["x2p";"t1";"t2"] THEN
  LOCAL_ADD_P521_TAC 0 ["t1";"y_1";"z_1"] THEN
  LOCAL_SQR_P521_TAC 0 ["x4p";"x2p"] THEN
  LOCAL_WEAKMUL_P521_TAC 0 ["xy2";"x_1";"y2"] THEN
  LOCAL_SQR_P521_TAC 0 ["t2";"t1"] THEN
  LOCAL_CMSUBC9_P521_TAC 0 ["d";"xy2";"x4p"] THEN
  LOCAL_SUB_P521_TAC 0 ["t1";"t2";"z2"] THEN
  LOCAL_SQR_P521_TAC 0 ["y4";"y2"] THEN
  LOCAL_SUB_P521_TAC 0 ["z_3";"t1";"y2"] THEN
  LOCAL_WEAKMUL_P521_TAC 0 ["dx2";"d";"x2p"] THEN
  LOCAL_CMSUB41_P521_TAC 0 ["x_3";"xy2";"d"] THEN
  LOCAL_CMSUB38_P521_TAC 0 ["y_3";"dx2";"y4"] THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s18" THEN
  DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN

  X_GEN_TAC `P:(int#int)option` THEN
  REWRITE_TAC[represents_p521; tripled] THEN
  REWRITE_TAC[modular_decode; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [REWRITE_TAC[p_521] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_521]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
    (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
     DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
     STRIP_TAC)]) THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_POW_2]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_MUL_REM]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o
    check(can (term_match [] `weierstrass_of_jacobian f j = p`) o concl)) THEN
  MATCH_MP_TAC weierstrass_of_jacobian_p521_double THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[jacobian_double_unexceptional; nistp521;
                  INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let P521_JDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 592),592))
            [(word pc,0x29f0); (p1,216); (p3,216)] /\
        nonoverlapping (p3,216) (word pc,0x29f0)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p521_jdouble_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,9) s = t1)
             (\s. read PC s = returnaddress /\
                  !P. represents_p521 P t1
                      ==> represents_p521 (group_mul p521_group P P)
                            (bignum_triple_from_memory(p3,9) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(p3,216);
                      memory :> bytes(word_sub stackpointer (word 592),592)])`,
  ARM_ADD_RETURN_STACK_TAC P521_JDOUBLE_ALT_EXEC
   P521_JDOUBLE_ALT_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28]`
   592);;
