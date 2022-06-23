(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Montgomery ladder step in (X,Z)-projective coordinates for curve25519.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/curve25519.ml";;
needs "EC/formulary_xzprojective.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/curve25519/curve25519_ladderstep.o";;
 ****)

let curve25519_ladderstep_mc = define_assert_from_elf
  "curve25519_ladderstep_mc" "arm/curve25519/curve25519_ladderstep.o"
[
  0xa9bf7bf3;       (* arm_STP X19 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf57f4;       (* arm_STP X20 X21 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10603ff;       (* arm_SUB SP SP (rvalue (word 384)) *)
  0xaa0003f1;       (* arm_MOV X17 X0 *)
  0xaa0103f3;       (* arm_MOV X19 X1 *)
  0xaa0203f4;       (* arm_MOV X20 X2 *)
  0xaa0303f5;       (* arm_MOV X21 X3 *)
  0xa9441a85;       (* arm_LDP X5 X6 X20 (Immediate_Offset (iword (&64))) *)
  0xa9460e84;       (* arm_LDP X4 X3 X20 (Immediate_Offset (iword (&96))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9452287;       (* arm_LDP X7 X8 X20 (Immediate_Offset (iword (&80))) *)
  0xa9470e84;       (* arm_LDP X4 X3 X20 (Immediate_Offset (iword (&112))) *)
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
  0xa9400680;       (* arm_LDP X0 X1 X20 (Immediate_Offset (iword (&0))) *)
  0xa9421684;       (* arm_LDP X4 X5 X20 (Immediate_Offset (iword (&32))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa9410e82;       (* arm_LDP X2 X3 X20 (Immediate_Offset (iword (&16))) *)
  0xa9431e86;       (* arm_LDP X6 X7 X20 (Immediate_Offset (iword (&48))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xa90207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&32))) *)
  0xa9030fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0xa9401a85;       (* arm_LDP X5 X6 X20 (Immediate_Offset (iword (&0))) *)
  0xa9420e84;       (* arm_LDP X4 X3 X20 (Immediate_Offset (iword (&32))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412287;       (* arm_LDP X7 X8 X20 (Immediate_Offset (iword (&16))) *)
  0xa9430e84;       (* arm_LDP X4 X3 X20 (Immediate_Offset (iword (&48))) *)
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
  0xa9440680;       (* arm_LDP X0 X1 X20 (Immediate_Offset (iword (&64))) *)
  0xa9461684;       (* arm_LDP X4 X5 X20 (Immediate_Offset (iword (&96))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa9450e82;       (* arm_LDP X2 X3 X20 (Immediate_Offset (iword (&80))) *)
  0xa9471e86;       (* arm_LDP X6 X7 X20 (Immediate_Offset (iword (&112))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xa90007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9010fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&16))) *)
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
  0xa90823e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0xa9092be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0xf90053eb;       (* arm_STR X11 SP (Immediate_Offset (word 160)) *)
  0xeb1f02bf;       (* arm_CMP X21 XZR *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9460fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&96))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa94507e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&80))) *)
  0xa9470fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91307e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&304))) *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9420fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&256))) *)
  0xa94107e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&16))) *)
  0xa9430fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91107e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&272))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9461be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&96))) *)
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
  0xa94113e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&16))) *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0xa94113e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&16))) *)
  0xa94043ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&0))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa94603ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&96))) *)
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
  0xa9521fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&288))) *)
  0xa9532fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&304))) *)
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
  0xa9120fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0xa91317e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&304))) *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa94c17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&192))) *)
  0xeb040000;       (* arm_SUBS X0 X0 X4 *)
  0xfa050021;       (* arm_SBCS X1 X1 X5 *)
  0xa9490fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0xa94d1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&208))) *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0xfa070063;       (* arm_SBCS X3 X3 X7 *)
  0xf94053e4;       (* arm_LDR X4 SP (Immediate_Offset (word 160)) *)
  0xf94073e5;       (* arm_LDR X5 SP (Immediate_Offset (word 224)) *)
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
  0xa90207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&32))) *)
  0xa9030fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&48))) *)
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
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0x9a0600cd;       (* arm_ADC X13 X6 X6 *)
  0xd280026a;       (* arm_MOV X10 (rvalue (word 19)) *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9100fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&256))) *)
  0xa91117e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&272))) *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa94c17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&192))) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xa9490fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0xa94d1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&208))) *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xf94053e4;       (* arm_LDR X4 SP (Immediate_Offset (word 160)) *)
  0xf94073e5;       (* arm_LDR X5 SP (Immediate_Offset (word 224)) *)
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
  0xa90c07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xa90d0fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0xa9421fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&32))) *)
  0xa9432fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&48))) *)
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
  0xa9020fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0xa90317e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&48))) *)
  0xa9501be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa9520fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&288))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xa9530fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&304))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9141be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&320))) *)
  0xa91523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&336))) *)
  0xa94c1fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&192))) *)
  0xa94d2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&208))) *)
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
  0xa9000fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0xa90117e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&16))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa95423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&320))) *)
  0xa9552be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&336))) *)
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
  0xa95223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&288))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
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
  0xa95013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&256))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
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
  0xa95113e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&272))) *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
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
  0xa95113e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&272))) *)
  0xa95043ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&256))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa95203ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&288))) *)
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
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa9401a65;       (* arm_LDP X5 X6 X19 (Immediate_Offset (iword (&0))) *)
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
  0xa94313e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&48))) *)
  0xa9411a65;       (* arm_LDP X5 X6 X19 (Immediate_Offset (iword (&16))) *)
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
  0xa94313e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&48))) *)
  0xa94243ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&32))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa940026f;       (* arm_LDP X15 X0 X19 (Immediate_Offset (iword (&0))) *)
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
  0xa90223e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0xa9032be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0xa95413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&320))) *)
  0xa9461be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&96))) *)
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
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0xa94603ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&96))) *)
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
  0xa90623e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0xa9072be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  0xeb1f02bf;       (* arm_CMP X21 XZR *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9400fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0x9a820004;       (* arm_CSEL X4 X0 X2 Condition_EQ *)
  0x9a821006;       (* arm_CSEL X6 X0 X2 Condition_NE *)
  0x9a830025;       (* arm_CSEL X5 X1 X3 Condition_EQ *)
  0x9a831027;       (* arm_CSEL X7 X1 X3 Condition_NE *)
  0xa9001624;       (* arm_STP X4 X5 X17 (Immediate_Offset (iword (&0))) *)
  0xa9041e26;       (* arm_STP X6 X7 X17 (Immediate_Offset (iword (&64))) *)
  0xa94507e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&80))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0x9a820004;       (* arm_CSEL X4 X0 X2 Condition_EQ *)
  0x9a821006;       (* arm_CSEL X6 X0 X2 Condition_NE *)
  0x9a830025;       (* arm_CSEL X5 X1 X3 Condition_EQ *)
  0x9a831027;       (* arm_CSEL X7 X1 X3 Condition_NE *)
  0xa9011624;       (* arm_STP X4 X5 X17 (Immediate_Offset (iword (&16))) *)
  0xa9051e26;       (* arm_STP X6 X7 X17 (Immediate_Offset (iword (&80))) *)
  0xa94607e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xa9420fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0x9a820004;       (* arm_CSEL X4 X0 X2 Condition_EQ *)
  0x9a821006;       (* arm_CSEL X6 X0 X2 Condition_NE *)
  0x9a830025;       (* arm_CSEL X5 X1 X3 Condition_EQ *)
  0x9a831027;       (* arm_CSEL X7 X1 X3 Condition_NE *)
  0xa9021624;       (* arm_STP X4 X5 X17 (Immediate_Offset (iword (&32))) *)
  0xa9061e26;       (* arm_STP X6 X7 X17 (Immediate_Offset (iword (&96))) *)
  0xa94707e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&112))) *)
  0xa9430fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0x9a820004;       (* arm_CSEL X4 X0 X2 Condition_EQ *)
  0x9a821006;       (* arm_CSEL X6 X0 X2 Condition_NE *)
  0x9a830025;       (* arm_CSEL X5 X1 X3 Condition_EQ *)
  0x9a831027;       (* arm_CSEL X7 X1 X3 Condition_NE *)
  0xa9031624;       (* arm_STP X4 X5 X17 (Immediate_Offset (iword (&48))) *)
  0xa9071e26;       (* arm_STP X6 X7 X17 (Immediate_Offset (iword (&112))) *)
  0x910603ff;       (* arm_ADD SP SP (rvalue (word 384)) *)
  0xa8c157f4;       (* arm_LDP X20 X21 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c17bf3;       (* arm_LDP X19 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CURVE25519_LADDERSTEP_EXEC =
  ARM_MK_EXEC_RULE curve25519_ladderstep_mc;;

(* ------------------------------------------------------------------------- *)
(* Abbreviations used to state the specification.                            *)
(* ------------------------------------------------------------------------- *)

let p_25519 = define `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let curve25519 = define
 `curve25519 = (integer_mod_ring p_25519,&A_25519:int,&1:int)`;;

let curve25519_encode = new_definition
  `curve25519_encode = modular_encode(256,p_25519)`;;

let montgomery_ladderstep = new_definition
 `montgomery_ladderstep cparams b Q Qm Qn =
        if b then (montgomery_xzdiffadd cparams Q Qm Qn,
                   montgomery_xzdouble cparams Qn)
        else (montgomery_xzdouble cparams Qm,
              montgomery_xzdiffadd cparams Q Qm Qn)`;;

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
 ["x",[`X19`;`0`];
  "z",[`X19`;`32`];
  "xn",[`X20`;`0`];
  "zn",[`X20`;`32`];
  "xm",[`X20`;`64`];
  "zm",[`X20`;`96`];
  "sm",[`SP`;`0`];
  "sumx",[`SP`;`0`];
  "sn",[`SP`;`32`];
  "sumz",[`SP`;`32`];
  "dpro",[`SP`;`32`];
  "dm",[`SP`;`64`];
  "dubx",[`SP`;`64`];
  "dn",[`SP`;`96`];
  "dubz",[`SP`;`96`];
  "e",[`SP`;`96`];
  "dmsn",[`SP`;`128`];
  "dnsm",[`SP`;`192`];
  "spro",[`SP`;`192`];
  "s",[`SP`;`256`];
  "d",[`SP`;`288`];
  "p",[`SP`;`320`];
  "res0",[`X17`;`0`];
  "res1",[`X17`;`32`];
  "res2",[`X17`;`64`];
  "res3",[`X17`;`96`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 161 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (69--72) (69--72) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (145--147) (145--147) THEN
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
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (159--160) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (150--161) (150--161) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 114 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
        aligned 16 (read SP t) /\
        nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                  read PC s = pcin /\
                  read SP s = read SP t /\
                  read X19 s = read X19 t /\
                  read X20 s = read X20 t /\
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (98--100) (98--100) THEN
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
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (101--102) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (103--114) (103--114) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 147 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 5)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (69--72) (69--72) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 108 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n.
      read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (98--100) (98--100) THEN
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
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (101--102) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (103--106) (103--108) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 10 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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
  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC [3;4;7;8] (1--10) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 22 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC CURVE25519_LADDERSTEP_EXEC (1--22)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC [3;4;7;8;11] (1--11) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (12--14) (12--14) THEN
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
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (15--16) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (17--20) (17--22) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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
  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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
  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (11--14) (9--16) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 29 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 5)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 5)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC CURVE25519_LADDERSTEP_EXEC (1--29)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (19--21) (19--21) THEN
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
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (22--23) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (24--27) (24--29) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 32 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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
  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (22--24) (22--24) THEN
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
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (25--26) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_LADDERSTEP_EXEC (27--30) (27--32) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 10 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !b. read ZF t = b
     ==>
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
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
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Instances of muxpair_4.                                                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUXPAIR_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_ladderstep_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p4 n4 p1 n1 p2 n2.
     !b. read ZF t = b
     ==>
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x1664) (rr:int64,8 * 16) /\
      nonoverlapping (stackpointer,384) (rr,8 * 16)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read X19 s = read X19 t /\
                read X20 s = read X20 t /\
                read ZF s = b /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (if b then m else n) /\
                read(memory :> bytes(word_add (read p4 t) (word n4),8 * 4)) s =
                (if b then n else m))
        (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4);
                    memory :> bytes(word_add (read p4 t) (word n4),8 * 4)])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_STEPS_TAC CURVE25519_LADDERSTEP_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[COND_SWAP] THEN
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

let CURVE25519_LADDERSTEP_CORRECT = time prove
 (`!rr point P pp Pm Pn b pc stackpointer.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
     [(rr,128); (stackpointer,384)]
     [(word pc,0x1664); (point,64); (pp,128)] /\
    nonoverlapping (rr,128) (stackpointer,384)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
              read PC s = word(pc + 0xc) /\
              read SP s = stackpointer /\
              C_ARGUMENTS [rr; point; pp; b] s /\
              bignum_pair_from_memory (point,4) s = P /\
              bignum_quadruple_from_memory (pp,4) s = (Pm,Pn))
         (\s. read PC s = word (pc + 0x1654) /\
              !Q Qm Qn.
               P = paired curve25519_encode Q /\ SND Q = &1 /\
               (Pm,Pn) = quadrupled curve25519_encode (Qm,Qn)
               ==> bignum_quadruple_from_memory(rr,4) s =
                   quadrupled curve25519_encode
                    (montgomery_ladderstep curve25519 (~(b = word 0)) Q Qm Qn))
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                  X11; X12; X13; X14; X15; X16; X17; X19; X20; X21] ,,
       MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [memory :> bytes(rr,128);
                  memory :> bytes(stackpointer,384)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`rr:int64`; `point:int64`; `X:num`; `Z:num`;
    `pp:int64`; `Xn:num`; `Zn:num`; `Xm:num`; `Zm:num`;
    `b:int64`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ;
     bignum_pair_from_memory; bignum_quadruple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_SUB_4_TAC 4 ["dm"; "xm"; "zm"] THEN
  LOCAL_ADD_4_TAC 0 ["sn"; "xn"; "zn"] THEN
  LOCAL_SUB_4_TAC 0 ["dn"; "xn"; "zn"] THEN
  LOCAL_ADD_4_TAC 0 ["sm"; "xm"; "zm"] THEN

  LOCAL_MUL_5_TAC 0 ["dmsn"; "dm"; "sn"] THEN

  LOCAL_MUX_4_TAC 1 ["d"; "dm"; "dn"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_SUB_0]) THEN
  LOCAL_MUX_4_TAC 0 ["s"; "sm"; "sn"] THEN

  LOCAL_MUL_5_TAC 0 ["dnsm"; "sm"; "dn"] THEN
  LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN

  LOCAL_SUB5_4_TAC 0 ["dpro"; "dmsn"; "dnsm"] THEN
  LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
  LOCAL_ADD5_4_TAC 0 ["spro"; "dmsn"; "dnsm"] THEN
  LOCAL_SQR_4_TAC 0 ["dpro"; "dpro"] THEN

  LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
  LOCAL_SQR_P25519_TAC 0 ["sumx"; "spro"] THEN

  LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
  LOCAL_MUL_P25519_TAC 0 ["dubx"; "s"; "d"] THEN
  LOCAL_MUL_P25519_TAC 0 ["sumz"; "dpro"; "x"] THEN
  LOCAL_MUL_P25519_TAC 0 ["dubz"; "p"; "e"] THEN

  LOCAL_MUXPAIR_4_TAC 1 ["res0"; "res2"; "dubx"; "sumx"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_SUB_0]) THEN
  ABBREV_TAC
   `ares0 = read (memory :> bytes(rr,8 * 4)) s28` THEN
  LOCAL_MUXPAIR_4_TAC 0 ["res1"; "res3"; "dubz"; "sumz"] THEN
  ABBREV_TAC
   `ares1 = read (memory :> bytes(word_add rr (word 32),8 * 4)) s29` THEN

  (*** Clean up the final statement ***)

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[quadrupled; paired; PAIR_EQ] THEN
  REWRITE_TAC[curve25519_encode; modular_encode] THEN
  MAP_EVERY X_GEN_TAC
   [`x:int`; `z:int`; `xm:int`; `zm:int`; `xn:int`; `zn:int`] THEN
  ASM_CASES_TAC `z:int = &1` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
    (STRIP_ASSUME_TAC o MATCH_MP lemma)) THEN
  DISCARD_STATE_TAC "s29" THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`aligned a b`; `nonoverlapping_modulo a b c`] THEN

  (*** Eliminate range side-conditions ***)

  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN

  (*** Case split over b = 0 ***)

  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[quadrupled; paired; montgomery_ladderstep; modular_encode;
   montgomery_xzdouble; montgomery_xzdiffadd; curve25519; PAIR_EQ] THEN
  STRIP_TAC THEN REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; modular_encode] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ; GSYM INT_OF_NUM_EQ; nintlemma] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[GSYM INT_POW_REM; GSYM INT_MUL_REM] THEN

  (*** Systematize equational assumptions ***)

  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN

  (*** Do the algebra ***)

  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[A_25519] THEN INT_ARITH_TAC);;

let CURVE25519_LADDERSTEP_SUBROUTINE_CORRECT = time prove
 (`!rr point P pp Pm Pn b pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
     [(rr,128); (word_sub stackpointer (word 416),416)]
     [(word pc,0x1664); (point,64); (pp,128)] /\
    nonoverlapping (rr,128) (word_sub stackpointer (word 416),416)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_ladderstep_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [rr; point; pp; b] s /\
              bignum_pair_from_memory (point,4) s = P /\
              bignum_quadruple_from_memory (pp,4) s = (Pm,Pn))
         (\s. read PC s = returnaddress /\
              !Q Qm Qn.
               P = paired curve25519_encode Q /\ SND Q = &1 /\
               (Pm,Pn) = quadrupled curve25519_encode (Qm,Qn)
               ==> bignum_quadruple_from_memory(rr,4) s =
                   quadrupled curve25519_encode
                    (montgomery_ladderstep curve25519 (~(b = word 0)) Q Qm Qn))
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                  X11; X12; X13; X14; X15; X16; X17] ,,
       MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [memory :> bytes(rr,128);
                  memory :> bytes(word_sub stackpointer (word 416),416)])`,
  ARM_ADD_RETURN_STACK_TAC CURVE25519_LADDERSTEP_EXEC
   CURVE25519_LADDERSTEP_CORRECT
   `[X19;X20;X21;X30]` 416);;
