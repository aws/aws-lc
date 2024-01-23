(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 16x16 -> 32 squaring, using Karatsuba reduction.                          *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_ksqr_16_32.o";;
 ****)

let bignum_ksqr_16_32_mc = define_assert_from_elf "bignum_ksqr_16_32_mc" "arm/fastmul/bignum_ksqr_16_32.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf9;       (* arm_STP X25 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa0003f7;       (* arm_MOV X23 X0 *)
  0xaa0103f8;       (* arm_MOV X24 X1 *)
  0xaa0203f9;       (* arm_MOV X25 X2 *)
  0x940000a9;       (* arm_BL (word 676) *)
  0xa9402f0a;       (* arm_LDP X10 X11 X24 (Immediate_Offset (iword (&0))) *)
  0xa9442708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&64))) *)
  0xeb08014a;       (* arm_SUBS X10 X10 X8 *)
  0xfa09016b;       (* arm_SBCS X11 X11 X9 *)
  0xa941370c;       (* arm_LDP X12 X13 X24 (Immediate_Offset (iword (&16))) *)
  0xa9452708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&80))) *)
  0xfa08018c;       (* arm_SBCS X12 X12 X8 *)
  0xfa0901ad;       (* arm_SBCS X13 X13 X9 *)
  0xa9423f0e;       (* arm_LDP X14 X15 X24 (Immediate_Offset (iword (&32))) *)
  0xa9462708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&96))) *)
  0xfa0801ce;       (* arm_SBCS X14 X14 X8 *)
  0xfa0901ef;       (* arm_SBCS X15 X15 X9 *)
  0xa9434710;       (* arm_LDP X16 X17 X24 (Immediate_Offset (iword (&48))) *)
  0xa9472708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&112))) *)
  0xfa080210;       (* arm_SBCS X16 X16 X8 *)
  0xfa090231;       (* arm_SBCS X17 X17 X9 *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xab13027f;       (* arm_CMN X19 X19 *)
  0xca13014a;       (* arm_EOR X10 X10 X19 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca13016b;       (* arm_EOR X11 X11 X19 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa9002f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&0))) *)
  0xca13018c;       (* arm_EOR X12 X12 X19 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xca1301ad;       (* arm_EOR X13 X13 X19 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xa901372c;       (* arm_STP X12 X13 X25 (Immediate_Offset (iword (&16))) *)
  0xca1301ce;       (* arm_EOR X14 X14 X19 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xca1301ef;       (* arm_EOR X15 X15 X19 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xa9023f2e;       (* arm_STP X14 X15 X25 (Immediate_Offset (iword (&32))) *)
  0xca130210;       (* arm_EOR X16 X16 X19 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xca130231;       (* arm_EOR X17 X17 X19 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xa9034730;       (* arm_STP X16 X17 X25 (Immediate_Offset (iword (&48))) *)
  0x910202e0;       (* arm_ADD X0 X23 (rvalue (word 128)) *)
  0x91010301;       (* arm_ADD X1 X24 (rvalue (word 64)) *)
  0x94000080;       (* arm_BL (word 512) *)
  0xa9482eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&128))) *)
  0xa94436ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&64))) *)
  0xab0c014a;       (* arm_ADDS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9082eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&128))) *)
  0xa9492eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94536ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&80))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9092eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94a2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&160))) *)
  0xa94636ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&96))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90a2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&160))) *)
  0xa94b2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&176))) *)
  0xa94736ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&112))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90b2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&176))) *)
  0xa94c2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90c2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xa94d2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90d2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xa94e2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90e2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xa94f2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90f2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0x91010320;       (* arm_ADD X0 X25 (rvalue (word 64)) *)
  0xaa1903e1;       (* arm_MOV X1 X25 *)
  0x94000059;       (* arm_BL (word 356) *)
  0xa94006e0;       (* arm_LDP X0 X1 X23 (Immediate_Offset (iword (&0))) *)
  0xa94846f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&128))) *)
  0xab100000;       (* arm_ADDS X0 X0 X16 *)
  0xba110021;       (* arm_ADCS X1 X1 X17 *)
  0xa9410ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&16))) *)
  0xa94946f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&144))) *)
  0xba100042;       (* arm_ADCS X2 X2 X16 *)
  0xba110063;       (* arm_ADCS X3 X3 X17 *)
  0xa94216e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&32))) *)
  0xa94a46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&160))) *)
  0xba100084;       (* arm_ADCS X4 X4 X16 *)
  0xba1100a5;       (* arm_ADCS X5 X5 X17 *)
  0xa9431ee6;       (* arm_LDP X6 X7 X23 (Immediate_Offset (iword (&48))) *)
  0xa94b46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&176))) *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0xba1100e7;       (* arm_ADCS X7 X7 X17 *)
  0xa94826e8;       (* arm_LDP X8 X9 X23 (Immediate_Offset (iword (&128))) *)
  0xa94c46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&192))) *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba110129;       (* arm_ADCS X9 X9 X17 *)
  0xa9492eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94d46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&208))) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xa94a36ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&160))) *)
  0xa94e46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&224))) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xa94b3eee;       (* arm_LDP X14 X15 X23 (Immediate_Offset (iword (&176))) *)
  0xa94f46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&240))) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0xa9444730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&64))) *)
  0xeb100000;       (* arm_SUBS X0 X0 X16 *)
  0xfa110021;       (* arm_SBCS X1 X1 X17 *)
  0xa90406e0;       (* arm_STP X0 X1 X23 (Immediate_Offset (iword (&64))) *)
  0xa9454730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&80))) *)
  0xfa100042;       (* arm_SBCS X2 X2 X16 *)
  0xfa110063;       (* arm_SBCS X3 X3 X17 *)
  0xa9050ee2;       (* arm_STP X2 X3 X23 (Immediate_Offset (iword (&80))) *)
  0xa9464730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&96))) *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xfa1100a5;       (* arm_SBCS X5 X5 X17 *)
  0xa90616e4;       (* arm_STP X4 X5 X23 (Immediate_Offset (iword (&96))) *)
  0xa9474730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&112))) *)
  0xfa1000c6;       (* arm_SBCS X6 X6 X16 *)
  0xfa1100e7;       (* arm_SBCS X7 X7 X17 *)
  0xa9071ee6;       (* arm_STP X6 X7 X23 (Immediate_Offset (iword (&112))) *)
  0xa9484730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&128))) *)
  0xfa100108;       (* arm_SBCS X8 X8 X16 *)
  0xfa110129;       (* arm_SBCS X9 X9 X17 *)
  0xa90826e8;       (* arm_STP X8 X9 X23 (Immediate_Offset (iword (&128))) *)
  0xa9494730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&144))) *)
  0xfa10014a;       (* arm_SBCS X10 X10 X16 *)
  0xfa11016b;       (* arm_SBCS X11 X11 X17 *)
  0xa9092eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94a4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&160))) *)
  0xfa10018c;       (* arm_SBCS X12 X12 X16 *)
  0xfa1101ad;       (* arm_SBCS X13 X13 X17 *)
  0xa90a36ec;       (* arm_STP X12 X13 X23 (Immediate_Offset (iword (&160))) *)
  0xa94b4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&176))) *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xfa1101ef;       (* arm_SBCS X15 X15 X17 *)
  0xa90b3eee;       (* arm_STP X14 X15 X23 (Immediate_Offset (iword (&176))) *)
  0xfa1f0318;       (* arm_SBCS X24 X24 XZR *)
  0xda9f23f9;       (* arm_CSETM X25 Condition_CC *)
  0xa94c2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xab18014a;       (* arm_ADDS X10 X10 X24 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90c2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xa94d2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90d2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xa94e2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90e2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xa94f2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90f2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xa8c17bf9;       (* arm_LDP X25 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x9b047c51;       (* arm_MUL X17 X2 X4 *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x9bc47c54;       (* arm_UMULH X20 X2 X4 *)
  0xeb030055;       (* arm_SUBS X21 X2 X3 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x9bc57c75;       (* arm_UMULH X21 X3 X5 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x9b027c4c;       (* arm_MUL X12 X2 X2 *)
  0x9b037c6d;       (* arm_MUL X13 X3 X3 *)
  0x9b037c4f;       (* arm_MUL X15 X2 X3 *)
  0x9bc27c4b;       (* arm_UMULH X11 X2 X2 *)
  0x9bc37c6e;       (* arm_UMULH X14 X3 X3 *)
  0x9bc37c50;       (* arm_UMULH X16 X2 X3 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9002c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&0))) *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9b057cad;       (* arm_MUL X13 X5 X5 *)
  0x9b057c8f;       (* arm_MUL X15 X4 X5 *)
  0x9bc47c8b;       (* arm_UMULH X11 X4 X4 *)
  0x9bc57cae;       (* arm_UMULH X14 X5 X5 *)
  0x9bc57c90;       (* arm_UMULH X16 X4 X5 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xa9022c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa903380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&48))) *)
  0x9b087cd1;       (* arm_MUL X17 X6 X8 *)
  0x9b097cee;       (* arm_MUL X14 X7 X9 *)
  0x9bc87cd4;       (* arm_UMULH X20 X6 X8 *)
  0xeb0700d5;       (* arm_SUBS X21 X6 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb08012c;       (* arm_SUBS X12 X9 X8 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x9bc97cf5;       (* arm_UMULH X21 X7 X9 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x9b067ccc;       (* arm_MUL X12 X6 X6 *)
  0x9b077ced;       (* arm_MUL X13 X7 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67ccb;       (* arm_UMULH X11 X6 X6 *)
  0x9bc77cee;       (* arm_UMULH X14 X7 X7 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9042c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&64))) *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa9054c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&80))) *)
  0x9b087d0c;       (* arm_MUL X12 X8 X8 *)
  0x9b097d2d;       (* arm_MUL X13 X9 X9 *)
  0x9b097d0f;       (* arm_MUL X15 X8 X9 *)
  0x9bc87d0b;       (* arm_UMULH X11 X8 X8 *)
  0x9bc97d2e;       (* arm_UMULH X14 X9 X9 *)
  0x9bc97d10;       (* arm_UMULH X16 X8 X9 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xa9062c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&96))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa907380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&112))) *)
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
  0xab0a014a;       (* arm_ADDS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xa9420c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&32))) *)
  0xab02014a;       (* arm_ADDS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa9430c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&48))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xa903340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xa9440c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&64))) *)
  0xba0201ce;       (* arm_ADCS X14 X14 X2 *)
  0xba0301ef;       (* arm_ADCS X15 X15 X3 *)
  0xa9043c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&64))) *)
  0xa9450c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&80))) *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba030231;       (* arm_ADCS X17 X17 X3 *)
  0xa9054410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&80))) *)
  0xa9460c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xba130042;       (* arm_ADCS X2 X2 X19 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xa9060c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xa9470c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9070c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_KSQR_16_32_EXEC = ARM_MK_EXEC_RULE bignum_ksqr_16_32_mc;;

(* ------------------------------------------------------------------------- *)
(* First of all the correctness lemma for the embedded bignum_sqr_8_16       *)
(* ------------------------------------------------------------------------- *)

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

let ADK_48_TAC =
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
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;;

let BIGNUM_KSQR_16_32_LEMMA = prove
 (`!z x a pc returnaddress.
      nonoverlapping (word pc,0x74c) (z,8 * 16)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word(pc + 0x0)) bignum_ksqr_16_32_mc /\
                read PC s = word(pc + 0x2c0) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,8) s = a)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
            MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
            MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_EXEC
   [5;6;13;18;19;21;22;23;24;25;27;28;29;30;31;32;33;34;35;36;37;
    41;42;43;44;45;46;48;49;50;51;52;54;55;56;60;61;62;63;64;65;
    66;67;69;70]
   (1--71) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2 =
    bignum_of_wordlist [mullo_s35; sum_s44; sum_s48; sum_s49;
                        sum_s66; sum_s67; sum_s69; sum_s70]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_EXEC
   [72;73;80;85;86;88;89;90;91;92;94;95;96;97;98;99;100;101;102;103;
    104;108;109;110;111;112;113;115;116;117;118;119;121;122;123;127;
    128;129;130;131;132;133;134;136;137]
   (72--138) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2 =
    bignum_of_wordlist [mullo_s102;sum_s111;sum_s115;sum_s116;
                        sum_s133;sum_s134;sum_s136;sum_s137]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_EXEC
   [139;140;141;142;144;146;148;150;151;152;153;154;155;156;157;
    158;159;160;161;167;172;174;175;181;186;188;189;190;191;192;
    193;199;204;206;207;208;214;219;221;222;223;224;225;231;236;
    238;239;240;241;247;252;254;255;256;257]
   (139--257) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] *
    bignum_of_wordlist [x_4;x_5;x_6;x_7] =
    bignum_of_wordlist
     [mullo_s139; sum_s186; sum_s219; sum_s252;
      sum_s254; sum_s255; sum_s256; sum_s257]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_EXEC (258--290) (258--291) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s291" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`1024`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `(&a:real) pow 2 =
    &(bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2) +
    &2 pow 512 * &(bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2) +
    &2 pow 257 * &(bignum_of_wordlist [x_0;x_1;x_2;x_3] *
                   bignum_of_wordlist [x_4;x_5;x_6;x_7])`
  SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KSQR_16_32_LEMMA_TAC =
  ARM_SUBROUTINE_SIM_TAC
    (bignum_ksqr_16_32_mc,BIGNUM_KSQR_16_32_EXEC,
     0x0,bignum_ksqr_16_32_mc,BIGNUM_KSQR_16_32_LEMMA)
    [`read X0 s`; `read X1 s`;
     `bignum_from_memory (read X1 s,8) s`;
     `pc:num`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* Now the main proof.                                                       *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_KSQR_16_32_CORRECT = prove
 (`!z x a t pc.
        nonoverlapping (z,8 * 32) (t,8 * 24) /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 24)]
         [(word pc,0x74c); (x,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_ksqr_16_32_mc /\
                   read PC s = word(pc + 0x10) /\
                   C_ARGUMENTS [z; x; t] s /\
                   bignum_from_memory (x,16) s = a)
              (\s. read PC s = word (pc + 0x2ac) /\
                   bignum_from_memory (z,32) s = a EXP 2)
              (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                          X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                          X22; X23; X24; X25; X30] ,,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 24)] ,,
               MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `t:int64`;`pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,16) s0` THEN

  (*** First nested 8x8 squaring block ***)

  ARM_STEPS_TAC BIGNUM_KSQR_16_32_EXEC (1--4) THEN
  BIGNUM_KSQR_16_32_LEMMA_TAC 5 THEN
  BIGNUM_LDIGITIZE_TAC "l_" `read (memory :> bytes (z,8 * 16)) s5` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_EXEC
   [8;9;12;13;16;17;20;21; 25;27;30;32;35;37;40;42] (6--43) THEN
  SUBGOAL_THEN
   `&(bignum_from_memory(t,8) s43):real =
    abs(&(bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7]) -
        &(bignum_of_wordlist [x_8;x_9;x_10;x_11;x_12;x_13;x_14;x_15]))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 8`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC(REAL_ARITH
       `&x < e /\ &y < e ==> abs(&x - &y):real < e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &x < &y then &y - &x else &x - &y`] THEN
    SUBGOAL_THEN
     `carry_s21 <=>
      bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] <
      bignum_of_wordlist [x_8;x_9;x_10;x_11;x_12;x_13;x_14;x_15]`
    (SUBST_ALL_TAC o SYM) THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_UNMASK_64; WORD_XOR_MASK] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM)] THEN

  (*** Second nested squaring ***)

  ARM_STEPS_TAC BIGNUM_KSQR_16_32_EXEC (44--46) THEN
  BIGNUM_KSQR_16_32_LEMMA_TAC 47 THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 128),8 * 16)) s47` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Computation of H' = H + L_top ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_EXEC
   [50;51;55;56;60;61;65;66;69;70;73;74;77;78;81;82] (48--83) THEN
  SUBGOAL_THEN
   `bignum_from_memory(word_add z (word 128),16) s83 =
    bignum_of_wordlist
     [h_0;h_1;h_2;h_3;h_4;h_5;h_6;h_7;h_8;h_9;h_10;h_11;h_12;h_13;h_14;h_15] +
    bignum_of_wordlist[l_8;l_9;l_10;l_11;l_12;l_13;l_14;l_15]`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 16`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN

  (*** Third and final nested squaring ***)

  ARM_STEPS_TAC BIGNUM_KSQR_16_32_EXEC (84--86) THEN
  BIGNUM_KSQR_16_32_LEMMA_TAC 87 THEN
  BIGNUM_LDIGITIZE_TAC "m_"
   `read (memory :> bytes (word_add t (word 64),8 * 16)) s87` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** All remaining accumulation of sub-results ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_EXEC
   [90;91;94;95;98;99;102;103;106;107;110;111;114;115;118;119;
    122;123;126;127;130;131;134;135;138;139;142;143;146;147;150;151; 153;
    156;157;160;161;164;165;168;169]
   (88--170) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * 32`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `(&a:real) pow 2 =
    (&(bignum_of_wordlist[l_0; l_1; l_2; l_3; l_4; l_5; l_6; l_7]) +
     &2 pow 512 *
     &(bignum_of_wordlist
       [sum_s50; sum_s51; sum_s55; sum_s56; sum_s60; sum_s61; sum_s65;
        sum_s66; sum_s69; sum_s70; sum_s73; sum_s74; sum_s77; sum_s78;
        sum_s81; sum_s82])) *
    (&2 pow 512 + &1) -
    &2 pow 512 *
    &(bignum_of_wordlist
      [m_0; m_1; m_2; m_3; m_4; m_5; m_6; m_7; m_8; m_9; m_10; m_11; m_12;
       m_13; m_14; m_15])`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
     `l + e * (h + m):num = (l + e * m) + e * h`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(8,8))] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `x EXP 2 = y ==> y = x EXP 2`))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[]
     `abs x:real = y ==> y = abs x`)) THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_UNMASK_64; REAL_VAL_WORD_MASK; DIMINDEX_64;
              COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KSQR_16_32_SUBROUTINE_CORRECT = prove
 (`!z x a t pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(z,8 * 32); (t,8 * 24); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 24); (word_sub stackpointer (word 64),64)]
         [(word pc,0x74c); (x,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_ksqr_16_32_mc /\
                   read PC s = word pc /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [z; x; t] s /\
                   bignum_from_memory (x,16) s = a)
              (\s. read PC s = returnaddress /\
                   bignum_from_memory (z,32) s = a EXP 2)
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 24);
                     memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_KSQR_16_32_EXEC BIGNUM_KSQR_16_32_CORRECT
    `[X19;X20;X21;X22;X23;X24;X25;X30]` 64);;
