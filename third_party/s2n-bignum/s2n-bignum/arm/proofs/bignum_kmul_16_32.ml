(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 16x16 -> 32 multiplication, using Karatsuba reduction.                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_kmul_16_32.o";;
 ****)

let bignum_kmul_16_32_mc = define_assert_from_elf "bignum_kmul_16_32_mc" "arm/fastmul/bignum_kmul_16_32.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf73fb;       (* arm_STP X27 X28 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa0003f9;       (* arm_MOV X25 X0 *)
  0xaa0103fa;       (* arm_MOV X26 X1 *)
  0xaa0203fb;       (* arm_MOV X27 X2 *)
  0xaa0303fc;       (* arm_MOV X28 X3 *)
  0x940000e5;       (* arm_BL (word 916) *)
  0xa9402f4a;       (* arm_LDP X10 X11 X26 (Immediate_Offset (iword (&0))) *)
  0xa9442748;       (* arm_LDP X8 X9 X26 (Immediate_Offset (iword (&64))) *)
  0xeb08014a;       (* arm_SUBS X10 X10 X8 *)
  0xfa09016b;       (* arm_SBCS X11 X11 X9 *)
  0xa941374c;       (* arm_LDP X12 X13 X26 (Immediate_Offset (iword (&16))) *)
  0xa9452748;       (* arm_LDP X8 X9 X26 (Immediate_Offset (iword (&80))) *)
  0xfa08018c;       (* arm_SBCS X12 X12 X8 *)
  0xfa0901ad;       (* arm_SBCS X13 X13 X9 *)
  0xa9423f4e;       (* arm_LDP X14 X15 X26 (Immediate_Offset (iword (&32))) *)
  0xa9462748;       (* arm_LDP X8 X9 X26 (Immediate_Offset (iword (&96))) *)
  0xfa0801ce;       (* arm_SBCS X14 X14 X8 *)
  0xfa0901ef;       (* arm_SBCS X15 X15 X9 *)
  0xa9434750;       (* arm_LDP X16 X17 X26 (Immediate_Offset (iword (&48))) *)
  0xa9472748;       (* arm_LDP X8 X9 X26 (Immediate_Offset (iword (&112))) *)
  0xfa080210;       (* arm_SBCS X16 X16 X8 *)
  0xfa090231;       (* arm_SBCS X17 X17 X9 *)
  0xda9f23fd;       (* arm_CSETM X29 Condition_CC *)
  0xab1d03bf;       (* arm_CMN X29 X29 *)
  0xca1d014a;       (* arm_EOR X10 X10 X29 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca1d016b;       (* arm_EOR X11 X11 X29 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa9002f8a;       (* arm_STP X10 X11 X28 (Immediate_Offset (iword (&0))) *)
  0xca1d018c;       (* arm_EOR X12 X12 X29 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xca1d01ad;       (* arm_EOR X13 X13 X29 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xa901378c;       (* arm_STP X12 X13 X28 (Immediate_Offset (iword (&16))) *)
  0xca1d01ce;       (* arm_EOR X14 X14 X29 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xca1d01ef;       (* arm_EOR X15 X15 X29 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xa9023f8e;       (* arm_STP X14 X15 X28 (Immediate_Offset (iword (&32))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xa9034790;       (* arm_STP X16 X17 X28 (Immediate_Offset (iword (&48))) *)
  0x91020320;       (* arm_ADD X0 X25 (rvalue (word 128)) *)
  0x91010341;       (* arm_ADD X1 X26 (rvalue (word 64)) *)
  0x91010362;       (* arm_ADD X2 X27 (rvalue (word 64)) *)
  0x940000bb;       (* arm_BL (word 748) *)
  0xa9402f6a;       (* arm_LDP X10 X11 X27 (Immediate_Offset (iword (&0))) *)
  0xa9442768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&64))) *)
  0xeb0a010a;       (* arm_SUBS X10 X8 X10 *)
  0xfa0b012b;       (* arm_SBCS X11 X9 X11 *)
  0xa941376c;       (* arm_LDP X12 X13 X27 (Immediate_Offset (iword (&16))) *)
  0xa9452768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&80))) *)
  0xfa0c010c;       (* arm_SBCS X12 X8 X12 *)
  0xfa0d012d;       (* arm_SBCS X13 X9 X13 *)
  0xa9423f6e;       (* arm_LDP X14 X15 X27 (Immediate_Offset (iword (&32))) *)
  0xa9462768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&96))) *)
  0xfa0e010e;       (* arm_SBCS X14 X8 X14 *)
  0xfa0f012f;       (* arm_SBCS X15 X9 X15 *)
  0xa9434770;       (* arm_LDP X16 X17 X27 (Immediate_Offset (iword (&48))) *)
  0xa9472768;       (* arm_LDP X8 X9 X27 (Immediate_Offset (iword (&112))) *)
  0xfa100110;       (* arm_SBCS X16 X8 X16 *)
  0xfa110131;       (* arm_SBCS X17 X9 X17 *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xab13027f;       (* arm_CMN X19 X19 *)
  0xca13014a;       (* arm_EOR X10 X10 X19 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca13016b;       (* arm_EOR X11 X11 X19 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa9042f8a;       (* arm_STP X10 X11 X28 (Immediate_Offset (iword (&64))) *)
  0xca13018c;       (* arm_EOR X12 X12 X19 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xca1301ad;       (* arm_EOR X13 X13 X19 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xa905378c;       (* arm_STP X12 X13 X28 (Immediate_Offset (iword (&80))) *)
  0xca1301ce;       (* arm_EOR X14 X14 X19 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xca1301ef;       (* arm_EOR X15 X15 X19 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xa9063f8e;       (* arm_STP X14 X15 X28 (Immediate_Offset (iword (&96))) *)
  0xca130210;       (* arm_EOR X16 X16 X19 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xca130231;       (* arm_EOR X17 X17 X19 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xa9074790;       (* arm_STP X16 X17 X28 (Immediate_Offset (iword (&112))) *)
  0xca1303bd;       (* arm_EOR X29 X29 X19 *)
  0xa9482f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&128))) *)
  0xa944372c;       (* arm_LDP X12 X13 X25 (Immediate_Offset (iword (&64))) *)
  0xab0c014a;       (* arm_ADDS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9082f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&128))) *)
  0xa9492f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&144))) *)
  0xa945372c;       (* arm_LDP X12 X13 X25 (Immediate_Offset (iword (&80))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9092f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&144))) *)
  0xa94a2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&160))) *)
  0xa946372c;       (* arm_LDP X12 X13 X25 (Immediate_Offset (iword (&96))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90a2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&160))) *)
  0xa94b2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&176))) *)
  0xa947372c;       (* arm_LDP X12 X13 X25 (Immediate_Offset (iword (&112))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90b2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&176))) *)
  0xa94c2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&192))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90c2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&192))) *)
  0xa94d2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&208))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90d2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&208))) *)
  0xa94e2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&224))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90e2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&224))) *)
  0xa94f2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&240))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90f2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&240))) *)
  0x91020380;       (* arm_ADD X0 X28 (rvalue (word 128)) *)
  0xaa1c03e1;       (* arm_MOV X1 X28 *)
  0x91010382;       (* arm_ADD X2 X28 (rvalue (word 64)) *)
  0x9400006c;       (* arm_BL (word 432) *)
  0xa9400720;       (* arm_LDP X0 X1 X25 (Immediate_Offset (iword (&0))) *)
  0xa9484730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&128))) *)
  0xab100000;       (* arm_ADDS X0 X0 X16 *)
  0xba110021;       (* arm_ADCS X1 X1 X17 *)
  0xa9410f22;       (* arm_LDP X2 X3 X25 (Immediate_Offset (iword (&16))) *)
  0xa9494730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&144))) *)
  0xba100042;       (* arm_ADCS X2 X2 X16 *)
  0xba110063;       (* arm_ADCS X3 X3 X17 *)
  0xa9421724;       (* arm_LDP X4 X5 X25 (Immediate_Offset (iword (&32))) *)
  0xa94a4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&160))) *)
  0xba100084;       (* arm_ADCS X4 X4 X16 *)
  0xba1100a5;       (* arm_ADCS X5 X5 X17 *)
  0xa9431f26;       (* arm_LDP X6 X7 X25 (Immediate_Offset (iword (&48))) *)
  0xa94b4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&176))) *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0xba1100e7;       (* arm_ADCS X7 X7 X17 *)
  0xa9482728;       (* arm_LDP X8 X9 X25 (Immediate_Offset (iword (&128))) *)
  0xa94c4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&192))) *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba110129;       (* arm_ADCS X9 X9 X17 *)
  0xa9492f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&144))) *)
  0xa94d4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&208))) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xa94a372c;       (* arm_LDP X12 X13 X25 (Immediate_Offset (iword (&160))) *)
  0xa94e4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&224))) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xa94b3f2e;       (* arm_LDP X14 X15 X25 (Immediate_Offset (iword (&176))) *)
  0xa94f4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&240))) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0x9a9f37fa;       (* arm_CSET X26 Condition_CS *)
  0xab1d03bf;       (* arm_CMN X29 X29 *)
  0xa9484790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&128))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba110021;       (* arm_ADCS X1 X1 X17 *)
  0xa9040720;       (* arm_STP X0 X1 X25 (Immediate_Offset (iword (&64))) *)
  0xa9494790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&144))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba100042;       (* arm_ADCS X2 X2 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba110063;       (* arm_ADCS X3 X3 X17 *)
  0xa9050f22;       (* arm_STP X2 X3 X25 (Immediate_Offset (iword (&80))) *)
  0xa94a4790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&160))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba100084;       (* arm_ADCS X4 X4 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba1100a5;       (* arm_ADCS X5 X5 X17 *)
  0xa9061724;       (* arm_STP X4 X5 X25 (Immediate_Offset (iword (&96))) *)
  0xa94b4790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&176))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba1100e7;       (* arm_ADCS X7 X7 X17 *)
  0xa9071f26;       (* arm_STP X6 X7 X25 (Immediate_Offset (iword (&112))) *)
  0xa94c4790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&192))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba110129;       (* arm_ADCS X9 X9 X17 *)
  0xa9082728;       (* arm_STP X8 X9 X25 (Immediate_Offset (iword (&128))) *)
  0xa94d4790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&208))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xa9092f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&144))) *)
  0xa94e4790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&224))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xa90a372c;       (* arm_STP X12 X13 X25 (Immediate_Offset (iword (&160))) *)
  0xa94f4790;       (* arm_LDP X16 X17 X28 (Immediate_Offset (iword (&240))) *)
  0xca1d0210;       (* arm_EOR X16 X16 X29 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xca1d0231;       (* arm_EOR X17 X17 X29 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0xa90b3f2e;       (* arm_STP X14 X15 X25 (Immediate_Offset (iword (&176))) *)
  0xba1a03bb;       (* arm_ADCS X27 X29 X26 *)
  0x9a1f03bc;       (* arm_ADC X28 X29 XZR *)
  0xa94c2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&192))) *)
  0xab1b014a;       (* arm_ADDS X10 X10 X27 *)
  0xba1c016b;       (* arm_ADCS X11 X11 X28 *)
  0xa90c2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&192))) *)
  0xa94d2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&208))) *)
  0xba1c014a;       (* arm_ADCS X10 X10 X28 *)
  0xba1c016b;       (* arm_ADCS X11 X11 X28 *)
  0xa90d2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&208))) *)
  0xa94e2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&224))) *)
  0xba1c014a;       (* arm_ADCS X10 X10 X28 *)
  0xba1c016b;       (* arm_ADCS X11 X11 X28 *)
  0xa90e2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&224))) *)
  0xa94f2f2a;       (* arm_LDP X10 X11 X25 (Immediate_Offset (iword (&240))) *)
  0xba1c014a;       (* arm_ADCS X10 X10 X28 *)
  0xba1c016b;       (* arm_ADCS X11 X11 X28 *)
  0xa90f2f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&240))) *)
  0xa8c17bfd;       (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0x3dc00041;       (* arm_LDR Q1 X2 (Immediate_Offset (word 0)) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x3dc00422;       (* arm_LDR Q2 X1 (Immediate_Offset (word 16)) *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x3dc00443;       (* arm_LDR Q3 X2 (Immediate_Offset (word 16)) *)
  0x4e801824;       (* arm_UZIP1 Q4 Q1 Q0 32 *)
  0x4ea00821;       (* arm_REV64_VEC Q1 Q1 32 *)
  0x4e801805;       (* arm_UZIP1 Q5 Q0 Q0 32 *)
  0x4ea09c20;       (* arm_MUL_VEC Q0 Q1 Q0 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0x4f605400;       (* arm_SHL_VEC Q0 Q0 32 64 *)
  0x2ea480a0;       (* arm_UMLAL Q0 Q5 Q4 32 *)
  0x4e083c0b;       (* arm_UMOV X11 Q0 0 8 *)
  0x4e183c0f;       (* arm_UMOV X15 Q0 1 8 *)
  0x4e821860;       (* arm_UZIP1 Q0 Q3 Q2 32 *)
  0x4ea00861;       (* arm_REV64_VEC Q1 Q3 32 *)
  0x4e821843;       (* arm_UZIP1 Q3 Q2 Q2 32 *)
  0x4ea29c21;       (* arm_MUL_VEC Q1 Q1 Q2 32 *)
  0x6ea02821;       (* arm_UADDLP Q1 Q1 32 *)
  0x4f605421;       (* arm_SHL_VEC Q1 Q1 32 64 *)
  0x2ea08061;       (* arm_UMLAL Q1 Q3 Q0 32 *)
  0x4e083c30;       (* arm_UMOV X16 Q1 0 8 *)
  0x4e183c31;       (* arm_UMOV X17 Q1 1 8 *)
  0x3dc00820;       (* arm_LDR Q0 X1 (Immediate_Offset (word 32)) *)
  0x3dc00841;       (* arm_LDR Q1 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c22;       (* arm_LDR Q2 X1 (Immediate_Offset (word 48)) *)
  0x3dc00c43;       (* arm_LDR Q3 X2 (Immediate_Offset (word 48)) *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xab1301ef;       (* arm_ADDS X15 X15 X19 *)
  0x9bc87c93;       (* arm_UMULH X19 X4 X8 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9bc97cb3;       (* arm_UMULH X19 X5 X9 *)
  0xba130231;       (* arm_ADCS X17 X17 X19 *)
  0x9bca7cd3;       (* arm_UMULH X19 X6 X10 *)
  0x4e801824;       (* arm_UZIP1 Q4 Q1 Q0 32 *)
  0x4ea00821;       (* arm_REV64_VEC Q1 Q1 32 *)
  0x4e801805;       (* arm_UZIP1 Q5 Q0 Q0 32 *)
  0x4ea09c20;       (* arm_MUL_VEC Q0 Q1 Q0 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0x4f605400;       (* arm_SHL_VEC Q0 Q0 32 64 *)
  0x2ea480a0;       (* arm_UMLAL Q0 Q5 Q4 32 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab0b01ec;       (* arm_ADDS X12 X15 X11 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0xba110271;       (* arm_ADCS X17 X19 X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xab0b01ed;       (* arm_ADDS X13 X15 X11 *)
  0xba0c020e;       (* arm_ADCS X14 X16 X12 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba100270;       (* arm_ADCS X16 X19 X16 *)
  0xba1103f1;       (* arm_ADCS X17 XZR X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xeb0600b8;       (* arm_SUBS X24 X5 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb090155;       (* arm_SUBS X21 X10 X9 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070115;       (* arm_SUBS X21 X8 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba16018c;       (* arm_ADCS X12 X12 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb080155;       (* arm_SUBS X21 X10 X8 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070135;       (* arm_SUBS X21 X9 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070155;       (* arm_SUBS X21 X10 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb080135;       (* arm_SUBS X21 X9 X8 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0xa900300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&0))) *)
  0xa9422047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&32))) *)
  0xa901380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&16))) *)
  0xa9431825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&48))) *)
  0xa902400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&32))) *)
  0xa9432849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&48))) *)
  0xa9034c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&48))) *)
  0x4e083c0b;       (* arm_UMOV X11 Q0 0 8 *)
  0x4e183c0f;       (* arm_UMOV X15 Q0 1 8 *)
  0x4e821860;       (* arm_UZIP1 Q0 Q3 Q2 32 *)
  0x4ea00861;       (* arm_REV64_VEC Q1 Q3 32 *)
  0x4e821843;       (* arm_UZIP1 Q3 Q2 Q2 32 *)
  0x4ea29c21;       (* arm_MUL_VEC Q1 Q1 Q2 32 *)
  0x6ea02821;       (* arm_UADDLP Q1 Q1 32 *)
  0x4f605421;       (* arm_SHL_VEC Q1 Q1 32 64 *)
  0x2ea08061;       (* arm_UMLAL Q1 Q3 Q0 32 *)
  0x4e083c30;       (* arm_UMOV X16 Q1 0 8 *)
  0x4e183c31;       (* arm_UMOV X17 Q1 1 8 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xab1301ef;       (* arm_ADDS X15 X15 X19 *)
  0x9bc87c93;       (* arm_UMULH X19 X4 X8 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9bc97cb3;       (* arm_UMULH X19 X5 X9 *)
  0xba130231;       (* arm_ADCS X17 X17 X19 *)
  0x9bca7cd3;       (* arm_UMULH X19 X6 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab0b01ec;       (* arm_ADDS X12 X15 X11 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0xba110271;       (* arm_ADCS X17 X19 X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xab0b01ed;       (* arm_ADDS X13 X15 X11 *)
  0xba0c020e;       (* arm_ADCS X14 X16 X12 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba100270;       (* arm_ADCS X16 X19 X16 *)
  0xba1103f1;       (* arm_ADCS X17 XZR X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xa9425416;       (* arm_LDP X22 X21 X0 (Immediate_Offset (iword (&32))) *)
  0xab16016b;       (* arm_ADDS X11 X11 X22 *)
  0xba15018c;       (* arm_ADCS X12 X12 X21 *)
  0xa9435416;       (* arm_LDP X22 X21 X0 (Immediate_Offset (iword (&48))) *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xeb0600b8;       (* arm_SUBS X24 X5 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb090155;       (* arm_SUBS X21 X10 X9 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070115;       (* arm_SUBS X21 X8 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba16018c;       (* arm_ADCS X12 X12 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb080155;       (* arm_SUBS X21 X10 X8 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070135;       (* arm_SUBS X21 X9 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070155;       (* arm_SUBS X21 X10 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb080135;       (* arm_SUBS X21 X9 X8 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xa9405436;       (* arm_LDP X22 X21 X1 (Immediate_Offset (iword (&0))) *)
  0xeb160063;       (* arm_SUBS X3 X3 X22 *)
  0xfa150084;       (* arm_SBCS X4 X4 X21 *)
  0xa9415436;       (* arm_LDP X22 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xfa1600a5;       (* arm_SBCS X5 X5 X22 *)
  0xfa1500c6;       (* arm_SBCS X6 X6 X21 *)
  0xda9f23f8;       (* arm_CSETM X24 Condition_CC *)
  0xa904300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&64))) *)
  0xa9405456;       (* arm_LDP X22 X21 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0702c7;       (* arm_SUBS X7 X22 X7 *)
  0xfa0802a8;       (* arm_SBCS X8 X21 X8 *)
  0xa9415456;       (* arm_LDP X22 X21 X2 (Immediate_Offset (iword (&16))) *)
  0xfa0902c9;       (* arm_SBCS X9 X22 X9 *)
  0xfa0a02aa;       (* arm_SBCS X10 X21 X10 *)
  0xda9f23e1;       (* arm_CSETM X1 Condition_CC *)
  0xa905380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&80))) *)
  0xca180063;       (* arm_EOR X3 X3 X24 *)
  0xeb180063;       (* arm_SUBS X3 X3 X24 *)
  0xca180084;       (* arm_EOR X4 X4 X24 *)
  0xfa180084;       (* arm_SBCS X4 X4 X24 *)
  0xca1800a5;       (* arm_EOR X5 X5 X24 *)
  0xfa1800a5;       (* arm_SBCS X5 X5 X24 *)
  0xca1800c6;       (* arm_EOR X6 X6 X24 *)
  0xda1800c6;       (* arm_SBC X6 X6 X24 *)
  0xa906400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&96))) *)
  0xca0100e7;       (* arm_EOR X7 X7 X1 *)
  0xeb0100e7;       (* arm_SUBS X7 X7 X1 *)
  0xca010108;       (* arm_EOR X8 X8 X1 *)
  0xfa010108;       (* arm_SBCS X8 X8 X1 *)
  0xca010129;       (* arm_EOR X9 X9 X1 *)
  0xfa010129;       (* arm_SBCS X9 X9 X1 *)
  0xca01014a;       (* arm_EOR X10 X10 X1 *)
  0xda01014a;       (* arm_SBC X10 X10 X1 *)
  0xa9074c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&112))) *)
  0xca180021;       (* arm_EOR X1 X1 X24 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9b087c8f;       (* arm_MUL X15 X4 X8 *)
  0x9b097cb0;       (* arm_MUL X16 X5 X9 *)
  0x9b0a7cd1;       (* arm_MUL X17 X6 X10 *)
  0x9bc77c73;       (* arm_UMULH X19 X3 X7 *)
  0xab1301ef;       (* arm_ADDS X15 X15 X19 *)
  0x9bc87c93;       (* arm_UMULH X19 X4 X8 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9bc97cb3;       (* arm_UMULH X19 X5 X9 *)
  0xba130231;       (* arm_ADCS X17 X17 X19 *)
  0x9bca7cd3;       (* arm_UMULH X19 X6 X10 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab0b01ec;       (* arm_ADDS X12 X15 X11 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0xba110271;       (* arm_ADCS X17 X19 X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xab0b01ed;       (* arm_ADDS X13 X15 X11 *)
  0xba0c020e;       (* arm_ADCS X14 X16 X12 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba100270;       (* arm_ADCS X16 X19 X16 *)
  0xba1103f1;       (* arm_ADCS X17 XZR X17 *)
  0x9a1303f3;       (* arm_ADC X19 XZR X19 *)
  0xeb0600b8;       (* arm_SUBS X24 X5 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb090155;       (* arm_SUBS X21 X10 X9 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070115;       (* arm_SUBS X21 X8 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba16018c;       (* arm_ADCS X12 X12 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb080155;       (* arm_SUBS X21 X10 X8 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070135;       (* arm_SUBS X21 X9 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb070155;       (* arm_SUBS X21 X10 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f4;       (* arm_CSETM X20 Condition_CC *)
  0xeb080135;       (* arm_SUBS X21 X9 X8 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x9b157f16;       (* arm_MUL X22 X24 X21 *)
  0x9bd57f15;       (* arm_UMULH X21 X24 X21 *)
  0xda942294;       (* arm_CINV X20 X20 Condition_CC *)
  0xb100069f;       (* arm_CMN X20 (rvalue (word 1)) *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xca1402b5;       (* arm_EOR X21 X21 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0xba140231;       (* arm_ADCS X17 X17 X20 *)
  0x9a140273;       (* arm_ADC X19 X19 X20 *)
  0xa9401003;       (* arm_LDP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9442007;       (* arm_LDP X7 X8 X0 (Immediate_Offset (iword (&64))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9411805;       (* arm_LDP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xa9452809;       (* arm_LDP X9 X10 X0 (Immediate_Offset (iword (&80))) *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xa9465414;       (* arm_LDP X20 X21 X0 (Immediate_Offset (iword (&96))) *)
  0xba1400e7;       (* arm_ADCS X7 X7 X20 *)
  0xba150108;       (* arm_ADCS X8 X8 X21 *)
  0xa9475c16;       (* arm_LDP X22 X23 X0 (Immediate_Offset (iword (&112))) *)
  0xba160129;       (* arm_ADCS X9 X9 X22 *)
  0xba17014a;       (* arm_ADCS X10 X10 X23 *)
  0xba1f0038;       (* arm_ADCS X24 X1 XZR *)
  0x9a1f0022;       (* arm_ADC X2 X1 XZR *)
  0xb100043f;       (* arm_CMN X1 (rvalue (word 1)) *)
  0xca01016b;       (* arm_EOR X11 X11 X1 *)
  0xba030163;       (* arm_ADCS X3 X11 X3 *)
  0xca01018c;       (* arm_EOR X12 X12 X1 *)
  0xba040184;       (* arm_ADCS X4 X12 X4 *)
  0xca0101ad;       (* arm_EOR X13 X13 X1 *)
  0xba0501a5;       (* arm_ADCS X5 X13 X5 *)
  0xca0101ce;       (* arm_EOR X14 X14 X1 *)
  0xba0601c6;       (* arm_ADCS X6 X14 X6 *)
  0xca0101ef;       (* arm_EOR X15 X15 X1 *)
  0xba0701e7;       (* arm_ADCS X7 X15 X7 *)
  0xca010210;       (* arm_EOR X16 X16 X1 *)
  0xba080208;       (* arm_ADCS X8 X16 X8 *)
  0xca010231;       (* arm_EOR X17 X17 X1 *)
  0xba090229;       (* arm_ADCS X9 X17 X9 *)
  0xca010273;       (* arm_EOR X19 X19 X1 *)
  0xba0a026a;       (* arm_ADCS X10 X19 X10 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0xba0202b5;       (* arm_ADCS X21 X21 X2 *)
  0xba0202d6;       (* arm_ADCS X22 X22 X2 *)
  0x9a0202f7;       (* arm_ADC X23 X23 X2 *)
  0xa9021003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&32))) *)
  0xa9031805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&48))) *)
  0xa9042007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&64))) *)
  0xa9052809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&80))) *)
  0xa9065414;       (* arm_STP X20 X21 X0 (Immediate_Offset (iword (&96))) *)
  0xa9075c16;       (* arm_STP X22 X23 X0 (Immediate_Offset (iword (&112))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_KMUL_16_32_EXEC = ARM_MK_EXEC_RULE bignum_kmul_16_32_mc;;

(* ------------------------------------------------------------------------- *)
(* First of all the correctness lemma for the embedded bignum_mul_8_16       *)
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

needs "arm/proofs/neon_helper.ml";;

let rewrite_assumptions t tac = SUBGOAL_THEN t
  (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE [thm])) THENL
  [tac; ALL_TAC];;

let simplify_128bit_words =
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO]);;

let simplify_128bit_words_and_accumulate state_name =
  simplify_128bit_words THEN
  (* Rewrite word_mul x y into the pattern that ACCUMULATE_ARITH_TAC can recognize. *)
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_RULE
      `word_mul (a:(64)word) (b:(64)word) =
       word (0 + val (a:(64)word) * val (b:(64)word))`]) THEN
  ACCUMULATE_ARITH_TAC state_name THEN CLARIFY_TAC;;

let ADK_48_TAC =
  DISCARD_READ_QREGS THEN
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

let BIGNUM_KMUL_16_32_LEMMA = prove
 (`!z x y a b pc returnaddress.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc,2932); (x,8 * 8); (y,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word(pc + 0)) bignum_kmul_16_32_mc /\
                 read PC s = word(pc + 0x3bc) /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,8) s = a /\
                 bignum_from_memory (y,8) s = b)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,16) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
                        X9; X10; X11; X12; X13; X14; X15; X16;
                        X17; X19; X20; X21; X22; X23; X24] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5],,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,8) s0` THEN
  (* Split 128-bit reads to word_join of 64-bit low and highs *)
  ABBREV_TAC `x_0_1:(128)word = read (memory :> bytes128 x) s0` THEN
  rewrite_assumptions `x_0_1 = word_join (x_1:(64)word) (x_0:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["x_0_1"; "x_1"; "x_0"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT]) THEN
  ABBREV_TAC `x_2_3:(128)word = read (memory :> bytes128 (word_add x (word 16))) s0` THEN
  rewrite_assumptions `x_2_3 = word_join (x_3:(64)word) (x_2:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["x_2_3"; "x_3"; "x_2"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
     ARITH_TAC) THEN

  ABBREV_TAC `y_0_1:(128)word = read (memory :> bytes128 y) s0` THEN
  rewrite_assumptions `y_0_1 = word_join (y_1:(64)word) (y_0:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["y_0_1"; "y_1"; "y_0"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT]) THEN
  ABBREV_TAC `y_2_3:(128)word = read (memory :> bytes128 (word_add y (word 16))) s0` THEN
  rewrite_assumptions `y_2_3 = word_join (y_3:(64)word) (y_2:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["y_2_3"; "y_3"; "y_2"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
     ARITH_TAC) THEN

  (*** First ADK block multiplying the lower halves ***)

  (* Run the vectorized parts first *)
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (1--16) THEN
  simplify_128bit_words_and_accumulate "s16" THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (17--17) THEN
  simplify_128bit_words_and_accumulate "s17" THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (18--25) THEN
  simplify_128bit_words_and_accumulate "s25" THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (26--26) THEN
  simplify_128bit_words_and_accumulate "s26" THEN

  (* Second ADK block multiplying the upper halves with q1 added:
     vector loads hoisted *)

  ABBREV_TAC `x_4_5:(128)word = read (memory :> bytes128 (word_add x (word 32))) s26` THEN
  rewrite_assumptions `x_4_5 = word_join (x_5:(64)word) (x_4:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["x_4_5"; "x_5"; "x_4"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
     ARITH_TAC) THEN
  ABBREV_TAC `x_6_7:(128)word = read (memory :> bytes128 (word_add x (word 48))) s26` THEN
  rewrite_assumptions `x_6_7 = word_join (x_7:(64)word) (x_6:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["x_6_7"; "x_7"; "x_6"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
     ARITH_TAC) THEN
  ABBREV_TAC `y_4_5:(128)word = read (memory :> bytes128 (word_add y (word 32))) s26` THEN
  rewrite_assumptions `y_4_5 = word_join (y_5:(64)word) (y_4:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["y_4_5"; "y_5"; "y_4"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
     ARITH_TAC) THEN
  ABBREV_TAC `y_6_7:(128)word = read (memory :> bytes128 (word_add y (word 48))) s26` THEN
  rewrite_assumptions `y_6_7 = word_join (y_7:(64)word) (y_6:(64)word):(128)word`
    (MAP_EVERY EXPAND_TAC ["y_6_7"; "y_7"; "y_6"] THEN
     REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
     ARITH_TAC) THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (27--30) THEN

  (* First ADK block: Run the remaining scalar parts (1) *)
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [32;34;36] (31--37) THEN

  (* Second ADK block: multiply using vector instructions, but not move the
     results to scalar registers *)
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (38--44) THEN
  simplify_128bit_words THEN

  (* First ADK block: Run the remaining scalar parts *)
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [45;46;47;48;49;50;51;52;53;54;55;56;62;67;69;70;76;81;83;84;85;86;87;88;94;
    99;101;102;103;109;114;116;117;118;119;120;126;131;133;134;135;136;142;147;
    149;150;151;152] (45--152) THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = bignum_of_wordlist[mullo_s16;sum_s81;sum_s114;sum_s147]`;
    `q1 = bignum_of_wordlist[sum_s149;sum_s150;sum_s151;sum_s152]`] THEN
  SUBGOAL_THEN
   `2 EXP 256 * q1 + q0 =
    bignum_of_wordlist [x_0;x_1;x_2;x_3] *
    bignum_of_wordlist [y_0;y_1;y_2;y_3]`
  ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["q0"; "q1"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Second ADK block multiplying the upper halves with q1 added ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (153--161) THEN
  simplify_128bit_words_and_accumulate "s161" THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (162--162) THEN
  simplify_128bit_words_and_accumulate "s162" THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (163--170) THEN
  simplify_128bit_words_and_accumulate "s170" THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC [] (171--171) THEN
  simplify_128bit_words_and_accumulate "s171" THEN

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [173;175;177;179;180;181;182;183;184;185;186;187;188;189;190;192;193;195;
    196;197;198;199;200;206;211;213;214;220;225;227;228;229;230;231;232;238;
    243;245;246;247;253;258;260;261;262;263;264;270;275;277;278;279;280;286;
    291;293;294;295;296]
   (172--296) THEN

  MAP_EVERY ABBREV_TAC
   [`q2 = bignum_of_wordlist[sum_s192; sum_s225; sum_s258; sum_s291]`;
    `q3 = bignum_of_wordlist[sum_s293; sum_s294; sum_s295; sum_s296]`] THEN
  SUBGOAL_THEN
   `2 EXP 256 * q3 + q2 =
    bignum_of_wordlist [x_4;x_5;x_6;x_7] *
    bignum_of_wordlist [y_4;y_5;y_6;y_7] + q1`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "q2"; "q3"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The sign-magnitude difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [298;299;301;302;306;307;309;310;314;316;318;320;323;325;327;329]
   (297--330) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN

  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s310 <=> carry_s302)`;
   `xd = bignum_of_wordlist[sum_s314;sum_s316;sum_s318;sum_s320]`;
   `yd = bignum_of_wordlist[sum_s323;sum_s325;sum_s327;sum_s329]`] THEN

  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_4;x_5;x_6;x_7]) -
     &(bignum_of_wordlist[x_0;x_1;x_2;x_3])) *
    (&(bignum_of_wordlist[y_0;y_1;y_2;y_3]) -
     &(bignum_of_wordlist[y_4;y_5;y_6;y_7])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s302 * &xd) *
      (--(&1) pow bitval carry_s310 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s302 <=>
       bignum_of_wordlist[x_4;x_5;x_6;x_7] <
       bignum_of_wordlist[x_0;x_1;x_2;x_3]) /\
      (carry_s310 <=>
       bignum_of_wordlist[y_0;y_1;y_2;y_3] <
       bignum_of_wordlist[y_4;y_5;y_6;y_7])`
     (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    BINOP_TAC THEN REWRITE_TAC[bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = --(&1) pow 1 * z <=> y - x = z`] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
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

  (*** Third ADK block multiplying the absolute differences ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [332;333;334;335;337;339;341;343;344;345;346;347;348;349;350;351;352;353;354;360;365;367;368;374;379;381;382;383;384;385;386;392;397;399;400;401;407;412;414;415;416;417;418;424;429;431;432;433;434;440;445;447;448;449;450]
   (331--450) THEN

  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist
       [mullo_s332; sum_s379; sum_s412; sum_s445;
        sum_s447; sum_s448; sum_s449;  sum_s450])`
  SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Clean up the overall sign ***)

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_XOR_MASKS]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** Final accumulation simulation and 16-digit focusing ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [453;454;457;458;460;461;463;464;465;466;469;471;472;473;475;477;479;481;483;484;485;486;487]
   (451--494) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s493" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`1024`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN

  (*** The core rearrangement we are using ***)

  SUBGOAL_THEN
   `&a * &b:real =
    (&1 + &2 pow 256) * (&q0 + &2 pow 256 * &q2 + &2 pow 512 * &q3) +
    &2 pow 256 *
    (&(bignum_of_wordlist [x_4; x_5; x_6; x_7]) -
     &(bignum_of_wordlist [x_0; x_1; x_2; x_3])) *
    (&(bignum_of_wordlist [y_0; y_1; y_2; y_3]) -
     &(bignum_of_wordlist [y_4; y_5; y_6; y_7]))`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`2 EXP 256 * q1 + q0 =
       bignum_of_wordlist[x_0; x_1; x_2; x_3] *
       bignum_of_wordlist[y_0; y_1; y_2; y_3]`;
      `2 EXP 256 * q3 + q2 =
       bignum_of_wordlist[x_4; x_5; x_6; x_7] *
       bignum_of_wordlist[y_4; y_5; y_6; y_7] +
       q1`] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[]] THEN

  MAP_EVERY EXPAND_TAC ["q0"; "q2"; "q3"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN DISCH_TAC THEN

  (*** A bit of manual logic for the carry connections in negative case ***)
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THENL
  [SUBGOAL_THEN
     `&(bitval carry_s465):real = &(bitval carry_s466)`
    SUBST1_TAC THENL [ALL_TAC; REAL_INTEGER_TAC] THEN
    POP_ASSUM MP_TAC THEN BOOL_CASES_TAC `carry_s465:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[REAL_RAT_REDUCE_CONV `(&2 pow 64 - &1) * &1 + &0`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC;
  ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o
    filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KMUL_16_32_LEMMA_TAC =
  ARM_SUBROUTINE_SIM_TAC
    (bignum_kmul_16_32_mc,BIGNUM_KMUL_16_32_EXEC,
     0x0,bignum_kmul_16_32_mc,BIGNUM_KMUL_16_32_LEMMA)
    [`read X0 s`; `read X1 s`; `read X2 s`;
     `bignum_from_memory (read X1 s,8) s`;
     `bignum_from_memory (read X2 s,8) s`;
     `pc:num`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* Now the main proof.                                                       *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_KMUL_16_32_CORRECT = prove
 (`!z x y a b t pc.
        nonoverlapping (z,8 * 32) (t,8 * 32) /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 32)]
         [(word pc,2932); (x,8 * 16); (y,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_kmul_16_32_mc /\
                   read PC s = word(pc + 0x18) /\
                   C_ARGUMENTS [z; x; y; t] s /\
                   bignum_from_memory (x,16) s = a /\
                   bignum_from_memory (y,16) s = b)
              (\s. read PC s = word (pc + 0x3a0) /\
                   bignum_from_memory (z,32) s = a * b)
              (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                          X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                          X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
               MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5],,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 32)] ,,
               MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `t:int64`;`pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,16) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `bignum_from_memory (y,16) s0` THEN

  (*** First nested 8x8 multiply block ***)

  ARM_STEPS_TAC BIGNUM_KMUL_16_32_EXEC (1--5) THEN
  BIGNUM_KMUL_16_32_LEMMA_TAC 6 THEN
  BIGNUM_LDIGITIZE_TAC "l_" `read (memory :> bytes (z,8 * 16)) s6` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x:num = y * z`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(BINOP_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Sign-difference computation for x ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [9;10;13;14;17;18;21;22] (7--23) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] <
    bignum_of_wordlist [x_8;x_9;x_10;x_11;x_12;x_13;x_14;x_15] <=>
    carry_s22`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `512` THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [26;28;31;33;36;38;41;43] (24--44) THEN
  SUBGOAL_THEN
   `&(bignum_from_memory(t,8) s44):real =
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
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &x < &y then &y - &x else &x - &y`] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_UNMASK_64; WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM)] THEN

  (*** Second nested 8x8 multiply ***)

  ARM_STEPS_TAC BIGNUM_KMUL_16_32_EXEC (45--48) THEN
  BIGNUM_KMUL_16_32_LEMMA_TAC 49 THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 128),8 * 16)) s49` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x:num = y * z`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(BINOP_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Sign-difference computation for y ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [52;53;56;57;60;61;64;65] (50--66) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [y_8;y_9;y_10;y_11;y_12;y_13;y_14;y_15] <
    bignum_of_wordlist [y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7] <=>
    carry_s65`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `512` THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [69;71;74;76;79;81;84;86] (67--88) THEN
  SUBGOAL_THEN
   `&(bignum_from_memory(word_add t (word 64),8) s88):real =
    abs(&(bignum_of_wordlist [y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7]) -
        &(bignum_of_wordlist [y_8;y_9;y_10;y_11;y_12;y_13;y_14;y_15]))`
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
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &y < &x then &x - &y else &y - &x`] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_UNMASK_64; WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM)] THEN

  (*** Collected sign ***)

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_MASKS]) THEN
  ABBREV_TAC `sgn <=> ~(carry_s22 <=> carry_s65)` THEN

  (*** Computation of H' = H + L_top ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [91;92;96;97;101;102;106;107;110;111;114;115;118;119;122;123]
   (89--124) THEN
  SUBGOAL_THEN
   `bignum_from_memory(word_add z (word 128),16) s124 =
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

  (*** Third and final nested multiply ***)

  ARM_STEPS_TAC BIGNUM_KMUL_16_32_EXEC (125--128) THEN
  BIGNUM_KMUL_16_32_LEMMA_TAC 129 THEN
  BIGNUM_LDIGITIZE_TAC "m_"
   `read (memory :> bytes (word_add t (word 128),8 * 16)) s129` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x:num = y * z`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(BINOP_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** All remaining accumulation of sub-results ***)

  ARM_ACCSTEPS_TAC BIGNUM_KMUL_16_32_EXEC
   [132; 133; 136; 137; 140; 141; 144; 145; 148; 149; 152; 153; 156;
    157; 160; 161; 166; 168; 172; 174; 178; 180; 184; 186; 190; 192;
    196; 198; 202; 204; 208; 210; 212; 213; 215; 216; 219; 220; 223;
    224; 227; 228]
   (130--229) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * 32`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `(&a:real) * &b =
    (&(bignum_of_wordlist[l_0; l_1; l_2; l_3; l_4; l_5; l_6; l_7]) +
     &2 pow 512 *
     &(bignum_of_wordlist
      [sum_s91; sum_s92; sum_s96; sum_s97; sum_s101; sum_s102; sum_s106;
       sum_s107; sum_s110; sum_s111; sum_s114; sum_s115; sum_s118; sum_s119;
       sum_s122; sum_s123])) *
    (&2 pow 512 + &1) +
    &2 pow 512 *
    --(&1) pow bitval sgn *
    &(bignum_of_wordlist
      [m_0; m_1; m_2; m_3; m_4; m_5; m_6; m_7; m_8; m_9; m_10; m_11; m_12;
       m_13; m_14; m_15])`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
     `l + e * (h + m):num = (l + e * m) + e * h`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(8,8))] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `w * z:num = y ==> y = w * z`))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[]
     `abs x:real = y ==> y = abs x`))) THEN
    ONCE_REWRITE_TAC[MESON[REAL_ABS_NEG]
     `abs x * abs y:real = abs x * abs(--y)`] THEN
    REWRITE_TAC[REAL_NEG_SUB; REAL_ARITH
     `abs(x - x'):real = if x < x' then x' - x else x - x'`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,8)] THEN
    EXPAND_TAC "sgn" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_XOR_MASK] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `sgn:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN STRIP_TAC THEN
  ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
    filter (vfree_in `carry_s212:bool` o concl))
  THENL
   [ASM_CASES_TAC `carry_s212:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KMUL_16_32_SUBROUTINE_CORRECT = prove
 (`!z x y a b t pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(z,8 * 32); (t,8 * 32); (word_sub stackpointer (word 96),96)] /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 32); (word_sub stackpointer (word 96),96)]
         [(word pc,LENGTH bignum_kmul_16_32_mc); (x,8 * 16); (y,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_kmul_16_32_mc /\
                   read PC s = word pc /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [z; x; y; t] s /\
                   bignum_from_memory (x,16) s = a /\
                   bignum_from_memory (y,16) s = b)
              (\s. read PC s = returnaddress /\
                   bignum_from_memory (z,32) s = a * b)
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 32);
                     memory :> bytes(word_sub stackpointer (word 96),96)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_KMUL_16_32_EXEC BIGNUM_KMUL_16_32_CORRECT
    `[X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30]` 96);;
