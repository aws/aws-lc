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

(**** print_literal_from_elf "arm/p384/p384_montjdouble.o";;
 ****)

let p384_montjdouble_mc = define_assert_from_elf
  "p384_montjdouble_mc" "arm/p384/p384_montjdouble.o"
[
  0xd10643ff;       (* arm_SUB SP SP (rvalue (word 400)) *)
  0xa91553f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&336))) *)
  0xa9165bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&352))) *)
  0xa91763f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&368))) *)
  0xa9186bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&384))) *)
  0xaa0003f9;       (* arm_MOV X25 X0 *)
  0xaa0103fa;       (* arm_MOV X26 X1 *)
  0xa9460f42;       (* arm_LDP X2 X3 X26 (Immediate_Offset (iword (&96))) *)
  0xa9471744;       (* arm_LDP X4 X5 X26 (Immediate_Offset (iword (&112))) *)
  0xa9481f46;       (* arm_LDP X6 X7 X26 (Immediate_Offset (iword (&128))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9bc37c51;       (* arm_UMULH X17 X2 X3 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc47c51;       (* arm_UMULH X17 X2 X4 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc47c71;       (* arm_UMULH X17 X3 X4 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc27c49;       (* arm_UMULH X9 X2 X2 *)
  0x9bc37c6b;       (* arm_UMULH X11 X3 X3 *)
  0x9bc47c8d;       (* arm_UMULH X13 X4 X4 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607d10;       (* arm_LSL X16 X8 32 *)
  0x8b080208;       (* arm_ADD X8 X16 X8 *)
  0xd360fd10;       (* arm_LSR X16 X8 32 *)
  0xeb080210;       (* arm_SUBS X16 X16 X8 *)
  0xda1f010f;       (* arm_SBC X15 X8 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0801ef;       (* arm_ADDS X15 X15 X8 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb100129;       (* arm_SUBS X9 X9 X16 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d30;       (* arm_LSL X16 X9 32 *)
  0x8b090209;       (* arm_ADD X9 X16 X9 *)
  0xd360fd30;       (* arm_LSR X16 X9 32 *)
  0xeb090210;       (* arm_SUBS X16 X16 X9 *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0901ef;       (* arm_ADDS X15 X15 X9 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xfa0f016b;       (* arm_SBCS X11 X11 X15 *)
  0xfa0e018c;       (* arm_SBCS X12 X12 X14 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d50;       (* arm_LSL X16 X10 32 *)
  0x8b0a020a;       (* arm_ADD X10 X16 X10 *)
  0xd360fd50;       (* arm_LSR X16 X10 32 *)
  0xeb0a0210;       (* arm_SUBS X16 X16 X10 *)
  0xda1f014f;       (* arm_SBC X15 X10 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10016b;       (* arm_SUBS X11 X11 X16 *)
  0xfa0f018c;       (* arm_SBCS X12 X12 X15 *)
  0xfa0e01ad;       (* arm_SBCS X13 X13 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xa90033eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&0))) *)
  0xa90123ed;       (* arm_STP X13 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9022be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&32))) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c81;       (* arm_UMULH X1 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba11002b;       (* arm_ADCS X11 X1 X17 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f002d;       (* arm_ADC X13 X1 XZR *)
  0xeb030051;       (* arm_SUBS X17 X2 X3 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500cf;       (* arm_SUBS X15 X6 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040051;       (* arm_SUBS X17 X2 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500ef;       (* arm_SUBS X15 X7 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040071;       (* arm_SUBS X17 X3 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0600ef;       (* arm_SUBS X15 X7 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba0f018c;       (* arm_ADCS X12 X12 X15 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xa9400fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0xab020108;       (* arm_ADDS X8 X8 X2 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9420fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0x8b080088;       (* arm_ADD X8 X4 X8 *)
  0xd360fd04;       (* arm_LSR X4 X8 32 *)
  0xeb080084;       (* arm_SUBS X4 X4 X8 *)
  0xda1f0103;       (* arm_SBC X3 X8 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa02016b;       (* arm_SBCS X11 X11 X2 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0x8b090089;       (* arm_ADD X9 X4 X9 *)
  0xd360fd24;       (* arm_LSR X4 X9 32 *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xda1f0123;       (* arm_SBC X3 X9 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0x8b0a008a;       (* arm_ADD X10 X4 X10 *)
  0xd360fd44;       (* arm_LSR X4 X10 32 *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xda1f0143;       (* arm_SBC X3 X10 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab0a0063;       (* arm_ADDS X3 X3 X10 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa0201ad;       (* arm_SBCS X13 X13 X2 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab080231;       (* arm_ADDS X17 X17 X8 *)
  0xba1f0128;       (* arm_ADCS X8 X9 XZR *)
  0xba1f0149;       (* arm_ADCS X9 X10 XZR *)
  0xba1f03ea;       (* arm_ADCS X10 XZR XZR *)
  0x9b057ca1;       (* arm_MUL X1 X5 X5 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x9b067cce;       (* arm_MUL X14 X6 X6 *)
  0x9b077cef;       (* arm_MUL X15 X7 X7 *)
  0x9bc57ca1;       (* arm_UMULH X1 X5 X5 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0x9bc67cc1;       (* arm_UMULH X1 X6 X6 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9bc77ce1;       (* arm_UMULH X1 X7 X7 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9b067ca1;       (* arm_MUL X1 X5 X6 *)
  0x9b077cae;       (* arm_MUL X14 X5 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0xab1001ce;       (* arm_ADDS X14 X14 X16 *)
  0x9bc77cb0;       (* arm_UMULH X16 X5 X7 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab010021;       (* arm_ADDS X1 X1 X1 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb26083e1;       (* arm_MOV X1 (rvalue (word 18446744069414584321)) *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0xd280002f;       (* arm_MOV X15 (rvalue (word 1)) *)
  0xab01017f;       (* arm_CMN X11 X1 *)
  0xba0e019f;       (* arm_ADCS XZR X12 X14 *)
  0xba0f01bf;       (* arm_ADCS XZR X13 X15 *)
  0xba1f023f;       (* arm_ADCS XZR X17 XZR *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x8a0a0021;       (* arm_AND X1 X1 X10 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x8a0a01ce;       (* arm_AND X14 X14 X10 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xa90033eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&0))) *)
  0xa90147ed;       (* arm_STP X13 X17 SP (Immediate_Offset (iword (&16))) *)
  0xa90227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&32))) *)
  0xa9430f42;       (* arm_LDP X2 X3 X26 (Immediate_Offset (iword (&48))) *)
  0xa9441744;       (* arm_LDP X4 X5 X26 (Immediate_Offset (iword (&64))) *)
  0xa9451f46;       (* arm_LDP X6 X7 X26 (Immediate_Offset (iword (&80))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9bc37c51;       (* arm_UMULH X17 X2 X3 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc47c51;       (* arm_UMULH X17 X2 X4 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc47c71;       (* arm_UMULH X17 X3 X4 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc27c49;       (* arm_UMULH X9 X2 X2 *)
  0x9bc37c6b;       (* arm_UMULH X11 X3 X3 *)
  0x9bc47c8d;       (* arm_UMULH X13 X4 X4 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607d10;       (* arm_LSL X16 X8 32 *)
  0x8b080208;       (* arm_ADD X8 X16 X8 *)
  0xd360fd10;       (* arm_LSR X16 X8 32 *)
  0xeb080210;       (* arm_SUBS X16 X16 X8 *)
  0xda1f010f;       (* arm_SBC X15 X8 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0801ef;       (* arm_ADDS X15 X15 X8 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb100129;       (* arm_SUBS X9 X9 X16 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d30;       (* arm_LSL X16 X9 32 *)
  0x8b090209;       (* arm_ADD X9 X16 X9 *)
  0xd360fd30;       (* arm_LSR X16 X9 32 *)
  0xeb090210;       (* arm_SUBS X16 X16 X9 *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0901ef;       (* arm_ADDS X15 X15 X9 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xfa0f016b;       (* arm_SBCS X11 X11 X15 *)
  0xfa0e018c;       (* arm_SBCS X12 X12 X14 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d50;       (* arm_LSL X16 X10 32 *)
  0x8b0a020a;       (* arm_ADD X10 X16 X10 *)
  0xd360fd50;       (* arm_LSR X16 X10 32 *)
  0xeb0a0210;       (* arm_SUBS X16 X16 X10 *)
  0xda1f014f;       (* arm_SBC X15 X10 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10016b;       (* arm_SUBS X11 X11 X16 *)
  0xfa0f018c;       (* arm_SBCS X12 X12 X15 *)
  0xfa0e01ad;       (* arm_SBCS X13 X13 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xa90333eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&48))) *)
  0xa90423ed;       (* arm_STP X13 X8 SP (Immediate_Offset (iword (&64))) *)
  0xa9052be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c81;       (* arm_UMULH X1 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba11002b;       (* arm_ADCS X11 X1 X17 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f002d;       (* arm_ADC X13 X1 XZR *)
  0xeb030051;       (* arm_SUBS X17 X2 X3 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500cf;       (* arm_SUBS X15 X6 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040051;       (* arm_SUBS X17 X2 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500ef;       (* arm_SUBS X15 X7 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040071;       (* arm_SUBS X17 X3 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0600ef;       (* arm_SUBS X15 X7 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba0f018c;       (* arm_ADCS X12 X12 X15 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xa9430fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0xab020108;       (* arm_ADDS X8 X8 X2 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xa9440fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&64))) *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9450fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&80))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0x8b080088;       (* arm_ADD X8 X4 X8 *)
  0xd360fd04;       (* arm_LSR X4 X8 32 *)
  0xeb080084;       (* arm_SUBS X4 X4 X8 *)
  0xda1f0103;       (* arm_SBC X3 X8 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa02016b;       (* arm_SBCS X11 X11 X2 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0x8b090089;       (* arm_ADD X9 X4 X9 *)
  0xd360fd24;       (* arm_LSR X4 X9 32 *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xda1f0123;       (* arm_SBC X3 X9 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0x8b0a008a;       (* arm_ADD X10 X4 X10 *)
  0xd360fd44;       (* arm_LSR X4 X10 32 *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xda1f0143;       (* arm_SBC X3 X10 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab0a0063;       (* arm_ADDS X3 X3 X10 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa0201ad;       (* arm_SBCS X13 X13 X2 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab080231;       (* arm_ADDS X17 X17 X8 *)
  0xba1f0128;       (* arm_ADCS X8 X9 XZR *)
  0xba1f0149;       (* arm_ADCS X9 X10 XZR *)
  0xba1f03ea;       (* arm_ADCS X10 XZR XZR *)
  0x9b057ca1;       (* arm_MUL X1 X5 X5 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x9b067cce;       (* arm_MUL X14 X6 X6 *)
  0x9b077cef;       (* arm_MUL X15 X7 X7 *)
  0x9bc57ca1;       (* arm_UMULH X1 X5 X5 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0x9bc67cc1;       (* arm_UMULH X1 X6 X6 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9bc77ce1;       (* arm_UMULH X1 X7 X7 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9b067ca1;       (* arm_MUL X1 X5 X6 *)
  0x9b077cae;       (* arm_MUL X14 X5 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0xab1001ce;       (* arm_ADDS X14 X14 X16 *)
  0x9bc77cb0;       (* arm_UMULH X16 X5 X7 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab010021;       (* arm_ADDS X1 X1 X1 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb26083e1;       (* arm_MOV X1 (rvalue (word 18446744069414584321)) *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0xd280002f;       (* arm_MOV X15 (rvalue (word 1)) *)
  0xab01017f;       (* arm_CMN X11 X1 *)
  0xba0e019f;       (* arm_ADCS XZR X12 X14 *)
  0xba0f01bf;       (* arm_ADCS XZR X13 X15 *)
  0xba1f023f;       (* arm_ADCS XZR X17 XZR *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x8a0a0021;       (* arm_AND X1 X1 X10 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x8a0a01ce;       (* arm_AND X14 X14 X10 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xa90333eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&48))) *)
  0xa90447ed;       (* arm_STP X13 X17 SP (Immediate_Offset (iword (&64))) *)
  0xa90527e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&80))) *)
  0xa9401b45;       (* arm_LDP X5 X6 X26 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9412347;       (* arm_LDP X7 X8 X26 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9422b49;       (* arm_LDP X9 X10 X26 (Immediate_Offset (iword (&32))) *)
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
  0xa9401b45;       (* arm_LDP X5 X6 X26 (Immediate_Offset (iword (&0))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9412347;       (* arm_LDP X7 X8 X26 (Immediate_Offset (iword (&16))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xa9422b49;       (* arm_LDP X9 X10 X26 (Immediate_Offset (iword (&32))) *)
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
  0xa9501be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xa94c2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&192))) *)
  0xa94d33eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&208))) *)
  0xa94e3bed;       (* arm_LDP X13 X14 SP (Immediate_Offset (iword (&224))) *)
  0x9b097c6f;       (* arm_MUL X15 X3 X9 *)
  0x9b0a7c95;       (* arm_MUL X21 X4 X10 *)
  0x9b0b7cb6;       (* arm_MUL X22 X5 X11 *)
  0x9bc97c77;       (* arm_UMULH X23 X3 X9 *)
  0x9bca7c98;       (* arm_UMULH X24 X4 X10 *)
  0x9bcb7ca1;       (* arm_UMULH X1 X5 X11 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090176;       (* arm_SUBS X22 X11 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0a0176;       (* arm_SUBS X22 X11 X10 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xd3607df7;       (* arm_LSL X23 X15 32 *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 32 *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 32 *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 32 *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 32 *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 32 *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170273;       (* arm_SUBS X19 X19 X23 *)
  0xfa160294;       (* arm_SBCS X20 X20 X22 *)
  0xfa150021;       (* arm_SBCS X1 X1 X21 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xa90653f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&96))) *)
  0xa9073fe1;       (* arm_STP X1 X15 SP (Immediate_Offset (iword (&112))) *)
  0xa90847f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&128))) *)
  0x9b0c7ccf;       (* arm_MUL X15 X6 X12 *)
  0x9b0d7cf5;       (* arm_MUL X21 X7 X13 *)
  0x9b0e7d16;       (* arm_MUL X22 X8 X14 *)
  0x9bcc7cd7;       (* arm_UMULH X23 X6 X12 *)
  0x9bcd7cf8;       (* arm_UMULH X24 X7 X13 *)
  0x9bce7d01;       (* arm_UMULH X1 X8 X14 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0700d8;       (* arm_SUBS X24 X6 X7 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0c01b6;       (* arm_SUBS X22 X13 X12 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800d8;       (* arm_SUBS X24 X6 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0c01d6;       (* arm_SUBS X22 X14 X12 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800f8;       (* arm_SUBS X24 X7 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0d01d6;       (* arm_SUBS X22 X14 X13 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0300c6;       (* arm_SUBS X6 X6 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa050108;       (* arm_SBCS X8 X8 X5 *)
  0xda1f03e3;       (* arm_NGC X3 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xca0300c6;       (* arm_EOR X6 X6 X3 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xca0300e7;       (* arm_EOR X7 X7 X3 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xeb0c0129;       (* arm_SUBS X9 X9 X12 *)
  0xfa0d014a;       (* arm_SBCS X10 X10 X13 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xda1f03ee;       (* arm_NGC X14 XZR *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xca0e0129;       (* arm_EOR X9 X9 X14 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xca0e014a;       (* arm_EOR X10 X10 X14 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca0e016b;       (* arm_EOR X11 X11 X14 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xca0e006e;       (* arm_EOR X14 X3 X14 *)
  0xa9465bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&96))) *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xa9475bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&112))) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xa9485bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&128))) *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0xba160021;       (* arm_ADCS X1 X1 X22 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xa90643ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&96))) *)
  0xa9074ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&112))) *)
  0xa90807f4;       (* arm_STP X20 X1 SP (Immediate_Offset (iword (&128))) *)
  0x9b097ccf;       (* arm_MUL X15 X6 X9 *)
  0x9b0a7cf5;       (* arm_MUL X21 X7 X10 *)
  0x9b0b7d16;       (* arm_MUL X22 X8 X11 *)
  0x9bc97cd7;       (* arm_UMULH X23 X6 X9 *)
  0x9bca7cf8;       (* arm_UMULH X24 X7 X10 *)
  0x9bcb7d01;       (* arm_UMULH X1 X8 X11 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0700d8;       (* arm_SUBS X24 X6 X7 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800d8;       (* arm_SUBS X24 X6 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090176;       (* arm_SUBS X22 X11 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800f8;       (* arm_SUBS X24 X7 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0a0176;       (* arm_SUBS X22 X11 X10 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xba0301ef;       (* arm_ADCS X15 X15 X3 *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xba040210;       (* arm_ADCS X16 X16 X4 *)
  0xca0e0231;       (* arm_EOR X17 X17 X14 *)
  0xba050231;       (* arm_ADCS X17 X17 X5 *)
  0xca0e0273;       (* arm_EOR X19 X19 X14 *)
  0xba060273;       (* arm_ADCS X19 X19 X6 *)
  0xca0e0294;       (* arm_EOR X20 X20 X14 *)
  0xba070294;       (* arm_ADCS X20 X20 X7 *)
  0xca0e0021;       (* arm_EOR X1 X1 X14 *)
  0xba080021;       (* arm_ADCS X1 X1 X8 *)
  0xba0201c9;       (* arm_ADCS X9 X14 X2 *)
  0xba1f01ca;       (* arm_ADCS X10 X14 XZR *)
  0xba1f01cb;       (* arm_ADCS X11 X14 XZR *)
  0x9a1f01cc;       (* arm_ADC X12 X14 XZR *)
  0xab030273;       (* arm_ADDS X19 X19 X3 *)
  0xba040294;       (* arm_ADCS X20 X20 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9a02018c;       (* arm_ADC X12 X12 X2 *)
  0xd3607df7;       (* arm_LSL X23 X15 32 *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 32 *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 32 *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 32 *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 32 *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 32 *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170273;       (* arm_SUBS X19 X19 X23 *)
  0xfa160294;       (* arm_SBCS X20 X20 X22 *)
  0xfa150021;       (* arm_SBCS X1 X1 X21 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xab0f0129;       (* arm_ADDS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x91000596;       (* arm_ADD X22 X12 (rvalue (word 1)) *)
  0xd3607ed5;       (* arm_LSL X21 X22 32 *)
  0xeb1502d8;       (* arm_SUBS X24 X22 X21 *)
  0xda1f02b5;       (* arm_SBC X21 X21 XZR *)
  0xab180273;       (* arm_ADDS X19 X19 X24 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0xba160021;       (* arm_ADCS X1 X1 X22 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xda9f23f6;       (* arm_CSETM X22 Condition_CC *)
  0xb2407ff7;       (* arm_MOV X23 (rvalue (word 4294967295)) *)
  0x8a1602f7;       (* arm_AND X23 X23 X22 *)
  0xab170273;       (* arm_ADDS X19 X19 X23 *)
  0xca1602f7;       (* arm_EOR X23 X23 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x92800037;       (* arm_MOVN X23 (word 1) 0 *)
  0x8a1602f7;       (* arm_AND X23 X23 X22 *)
  0xba170021;       (* arm_ADCS X1 X1 X23 *)
  0xba160129;       (* arm_ADCS X9 X9 X22 *)
  0xba16014a;       (* arm_ADCS X10 X10 X22 *)
  0x9a16016b;       (* arm_ADC X11 X11 X22 *)
  0xa90653f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&96))) *)
  0xa90727e1;       (* arm_STP X1 X9 SP (Immediate_Offset (iword (&112))) *)
  0xa9082fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&128))) *)
  0xa9431b45;       (* arm_LDP X5 X6 X26 (Immediate_Offset (iword (&48))) *)
  0xa9460f44;       (* arm_LDP X4 X3 X26 (Immediate_Offset (iword (&96))) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9442347;       (* arm_LDP X7 X8 X26 (Immediate_Offset (iword (&64))) *)
  0xa9470f44;       (* arm_LDP X4 X3 X26 (Immediate_Offset (iword (&112))) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9452b49;       (* arm_LDP X9 X10 X26 (Immediate_Offset (iword (&80))) *)
  0xa9480f44;       (* arm_LDP X4 X3 X26 (Immediate_Offset (iword (&128))) *)
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
  0xa94717e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&112))) *)
  0xa9481fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&128))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9bc37c51;       (* arm_UMULH X17 X2 X3 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc47c51;       (* arm_UMULH X17 X2 X4 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc47c71;       (* arm_UMULH X17 X3 X4 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc27c49;       (* arm_UMULH X9 X2 X2 *)
  0x9bc37c6b;       (* arm_UMULH X11 X3 X3 *)
  0x9bc47c8d;       (* arm_UMULH X13 X4 X4 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607d10;       (* arm_LSL X16 X8 32 *)
  0x8b080208;       (* arm_ADD X8 X16 X8 *)
  0xd360fd10;       (* arm_LSR X16 X8 32 *)
  0xeb080210;       (* arm_SUBS X16 X16 X8 *)
  0xda1f010f;       (* arm_SBC X15 X8 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0801ef;       (* arm_ADDS X15 X15 X8 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb100129;       (* arm_SUBS X9 X9 X16 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d30;       (* arm_LSL X16 X9 32 *)
  0x8b090209;       (* arm_ADD X9 X16 X9 *)
  0xd360fd30;       (* arm_LSR X16 X9 32 *)
  0xeb090210;       (* arm_SUBS X16 X16 X9 *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0901ef;       (* arm_ADDS X15 X15 X9 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xfa0f016b;       (* arm_SBCS X11 X11 X15 *)
  0xfa0e018c;       (* arm_SBCS X12 X12 X14 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d50;       (* arm_LSL X16 X10 32 *)
  0x8b0a020a;       (* arm_ADD X10 X16 X10 *)
  0xd360fd50;       (* arm_LSR X16 X10 32 *)
  0xeb0a0210;       (* arm_SUBS X16 X16 X10 *)
  0xda1f014f;       (* arm_SBC X15 X10 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10016b;       (* arm_SUBS X11 X11 X16 *)
  0xfa0f018c;       (* arm_SBCS X12 X12 X15 *)
  0xfa0e01ad;       (* arm_SBCS X13 X13 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xa91233eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&288))) *)
  0xa91323ed;       (* arm_STP X13 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9142be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&320))) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c81;       (* arm_UMULH X1 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba11002b;       (* arm_ADCS X11 X1 X17 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f002d;       (* arm_ADC X13 X1 XZR *)
  0xeb030051;       (* arm_SUBS X17 X2 X3 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500cf;       (* arm_SUBS X15 X6 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040051;       (* arm_SUBS X17 X2 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500ef;       (* arm_SUBS X15 X7 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040071;       (* arm_SUBS X17 X3 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0600ef;       (* arm_SUBS X15 X7 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba0f018c;       (* arm_ADCS X12 X12 X15 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xa9520fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0xab020108;       (* arm_ADDS X8 X8 X2 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xa9530fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&304))) *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9540fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&320))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0x8b080088;       (* arm_ADD X8 X4 X8 *)
  0xd360fd04;       (* arm_LSR X4 X8 32 *)
  0xeb080084;       (* arm_SUBS X4 X4 X8 *)
  0xda1f0103;       (* arm_SBC X3 X8 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa02016b;       (* arm_SBCS X11 X11 X2 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0x8b090089;       (* arm_ADD X9 X4 X9 *)
  0xd360fd24;       (* arm_LSR X4 X9 32 *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xda1f0123;       (* arm_SBC X3 X9 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0x8b0a008a;       (* arm_ADD X10 X4 X10 *)
  0xd360fd44;       (* arm_LSR X4 X10 32 *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xda1f0143;       (* arm_SBC X3 X10 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab0a0063;       (* arm_ADDS X3 X3 X10 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa0201ad;       (* arm_SBCS X13 X13 X2 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab080231;       (* arm_ADDS X17 X17 X8 *)
  0xba1f0128;       (* arm_ADCS X8 X9 XZR *)
  0xba1f0149;       (* arm_ADCS X9 X10 XZR *)
  0xba1f03ea;       (* arm_ADCS X10 XZR XZR *)
  0x9b057ca1;       (* arm_MUL X1 X5 X5 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x9b067cce;       (* arm_MUL X14 X6 X6 *)
  0x9b077cef;       (* arm_MUL X15 X7 X7 *)
  0x9bc57ca1;       (* arm_UMULH X1 X5 X5 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0x9bc67cc1;       (* arm_UMULH X1 X6 X6 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9bc77ce1;       (* arm_UMULH X1 X7 X7 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9b067ca1;       (* arm_MUL X1 X5 X6 *)
  0x9b077cae;       (* arm_MUL X14 X5 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0xab1001ce;       (* arm_ADDS X14 X14 X16 *)
  0x9bc77cb0;       (* arm_UMULH X16 X5 X7 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab010021;       (* arm_ADDS X1 X1 X1 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb26083e1;       (* arm_MOV X1 (rvalue (word 18446744069414584321)) *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0xd280002f;       (* arm_MOV X15 (rvalue (word 1)) *)
  0xab01017f;       (* arm_CMN X11 X1 *)
  0xba0e019f;       (* arm_ADCS XZR X12 X14 *)
  0xba0f01bf;       (* arm_ADCS XZR X13 X15 *)
  0xba1f023f;       (* arm_ADCS XZR X17 XZR *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x8a0a0021;       (* arm_AND X1 X1 X10 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x8a0a01ce;       (* arm_AND X14 X14 X10 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xa91233eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&288))) *)
  0xa91347ed;       (* arm_STP X13 X17 SP (Immediate_Offset (iword (&304))) *)
  0xa91427e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&320))) *)
  0xa9401343;       (* arm_LDP X3 X4 X26 (Immediate_Offset (iword (&0))) *)
  0xa9411b45;       (* arm_LDP X5 X6 X26 (Immediate_Offset (iword (&16))) *)
  0xa9422347;       (* arm_LDP X7 X8 X26 (Immediate_Offset (iword (&32))) *)
  0xa9432be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0xa94433eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&64))) *)
  0xa9453bed;       (* arm_LDP X13 X14 SP (Immediate_Offset (iword (&80))) *)
  0x9b097c6f;       (* arm_MUL X15 X3 X9 *)
  0x9b0a7c95;       (* arm_MUL X21 X4 X10 *)
  0x9b0b7cb6;       (* arm_MUL X22 X5 X11 *)
  0x9bc97c77;       (* arm_UMULH X23 X3 X9 *)
  0x9bca7c98;       (* arm_UMULH X24 X4 X10 *)
  0x9bcb7ca1;       (* arm_UMULH X1 X5 X11 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090176;       (* arm_SUBS X22 X11 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0a0176;       (* arm_SUBS X22 X11 X10 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xd3607df7;       (* arm_LSL X23 X15 32 *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 32 *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 32 *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 32 *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 32 *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 32 *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170273;       (* arm_SUBS X19 X19 X23 *)
  0xfa160294;       (* arm_SBCS X20 X20 X22 *)
  0xfa150021;       (* arm_SBCS X1 X1 X21 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xa90953f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&144))) *)
  0xa90a3fe1;       (* arm_STP X1 X15 SP (Immediate_Offset (iword (&160))) *)
  0xa90b47f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&176))) *)
  0x9b0c7ccf;       (* arm_MUL X15 X6 X12 *)
  0x9b0d7cf5;       (* arm_MUL X21 X7 X13 *)
  0x9b0e7d16;       (* arm_MUL X22 X8 X14 *)
  0x9bcc7cd7;       (* arm_UMULH X23 X6 X12 *)
  0x9bcd7cf8;       (* arm_UMULH X24 X7 X13 *)
  0x9bce7d01;       (* arm_UMULH X1 X8 X14 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0700d8;       (* arm_SUBS X24 X6 X7 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0c01b6;       (* arm_SUBS X22 X13 X12 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800d8;       (* arm_SUBS X24 X6 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0c01d6;       (* arm_SUBS X22 X14 X12 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800f8;       (* arm_SUBS X24 X7 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0d01d6;       (* arm_SUBS X22 X14 X13 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0300c6;       (* arm_SUBS X6 X6 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa050108;       (* arm_SBCS X8 X8 X5 *)
  0xda1f03e3;       (* arm_NGC X3 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xca0300c6;       (* arm_EOR X6 X6 X3 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xca0300e7;       (* arm_EOR X7 X7 X3 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xeb0c0129;       (* arm_SUBS X9 X9 X12 *)
  0xfa0d014a;       (* arm_SBCS X10 X10 X13 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xda1f03ee;       (* arm_NGC X14 XZR *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xca0e0129;       (* arm_EOR X9 X9 X14 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xca0e014a;       (* arm_EOR X10 X10 X14 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca0e016b;       (* arm_EOR X11 X11 X14 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xca0e006e;       (* arm_EOR X14 X3 X14 *)
  0xa9495bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&144))) *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xa94a5bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&160))) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xa94b5bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&176))) *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0xba160021;       (* arm_ADCS X1 X1 X22 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xa90943ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&144))) *)
  0xa90a4ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&160))) *)
  0xa90b07f4;       (* arm_STP X20 X1 SP (Immediate_Offset (iword (&176))) *)
  0x9b097ccf;       (* arm_MUL X15 X6 X9 *)
  0x9b0a7cf5;       (* arm_MUL X21 X7 X10 *)
  0x9b0b7d16;       (* arm_MUL X22 X8 X11 *)
  0x9bc97cd7;       (* arm_UMULH X23 X6 X9 *)
  0x9bca7cf8;       (* arm_UMULH X24 X7 X10 *)
  0x9bcb7d01;       (* arm_UMULH X1 X8 X11 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0700d8;       (* arm_SUBS X24 X6 X7 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800d8;       (* arm_SUBS X24 X6 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090176;       (* arm_SUBS X22 X11 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800f8;       (* arm_SUBS X24 X7 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0a0176;       (* arm_SUBS X22 X11 X10 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xa94913e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0xa94a1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa94b23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xba0301ef;       (* arm_ADCS X15 X15 X3 *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xba040210;       (* arm_ADCS X16 X16 X4 *)
  0xca0e0231;       (* arm_EOR X17 X17 X14 *)
  0xba050231;       (* arm_ADCS X17 X17 X5 *)
  0xca0e0273;       (* arm_EOR X19 X19 X14 *)
  0xba060273;       (* arm_ADCS X19 X19 X6 *)
  0xca0e0294;       (* arm_EOR X20 X20 X14 *)
  0xba070294;       (* arm_ADCS X20 X20 X7 *)
  0xca0e0021;       (* arm_EOR X1 X1 X14 *)
  0xba080021;       (* arm_ADCS X1 X1 X8 *)
  0xba0201c9;       (* arm_ADCS X9 X14 X2 *)
  0xba1f01ca;       (* arm_ADCS X10 X14 XZR *)
  0xba1f01cb;       (* arm_ADCS X11 X14 XZR *)
  0x9a1f01cc;       (* arm_ADC X12 X14 XZR *)
  0xab030273;       (* arm_ADDS X19 X19 X3 *)
  0xba040294;       (* arm_ADCS X20 X20 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9a02018c;       (* arm_ADC X12 X12 X2 *)
  0xd3607df7;       (* arm_LSL X23 X15 32 *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 32 *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 32 *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 32 *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 32 *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 32 *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170273;       (* arm_SUBS X19 X19 X23 *)
  0xfa160294;       (* arm_SBCS X20 X20 X22 *)
  0xfa150021;       (* arm_SBCS X1 X1 X21 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xab0f0129;       (* arm_ADDS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x91000596;       (* arm_ADD X22 X12 (rvalue (word 1)) *)
  0xd3607ed5;       (* arm_LSL X21 X22 32 *)
  0xeb1502d8;       (* arm_SUBS X24 X22 X21 *)
  0xda1f02b5;       (* arm_SBC X21 X21 XZR *)
  0xab180273;       (* arm_ADDS X19 X19 X24 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0xba160021;       (* arm_ADCS X1 X1 X22 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xda9f23f6;       (* arm_CSETM X22 Condition_CC *)
  0xb2407ff7;       (* arm_MOV X23 (rvalue (word 4294967295)) *)
  0x8a1602f7;       (* arm_AND X23 X23 X22 *)
  0xab170273;       (* arm_ADDS X19 X19 X23 *)
  0xca1602f7;       (* arm_EOR X23 X23 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x92800037;       (* arm_MOVN X23 (word 1) 0 *)
  0x8a1602f7;       (* arm_AND X23 X23 X22 *)
  0xba170021;       (* arm_ADCS X1 X1 X23 *)
  0xba160129;       (* arm_ADCS X9 X9 X22 *)
  0xba16014a;       (* arm_ADCS X10 X10 X22 *)
  0x9a16016b;       (* arm_ADC X11 X11 X22 *)
  0xa90953f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&144))) *)
  0xa90a27e1;       (* arm_STP X1 X9 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0xa94f0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&240))) *)
  0xa95017e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&256))) *)
  0xa9511fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&272))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9bc37c51;       (* arm_UMULH X17 X2 X3 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc47c51;       (* arm_UMULH X17 X2 X4 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc47c71;       (* arm_UMULH X17 X3 X4 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc27c49;       (* arm_UMULH X9 X2 X2 *)
  0x9bc37c6b;       (* arm_UMULH X11 X3 X3 *)
  0x9bc47c8d;       (* arm_UMULH X13 X4 X4 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607d10;       (* arm_LSL X16 X8 32 *)
  0x8b080208;       (* arm_ADD X8 X16 X8 *)
  0xd360fd10;       (* arm_LSR X16 X8 32 *)
  0xeb080210;       (* arm_SUBS X16 X16 X8 *)
  0xda1f010f;       (* arm_SBC X15 X8 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0801ef;       (* arm_ADDS X15 X15 X8 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb100129;       (* arm_SUBS X9 X9 X16 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d30;       (* arm_LSL X16 X9 32 *)
  0x8b090209;       (* arm_ADD X9 X16 X9 *)
  0xd360fd30;       (* arm_LSR X16 X9 32 *)
  0xeb090210;       (* arm_SUBS X16 X16 X9 *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0901ef;       (* arm_ADDS X15 X15 X9 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xfa0f016b;       (* arm_SBCS X11 X11 X15 *)
  0xfa0e018c;       (* arm_SBCS X12 X12 X14 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d50;       (* arm_LSL X16 X10 32 *)
  0x8b0a020a;       (* arm_ADD X10 X16 X10 *)
  0xd360fd50;       (* arm_LSR X16 X10 32 *)
  0xeb0a0210;       (* arm_SUBS X16 X16 X10 *)
  0xda1f014f;       (* arm_SBC X15 X10 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10016b;       (* arm_SUBS X11 X11 X16 *)
  0xfa0f018c;       (* arm_SBCS X12 X12 X15 *)
  0xfa0e01ad;       (* arm_SBCS X13 X13 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23ed;       (* arm_STP X13 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa90e2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&224))) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c81;       (* arm_UMULH X1 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba11002b;       (* arm_ADCS X11 X1 X17 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f002d;       (* arm_ADC X13 X1 XZR *)
  0xeb030051;       (* arm_SUBS X17 X2 X3 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500cf;       (* arm_SUBS X15 X6 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040051;       (* arm_SUBS X17 X2 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500ef;       (* arm_SUBS X15 X7 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040071;       (* arm_SUBS X17 X3 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0600ef;       (* arm_SUBS X15 X7 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba0f018c;       (* arm_ADCS X12 X12 X15 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xa94c0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&192))) *)
  0xab020108;       (* arm_ADDS X8 X8 X2 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xa94d0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa94e0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&224))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0x8b080088;       (* arm_ADD X8 X4 X8 *)
  0xd360fd04;       (* arm_LSR X4 X8 32 *)
  0xeb080084;       (* arm_SUBS X4 X4 X8 *)
  0xda1f0103;       (* arm_SBC X3 X8 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa02016b;       (* arm_SBCS X11 X11 X2 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0x8b090089;       (* arm_ADD X9 X4 X9 *)
  0xd360fd24;       (* arm_LSR X4 X9 32 *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xda1f0123;       (* arm_SBC X3 X9 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0x8b0a008a;       (* arm_ADD X10 X4 X10 *)
  0xd360fd44;       (* arm_LSR X4 X10 32 *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xda1f0143;       (* arm_SBC X3 X10 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab0a0063;       (* arm_ADDS X3 X3 X10 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa0201ad;       (* arm_SBCS X13 X13 X2 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab080231;       (* arm_ADDS X17 X17 X8 *)
  0xba1f0128;       (* arm_ADCS X8 X9 XZR *)
  0xba1f0149;       (* arm_ADCS X9 X10 XZR *)
  0xba1f03ea;       (* arm_ADCS X10 XZR XZR *)
  0x9b057ca1;       (* arm_MUL X1 X5 X5 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x9b067cce;       (* arm_MUL X14 X6 X6 *)
  0x9b077cef;       (* arm_MUL X15 X7 X7 *)
  0x9bc57ca1;       (* arm_UMULH X1 X5 X5 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0x9bc67cc1;       (* arm_UMULH X1 X6 X6 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9bc77ce1;       (* arm_UMULH X1 X7 X7 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9b067ca1;       (* arm_MUL X1 X5 X6 *)
  0x9b077cae;       (* arm_MUL X14 X5 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0xab1001ce;       (* arm_ADDS X14 X14 X16 *)
  0x9bc77cb0;       (* arm_UMULH X16 X5 X7 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab010021;       (* arm_ADDS X1 X1 X1 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb26083e1;       (* arm_MOV X1 (rvalue (word 18446744069414584321)) *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0xd280002f;       (* arm_MOV X15 (rvalue (word 1)) *)
  0xab01017f;       (* arm_CMN X11 X1 *)
  0xba0e019f;       (* arm_ADCS XZR X12 X14 *)
  0xba0f01bf;       (* arm_ADCS XZR X13 X15 *)
  0xba1f023f;       (* arm_ADCS XZR X17 XZR *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x8a0a0021;       (* arm_AND X1 X1 X10 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x8a0a01ce;       (* arm_AND X14 X14 X10 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xa90d47ed;       (* arm_STP X13 X17 SP (Immediate_Offset (iword (&208))) *)
  0xa90e27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&224))) *)
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
  0xa94417e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&64))) *)
  0xa9451fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&80))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9bc37c51;       (* arm_UMULH X17 X2 X3 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc47c51;       (* arm_UMULH X17 X2 X4 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc47c71;       (* arm_UMULH X17 X3 X4 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc27c49;       (* arm_UMULH X9 X2 X2 *)
  0x9bc37c6b;       (* arm_UMULH X11 X3 X3 *)
  0x9bc47c8d;       (* arm_UMULH X13 X4 X4 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607d10;       (* arm_LSL X16 X8 32 *)
  0x8b080208;       (* arm_ADD X8 X16 X8 *)
  0xd360fd10;       (* arm_LSR X16 X8 32 *)
  0xeb080210;       (* arm_SUBS X16 X16 X8 *)
  0xda1f010f;       (* arm_SBC X15 X8 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0801ef;       (* arm_ADDS X15 X15 X8 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb100129;       (* arm_SUBS X9 X9 X16 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d30;       (* arm_LSL X16 X9 32 *)
  0x8b090209;       (* arm_ADD X9 X16 X9 *)
  0xd360fd30;       (* arm_LSR X16 X9 32 *)
  0xeb090210;       (* arm_SUBS X16 X16 X9 *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0901ef;       (* arm_ADDS X15 X15 X9 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xfa0f016b;       (* arm_SBCS X11 X11 X15 *)
  0xfa0e018c;       (* arm_SBCS X12 X12 X14 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d50;       (* arm_LSL X16 X10 32 *)
  0x8b0a020a;       (* arm_ADD X10 X16 X10 *)
  0xd360fd50;       (* arm_LSR X16 X10 32 *)
  0xeb0a0210;       (* arm_SUBS X16 X16 X10 *)
  0xda1f014f;       (* arm_SBC X15 X10 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10016b;       (* arm_SUBS X11 X11 X16 *)
  0xfa0f018c;       (* arm_SBCS X12 X12 X15 *)
  0xfa0e01ad;       (* arm_SBCS X13 X13 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23ed;       (* arm_STP X13 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa90e2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&224))) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c81;       (* arm_UMULH X1 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba11002b;       (* arm_ADCS X11 X1 X17 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f002d;       (* arm_ADC X13 X1 XZR *)
  0xeb030051;       (* arm_SUBS X17 X2 X3 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500cf;       (* arm_SUBS X15 X6 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040051;       (* arm_SUBS X17 X2 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500ef;       (* arm_SUBS X15 X7 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040071;       (* arm_SUBS X17 X3 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0600ef;       (* arm_SUBS X15 X7 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba0f018c;       (* arm_ADCS X12 X12 X15 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xa94c0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&192))) *)
  0xab020108;       (* arm_ADDS X8 X8 X2 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xa94d0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa94e0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&224))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xd3607d04;       (* arm_LSL X4 X8 32 *)
  0x8b080088;       (* arm_ADD X8 X4 X8 *)
  0xd360fd04;       (* arm_LSR X4 X8 32 *)
  0xeb080084;       (* arm_SUBS X4 X4 X8 *)
  0xda1f0103;       (* arm_SBC X3 X8 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa02016b;       (* arm_SBCS X11 X11 X2 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d24;       (* arm_LSL X4 X9 32 *)
  0x8b090089;       (* arm_ADD X9 X4 X9 *)
  0xd360fd24;       (* arm_LSR X4 X9 32 *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xda1f0123;       (* arm_SBC X3 X9 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d44;       (* arm_LSL X4 X10 32 *)
  0x8b0a008a;       (* arm_ADD X10 X4 X10 *)
  0xd360fd44;       (* arm_LSR X4 X10 32 *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xda1f0143;       (* arm_SBC X3 X10 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xab0a0063;       (* arm_ADDS X3 X3 X10 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa0201ad;       (* arm_SBCS X13 X13 X2 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab080231;       (* arm_ADDS X17 X17 X8 *)
  0xba1f0128;       (* arm_ADCS X8 X9 XZR *)
  0xba1f0149;       (* arm_ADCS X9 X10 XZR *)
  0xba1f03ea;       (* arm_ADCS X10 XZR XZR *)
  0x9b057ca1;       (* arm_MUL X1 X5 X5 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x9b067cce;       (* arm_MUL X14 X6 X6 *)
  0x9b077cef;       (* arm_MUL X15 X7 X7 *)
  0x9bc57ca1;       (* arm_UMULH X1 X5 X5 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0x9bc67cc1;       (* arm_UMULH X1 X6 X6 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9bc77ce1;       (* arm_UMULH X1 X7 X7 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9b067ca1;       (* arm_MUL X1 X5 X6 *)
  0x9b077cae;       (* arm_MUL X14 X5 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0xab1001ce;       (* arm_ADDS X14 X14 X16 *)
  0x9bc77cb0;       (* arm_UMULH X16 X5 X7 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab010021;       (* arm_ADDS X1 X1 X1 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb26083e1;       (* arm_MOV X1 (rvalue (word 18446744069414584321)) *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0xd280002f;       (* arm_MOV X15 (rvalue (word 1)) *)
  0xab01017f;       (* arm_CMN X11 X1 *)
  0xba0e019f;       (* arm_ADCS XZR X12 X14 *)
  0xba0f01bf;       (* arm_ADCS XZR X13 X15 *)
  0xba1f023f;       (* arm_ADCS XZR X17 XZR *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x8a0a0021;       (* arm_AND X1 X1 X10 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x8a0a01ce;       (* arm_AND X14 X14 X10 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xa90d47ed;       (* arm_STP X13 X17 SP (Immediate_Offset (iword (&208))) *)
  0xa90e27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&224))) *)
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
  0xa9061b25;       (* arm_STP X5 X6 X25 (Immediate_Offset (iword (&96))) *)
  0xa9072327;       (* arm_STP X7 X8 X25 (Immediate_Offset (iword (&112))) *)
  0xa9082b29;       (* arm_STP X9 X10 X25 (Immediate_Offset (iword (&128))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa95423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&320))) *)
  0xa9462be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&96))) *)
  0xa94733eb;       (* arm_LDP X11 X12 SP (Immediate_Offset (iword (&112))) *)
  0xa9483bed;       (* arm_LDP X13 X14 SP (Immediate_Offset (iword (&128))) *)
  0x9b097c6f;       (* arm_MUL X15 X3 X9 *)
  0x9b0a7c95;       (* arm_MUL X21 X4 X10 *)
  0x9b0b7cb6;       (* arm_MUL X22 X5 X11 *)
  0x9bc97c77;       (* arm_UMULH X23 X3 X9 *)
  0x9bca7c98;       (* arm_UMULH X24 X4 X10 *)
  0x9bcb7ca1;       (* arm_UMULH X1 X5 X11 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090176;       (* arm_SUBS X22 X11 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0a0176;       (* arm_SUBS X22 X11 X10 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xd3607df7;       (* arm_LSL X23 X15 32 *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 32 *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 32 *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 32 *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 32 *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 32 *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170273;       (* arm_SUBS X19 X19 X23 *)
  0xfa160294;       (* arm_SBCS X20 X20 X22 *)
  0xfa150021;       (* arm_SBCS X1 X1 X21 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xa90f53f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&240))) *)
  0xa9103fe1;       (* arm_STP X1 X15 SP (Immediate_Offset (iword (&256))) *)
  0xa91147f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&272))) *)
  0x9b0c7ccf;       (* arm_MUL X15 X6 X12 *)
  0x9b0d7cf5;       (* arm_MUL X21 X7 X13 *)
  0x9b0e7d16;       (* arm_MUL X22 X8 X14 *)
  0x9bcc7cd7;       (* arm_UMULH X23 X6 X12 *)
  0x9bcd7cf8;       (* arm_UMULH X24 X7 X13 *)
  0x9bce7d01;       (* arm_UMULH X1 X8 X14 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0700d8;       (* arm_SUBS X24 X6 X7 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0c01b6;       (* arm_SUBS X22 X13 X12 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800d8;       (* arm_SUBS X24 X6 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0c01d6;       (* arm_SUBS X22 X14 X12 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800f8;       (* arm_SUBS X24 X7 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0d01d6;       (* arm_SUBS X22 X14 X13 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0300c6;       (* arm_SUBS X6 X6 X3 *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa050108;       (* arm_SBCS X8 X8 X5 *)
  0xda1f03e3;       (* arm_NGC X3 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xca0300c6;       (* arm_EOR X6 X6 X3 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xca0300e7;       (* arm_EOR X7 X7 X3 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xeb0c0129;       (* arm_SUBS X9 X9 X12 *)
  0xfa0d014a;       (* arm_SBCS X10 X10 X13 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xda1f03ee;       (* arm_NGC X14 XZR *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xca0e0129;       (* arm_EOR X9 X9 X14 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xca0e014a;       (* arm_EOR X10 X10 X14 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca0e016b;       (* arm_EOR X11 X11 X14 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xca0e006e;       (* arm_EOR X14 X3 X14 *)
  0xa94f5bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&240))) *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xa9505bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&256))) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xa9515bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&272))) *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0xba160021;       (* arm_ADCS X1 X1 X22 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xa90f43ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&240))) *)
  0xa9104ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&256))) *)
  0xa91107f4;       (* arm_STP X20 X1 SP (Immediate_Offset (iword (&272))) *)
  0x9b097ccf;       (* arm_MUL X15 X6 X9 *)
  0x9b0a7cf5;       (* arm_MUL X21 X7 X10 *)
  0x9b0b7d16;       (* arm_MUL X22 X8 X11 *)
  0x9bc97cd7;       (* arm_UMULH X23 X6 X9 *)
  0x9bca7cf8;       (* arm_UMULH X24 X7 X10 *)
  0x9bcb7d01;       (* arm_UMULH X1 X8 X11 *)
  0xab1502f7;       (* arm_ADDS X23 X23 X21 *)
  0xba160318;       (* arm_ADCS X24 X24 X22 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0f02f0;       (* arm_ADDS X16 X23 X15 *)
  0xba170311;       (* arm_ADCS X17 X24 X23 *)
  0xba180033;       (* arm_ADCS X19 X1 X24 *)
  0x9a1f0034;       (* arm_ADC X20 X1 XZR *)
  0xab0f0231;       (* arm_ADDS X17 X17 X15 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba180294;       (* arm_ADCS X20 X20 X24 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0700d8;       (* arm_SUBS X24 X6 X7 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0xba170273;       (* arm_ADCS X19 X19 X23 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800d8;       (* arm_SUBS X24 X6 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb090176;       (* arm_SUBS X22 X11 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xeb0800f8;       (* arm_SUBS X24 X7 X8 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f7;       (* arm_CSETM X23 Condition_CC *)
  0xeb0a0176;       (* arm_SUBS X22 X11 X10 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f15;       (* arm_MUL X21 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9722f7;       (* arm_CINV X23 X23 Condition_CC *)
  0xca1702b5;       (* arm_EOR X21 X21 X23 *)
  0xca1702d6;       (* arm_EOR X22 X22 X23 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xba150273;       (* arm_ADCS X19 X19 X21 *)
  0xba160294;       (* arm_ADCS X20 X20 X22 *)
  0x9a170021;       (* arm_ADC X1 X1 X23 *)
  0xa94f13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&240))) *)
  0xa9501be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xba0301ef;       (* arm_ADCS X15 X15 X3 *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xba040210;       (* arm_ADCS X16 X16 X4 *)
  0xca0e0231;       (* arm_EOR X17 X17 X14 *)
  0xba050231;       (* arm_ADCS X17 X17 X5 *)
  0xca0e0273;       (* arm_EOR X19 X19 X14 *)
  0xba060273;       (* arm_ADCS X19 X19 X6 *)
  0xca0e0294;       (* arm_EOR X20 X20 X14 *)
  0xba070294;       (* arm_ADCS X20 X20 X7 *)
  0xca0e0021;       (* arm_EOR X1 X1 X14 *)
  0xba080021;       (* arm_ADCS X1 X1 X8 *)
  0xba0201c9;       (* arm_ADCS X9 X14 X2 *)
  0xba1f01ca;       (* arm_ADCS X10 X14 XZR *)
  0xba1f01cb;       (* arm_ADCS X11 X14 XZR *)
  0x9a1f01cc;       (* arm_ADC X12 X14 XZR *)
  0xab030273;       (* arm_ADDS X19 X19 X3 *)
  0xba040294;       (* arm_ADCS X20 X20 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9a02018c;       (* arm_ADC X12 X12 X2 *)
  0xd3607df7;       (* arm_LSL X23 X15 32 *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 32 *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 32 *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 32 *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 32 *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 32 *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 32 *)
  0xd360fed6;       (* arm_LSR X22 X22 32 *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170273;       (* arm_SUBS X19 X19 X23 *)
  0xfa160294;       (* arm_SBCS X20 X20 X22 *)
  0xfa150021;       (* arm_SBCS X1 X1 X21 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xab0f0129;       (* arm_ADDS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x91000596;       (* arm_ADD X22 X12 (rvalue (word 1)) *)
  0xd3607ed5;       (* arm_LSL X21 X22 32 *)
  0xeb1502d8;       (* arm_SUBS X24 X22 X21 *)
  0xda1f02b5;       (* arm_SBC X21 X21 XZR *)
  0xab180273;       (* arm_ADDS X19 X19 X24 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0xba160021;       (* arm_ADCS X1 X1 X22 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xda9f23f6;       (* arm_CSETM X22 Condition_CC *)
  0xb2407ff7;       (* arm_MOV X23 (rvalue (word 4294967295)) *)
  0x8a1602f7;       (* arm_AND X23 X23 X22 *)
  0xab170273;       (* arm_ADDS X19 X19 X23 *)
  0xca1602f7;       (* arm_EOR X23 X23 X22 *)
  0xba170294;       (* arm_ADCS X20 X20 X23 *)
  0x92800037;       (* arm_MOVN X23 (word 1) 0 *)
  0x8a1602f7;       (* arm_AND X23 X23 X22 *)
  0xba170021;       (* arm_ADCS X1 X1 X23 *)
  0xba160129;       (* arm_ADCS X9 X9 X22 *)
  0xba16014a;       (* arm_ADCS X10 X10 X22 *)
  0x9a16016b;       (* arm_ADC X11 X11 X22 *)
  0xa90f53f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&240))) *)
  0xa91027e1;       (* arm_STP X1 X9 SP (Immediate_Offset (iword (&256))) *)
  0xa9112fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&272))) *)
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
  0xa9000720;       (* arm_STP X0 X1 X25 (Immediate_Offset (iword (&0))) *)
  0xa9010f22;       (* arm_STP X2 X3 X25 (Immediate_Offset (iword (&16))) *)
  0xa9021724;       (* arm_STP X4 X5 X25 (Immediate_Offset (iword (&32))) *)
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
  0xa9030720;       (* arm_STP X0 X1 X25 (Immediate_Offset (iword (&48))) *)
  0xa9040f22;       (* arm_STP X2 X3 X25 (Immediate_Offset (iword (&64))) *)
  0xa9051724;       (* arm_STP X4 X5 X25 (Immediate_Offset (iword (&80))) *)
  0xa95553f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&336))) *)
  0xa9565bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&352))) *)
  0xa95763f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&368))) *)
  0xa9586bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&384))) *)
  0x910643ff;       (* arm_ADD SP SP (rvalue (word 400)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P384_MONTJDOUBLE_EXEC = ARM_MK_EXEC_RULE p384_montjdouble_mc;;

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

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(4294967297 * val x):int64)) * &18446744069414584321
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let p384shortredlemma = prove
 (`!n. n < 3 * p_384
       ==> let q = (n DIV 2 EXP 384) + 1 in
           q <= 3 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

(*** Intricate Montgomery steps done generically ***)

let montred_tac execth regs n =
  let topflag,[d7;d6;d5;d4;d3;d2;d1;d0; t3;t2;t1] =
    let rlist = dest_list regs in
    if length rlist = 11 then true,rlist
    else false,`XZR`::rlist in
  let modterm = subst
   ([d0,`X2`; d1,`X3`; d2,`X4`; d3,`X5`; d4,`X6`; d5,`X7`; d6,`X1`; d7,`X0`;
     t1,`X10`; t2,`X9`; t3,`X8`] @
    (map (fun i -> mk_var("s"^string_of_int(i+n-3),`:armstate`),
                   mk_var("s"^string_of_int(i),`:armstate`))
         (3--20)) @
    [mk_var("sum_s"^string_of_int(7+n-3),`:int64`),
     mk_var("sum_s"^string_of_int(7),`:int64`);
     mk_var("sum_s"^string_of_int(8+n-3),`:int64`),
     mk_var("sum_s"^string_of_int(8),`:int64`)] @
    [mk_var("mvl_"^string_of_int n,`:num`),mk_var("mvl",`:num`);
     mk_var("nvl_"^string_of_int n,`:num`),mk_var("nvl",`:num`);
     mk_var("ww_"^string_of_int n,`:int64`),mk_var("w",`:int64`);
     mk_var("tt_"^string_of_int n,`:num`),mk_var("t",`:num`)])
  and modstring =
   C assoc
    (zip (statenames "s" (3--20)) (statenames "s" (n--(n+17))) @
    ["mvl","mvl_"^string_of_int n;
     "w","ww_"^string_of_int n;
     "t","tt_"^string_of_int n]) in
  (*** Abbreviate the input ***)
  ABBREV_TAC
   (modterm `mvl =
    bignum_of_wordlist[read X2 s3; read X3 s3; read X4 s3; read X5 s3;
                       read X6 s3; read X7 s3]`) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (if topflag then
     ABBREV_TAC
     (modterm `nvl =
      bignum_of_wordlist[read X2 s3; read X3 s3; read X4 s3; read X5 s3;
                         read X6 s3; read X7 s3; read X1 s3]`) THEN
     POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
   else ALL_TAC) THEN
  (*** Selection of the multiplier, similar to the x86 case ***)
  MAP_EVERY (ARM_SINGLE_STEP_TAC execth)
            (map modstring (statenames "s" (4--5))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
  REABBREV_TAC (modterm `w = read X2 s5`) THEN
  (*** Next three steps setting up [t2;t1] = 2^64 * w - w + w_hi ***)
  ARM_SINGLE_STEP_TAC execth (modstring "s6") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s7") THEN
  ACCUMULATE_ARITH_TAC (modstring "s7") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s8") THEN
  ACCUMULATE_ARITH_TAC (modstring "s8") THEN
  SUBGOAL_THEN
   (modterm `&2 pow 64 * &(val(read X9 s8)) + &(val(read X10 s8)):real =
    &2 pow 64 * &(val(w:int64)) - &(val w) + &(val w DIV 2 EXP 32)`)
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (*** Next four steps setting up
   *** [t3;t2;t1] = (2^128 + 2^96 - 2^32 + 1) * w - w MOD 2^32
   ***)
  ARM_SINGLE_STEP_TAC execth (modstring "s9") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s10") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s11") THEN
  ACCUMULATE_ARITH_TAC (modstring "s11") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s12") THEN
  (*** This is what we really want ***)
  ABBREV_TAC
   (modterm `t = 2 EXP 64 * val(sum_s8:int64) + val(sum_s7:int64)`) THEN
  SUBGOAL_THEN
   (modterm `&(bignum_of_wordlist
       [word(mvl MOD 2 EXP 64); read X10 s12; read X9 s12; read X8 s12]):real =
    (&2 pow 128 + &2 pow 96 - &2 pow 32 + &1) * &(val(w:int64))`)
  MP_TAC THEN
  EXPAND_TAC (modstring "mvl") THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD; WORD_VAL] THENL
   [TRANS_TAC EQ_TRANS
     (modterm `&2 pow 128 * &(val(w:int64)) +
      &2 pow 32 * &t + &(val w MOD 2 EXP 32)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL EQ_DIVMOD))));
      EXPAND_TAC (modstring "t") THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      REAL_ARITH_TAC] THEN
    EXISTS_TAC `2 EXP 64` THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[DIV_LT; VAL_BOUND_64; ADD_CLAUSES] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `(2 EXP 128 * w + 2 EXP 32 * t + r MOD 2 EXP 32) DIV 2 EXP 64 =
        2 EXP 64 * w + t DIV 2 EXP 32`];
      REWRITE_TAC[GSYM CONG; num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `!y:int. z = y /\ (y == x) (mod n)
                ==> (x == z) (mod n)`) THEN
      EXISTS_TAC
       (modterm `(&2 pow 128 + &2 pow 96 - &2 pow 32 + &1) *
                 &(val(w:int64)):int`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[int_eq; int_pow_th; int_mul_th; int_sub_th; int_add_th;
                    int_of_num_th] THEN
        EXPAND_TAC (modstring "t") THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check
         (can (term_match [] `word(4294967297 * x) = w`) o concl)) THEN
        REWRITE_TAC[GSYM INT_REM_EQ; VAL_WORD; DIMINDEX_64] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
        CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
        MATCH_MP_TAC(INTEGER_RULE
         `(a * b:int == &1) (mod p) ==> (a * b * x == x) (mod p)`) THEN
        REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV]] THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `s + 2 EXP 64 * c = 2 EXP 64 * c + s`] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT; VAL_WORD_USHR] THEN
    REWRITE_TAC[VAL_WORD_0] THEN EXPAND_TAC (modstring "t") THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  (*** The main accumulation of the same-size portion and adding to w ***)
  MAP_EVERY (fun s ->
        ARM_SINGLE_STEP_TAC execth s THEN
        ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
    (map modstring (statenames "s" (13--18))) THEN
  SUBGOAL_THEN
   (modterm
     (if topflag then
       `&2 pow 64 * &(bignum_of_wordlist[read X3 s18; read X4 s18; read X5 s18;
                                  read X6 s18; read X7 s18; read X2 s18]) =
        &mvl + &p_384 * &(val(w:int64))`
      else
       `&2 pow 64 * &(bignum_of_wordlist[read X3 s18; read X4 s18; read X5 s18;
                                  read X6 s18; read X7 s18; read X1 s18]) =
        &mvl + &p_384 * &(val(w:int64))`))
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    EXPAND_TAC(modstring "mvl") THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o RAND_CONV)
     [CONJUNCT2 bignum_of_wordlist]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `x + a:real = b ==> x = b - a`)) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_REWRITE_TAC[] THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  (*** Final little accumulation in the non-short case ***)
  (if topflag then
     DISCH_TAC THEN
     ARM_SINGLE_STEP_TAC execth (modstring "s19") THEN
     ACCUMULATE_ARITH_TAC (modstring "s19") THEN
     ARM_SINGLE_STEP_TAC execth (modstring "s20") THEN
     SUBGOAL_THEN (modterm
      `&2 pow 64 * &(bignum_of_wordlist[read X3 s20; read X4 s20; read X5 s20;
                       read X6 s20; read X7 s20; read X1 s20; read X0 s20]) =
        &nvl + &p_384 * &(val(w:int64))`)
     MP_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `x:real = m + p * w  ==> n - m = y - x ==> y = n + p * w`)) THEN
       FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
       FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
       REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN REAL_ARITH_TAC;
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
        `x:real = m + p * w ==> (y = n + p * w ==> q)
         ==> y = n + p * w ==> q`)) THEN
       ASM_REWRITE_TAC[ADD_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])]
   else ALL_TAC);;

let montred_subst_tac execth regs n =
  montred_tac execth regs n THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> b = a - c`));;

let lvs =
 ["x_1",[`X26`; `0`];
  "y_1",[`X26`; `48`];
  "z_1",[`X26`; `96`];
  "x_3",[`X25`; `0`];
  "y_3",[`X25`; `48`];
  "z_3",[`X25`; `96`];
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
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 260 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = a
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
              read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) s =
              a)
             (\s. read PC s = pcout /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> read(memory :> bytes(word_add (read p3 t) (word n3),
                        8 * 6)) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
           (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                       X11; X12; X13; X14; X15; X16; X17] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_EXEC (1--260)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Squaring of the lower half ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (1--28) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 =
    bignum_of_wordlist [mullo_s7; sum_s24; sum_s25; sum_s26; sum_s27; sum_s28]`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three short Montgomery reductions ***)

  montred_tac P384_MONTJDOUBLE_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X14;X15;X16]` 28 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X14;X15;X16]` 43 THEN
  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X14;X15;X16]` 58 THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Three stashing stores ***)

  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC [74;75;76] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   ([77;78;79] @ (83--93) @ [99] @ (105--109) @ [115] @
   (121--124) @ [130] @ (136--138)) (77--138) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0; x_1; x_2] * bignum_of_wordlist [x_3; x_4; x_5] =
    bignum_of_wordlist [mullo_s77; sum_s105; sum_s121;
                        sum_s136; sum_s137; sum_s138]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

 (*** Double the cross-product and add the Montgomerified lower square ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (139--155) (139--155) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
    2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                    bignum_of_wordlist [x_3; x_4; x_5] +
    p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58] =
    2 EXP 192 *
    bignum_of_wordlist
     [sum_s147; sum_s148; sum_s150; sum_s151; sum_s153; sum_s154; sum_s155]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three more Montgomery reductions on that sum ***)

  montred_tac P384_MONTJDOUBLE_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X2;X3;X4]` 155 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X2;X3;X4]` 170 THEN

  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X2;X3;X4]` 185 THEN

  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Montgomery accumulation and addition of the high square ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (201--237) (201--237) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  (*** Main pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s206; sum_s232; sum_s233;
          sum_s234; sum_s235; sum_s236; sum_s237]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 384 * t =
      a EXP 2 +
      p_384 * bignum_of_wordlist
        [ww_28; ww_43; ww_58; ww_155; ww_170; ww_185]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
      `(bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
        2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                        bignum_of_wordlist [x_3; x_4; x_5] +
        p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58]) +
       2 EXP 384 * bignum_of_wordlist[x_3;x_4;x_5] EXP 2 +
       2 EXP 192 * p_384 *
       bignum_of_wordlist [ww_155; ww_170; ww_185]` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
         `x' - x:real = &(bignum_of_wordlist(CONS h t))
          ==> e * (&(bignum_of_wordlist(CONS h t')) -
                   &(bignum_of_wordlist(CONS h t))) = (w - e * (x' - x)) - z
              ==> w = e * &(bignum_of_wordlist(CONS h t')) + z`));
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

 (*** To make bounds reasoning more transparent, recast top as a bit ***)

  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(sum_s237:int64)` NUM_AS_BITVAL_ALT))) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN ANTS_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `topc:bool` SUBST_ALL_TAC)] THEN

  (*** Final comparison ****)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (238--247) (238--247) THEN
  SUBGOAL_THEN
   `sum_s247:int64 = word(bitval(p_384 <= t))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Corrective masked subtraction ***)

  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC [248] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word 0) x:int64 = word_neg x`]) THEN
  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (249--260) (249--260) THEN
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
  ASM_SIMP_TAC[MOD_CASES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of montmul.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MONTMUL_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 377 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !a. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = a
    ==>
    !b. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = b
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
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
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE
               [memory :> bytes(word_add (read p3 t) (word n3),8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_EXEC (1--377)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "x_" o lhand o concl) THEN

 (*** First ADK block multiplying lower halves.
  ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   ([7;8;9] @ (13--23) @ [29] @ (35--39) @ [45] @ (51--54) @ [60] @ (66--68))
   (1--68) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s7; sum_s35; sum_s51; sum_s66; sum_s67; sum_s68] =
    bignum_of_wordlist[x_0;x_1;x_2] * bignum_of_wordlist[y_0;y_1;y_2]`
  (ASSUME_TAC o SYM) THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** the three Montgomery steps on the low half ***)

  montred_tac P384_MONTJDOUBLE_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 68 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 83 THEN
  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 98 THEN

  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC (114--116) THEN
  SUBGOAL_THEN
   `2 EXP 192 *
    bignum_of_wordlist
     [sum_s108; sum_s109; sum_s110; sum_s111; sum_s112; sum_s113] =
    bignum_of_wordlist[x_0;x_1;x_2] * bignum_of_wordlist[y_0;y_1;y_2] +
    p_384 * bignum_of_wordlist[ww_68; ww_83; ww_98]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_EQ] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
    `L' = bignum_of_wordlist
            [sum_s108; sum_s109; sum_s110; sum_s111; sum_s112; sum_s113]` THEN

 (*** Second ADK block multiplying upper halves.
  ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   ([117;118;119] @ (123--133) @ [139] @ (145--149) @ [155] @
    (161--164) @ [170] @ (176--178))
   (117--178) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
      [mullo_s117; sum_s145; sum_s161; sum_s176; sum_s177; sum_s178] =
    bignum_of_wordlist[x_3;x_4;x_5] * bignum_of_wordlist[y_3;y_4;y_5]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** First absolute difference computation ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   [179;180;181;185;187;189] (179--189) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s185;sum_s187;sum_s189]) =
    abs(&(bignum_of_wordlist[x_3;x_4;x_5]) -
        &(bignum_of_wordlist[x_0;x_1;x_2])) /\
    (carry_s181 <=> bignum_of_wordlist[x_3;x_4;x_5] <
                   bignum_of_wordlist[x_0;x_1;x_2])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `192` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`192`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Second absolute difference computation ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   [190;191;192;196;198;200] (190--200) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_RULE
   `word_sub (word 0) x = word_neg x`]) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s196;sum_s198;sum_s200]) =
    abs(&(bignum_of_wordlist[y_0;y_1;y_2]) -
        &(bignum_of_wordlist[y_3;y_4;y_5])) /\
    (carry_s192 <=> bignum_of_wordlist[y_0;y_1;y_2] <
                    bignum_of_wordlist[y_3;y_4;y_5])`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `192` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`192`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(x - y):real = if x < y then y - x else x - y`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0; WORD_NEG_1] THEN
    REWRITE_TAC[WORD_XOR_NOT; WORD_XOR_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Collective sign-magnitude representation  of middle product ***)

  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC [201] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_MASKS]) THEN
  ABBREV_TAC
   `msgn <=> ~(bignum_of_wordlist[x_3;x_4;x_5] <
               bignum_of_wordlist[x_0;x_1;x_2] <=>
               bignum_of_wordlist[y_0;y_1;y_2] <
               bignum_of_wordlist[y_3;y_4;y_5])` THEN
  SUBGOAL_THEN
   `--(&1) pow bitval msgn *
    &(bignum_of_wordlist[sum_s185;sum_s187;sum_s189] *
      bignum_of_wordlist[sum_s196;sum_s198;sum_s200]) =
    (&(bignum_of_wordlist[x_3;x_4;x_5]) - &(bignum_of_wordlist[x_0;x_1;x_2])) *
    (&(bignum_of_wordlist[y_0;y_1;y_2]) - &(bignum_of_wordlist[y_3;y_4;y_5]))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SGN_ABS] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_RING
     `(~(z = &0) ==> x = y) ==> x * z = y * z`) THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_ABS_ZERO; REAL_SUB_0; DE_MORGAN_THM] THEN
    EXPAND_TAC "msgn" THEN POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_BITVAL; REAL_POW_ONE] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(x - y) * (u - v):real = (y - x) * (v - u)`] THEN
    REWRITE_TAC[REAL_SGN_MUL; GSYM REAL_OF_NUM_LT; real_sgn; REAL_SUB_LT] THEN
    REWRITE_TAC[MESON[]
     `(if p <=> q then x else y) =
      (if p then if q then x else y else if q then y else x)`] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** the H + L' addition (a result that we then use twice) ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (202--214) (202--214) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s203; sum_s204; sum_s206;
      sum_s207; sum_s209; sum_s210; word(bitval carry_s210)] =
    bignum_of_wordlist[x_3;x_4;x_5] * bignum_of_wordlist[y_3;y_4;y_5] + L'`
  ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Third and final ADK block computing the mid-product ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   ([215;216;217] @ (221--231) @ [237] @ (243--247) @ [253] @
    (259--262) @ [268] @ (274--276))
   (215--276) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
      [mullo_s215; sum_s243; sum_s259; sum_s274; sum_s275; sum_s276] =
    bignum_of_wordlist[sum_s185;sum_s187;sum_s189] *
    bignum_of_wordlist[sum_s196;sum_s198;sum_s200]`
  (SUBST_ALL_TAC o SYM) THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Big net accumulation computation absorbing cases over sign ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   ([282;284;286;288;290] @ (292--303)) (277--303) THEN
  SUBGOAL_THEN
   `2 EXP 192 *
    bignum_of_wordlist
      [sum_s282; sum_s284; sum_s286; sum_s297; sum_s298; sum_s299;
       sum_s300; sum_s301; sum_s302; sum_s303] =
    a * b + p_384 * (2 EXP 192 + 1) * bignum_of_wordlist[ww_68; ww_83; ww_98]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`832`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `&a * &b +
      &p_384 * (&2 pow 192 + &1) * &(bignum_of_wordlist[ww_68; ww_83; ww_98]) =
      (&2 pow 192 + &1) *
      &(2 EXP 192 * bignum_of_wordlist
        [sum_s203; sum_s204; sum_s206; sum_s207;
         sum_s209; sum_s210; word(bitval carry_s210)]) +
      &2 pow 192 *
      -- &1 pow bitval msgn *
        &(bignum_of_wordlist
           [mullo_s215; sum_s243; sum_s259; sum_s274; sum_s275; sum_s276])`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[VAL_WORD_BITVAL]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    BOOL_CASES_TAC `msgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_XOR_NOT; WORD_XOR_0;
                SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Last three Montgomery steps to get the pre-reduced result ***)

  montred_tac P384_MONTJDOUBLE_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 303 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 318 THEN

  montred_subst_tac P384_MONTJDOUBLE_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 333 THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (349--352) (349--352) THEN

  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s343; sum_s344; sum_s345; sum_s349; sum_s350; sum_s351; sum_s352]` THEN

  SUBGOAL_THEN
   `2 EXP 384 * t =
    a * b +
    p_384 * ((2 EXP 192 + 1) * bignum_of_wordlist[ww_68; ww_83; ww_98] +
             2 EXP 192 * bignum_of_wordlist[ww_303; ww_318; ww_333])`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`832`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC
      (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
      [SYM th]) THEN
    MATCH_MP_TAC(MESON[REAL_ARITH `(x + y) - y:real = x`]
     `!y. integer((x + y) - y) ==> integer(x)`) THEN
    EXISTS_TAC
     `&(bignum_of_wordlist
         [sum_s282; sum_s284; sum_s286; sum_s297; sum_s298; sum_s299]) /
      &2 pow 640` THEN
    FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC
        (RAND_CONV o  RAND_CONV o LAND_CONV)
        [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN
   `t < 3 * p_384 /\ (2 EXP 384 * t == a * b) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `ab <= 2 EXP 384 * p
      ==> 2 EXP 384 * t < ab + 2 * 2 EXP 384 * p ==> t < 3 * p`)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
    ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Quotient approximation computation and main property ***)

  ABBREV_TAC `h = t DIV 2 EXP 384` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 3 * p_384` THEN REWRITE_TAC[p_384] THEN
    EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s352:int64 = word h` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "t"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:num` p384shortredlemma) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (357--362) (353--362) THEN
  SUBGOAL_THEN
   `&2 pow 384 * (&(bitval carry_s362) - &1) +
    &(bignum_of_wordlist
       [sum_s357; sum_s358; sum_s359; sum_s360; sum_s361; sum_s362]) =
    &t - (&h + &1) * &p_384`
  ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE' o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN `carry_s362 <=> (h + 1) * p_384 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN

  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC [363] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM NOT_LT; COND_SWAP; GSYM WORD_MASK;
    SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN

  (*** The final corrective masked addition ***)

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
   [366;368;371;372;373;374] (364--377) THEN
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

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> t < (h + 1) * p_384` THEN
  REWRITE_TAC[p_384] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `&2 pow 384 * c + w:real = t - hp
    ==> t = (hp + w) + &2 pow 384 * c`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_P384_TAC =
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 27 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
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
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (1--12) (1--12) THEN

  SUBGOAL_THEN `carry_s12 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `384` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC [13] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (14--27) (14--27) THEN

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
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 27 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
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
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (1--12) (1--12) THEN
  SUBGOAL_THEN `carry_s12 <=> 2 EXP 384 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC [13] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (14--27) (14--27) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 38 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
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
          MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_DIGITIZE_TAC "m_" o lhand o concl) THEN

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (1--13) (1--13) THEN

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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (14--22) (14--22) THEN
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

  ARM_STEPS_TAC P384_MONTJDOUBLE_EXEC [23;24] THEN

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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (25--38) (25--38) THEN
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
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 86 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
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
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_EXEC (1--86)] THEN
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (1--13) (1--13) THEN
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (14--62) (14--62) THEN
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
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
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 44 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
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
           MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n <= p_384 assumption ***)

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_EXEC (1--44)] THEN
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC [6;8;11;13;16;18;20] (1--20) THEN
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
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
  ARM_MACRO_SIM_ABBREV_TAC p384_montjdouble_mc 74 lvs
  `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
    !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 6)) t = m
    ==>
    !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 6)) t = n
    ==>
    aligned 16 (read SP t) /\
    nonoverlapping (word pc,0x2ba8) (word_add (read p3 t) (word n3),48)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
              read PC s = pcin /\
              read SP s = read SP t /\
              read X25 s = read X25 t /\
              read X26 s = read X26 t /\
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
              MAYCHANGE SOME_FLAGS)`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC `n <= p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC P384_MONTJDOUBLE_EXEC (1--74)] THEN
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC (1--13) (1--13) THEN
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
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

  ARM_ACCSTEPS_TAC P384_MONTJDOUBLE_EXEC
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

let P384_MONTJDOUBLE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,336))
            [(word pc,0x2ba8); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc,0x2ba8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
                  read PC s = word(pc + 0x14) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [p3; p1] s /\
                  bignum_triple_from_memory (p1,6) s = t1)
             (\s. read PC s = word (pc + 0x2b90) /\
                  !P. represents_p384 P t1
                      ==> represents_p384 (group_mul p384_group P P)
                            (bignum_triple_from_memory(p3,6) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26] ,,
           MAYCHANGE SOME_FLAGS ,,
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

let P384_MONTJDOUBLE_SUBROUTINE_CORRECT = time prove
 (`!p3 p1 t1 pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 400),400))
            [(word pc,0x2ba8); (p1,144); (p3,144)] /\
        nonoverlapping (p3,144) (word pc,0x2ba8)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p384_montjdouble_mc /\
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
                      memory :> bytes(word_sub stackpointer (word 400),400)])`,
  ARM_ADD_RETURN_STACK_TAC P384_MONTJDOUBLE_EXEC
   P384_MONTJDOUBLE_CORRECT
    `[X19; X20; X21; X22; X23; X24; X25; X26]` 400);;
