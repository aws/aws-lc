(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication for NIST P-256 precomputed point.                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/jacobian.ml";;
needs "EC/nistp256.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

needs "arm/proofs/bignum_demont_p256.ml";;
needs "arm/proofs/bignum_inv_p256.ml";;
needs "arm/proofs/bignum_montmul_p256_alt.ml";;
needs "arm/proofs/bignum_montsqr_p256_alt.ml";;
needs "arm/proofs/p256_montjmixadd_alt.ml";;

(* ------------------------------------------------------------------------- *)
(* Code.                                                                     *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/p256/p256_scalarmulbase_alt.o";;
 ****)

let p256_scalarmulbase_alt_mc = define_assert_from_elf
  "p256_scalarmulbase_alt_mc" "arm/p256/p256_scalarmulbase_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf9;       (* arm_STP X25 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10483ff;       (* arm_SUB SP SP (rvalue (word 288)) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0xaa0203f4;       (* arm_MOV X20 X2 *)
  0xaa0303f5;       (* arm_MOV X21 X3 *)
  0xd284aa2c;       (* arm_MOV X12 (rvalue (word 9553)) *)
  0xf2bf8c6c;       (* arm_MOVK X12 (word 64611) 16 *)
  0xf2d9584c;       (* arm_MOVK X12 (word 51906) 32 *)
  0xf2fe772c;       (* arm_MOVK X12 (word 62393) 48 *)
  0xd293d08d;       (* arm_MOV X13 (rvalue (word 40580)) *)
  0xf2b4e2ed;       (* arm_MOVK X13 (word 42775) 16 *)
  0xf2df55ad;       (* arm_MOVK X13 (word 64173) 32 *)
  0xf2f79ccd;       (* arm_MOVK X13 (word 48358) 48 *)
  0x9280000e;       (* arm_MOVN X14 (word 0) 0 *)
  0xb2607fef;       (* arm_MOV X15 (rvalue (word 18446744069414584320)) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xeb0c0046;       (* arm_SUBS X6 X2 X12 *)
  0xfa0d0067;       (* arm_SBCS X7 X3 X13 *)
  0xfa0e0088;       (* arm_SBCS X8 X4 X14 *)
  0xfa0f00a9;       (* arm_SBCS X9 X5 X15 *)
  0x9a863042;       (* arm_CSEL X2 X2 X6 Condition_CC *)
  0x9a873063;       (* arm_CSEL X3 X3 X7 Condition_CC *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0xa9000fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0xa90117e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&16))) *)
  0xa9027fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&32))) *)
  0xa9037fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&48))) *)
  0xa9047fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&64))) *)
  0xa9057fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&80))) *)
  0xa9067fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&96))) *)
  0xa9077fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&112))) *)
  0xaa1f03f8;       (* arm_MOV X24 XZR *)
  0xaa1f03f6;       (* arm_MOV X22 XZR *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xd2800024;       (* arm_MOV X4 (rvalue (word 1)) *)
  0x9ad42084;       (* arm_LSLV X4 X4 X20 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x8a000084;       (* arm_AND X4 X4 X0 *)
  0x8b180097;       (* arm_ADD X23 X4 X24 *)
  0xcb1403e8;       (* arm_NEG X8 X20 *)
  0x9ac82025;       (* arm_LSLV X5 X1 X8 *)
  0x9ad42400;       (* arm_LSRV X0 X0 X20 *)
  0xaa050000;       (* arm_ORR X0 X0 X5 *)
  0x9ac82046;       (* arm_LSLV X6 X2 X8 *)
  0x9ad42421;       (* arm_LSRV X1 X1 X20 *)
  0xaa060021;       (* arm_ORR X1 X1 X6 *)
  0x9ac82067;       (* arm_LSLV X7 X3 X8 *)
  0x9ad42442;       (* arm_LSRV X2 X2 X20 *)
  0xaa070042;       (* arm_ORR X2 X2 X7 *)
  0x9ad42463;       (* arm_LSRV X3 X3 X20 *)
  0xa90007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa9010fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0x9ad42001;       (* arm_LSLV X1 X0 X20 *)
  0xd341fc20;       (* arm_LSR X0 X1 1 *)
  0xcb170022;       (* arm_SUB X2 X1 X23 *)
  0xeb17001f;       (* arm_CMP X0 X23 *)
  0x9a9f27f8;       (* arm_CSET X24 Condition_CC *)
  0x9a973059;       (* arm_CSEL X25 X2 X23 Condition_CC *)
  0xd2800030;       (* arm_MOV X16 (rvalue (word 1)) *)
  0x9ad42210;       (* arm_LSLV X16 X16 X20 *)
  0xd341fe10;       (* arm_LSR X16 X16 1 *)
  0xaa1903f1;       (* arm_MOV X17 X25 *)
  0xa94026a8;       (* arm_LDP X8 X9 X21 (Immediate_Offset (iword (&0))) *)
  0xa9412eaa;       (* arm_LDP X10 X11 X21 (Immediate_Offset (iword (&16))) *)
  0xa94236ac;       (* arm_LDP X12 X13 X21 (Immediate_Offset (iword (&32))) *)
  0xa9433eae;       (* arm_LDP X14 X15 X21 (Immediate_Offset (iword (&48))) *)
  0xf1000631;       (* arm_SUBS X17 X17 (rvalue (word 1)) *)
  0x9a800100;       (* arm_CSEL X0 X8 X0 Condition_EQ *)
  0x9a810121;       (* arm_CSEL X1 X9 X1 Condition_EQ *)
  0x9a820142;       (* arm_CSEL X2 X10 X2 Condition_EQ *)
  0x9a830163;       (* arm_CSEL X3 X11 X3 Condition_EQ *)
  0x9a840184;       (* arm_CSEL X4 X12 X4 Condition_EQ *)
  0x9a8501a5;       (* arm_CSEL X5 X13 X5 Condition_EQ *)
  0x9a8601c6;       (* arm_CSEL X6 X14 X6 Condition_EQ *)
  0x9a8701e7;       (* arm_CSEL X7 X15 X7 Condition_EQ *)
  0x910102b5;       (* arm_ADD X21 X21 (rvalue (word 64)) *)
  0xd1000610;       (* arm_SUB X16 X16 (rvalue (word 1)) *)
  0xb5fffe30;       (* arm_CBNZ X16 (word 2097092) *)
  0xa90e07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&224))) *)
  0xa90f0fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&240))) *)
  0x92800000;       (* arm_MOVN X0 (word 0) 0 *)
  0xeb040000;       (* arm_SUBS X0 X0 X4 *)
  0xb2407fe1;       (* arm_MOV X1 (rvalue (word 4294967295)) *)
  0xfa050021;       (* arm_SBCS X1 X1 X5 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0xfa0603e2;       (* arm_NGCS X2 X6 *)
  0xda070063;       (* arm_SBC X3 X3 X7 *)
  0xeb1f031f;       (* arm_CMP X24 XZR *)
  0x9a841004;       (* arm_CSEL X4 X0 X4 Condition_NE *)
  0x9a851025;       (* arm_CSEL X5 X1 X5 Condition_NE *)
  0x9a861046;       (* arm_CSEL X6 X2 X6 Condition_NE *)
  0x9a871067;       (* arm_CSEL X7 X3 X7 Condition_NE *)
  0xa91017e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&256))) *)
  0xa9111fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&272))) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910383e2;       (* arm_ADD X2 SP (rvalue (word 224)) *)
  0x94000567;       (* arm_BL (word 5532) *)
  0xeb1f033f;       (* arm_CMP X25 XZR *)
  0xa94207e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&32))) *)
  0xa94837ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  0x9a801180;       (* arm_CSEL X0 X12 X0 Condition_NE *)
  0x9a8111a1;       (* arm_CSEL X1 X13 X1 Condition_NE *)
  0xa9430fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0xa94937ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&144))) *)
  0x9a821182;       (* arm_CSEL X2 X12 X2 Condition_NE *)
  0x9a8311a3;       (* arm_CSEL X3 X13 X3 Condition_NE *)
  0xa94417e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&64))) *)
  0xa94a37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0x9a841184;       (* arm_CSEL X4 X12 X4 Condition_NE *)
  0x9a8511a5;       (* arm_CSEL X5 X13 X5 Condition_NE *)
  0xa9451fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&80))) *)
  0xa94b37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&176))) *)
  0x9a861186;       (* arm_CSEL X6 X12 X6 Condition_NE *)
  0x9a8711a7;       (* arm_CSEL X7 X13 X7 Condition_NE *)
  0xa94627e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&96))) *)
  0xa94c37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&192))) *)
  0x9a881188;       (* arm_CSEL X8 X12 X8 Condition_NE *)
  0x9a8911a9;       (* arm_CSEL X9 X13 X9 Condition_NE *)
  0xa9472fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&112))) *)
  0xa94d37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&208))) *)
  0x9a8a118a;       (* arm_CSEL X10 X12 X10 Condition_NE *)
  0x9a8b11ab;       (* arm_CSEL X11 X13 X11 Condition_NE *)
  0xa90207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&32))) *)
  0xa9030fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0xa90417e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&64))) *)
  0xa9051fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&80))) *)
  0xa90627e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&96))) *)
  0xa9072fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&112))) *)
  0x910006d6;       (* arm_ADD X22 X22 (rvalue (word 1)) *)
  0x9b167e80;       (* arm_MUL X0 X20 X22 *)
  0xf104041f;       (* arm_CMP X0 (rvalue (word 257)) *)
  0x54fff363;       (* arm_BCC (word 2096748) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x940004e5;       (* arm_BL (word 5012) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x9400046f;       (* arm_BL (word 4540) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
  0x94000016;       (* arm_BL (word 88) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910203e1;       (* arm_ADD X1 SP (rvalue (word 128)) *)
  0x94000038;       (* arm_BL (word 224) *)
  0x910203e0;       (* arm_ADD X0 SP (rvalue (word 128)) *)
  0x910183e1;       (* arm_ADD X1 SP (rvalue (word 96)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x94000465;       (* arm_BL (word 4500) *)
  0xaa1303e0;       (* arm_MOV X0 X19 *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0x910203e2;       (* arm_ADD X2 SP (rvalue (word 128)) *)
  0x94000461;       (* arm_BL (word 4484) *)
  0x91008260;       (* arm_ADD X0 X19 (rvalue (word 32)) *)
  0x910103e1;       (* arm_ADD X1 SP (rvalue (word 64)) *)
  0x910283e2;       (* arm_ADD X2 SP (rvalue (word 160)) *)
  0x9400045d;       (* arm_BL (word 4468) *)
  0x910483ff;       (* arm_ADD SP SP (rvalue (word 288)) *)
  0xa8c17bf9;       (* arm_LDP X25 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd3607c47;       (* arm_LSL X7 X2 32 *)
  0xeb070048;       (* arm_SUBS X8 X2 X7 *)
  0xd360fc46;       (* arm_LSR X6 X2 32 *)
  0xda060042;       (* arm_SBC X2 X2 X6 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9a1f0042;       (* arm_ADC X2 X2 XZR *)
  0xd3607c67;       (* arm_LSL X7 X3 32 *)
  0xeb070068;       (* arm_SUBS X8 X3 X7 *)
  0xd360fc66;       (* arm_LSR X6 X3 32 *)
  0xda060063;       (* arm_SBC X3 X3 X6 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0xba080042;       (* arm_ADCS X2 X2 X8 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xd3607c87;       (* arm_LSL X7 X4 32 *)
  0xeb070088;       (* arm_SUBS X8 X4 X7 *)
  0xd360fc86;       (* arm_LSR X6 X4 32 *)
  0xda060084;       (* arm_SBC X4 X4 X6 *)
  0xab0700a5;       (* arm_ADDS X5 X5 X7 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0xd3607ca7;       (* arm_LSL X7 X5 32 *)
  0xeb0700a8;       (* arm_SUBS X8 X5 X7 *)
  0xd360fca6;       (* arm_LSR X6 X5 32 *)
  0xda0600a5;       (* arm_SBC X5 X5 X6 *)
  0xab070042;       (* arm_ADDS X2 X2 X7 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10283ff;       (* arm_SUB SP SP (rvalue (word 160)) *)
  0xaa0003f4;       (* arm_MOV X20 X0 *)
  0x9280000a;       (* arm_MOVN X10 (word 0) 0 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb26083ed;       (* arm_MOV X13 (rvalue (word 18446744069414584321)) *)
  0xa9002fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0xa90137ff;       (* arm_STP XZR X13 SP (Immediate_Offset (iword (&16))) *)
  0xf90013ff;       (* arm_STR XZR SP (Immediate_Offset (word 32)) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xeb0a004a;       (* arm_SUBS X10 X2 X10 *)
  0xfa0b006b;       (* arm_SBCS X11 X3 X11 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xfa1f008c;       (* arm_SBCS X12 X4 XZR *)
  0xfa0d00ad;       (* arm_SBCS X13 X5 X13 *)
  0x9a8a3042;       (* arm_CSEL X2 X2 X10 Condition_CC *)
  0x9a8b3063;       (* arm_CSEL X3 X3 X11 Condition_CC *)
  0x9a8c3084;       (* arm_CSEL X4 X4 X12 Condition_CC *)
  0x9a8d30a5;       (* arm_CSEL X5 X5 X13 Condition_CC *)
  0xa9030fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&48))) *)
  0xa90417e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&64))) *)
  0xf9002bff;       (* arm_STR XZR SP (Immediate_Offset (word 80)) *)
  0xa9067fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&96))) *)
  0xa9077fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&112))) *)
  0xd2e0008a;       (* arm_MOVZ X10 (word 4) 48 *)
  0xa9087fea;       (* arm_STP X10 XZR SP (Immediate_Offset (iword (&128))) *)
  0xa9097fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&144))) *)
  0xd2800155;       (* arm_MOV X21 (rvalue (word 10)) *)
  0xd2800036;       (* arm_MOV X22 (rvalue (word 1)) *)
  0x14000131;       (* arm_B (word 1220) *)
  0xeb1f015f;       (* arm_CMP X10 XZR *)
  0xda9f53ee;       (* arm_CSETM X14 Condition_MI *)
  0xda8a554a;       (* arm_CNEG X10 X10 Condition_MI *)
  0xeb1f017f;       (* arm_CMP X11 XZR *)
  0xda9f53ef;       (* arm_CSETM X15 Condition_MI *)
  0xda8b556b;       (* arm_CNEG X11 X11 Condition_MI *)
  0xeb1f019f;       (* arm_CMP X12 XZR *)
  0xda9f53f0;       (* arm_CSETM X16 Condition_MI *)
  0xda8c558c;       (* arm_CNEG X12 X12 Condition_MI *)
  0xeb1f01bf;       (* arm_CMP X13 XZR *)
  0xda9f53f1;       (* arm_CSETM X17 Condition_MI *)
  0xda8d55ad;       (* arm_CNEG X13 X13 Condition_MI *)
  0x8a0e0140;       (* arm_AND X0 X10 X14 *)
  0x8a0f0161;       (* arm_AND X1 X11 X15 *)
  0x8b010009;       (* arm_ADD X9 X0 X1 *)
  0x8a100180;       (* arm_AND X0 X12 X16 *)
  0x8a1101a1;       (* arm_AND X1 X13 X17 *)
  0x8b010013;       (* arm_ADD X19 X0 X1 *)
  0xf94003e7;       (* arm_LDR X7 SP (Immediate_Offset (word 0)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf9401be8;       (* arm_LDR X8 SP (Immediate_Offset (word 48)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000265;       (* arm_ADDS X5 X19 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94007e7;       (* arm_LDR X7 SP (Immediate_Offset (word 8)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf9401fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 56)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0x93c4ec44;       (* arm_EXTR X4 X2 X4 59 *)
  0xf90003e4;       (* arm_STR X4 SP (Immediate_Offset (word 0)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0x93c5ec65;       (* arm_EXTR X5 X3 X5 59 *)
  0xf9001be5;       (* arm_STR X5 SP (Immediate_Offset (word 48)) *)
  0xf9400be7;       (* arm_LDR X7 SP (Immediate_Offset (word 16)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf94023e8;       (* arm_LDR X8 SP (Immediate_Offset (word 64)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0x93c2ecc2;       (* arm_EXTR X2 X6 X2 59 *)
  0xf90007e2;       (* arm_STR X2 SP (Immediate_Offset (word 8)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0x93c3ec83;       (* arm_EXTR X3 X4 X3 59 *)
  0xf9001fe3;       (* arm_STR X3 SP (Immediate_Offset (word 56)) *)
  0xf9400fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 24)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0xf94013f7;       (* arm_LDR X23 SP (Immediate_Offset (word 32)) *)
  0xca0e02e3;       (* arm_EOR X3 X23 X14 *)
  0x8a0a0063;       (* arm_AND X3 X3 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94027e8;       (* arm_LDR X8 SP (Immediate_Offset (word 72)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0xf9402bf8;       (* arm_LDR X24 SP (Immediate_Offset (word 80)) *)
  0xca0f0300;       (* arm_EOR X0 X24 X15 *)
  0x8a0b0000;       (* arm_AND X0 X0 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c6eca6;       (* arm_EXTR X6 X5 X6 59 *)
  0xf9000be6;       (* arm_STR X6 SP (Immediate_Offset (word 16)) *)
  0x93c5ec65;       (* arm_EXTR X5 X3 X5 59 *)
  0xf9000fe5;       (* arm_STR X5 SP (Immediate_Offset (word 24)) *)
  0x937bfc63;       (* arm_ASR X3 X3 59 *)
  0xf90013e3;       (* arm_STR X3 SP (Immediate_Offset (word 32)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0xca1002e5;       (* arm_EOR X5 X23 X16 *)
  0x8a0c00a5;       (* arm_AND X5 X5 X12 *)
  0xcb0503e5;       (* arm_NEG X5 X5 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0xca110300;       (* arm_EOR X0 X24 X17 *)
  0x8a0d0000;       (* arm_AND X0 X0 X13 *)
  0xcb0000a5;       (* arm_SUB X5 X5 X0 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0x93c4ec44;       (* arm_EXTR X4 X2 X4 59 *)
  0xf90023e4;       (* arm_STR X4 SP (Immediate_Offset (word 64)) *)
  0x93c2eca2;       (* arm_EXTR X2 X5 X2 59 *)
  0xf90027e2;       (* arm_STR X2 SP (Immediate_Offset (word 72)) *)
  0x937bfca5;       (* arm_ASR X5 X5 59 *)
  0xf9002be5;       (* arm_STR X5 SP (Immediate_Offset (word 80)) *)
  0xf94033e7;       (* arm_LDR X7 SP (Immediate_Offset (word 96)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94043e8;       (* arm_LDR X8 SP (Immediate_Offset (word 128)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90033e4;       (* arm_STR X4 SP (Immediate_Offset (word 96)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000265;       (* arm_ADDS X5 X19 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0xf90043e5;       (* arm_STR X5 SP (Immediate_Offset (word 128)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94037e7;       (* arm_LDR X7 SP (Immediate_Offset (word 104)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94047e8;       (* arm_LDR X8 SP (Immediate_Offset (word 136)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90037e2;       (* arm_STR X2 SP (Immediate_Offset (word 104)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xf90047e3;       (* arm_STR X3 SP (Immediate_Offset (word 136)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf9403be7;       (* arm_LDR X7 SP (Immediate_Offset (word 112)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9404be8;       (* arm_LDR X8 SP (Immediate_Offset (word 144)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf9003be6;       (* arm_STR X6 SP (Immediate_Offset (word 112)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf9004be4;       (* arm_STR X4 SP (Immediate_Offset (word 144)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf9403fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 120)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c3;       (* arm_AND X3 X14 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9404fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 152)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xa94607e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xf9403be6;       (* arm_LDR X6 SP (Immediate_Offset (word 112)) *)
  0xd2fc000e;       (* arm_MOVZ X14 (word 57344) 48 *)
  0xab0e0000;       (* arm_ADDS X0 X0 X14 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xb24073eb;       (* arm_MOV X11 (rvalue (word 536870911)) *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0xd2e4000a;       (* arm_MOVZ X10 (word 8192) 48 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xb2637fee;       (* arm_MOV X14 (rvalue (word 2305843008676823040)) *)
  0x9a0e0063;       (* arm_ADC X3 X3 X14 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xeb0b000e;       (* arm_SUBS X14 X0 X11 *)
  0xd360fc0a;       (* arm_LSR X10 X0 32 *)
  0xda0a0000;       (* arm_SBC X0 X0 X10 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xba0e00a5;       (* arm_ADCS X5 X5 X14 *)
  0xba000063;       (* arm_ADCS X3 X3 X0 *)
  0x9280000e;       (* arm_MOVN X14 (word 0) 0 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb26083ea;       (* arm_MOV X10 (rvalue (word 18446744069414584321)) *)
  0x9a9f21ce;       (* arm_CSEL X14 X14 XZR Condition_CS *)
  0x9a9f216b;       (* arm_CSEL X11 X11 XZR Condition_CS *)
  0x9a9f214a;       (* arm_CSEL X10 X10 XZR Condition_CS *)
  0xeb0e0021;       (* arm_SUBS X1 X1 X14 *)
  0xfa0b00c6;       (* arm_SBCS X6 X6 X11 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xda0a0063;       (* arm_SBC X3 X3 X10 *)
  0xa9061be1;       (* arm_STP X1 X6 SP (Immediate_Offset (iword (&96))) *)
  0xa9070fe5;       (* arm_STP X5 X3 SP (Immediate_Offset (iword (&112))) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x8a0c0205;       (* arm_AND X5 X16 X12 *)
  0xcb0503e5;       (* arm_NEG X5 X5 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x8a0d0220;       (* arm_AND X0 X17 X13 *)
  0xcb0000a5;       (* arm_SUB X5 X5 X0 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xf9404be3;       (* arm_LDR X3 SP (Immediate_Offset (word 144)) *)
  0xd2fc000e;       (* arm_MOVZ X14 (word 57344) 48 *)
  0xab0e0000;       (* arm_ADDS X0 X0 X14 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xb24073eb;       (* arm_MOV X11 (rvalue (word 536870911)) *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0xd2e4000a;       (* arm_MOVZ X10 (word 8192) 48 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0xb2637fee;       (* arm_MOV X14 (rvalue (word 2305843008676823040)) *)
  0x9a0e00a5;       (* arm_ADC X5 X5 X14 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xeb0b000e;       (* arm_SUBS X14 X0 X11 *)
  0xd360fc0a;       (* arm_LSR X10 X0 32 *)
  0xda0a0000;       (* arm_SBC X0 X0 X10 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xba0e0042;       (* arm_ADCS X2 X2 X14 *)
  0xba0000a5;       (* arm_ADCS X5 X5 X0 *)
  0x9280000e;       (* arm_MOVN X14 (word 0) 0 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb26083ea;       (* arm_MOV X10 (rvalue (word 18446744069414584321)) *)
  0x9a9f21ce;       (* arm_CSEL X14 X14 XZR Condition_CS *)
  0x9a9f216b;       (* arm_CSEL X11 X11 XZR Condition_CS *)
  0x9a9f214a;       (* arm_CSEL X10 X10 XZR Condition_CS *)
  0xeb0e0021;       (* arm_SUBS X1 X1 X14 *)
  0xfa0b0063;       (* arm_SBCS X3 X3 X11 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda0a00a5;       (* arm_SBC X5 X5 X10 *)
  0xa9080fe1;       (* arm_STP X1 X3 SP (Immediate_Offset (iword (&128))) *)
  0xa90917e2;       (* arm_STP X2 X5 SP (Immediate_Offset (iword (&144))) *)
  0xaa1603e1;       (* arm_MOV X1 X22 *)
  0xf94003e2;       (* arm_LDR X2 SP (Immediate_Offset (word 0)) *)
  0xf9401be3;       (* arm_LDR X3 SP (Immediate_Offset (word 48)) *)
  0x92404c44;       (* arm_AND X4 X2 (rvalue (word 1048575)) *)
  0xb2575884;       (* arm_ORR X4 X4 (rvalue (word 18446741874686296064)) *)
  0x92404c65;       (* arm_AND X5 X3 (rvalue (word 1048575)) *)
  0xb24204a5;       (* arm_ORR X5 X5 (rvalue (word 13835058055282163712)) *)
  0xf24000bf;       (* arm_TST X5 (rvalue (word 1)) *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x91440088;       (* arm_ADD X8 X4 (rvalue (word 1048576)) *)
  0x9355a508;       (* arm_SBFM X8 X8 21 41 *)
  0xd2a0020b;       (* arm_MOVZ X11 (word 16) 16 *)
  0x8b0b556b;       (* arm_ADD X11 X11 (Shiftedreg X11 LSL 21) *)
  0x8b0b0089;       (* arm_ADD X9 X4 X11 *)
  0x936afd29;       (* arm_ASR X9 X9 42 *)
  0x914400aa;       (* arm_ADD X10 X5 (rvalue (word 1048576)) *)
  0x9355a54a;       (* arm_SBFM X10 X10 21 41 *)
  0x8b0b00ab;       (* arm_ADD X11 X5 X11 *)
  0x936afd6b;       (* arm_ASR X11 X11 42 *)
  0x9b027d06;       (* arm_MUL X6 X8 X2 *)
  0x9b037d27;       (* arm_MUL X7 X9 X3 *)
  0x9b027d42;       (* arm_MUL X2 X10 X2 *)
  0x9b037d63;       (* arm_MUL X3 X11 X3 *)
  0x8b0700c4;       (* arm_ADD X4 X6 X7 *)
  0x8b030045;       (* arm_ADD X5 X2 X3 *)
  0x9354fc82;       (* arm_ASR X2 X4 20 *)
  0x9354fca3;       (* arm_ASR X3 X5 20 *)
  0x92404c44;       (* arm_AND X4 X2 (rvalue (word 1048575)) *)
  0xb2575884;       (* arm_ORR X4 X4 (rvalue (word 18446741874686296064)) *)
  0x92404c65;       (* arm_AND X5 X3 (rvalue (word 1048575)) *)
  0xb24204a5;       (* arm_ORR X5 X5 (rvalue (word 13835058055282163712)) *)
  0xf24000bf;       (* arm_TST X5 (rvalue (word 1)) *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9144008c;       (* arm_ADD X12 X4 (rvalue (word 1048576)) *)
  0x9355a58c;       (* arm_SBFM X12 X12 21 41 *)
  0xd2a0020f;       (* arm_MOVZ X15 (word 16) 16 *)
  0x8b0f55ef;       (* arm_ADD X15 X15 (Shiftedreg X15 LSL 21) *)
  0x8b0f008d;       (* arm_ADD X13 X4 X15 *)
  0x936afdad;       (* arm_ASR X13 X13 42 *)
  0x914400ae;       (* arm_ADD X14 X5 (rvalue (word 1048576)) *)
  0x9355a5ce;       (* arm_SBFM X14 X14 21 41 *)
  0x8b0f00af;       (* arm_ADD X15 X5 X15 *)
  0x936afdef;       (* arm_ASR X15 X15 42 *)
  0x9b027d86;       (* arm_MUL X6 X12 X2 *)
  0x9b037da7;       (* arm_MUL X7 X13 X3 *)
  0x9b027dc2;       (* arm_MUL X2 X14 X2 *)
  0x9b037de3;       (* arm_MUL X3 X15 X3 *)
  0x8b0700c4;       (* arm_ADD X4 X6 X7 *)
  0x8b030045;       (* arm_ADD X5 X2 X3 *)
  0x9354fc82;       (* arm_ASR X2 X4 20 *)
  0x9354fca3;       (* arm_ASR X3 X5 20 *)
  0x92404c44;       (* arm_AND X4 X2 (rvalue (word 1048575)) *)
  0xb2575884;       (* arm_ORR X4 X4 (rvalue (word 18446741874686296064)) *)
  0x92404c65;       (* arm_AND X5 X3 (rvalue (word 1048575)) *)
  0xb24204a5;       (* arm_ORR X5 X5 (rvalue (word 13835058055282163712)) *)
  0xf24000bf;       (* arm_TST X5 (rvalue (word 1)) *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9b087d82;       (* arm_MUL X2 X12 X8 *)
  0x9b097d83;       (* arm_MUL X3 X12 X9 *)
  0x9b087dc6;       (* arm_MUL X6 X14 X8 *)
  0x9b097dc7;       (* arm_MUL X7 X14 X9 *)
  0x9b0a09a8;       (* arm_MADD X8 X13 X10 X2 *)
  0x9b0b0da9;       (* arm_MADD X9 X13 X11 X3 *)
  0x9b0a19f0;       (* arm_MADD X16 X15 X10 X6 *)
  0x9b0b1df1;       (* arm_MADD X17 X15 X11 X7 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0xf27f00bf;       (* arm_TST X5 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9a9f1086;       (* arm_CSEL X6 X4 XZR Condition_NE *)
  0xfa5f1028;       (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  0xda81b421;       (* arm_CNEG X1 X1 Condition_GE *)
  0xda86b4c6;       (* arm_CNEG X6 X6 Condition_GE *)
  0x9a84a0a4;       (* arm_CSEL X4 X5 X4 Condition_GE *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0x9341fca5;       (* arm_ASR X5 X5 1 *)
  0x9144008c;       (* arm_ADD X12 X4 (rvalue (word 1048576)) *)
  0x9356a98c;       (* arm_SBFM X12 X12 22 42 *)
  0xd2a0020f;       (* arm_MOVZ X15 (word 16) 16 *)
  0x8b0f55ef;       (* arm_ADD X15 X15 (Shiftedreg X15 LSL 21) *)
  0x8b0f008d;       (* arm_ADD X13 X4 X15 *)
  0x936bfdad;       (* arm_ASR X13 X13 43 *)
  0x914400ae;       (* arm_ADD X14 X5 (rvalue (word 1048576)) *)
  0x9356a9ce;       (* arm_SBFM X14 X14 22 42 *)
  0x8b0f00af;       (* arm_ADD X15 X5 X15 *)
  0x936bfdef;       (* arm_ASR X15 X15 43 *)
  0x9b08fd82;       (* arm_MNEG X2 X12 X8 *)
  0x9b09fd83;       (* arm_MNEG X3 X12 X9 *)
  0x9b08fdc4;       (* arm_MNEG X4 X14 X8 *)
  0x9b09fdc5;       (* arm_MNEG X5 X14 X9 *)
  0x9b1089aa;       (* arm_MSUB X10 X13 X16 X2 *)
  0x9b118dab;       (* arm_MSUB X11 X13 X17 X3 *)
  0x9b1091ec;       (* arm_MSUB X12 X15 X16 X4 *)
  0x9b1195ed;       (* arm_MSUB X13 X15 X17 X5 *)
  0xaa0103f6;       (* arm_MOV X22 X1 *)
  0xf10006b5;       (* arm_SUBS X21 X21 (rvalue (word 1)) *)
  0x54ff8dc1;       (* arm_BNE (word 2093496) *)
  0xf94003e0;       (* arm_LDR X0 SP (Immediate_Offset (word 0)) *)
  0xf9401be1;       (* arm_LDR X1 SP (Immediate_Offset (word 48)) *)
  0x9b0a7c00;       (* arm_MUL X0 X0 X10 *)
  0x9b0b0021;       (* arm_MADD X1 X1 X11 X0 *)
  0x937ffc20;       (* arm_ASR X0 X1 63 *)
  0xeb1f015f;       (* arm_CMP X10 XZR *)
  0xda9f53ee;       (* arm_CSETM X14 Condition_MI *)
  0xda8a554a;       (* arm_CNEG X10 X10 Condition_MI *)
  0xca0001ce;       (* arm_EOR X14 X14 X0 *)
  0xeb1f017f;       (* arm_CMP X11 XZR *)
  0xda9f53ef;       (* arm_CSETM X15 Condition_MI *)
  0xda8b556b;       (* arm_CNEG X11 X11 Condition_MI *)
  0xca0001ef;       (* arm_EOR X15 X15 X0 *)
  0xeb1f019f;       (* arm_CMP X12 XZR *)
  0xda9f53f0;       (* arm_CSETM X16 Condition_MI *)
  0xda8c558c;       (* arm_CNEG X12 X12 Condition_MI *)
  0xca000210;       (* arm_EOR X16 X16 X0 *)
  0xeb1f01bf;       (* arm_CMP X13 XZR *)
  0xda9f53f1;       (* arm_CSETM X17 Condition_MI *)
  0xda8d55ad;       (* arm_CNEG X13 X13 Condition_MI *)
  0xca000231;       (* arm_EOR X17 X17 X0 *)
  0x8a0e0140;       (* arm_AND X0 X10 X14 *)
  0x8a0f0161;       (* arm_AND X1 X11 X15 *)
  0x8b010009;       (* arm_ADD X9 X0 X1 *)
  0xf94033e7;       (* arm_LDR X7 SP (Immediate_Offset (word 96)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94043e8;       (* arm_LDR X8 SP (Immediate_Offset (word 128)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90033e4;       (* arm_STR X4 SP (Immediate_Offset (word 96)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94037e7;       (* arm_LDR X7 SP (Immediate_Offset (word 104)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94047e8;       (* arm_LDR X8 SP (Immediate_Offset (word 136)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90037e2;       (* arm_STR X2 SP (Immediate_Offset (word 104)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xf9403be7;       (* arm_LDR X7 SP (Immediate_Offset (word 112)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9404be8;       (* arm_LDR X8 SP (Immediate_Offset (word 144)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf9003be6;       (* arm_STR X6 SP (Immediate_Offset (word 112)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xf9403fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 120)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c3;       (* arm_AND X3 X14 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9404fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 152)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xa94607e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xf9403be2;       (* arm_LDR X2 SP (Immediate_Offset (word 112)) *)
  0xd2fc000e;       (* arm_MOVZ X14 (word 57344) 48 *)
  0xab0e0000;       (* arm_ADDS X0 X0 X14 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xb24073eb;       (* arm_MOV X11 (rvalue (word 536870911)) *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0xd2e4000a;       (* arm_MOVZ X10 (word 8192) 48 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xb2637fee;       (* arm_MOV X14 (rvalue (word 2305843008676823040)) *)
  0x9a0e0063;       (* arm_ADC X3 X3 X14 *)
  0xd3607c0b;       (* arm_LSL X11 X0 32 *)
  0xeb0b000e;       (* arm_SUBS X14 X0 X11 *)
  0xd360fc0a;       (* arm_LSR X10 X0 32 *)
  0xda0a0000;       (* arm_SBC X0 X0 X10 *)
  0xab0b0021;       (* arm_ADDS X1 X1 X11 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0xba0e00a5;       (* arm_ADCS X5 X5 X14 *)
  0xba000063;       (* arm_ADCS X3 X3 X0 *)
  0x9280000e;       (* arm_MOVN X14 (word 0) 0 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb26083ea;       (* arm_MOV X10 (rvalue (word 18446744069414584321)) *)
  0x9a9f21ce;       (* arm_CSEL X14 X14 XZR Condition_CS *)
  0x9a9f216b;       (* arm_CSEL X11 X11 XZR Condition_CS *)
  0x9a9f214a;       (* arm_CSEL X10 X10 XZR Condition_CS *)
  0xeb0e0021;       (* arm_SUBS X1 X1 X14 *)
  0xfa0b0042;       (* arm_SBCS X2 X2 X11 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xda0a0063;       (* arm_SBC X3 X3 X10 *)
  0x9280000a;       (* arm_MOVN X10 (word 0) 0 *)
  0xeb0a002a;       (* arm_SUBS X10 X1 X10 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xfa0b004b;       (* arm_SBCS X11 X2 X11 *)
  0xb26083ed;       (* arm_MOV X13 (rvalue (word 18446744069414584321)) *)
  0xfa1f00ac;       (* arm_SBCS X12 X5 XZR *)
  0xfa0d006d;       (* arm_SBCS X13 X3 X13 *)
  0x9a8a302a;       (* arm_CSEL X10 X1 X10 Condition_CC *)
  0x9a8b304b;       (* arm_CSEL X11 X2 X11 Condition_CC *)
  0x9a8c30ac;       (* arm_CSEL X12 X5 X12 Condition_CC *)
  0x9a8d306d;       (* arm_CSEL X13 X3 X13 Condition_CC *)
  0xa9002e8a;       (* arm_STP X10 X11 X20 (Immediate_Offset (iword (&0))) *)
  0xa901368c;       (* arm_STP X12 X13 X20 (Immediate_Offset (iword (&16))) *)
  0x910283ff;       (* arm_ADD SP SP (rvalue (word 160)) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bca7c83;       (* arm_UMULH X3 X4 X10 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0x9b077cab;       (* arm_MUL X11 X5 X7 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b087cab;       (* arm_MUL X11 X5 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b097cab;       (* arm_MUL X11 X5 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7cab;       (* arm_MUL X11 X5 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bca7ca4;       (* arm_UMULH X4 X5 X10 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9bc77cab;       (* arm_UMULH X11 X5 X7 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc87cab;       (* arm_UMULH X11 X5 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc97cab;       (* arm_UMULH X11 X5 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0x9b077ccb;       (* arm_MUL X11 X6 X7 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b087ccb;       (* arm_MUL X11 X6 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
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
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xab0d81ce;       (* arm_ADDS X14 X14 (Shiftedreg X13 LSL 32) *)
  0xd360fdab;       (* arm_LSR X11 X13 32 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b0a7dab;       (* arm_MUL X11 X13 X10 *)
  0x9bca7dad;       (* arm_UMULH X13 X13 X10 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e81ef;       (* arm_ADDS X15 X15 (Shiftedreg X14 LSL 32) *)
  0xd360fdcb;       (* arm_LSR X11 X14 32 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9b0a7dcb;       (* arm_MUL X11 X14 X10 *)
  0x9bca7dce;       (* arm_UMULH X14 X14 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f818c;       (* arm_ADDS X12 X12 (Shiftedreg X15 LSL 32) *)
  0xd360fdeb;       (* arm_LSR X11 X15 32 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b0a7deb;       (* arm_MUL X11 X15 X10 *)
  0x9bca7def;       (* arm_UMULH X15 X15 X10 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xba0401ce;       (* arm_ADCS X14 X14 X4 *)
  0xba0501ef;       (* arm_ADCS X15 X15 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xb1000590;       (* arm_ADDS X16 X12 (rvalue (word 1)) *)
  0xfa0b01a3;       (* arm_SBCS X3 X13 X11 *)
  0xfa1f01c4;       (* arm_SBCS X4 X14 XZR *)
  0xfa0a01e5;       (* arm_SBCS X5 X15 X10 *)
  0xfa1f011f;       (* arm_SBCS XZR X8 XZR *)
  0x9a90318c;       (* arm_CSEL X12 X12 X16 Condition_CC *)
  0x9a8331ad;       (* arm_CSEL X13 X13 X3 Condition_CC *)
  0x9a8431ce;       (* arm_CSEL X14 X14 X4 Condition_CC *)
  0x9a8531ef;       (* arm_CSEL X15 X15 X5 Condition_CC *)
  0xa900340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&0))) *)
  0xa9013c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
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
  0xd360fd02;       (* arm_LSR X2 X8 32 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9b057d02;       (* arm_MUL X2 X8 X5 *)
  0x9bc57d08;       (* arm_UMULH X8 X8 X5 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd22;       (* arm_LSR X2 X9 32 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9b057d22;       (* arm_MUL X2 X9 X5 *)
  0x9bc57d29;       (* arm_UMULH X9 X9 X5 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd42;       (* arm_LSR X2 X10 32 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9b057d42;       (* arm_MUL X2 X10 X5 *)
  0x9bc57d4a;       (* arm_UMULH X10 X10 X5 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd62;       (* arm_LSR X2 X11 32 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
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
  0xa9002408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd10303ff;       (* arm_SUB SP SP (rvalue (word 192)) *)
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
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d02;       (* arm_MUL X2 X8 X3 *)
  0x9bc37d08;       (* arm_UMULH X8 X8 X3 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d22;       (* arm_MUL X2 X9 X3 *)
  0x9bc37d29;       (* arm_UMULH X9 X9 X3 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d42;       (* arm_MUL X2 X10 X3 *)
  0x9bc37d4a;       (* arm_UMULH X10 X10 X3 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d62;       (* arm_MUL X2 X11 X3 *)
  0x9bc37d6b;       (* arm_UMULH X11 X11 X3 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x92800002;       (* arm_MOVN X2 (word 0) 0 *)
  0x9a8233e2;       (* arm_CSEL X2 XZR X2 Condition_CC *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0x9a8333e3;       (* arm_CSEL X3 XZR X3 Condition_CC *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9a8533e5;       (* arm_CSEL X5 XZR X5 Condition_CC *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda05016b;       (* arm_SBC X11 X11 X5 *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
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
  0xa90437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&64))) *)
  0xa90503ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&80))) *)
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
  0xa90237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&32))) *)
  0xa90303ee;       (* arm_STP X14 X0 SP (Immediate_Offset (iword (&48))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9400e04;       (* arm_LDP X4 X3 X16 (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9410e04;       (* arm_LDP X4 X3 X16 (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa90a1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa90b23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xa9421be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa9420e04;       (* arm_LDP X4 X3 X16 (Immediate_Offset (iword (&32))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa9430e04;       (* arm_LDP X4 X3 X16 (Immediate_Offset (iword (&48))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
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
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d02;       (* arm_MUL X2 X8 X3 *)
  0x9bc37d08;       (* arm_UMULH X8 X8 X3 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d22;       (* arm_MUL X2 X9 X3 *)
  0x9bc37d29;       (* arm_UMULH X9 X9 X3 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d42;       (* arm_MUL X2 X10 X3 *)
  0x9bc37d4a;       (* arm_UMULH X10 X10 X3 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d62;       (* arm_MUL X2 X11 X3 *)
  0x9bc37d6b;       (* arm_UMULH X11 X11 X3 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x92800002;       (* arm_MOVN X2 (word 0) 0 *)
  0x9a8233e2;       (* arm_CSEL X2 XZR X2 Condition_CC *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0x9a8333e3;       (* arm_CSEL X3 XZR X3 Condition_CC *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9a8533e5;       (* arm_CSEL X5 XZR X5 Condition_CC *)
  0xeb020108;       (* arm_SUBS X8 X8 X2 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
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
  0xab088129;       (* arm_ADDS X9 X9 (Shiftedreg X8 LSL 32) *)
  0xd360fd03;       (* arm_LSR X3 X8 32 *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d02;       (* arm_MUL X2 X8 X3 *)
  0x9bc37d08;       (* arm_UMULH X8 X8 X3 *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab09814a;       (* arm_ADDS X10 X10 (Shiftedreg X9 LSL 32) *)
  0xd360fd23;       (* arm_LSR X3 X9 32 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d22;       (* arm_MUL X2 X9 X3 *)
  0x9bc37d29;       (* arm_UMULH X9 X9 X3 *)
  0xba020108;       (* arm_ADCS X8 X8 X2 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0a816b;       (* arm_ADDS X11 X11 (Shiftedreg X10 LSL 32) *)
  0xd360fd43;       (* arm_LSR X3 X10 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d42;       (* arm_MUL X2 X10 X3 *)
  0x9bc37d4a;       (* arm_UMULH X10 X10 X3 *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0b8108;       (* arm_ADDS X8 X8 (Shiftedreg X11 LSL 32) *)
  0xd360fd63;       (* arm_LSR X3 X11 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xb26083e3;       (* arm_MOV X3 (rvalue (word 18446744069414584321)) *)
  0x9b037d62;       (* arm_MUL X2 X11 X3 *)
  0x9bc37d6b;       (* arm_UMULH X11 X11 X3 *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0c0108;       (* arm_ADDS X8 X8 X12 *)
  0xba0d0129;       (* arm_ADCS X9 X9 X13 *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0xb2407fe3;       (* arm_MOV X3 (rvalue (word 4294967295)) *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
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
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
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
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
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
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
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
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
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
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
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
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0xba0400c6;       (* arm_ADCS X6 X6 X4 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb26083e4;       (* arm_MOV X4 (rvalue (word 18446744069414584321)) *)
  0x8a030084;       (* arm_AND X4 X4 X3 *)
  0x9a040108;       (* arm_ADC X8 X8 X4 *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9440600;       (* arm_LDP X0 X1 X16 (Immediate_Offset (iword (&64))) *)
  0xa9450e02;       (* arm_LDP X2 X3 X16 (Immediate_Offset (iword (&80))) *)
  0xaa010004;       (* arm_ORR X4 X0 X1 *)
  0xaa030045;       (* arm_ORR X5 X2 X3 *)
  0xaa050084;       (* arm_ORR X4 X4 X5 *)
  0xeb1f009f;       (* arm_CMP X4 XZR *)
  0xa94007e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&0))) *)
  0xa940362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa9410fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&16))) *)
  0xa941362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94817e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&128))) *)
  0xa942362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa9491fe6;       (* arm_LDP X6 X7 SP (Immediate_Offset (iword (&144))) *)
  0xa943362c;       (* arm_LDP X12 X13 X17 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94a27e8;       (* arm_LDP X8 X9 SP (Immediate_Offset (iword (&160))) *)
  0xd280002c;       (* arm_MOV X12 (rvalue (word 1)) *)
  0xb2607fed;       (* arm_MOV X13 (rvalue (word 18446744069414584320)) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94b2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&176))) *)
  0x9280000c;       (* arm_MOVN X12 (word 0) 0 *)
  0xb27f7bed;       (* arm_MOV X13 (rvalue (word 4294967294)) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0xa90005e0;       (* arm_STP X0 X1 X15 (Immediate_Offset (iword (&0))) *)
  0xa9010de2;       (* arm_STP X2 X3 X15 (Immediate_Offset (iword (&16))) *)
  0xa90215e4;       (* arm_STP X4 X5 X15 (Immediate_Offset (iword (&32))) *)
  0xa9031de6;       (* arm_STP X6 X7 X15 (Immediate_Offset (iword (&48))) *)
  0xa90425e8;       (* arm_STP X8 X9 X15 (Immediate_Offset (iword (&64))) *)
  0xa9052dea;       (* arm_STP X10 X11 X15 (Immediate_Offset (iword (&80))) *)
  0x910303ff;       (* arm_ADD SP SP (rvalue (word 192)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let P256_SCALARMULBASE_ALT_EXEC = ARM_MK_EXEC_RULE p256_scalarmulbase_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Local versions of the subroutines.                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DEMONT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_alt_mc,P256_SCALARMULBASE_ALT_EXEC,
    0x2ac,bignum_demont_p256_mc,BIGNUM_DEMONT_P256_SUBROUTINE_CORRECT)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `pc + 0x2ac`; `read X30 s`];;

let LOCAL_INV_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_alt_mc,P256_SCALARMULBASE_ALT_EXEC,
    0x340,bignum_inv_p256_mc,BIGNUM_INV_P256_SUBROUTINE_CORRECT)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `pc + 0x340`; `read SP s`; `read X30 s`];;

let LOCAL_MUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_alt_mc,P256_SCALARMULBASE_ALT_EXEC,
    0x1404,bignum_montmul_p256_alt_mc,
    BIGNUM_MONTMUL_P256_ALT_SUBROUTINE_CORRECT)
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s`;
   `pc + 0x1404`; `read X30 s`];;

let LOCAL_SQR_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_alt_mc,P256_SCALARMULBASE_ALT_EXEC,
    0x15cc,bignum_montsqr_p256_alt_mc,
    BIGNUM_MONTSQR_P256_ALT_SUBROUTINE_CORRECT)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s`;
   `pc + 0x15cc`; `read X30 s`];;

let LOCAL_JMIXADD_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
       P256_MONTJMIXADD_ALT_SUBROUTINE_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (p256_scalarmulbase_alt_mc,P256_SCALARMULBASE_ALT_EXEC,
    0x173c,p256_montjmixadd_alt_mc,th)
  [`read X0 s`; `read X1 s`;
   `read(memory :> bytes(read X1 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X1 s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read X1 s) (word 64),8 * 4)) s`;
   `read X2 s`;
   `read(memory :> bytes(read X2 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X2 s) (word 32),8 * 4)) s`;
   `pc + 0x173c`; `read SP s`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let affinepointz_p256 = new_definition
 `affinepointz_p256 (x,y) P <=>
        if x = 0 /\ y = 0 then P = NONE
        else P = SOME(paired (modular_decode (256,p_256)) (x,y))`;;

let REPRESENTS2_P256_NONZERO = prove
 (`!P x y. represents2_p256 P (x,y) ==> ~(P = group_id p256_group)`,
  REWRITE_TAC[represents2_p256; P256_GROUP] THEN MESON_TAC[option_DISTINCT]);;

let REPRESENTS_P256_2 = prove
 (`!P x y. represents_p256 P (x,y,(2 EXP 256) MOD p_256) <=>
           represents2_p256 P (x,y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[represents2_p256; represents_p256] THEN
  REWRITE_TAC[paired; tripled; weierstrass_of_jacobian] THEN
  REWRITE_TAC[montgomery_decode; INTEGER_MOD_RING_CLAUSES; p_256] THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INVERSE_MOD_CONV)) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[ring_div; RING_INV_INTEGER_MOD_RING;
              INTEGER_MOD_RING_CLAUSES; COPRIME_1] THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INVERSE_MOD_CONV)) THEN
  REWRITE_TAC[INT_MUL_RID] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[]);;

let REPRESENTS_P256_NEGATION = prove
 (`!P x y z.
        represents_p256 P (x,y,z)
        ==> P IN group_carrier p256_group /\ ~(P = group_id p256_group)
            ==> represents_p256 (group_inv p256_group P) (x,p_256 - y,z)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; P256_GROUP] THEN
  REWRITE_TAC[IN; option_DISTINCT] THEN REWRITE_TAC[weierstrass_curve] THEN
  REWRITE_TAC[represents_p256; weierstrass_of_jacobian; tripled] THEN
  MAP_EVERY X_GEN_TAC [`X:int`; `Y:int`; `x:num`; `y:num`; `z:num`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[montgomery_decode; option_INJ; PAIR_EQ; weierstrass_neg] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[INT_ARITH `a + --(&3) * b + c:int = a - &3 * b + c`] THEN
  ONCE_REWRITE_TAC[INT_CONG_SYM] THEN
  ASM_CASES_TAC `Y:int = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[NO_ROOTS_P256];
    ALL_TAC] THEN
  ASM_CASES_TAC `y = 0` THENL
   [ASM_REWRITE_TAC[ring_div; RING_INV_INTEGER_MOD_RING; INT_OF_NUM_CLAUSES;
                    INT_OF_NUM_REM; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[MULT_CLAUSES; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_REM_ZERO];
    ALL_TAC] THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ring_div]] THEN
  REWRITE_TAC[RING_INV_INTEGER_MOD_RING; INT_OF_NUM_CLAUSES;
              INT_OF_NUM_REM; INTEGER_MOD_RING_CLAUSES] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO; INT_NEG_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[INTEGER_RULE
   `((i * (p - y)) * j:int == --((i * y) * j)) (mod p)`]);;

let REPRESENTS_P256_Y_NONZERO = prove
 (`!P x y z.
        represents_p256 P (x,y,z)
        ==> P IN group_carrier p256_group /\ ~(z = 0)
            ==> ~(y = 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P256_NEGATION) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p256]) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[montgomery_decode; tripled; weierstrass_of_jacobian] THEN
  REWRITE_TAC[represents_p256; SUB_0; LT_REFL; P256_GROUP] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; INT_REM_EQ_0] THEN
  MATCH_MP_TAC(MESON[]
   `~(x = y) /\ ~p ==> (if p then x else y) = a ==> ~(a = x)`) THEN
  REWRITE_TAC[option_DISTINCT; GSYM INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(MP_TAC o SPEC `(&2:int) pow 256` o MATCH_MP (INTEGER_RULE
    `p divides i * z ==> !q:int. (q * i == &1) (mod p) ==> p divides z`)) THEN
  REWRITE_TAC[GSYM num_divides; INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2; NOT_IMP] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  MP_TAC p_256 THEN ASM_ARITH_TAC);;

let REPRESENTS2_P256_NEGATION = prove
 (`!P x y.
        represents2_p256 P (x,y)
        ==> P IN group_carrier p256_group
            ==> represents2_p256 (group_inv p256_group P) (x,p_256 - y)`,
  MESON_TAC[REPRESENTS2_P256_NONZERO; REPRESENTS_P256_2;
                REPRESENTS_P256_NEGATION]);;

let unilemma0 = prove
 (`x = a MOD p_256 ==> x < p_256 /\ &x = &a rem &p_256`,
  REWRITE_TAC[INT_OF_NUM_REM; p_256] THEN ARITH_TAC);;

let unilemma1 = prove
 (`&x = a rem &p_256 ==> x < p_256 /\ &x = a rem &p_256`,
  SIMP_TAC[GSYM INT_OF_NUM_LT; INT_LT_REM_EQ; p_256] THEN INT_ARITH_TAC);;

let fdivlemma = prove
  (`!f a b c:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ c IN ring_carrier f /\
        ~(b = ring_0 f) /\
        ring_mul f b c = a
        ==> ring_div f a b = c`,
  FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conveniently encoding tabulation in terms of specific byte array.         *)
(* ------------------------------------------------------------------------- *)

let p256_tabulates =
  let lemma = prove
   (`read (memory :> bytes(base,len)) s = read (memory :> bytes(base,len)) s'
     ==> m + n <= len
         ==> read (memory :> bytes(word_add base (word n),m)) s =
             read (memory :> bytes(word_add base (word n),m)) s'`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM
      `\x. x DIV 2 EXP (8 * n) MOD (2 EXP (8 * m))`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE `m + n <= len ==> MIN (len - n) m = m`]) in
  let eth = prove
   (`?f. !P blocksize table len s.
        f P blocksize table len (read (memory :> bytes(table,len)) s) <=>
        (256 DIV blocksize + 1) * 2 EXP (blocksize - 1) * 64 <= len /\
        !i. i <= 256 DIV blocksize
            ==> !j. 1 <= j /\ j <= 2 EXP (blocksize - 1)
                    ==> represents2_p256
                         (group_pow p256_group P (2 EXP (blocksize * i) * j))
                         (bignum_pair_from_memory
                           (word_add table
                         (word (64 * ((2 EXP (blocksize - 1) * i + j - 1)))),4)
                          s)`,
    REWRITE_TAC[GSYM SKOLEM_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC
     `(256 DIV blocksize + 1) * 2 EXP (blocksize - 1) * 64 <= len` THEN
    ASM_REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[EQ_SYM_EQ];
      EXISTS_TAC `\x:num. F` THEN REWRITE_TAC[]] THEN
    GEN_REWRITE_TAC I
     [GSYM(REWRITE_RULE[FUN_EQ_THM; o_THM] FUNCTION_FACTORS_LEFT)] THEN
    MAP_EVERY X_GEN_TAC [`s':armstate`; `s:armstate`] THEN DISCH_TAC THEN
    REPEAT(MATCH_MP_TAC(MESON[]
            `(!x. P x ==> (Q x <=> R x))
             ==> ((!x. P x ==> Q x) <=> (!x. P x ==> R x))`) THEN
           GEN_TAC THEN DISCH_TAC) THEN
    AP_TERM_TAC THEN REWRITE_TAC[bignum_pair_from_memory; PAIR_EQ] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONJ_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP lemma) THEN
    REWRITE_TAC[ARITH_RULE `8 * 4 + x + 8 * 4 = 8 * 8 + x`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `a * b * 64 <= len
      ==> x <= 64 /\ y < b * a ==> x + 64 * y <= len`)) THEN
    (CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `1 <= j /\ j <= b
      ==> b * (i + 1) <= b * k ==> b * i + j - 1 < b * k`)) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC) in
  new_specification ["p256_tabulates"] eth;;

let P256_SCALARMULBASE_ALT_CORRECT = time prove
 (`!res scalar blocksize tab n len tabulation pc stackpointer.
        2 <= val blocksize /\ val blocksize <= 31 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,512))
            [(word pc,0x2c84); (res,64); (scalar,32); (tab,len)] /\
        nonoverlapping (res,64) (word pc,0x2c84)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_scalarmulbase_alt_mc /\
                  read PC s = word(pc + 0x14) /\
                  read SP s = word_add stackpointer (word 224) /\
                  C_ARGUMENTS [res;scalar;blocksize;tab] s /\
                  bignum_from_memory (scalar,4) s = n /\
                  read (memory :> bytes(tab,len)) s = tabulation)
             (\s. read PC s = word (pc + 0x294) /\
                  !P. P IN group_carrier p256_group /\
                      p256_tabulates P (val blocksize) tab len tabulation
                      ==> affinepointz_p256
                           (bignum_pair_from_memory(res,4) s)
                           (group_pow p256_group P n))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X30] ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(stackpointer,512)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[GSYM SEQ_ASSOC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC [`res:int64`; `scalar:int64`] THEN
  W64_GEN_TAC `blocksize:num` THEN
  MAP_EVERY X_GEN_TAC
   [`tab:int64`; `n_input:num`; `len:num`; `tabulation:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ; bignum_pair_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `b <= 31 ==> b < 64`)) THEN

  SUBGOAL_THEN `val(word blocksize:int64) = blocksize` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Modified input argument, mathematically first ***)

  ABBREV_TAC `n = n_input MOD n_256` THEN
  SUBGOAL_THEN `n < n_256` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[n_256] THEN ARITH_TAC; ALL_TAC] THEN

  (*** Main loop invariant setup ***)

  ENSURES_WHILE_UP_TAC `256 DIV blocksize + 1` `pc + 0x98` `pc + 0x224`
   `\i s.
      read SP s = word_add stackpointer (word 224) /\
      read X19 s = res /\
      read X20 s = word blocksize /\
      read X21 s = word_add tab (word(64 * (2 EXP (blocksize - 1) * i))) /\
      read X22 s = word i /\
      val(read X24 s) <= 1 /\
      bignum_from_memory(word_add stackpointer (word 224),4) s =
      n DIV 2 EXP (blocksize * i) /\
      read (memory :> bytes(tab,len)) s = tabulation /\
      (~(val(read X24 s) = 0)
       ==> &2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)) /\
      !P. P IN group_carrier p256_group /\
          p256_tabulates P blocksize tab len tabulation
          ==> represents_p256
                (group_zpow p256_group P
                    (&n rem &2 pow (blocksize * i) -
                     &2 pow (blocksize * i) * &(val(read X24 s))))
                    (bignum_triple_from_memory
                     (word_add stackpointer (word 256),4) s)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of invariant ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "nin_" `read (memory :> bytes(scalar,8 * 4)) s0` THEN
    ARM_ACCSTEPS_TAC P256_SCALARMULBASE_ALT_EXEC (16--19) (1--33) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    REWRITE_TAC[bignum_triple_from_memory] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s33" THEN
    REWRITE_TAC[MULT_CLAUSES; INT_POW; INT_REM_1] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `carry_s19 <=> n_input < n_256` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "n_input" THEN
        REWRITE_TAC[n_256; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[DIV_1] THEN EXPAND_TAC "n" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[n_256] THEN EXPAND_TAC "n_input" THEN BOUNDER_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_SUB] THEN
      EXPAND_TAC "n_input" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
        ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `x:real < y ==> x - &n < y`) THEN
        REWRITE_TAC[REAL_OF_NUM_LT] THEN EXPAND_TAC "n_input" THEN
        BOUNDER_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
      EXPAND_TAC "n_input" THEN
      REWRITE_TAC[bignum_of_wordlist; n_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; n_256] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_NPOW; group_pow] THEN
      REWRITE_TAC[represents_p256; P256_GROUP; tripled; montgomery_decode;
                  weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES;
                  bignum_of_wordlist; p_256] THEN
      CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC INVERSE_MOD_CONV))];

    (*** Defer the interesting bit, invariant preservation, till later ***)

    ALL_TAC;

    (*** Trivial loop-back goal ***)

    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC P256_SCALARMULBASE_ALT_EXEC (1--3) THEN
    ASM_REWRITE_TAC[VAL_WORD; ADD_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    UNDISCH_TAC `i < 256 DIV blocksize + 1` THEN
    REWRITE_TAC[ARITH_RULE `i < n + 1 <=> i <= n`] THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN
    REWRITE_TAC[ARITH_RULE `i < 257 <=> i <= 256`] THEN
    MESON_TAC[LE_TRANS; MOD_LE];

    (*** Final conversion and mathematics ***)

    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN

    SUBGOAL_THEN `257 <= blocksize * (256 DIV blocksize + 1)` ASSUME_TAC THENL
     [MP_TAC(GSYM(SPECL [`256`; `blocksize:num`] DIVISION)) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&n rem &2 pow (blocksize * (256 DIV blocksize + 1)) = &n`
    SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP 257` THEN
      ASM_SIMP_TAC[LE_EXP; ARITH_EQ] THEN
      UNDISCH_TAC `n < n_256` THEN REWRITE_TAC[n_256] THEN ARITH_TAC;
      ALL_TAC] THEN

    GHOST_INTRO_TAC `X:num`
     `bignum_from_memory (word_add stackpointer (word 256),4)` THEN
    GHOST_INTRO_TAC `Y:num`
     `bignum_from_memory (word_add stackpointer (word 288),4)` THEN
    GHOST_INTRO_TAC `Z:num`
     `bignum_from_memory (word_add stackpointer (word 320),4)` THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (1--3) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[]
     `read PC s = (if p then x else y) ==> ~p ==> read PC s = y`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD; ADD_CLAUSES; DIMINDEX_64] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[NOT_LT] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o rand o snd) THEN
      ANTS_TAC THENL
       [TRANS_TAC LET_TRANS `31 * (256 + 1)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC LE_MULT2; CONV_TAC NUM_REDUCE_CONV] THEN
        ASM_REWRITE_TAC[LE_ADD_RCANCEL; DIV_LE];
        ASM_SIMP_TAC[]];
      DISCH_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GE; NOT_LE] THEN ANTS_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP 257` THEN
      ASM_SIMP_TAC[LE_EXP; ARITH_EQ] THEN
      UNDISCH_TAC `n < n_256` THEN REWRITE_TAC[n_256] THEN ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INT_MUL_RZERO; INT_SUB_RZERO])] THEN

    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (4--6) THEN LOCAL_SQR_TAC 7 THEN
    ABBREV_TAC
     `Z2 =
      read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s7` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (8--11) THEN
    LOCAL_MUL_TAC 12 THEN
    ABBREV_TAC
     `Z3 =
      read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s12` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (13--15) THEN
    LOCAL_DEMONT_TAC 16 THEN
    ABBREV_TAC
     `Z3' =
      read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s16` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (17--19) THEN
    LOCAL_INV_TAC 20 THEN
    ABBREV_TAC
     `I3 =
      read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s20` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (21--24) THEN
    LOCAL_MUL_TAC 25 THEN
    ABBREV_TAC
     `I2 =
      read (memory :> bytes(word_add stackpointer (word 352),8 * 4)) s25` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (26--29) THEN
    LOCAL_MUL_TAC 30 THEN
    ABBREV_TAC `X' = read (memory :> bytes(res,8 * 4)) s30` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (31--34) THEN
    LOCAL_MUL_TAC 35 THEN
    ABBREV_TAC
     `Y' = read (memory :> bytes(word_add res (word 32),8 * 4)) s35` THEN

    (*** Final mathematics sorting out last affine conversion operations ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s35" THEN X_GEN_TAC `P:(int#int)option` THEN
    STRIP_TAC THEN

    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[GROUP_NPOW] THEN
    SUBGOAL_THEN
     `group_pow p256_group P n = group_pow p256_group P n_input`
    SUBST1_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[GSYM P256_GROUP_ORDER] THEN
      ASM_SIMP_TAC[GROUP_POW_MOD_ORDER; FINITE_GROUP_CARRIER_P256];
      ALL_TAC] THEN

    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS_P256_Y_NONZERO) THEN
    ASM_SIMP_TAC[GROUP_POW] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [represents_p256]) THEN
    REWRITE_TAC[affinepointz_p256] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN

    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    REPEAT(ANTS_TAC THENL
     [TRY(COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
          W(MP_TAC o PART_MATCH (lhand o lhand) INVERSE_MOD_BOUND o
            rand o lhand o snd) THEN
          REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC) THEN
      REWRITE_TAC[p_256] THEN RULE_ASSUM_TAC(REWRITE_RULE[p_256]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[];
      (DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma0) ORELSE
       DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP unilemma1) ORELSE
       STRIP_TAC)]) THEN

    ASM_CASES_TAC `Z = 0` THENL
     [ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_MUL_LZERO; INT_MUL_RZERO;
                      INT_REM_ZERO; num_divides; INT_DIVIDES_0; tripled;
                      weierstrass_of_jacobian; INTEGER_MOD_RING_CLAUSES;
                      montgomery_decode];
      ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN

    MP_TAC(SPECL [`p_256`; `2 EXP 256`] INVERSE_MOD_LMUL_EQ) THEN
    REWRITE_TAC[COPRIME_REXP; COPRIME_2] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [REWRITE_TAC[p_256] THEN ARITH_TAC; DISCH_TAC] THEN

    SUBGOAL_THEN `~(p_256 divides Z3')` MP_TAC THENL
     [ASM_REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      MP_TAC(SPECL [`3`; `p_256`; `Z:num`] PRIME_DIVEXP_EQ) THEN
      ASM_SIMP_TAC[DIVIDES_EQ_ZERO; ARITH_EQ; PRIME_P256] THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
      REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[TAUT `p ==> ~q ==> ~r <=> p /\ r ==> q`] THEN
      CONV_TAC INTEGER_RULE;
      DISCH_THEN(fun th ->
       RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)] THEN

    SUBGOAL_THEN `~(p_256 divides Y')` MP_TAC THENL
     [ASM_REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      MP_TAC(SPECL [`p_256`; `Z3':num`] INVERSE_MOD_LMUL_EQ) THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P256] THEN
      MP_TAC(SPECL [`p_256`; `Y:num`] DIVIDES_EQ_ZERO) THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
      REWRITE_TAC[num_divides; num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[TAUT `p ==> ~q ==> r ==> ~s <=> p /\ r /\ s ==> q`] THEN
      CONV_TAC INTEGER_RULE;
      ASM_SIMP_TAC[DIVIDES_EQ_ZERO] THEN DISCH_TAC] THEN

    ASM_REWRITE_TAC[weierstrass_of_jacobian; tripled; paired] THEN
    COND_CASES_TAC THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
      REWRITE_TAC[montgomery_decode; INTEGER_MOD_RING_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
      SIMP_TAC[INT_REM_EQ_0; PRIME_INT_DIVPROD_EQ; PRIME_P256;
               GSYM INT_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[GSYM num_divides; DIVIDES_EQ_ZERO] THEN
      SIMP_TAC[GSYM PRIME_COPRIME_EQ; PRIME_P256; num_coprime] THEN
      CONV_TAC INTEGER_RULE;
      REWRITE_TAC[option_INJ; PAIR_EQ]] THEN

    RULE_ASSUM_TAC(REWRITE_RULE
     [montgomery_decode; INTEGER_MOD_RING_CLAUSES]) THEN
    CONJ_TAC THEN MATCH_MP_TAC fdivlemma THEN
    SIMP_TAC[INTEGER_MOD_RING_CARRIER_REM; montgomery_decode; modular_decode;
             RING_POW; FIELD_POW_EQ_0; FIELD_INTEGER_MOD_RING; PRIME_P256] THEN
    ASM_REWRITE_TAC[ARITH_EQ; INTEGER_MOD_RING_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC[INT_MUL_ASSOC] THEN MATCH_MP_TAC(INTEGER_RULE
     `!e:int. (i * e == &1) (mod p) /\ (b * e == a) (mod p)
              ==> (a * i == b) (mod p)`) THEN
    EXISTS_TAC `&Z3':int` THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
       ASM_SIMP_TAC[INVERSE_MOD_LMUL_EQ; PRIME_COPRIME_EQ; PRIME_P256];
       ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES]]) THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC; INT_REM_EQ] THEN
    CONV_TAC INTEGER_RULE] THEN

  (*** Initial ghosting and abbreviations for invariant step ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < 129` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `i < 256 DIV b + 1 ==> 256 DIV b <= 256 DIV 2==> i < 129`)) THEN
    MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [bignum_triple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  GHOST_INTRO_TAC `X:num`
   `bignum_from_memory (word_add stackpointer (word 256),4)` THEN
  GHOST_INTRO_TAC `Y:num`
   `bignum_from_memory (word_add stackpointer (word 288),4)` THEN
  GHOST_INTRO_TAC `Z:num`
   `bignum_from_memory (word_add stackpointer (word 320),4)` THEN
  GHOST_INTRO_TAC `ncf:num` `\s. val(read X24 s)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:bool` SUBST_ALL_TAC) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQ_BITVAL]) THEN
  ABBREV_TAC `bf = n DIV 2 EXP (blocksize * i) MOD 2 EXP blocksize` THEN
  SUBGOAL_THEN `bf < 2 EXP blocksize` ASSUME_TAC THENL
   [EXPAND_TAC "bf" THEN REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `bf + bitval cf <= 2 EXP blocksize` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `b < e /\ c <= 1 ==> b + c <= e`) THEN
    ASM_REWRITE_TAC[BITVAL_BOUND];
    ALL_TAC] THEN
  ABBREV_TAC `cf' <=> bf + bitval cf > 2 EXP (blocksize - 1)` THEN
  ABBREV_TAC
   `j = if cf' then 2 EXP blocksize - (bf + bitval cf)
         else bf + bitval cf` THEN
  SUBGOAL_THEN `j <= 2 EXP (blocksize - 1)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN UNDISCH_TAC `bf + bitval cf <= 2 EXP blocksize` THEN
    SUBGOAL_THEN `2 EXP blocksize = 2 * 2 EXP (blocksize - 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `2 <= blocksize` THEN ARITH_TAC;
      EXPAND_TAC "cf'" THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Setup of the inner loop for constant-time table selection ***)

  ENSURES_WHILE_UP_TAC `2 EXP (blocksize - 1)` `pc + 0x114` `pc + 0x150`
   `\k s.
      read SP s = word_add stackpointer (word 224) /\
      read X19 s = res /\
      read X20 s = word blocksize /\
      read X21 s = word_add tab
       (word(64 * (2 EXP (blocksize - 1) * i + k))) /\
      read X22 s = word i /\
      bignum_from_memory(word_add stackpointer (word 224),4) s =
      n DIV 2 EXP (blocksize * (i + 1)) /\
      read (memory :> bytes(tab,len)) s = tabulation /\
      bignum_from_memory (word_add stackpointer (word 256),4) s = X /\
      bignum_from_memory (word_add stackpointer (word 288),4) s = Y /\
      bignum_from_memory (word_add stackpointer (word 320),4) s = Z /\
      read X25 s = word j /\
      read X24 s = word (bitval cf') /\
      read X16 s = word_sub (word(2 EXP (blocksize - 1))) (word k) /\
      read X17 s = word_sub (word j) (word k) /\
      !P. ~(j = 0) /\ j <= k /\
          P IN group_carrier p256_group /\
          p256_tabulates P blocksize tab len tabulation
          ==> represents2_p256
               (group_pow p256_group P (2 EXP (blocksize * i) * j))
               (bignum_of_wordlist[read X0 s;read X1 s;read X2 s;read X3 s],
                bignum_of_wordlist[read X4 s;read X5 s;read X6 s;read X7 s])`
  THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ];

    (*** Bitfield selection and processing for indexing step ***)
    (*** Finished lazily by case analysis over blocksize not intelligence ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "nin_"
     `read (memory :> bytes (word_add stackpointer (word 224),8 * 4)) s0` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (1--6) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `word bf:int64` o  MATCH_MP (MESON[]
        `read X4 s = a ==> !a'. a = a' ==> read X4 s = a'`)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[word_jshl; DIMINDEX_64; MOD_LT] THEN EXPAND_TAC "bf" THEN
      SUBGOAL_THEN
       `(n DIV 2 EXP (blocksize * i)) MOD 2 EXP blocksize =
        (n DIV 2 EXP (blocksize * i)) MOD 2 EXP 64 MOD 2 EXP blocksize`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `n < s ==> MIN s n = n`];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
        (RAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV) [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      ONCE_REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; VAL_MOD_REFL] THEN
      REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD; WORD_VAL] THEN
      SIMP_TAC[WORD_SUB; EXP_EQ_0; ARITH_EQ; LE_1] THEN
      REWRITE_TAC[word_shl; MULT_CLAUSES; VAL_WORD_1] THEN
      REWRITE_TAC[WORD_AND_SYM];
      DISCH_TAC] THEN

    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (7--31) THEN

    SUBGOAL_THEN
     `word_add (word bf) (word(bitval cf)):int64 =
      word(bf + bitval cf)`
    SUBST_ALL_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o check (can
      (term_match [] `read X24 s = a` o concl))) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM NOT_LT] THEN
    SUBGOAL_THEN
     `val(word_ushr (word_jshl (word 1:int64) (word blocksize)) 1) <
      val(word(bf + bitval cf):int64) <=>
      cf'`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "cf'" THEN REWRITE_TAC[GT; word_jshl] THEN
      ASM_SIMP_TAC[DIMINDEX_64; MOD_LT; VAL_WORD_USHR; VAL_WORD_SHL;
                   VAL_WORD_1; MULT_CLAUSES; MOD_LT; LT_EXP;
                   ARITH_EQ; ARITH_LE; ARITH_LT; DIV_EXP] THEN
      ASM_SIMP_TAC[ARITH_RULE `2 <= b ==> 1 <= b`] THEN AP_TERM_TAC THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LET_TRANS `2 EXP blocksize` THEN
      ASM_REWRITE_TAC[LT_EXP; ARITH_EQ; LE_REFL];
      REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL] THEN DISCH_TAC] THEN

    SUBGOAL_THEN
     `(if cf'
       then word_sub (word_jshl (word 1) (word blocksize))
            (word (bf + bitval cf)):int64
       else word (bf + bitval cf)) = word j`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "j" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB; word_jshl; word_shl; VAL_WORD_1] THEN
      ASM_SIMP_TAC[DIMINDEX_64; MOD_LT; VAL_WORD_USHR; VAL_WORD_SHL;
                   VAL_WORD_1; MULT_CLAUSES; MOD_LT; LT_EXP;
                   ARITH_EQ; ARITH_LE; ARITH_LT; DIV_EXP];
      ALL_TAC] THEN

    SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
      ASM_REWRITE_TAC[LT_EXP; ARITH_EQ; LE_REFL] THEN
      UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; SUB_0; WORD_SUB_0] THEN
    REWRITE_TAC[MESON[LE] `~(j = 0) /\ j <= 0 /\ P <=> F`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `b * (i + 1) = b * i + b`] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
      EXISTS_TAC `val(nin_0:int64) MOD 2 EXP blocksize` THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    UNDISCH_TAC `2 <= blocksize` THEN UNDISCH_TAC `blocksize < 64` THEN
    SPEC_TAC(`blocksize:num`,`blocksize:num`) THEN
    REWRITE_TAC[bignum_of_wordlist; word_jushr; word_jshl; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The actual indexing ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY ABBREV_TAC
     [`t0 = read X0 s0`;
      `t1 = read X1 s0`;
      `t2 = read X2 s0`;
      `t3 = read X3 s0`;
      `t4 = read X4 s0`;
      `t5 = read X5 s0`;
      `t6 = read X6 s0`;
      `t7 = read X7 s0`] THEN
    ABBREV_TAC
     `newtab:int64 = word_add tab
                     (word(64 * (2 EXP (blocksize - 1) * i + k)))` THEN
    BIGNUM_LDIGITIZE_TAC "tabw_"
     `read (memory :> bytes (newtab,8 * 8)) s0` THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (1--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [EXPAND_TAC "newtab" THEN CONV_TAC WORD_RULE; ALL_TAC]) THEN
    X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    REWRITE_TAC[VAL_EQ_0; GSYM WORD_ADD; WORD_RULE
     `word_sub (word_sub x y) (word 1) = word 0 <=>
      word_add y (word 1) = x`] THEN
    SUBGOAL_THEN `word(k + 1):int64 = word j <=> j = k + 1` SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
      REWRITE_TAC[GSYM VAL_EQ] THEN BINOP_TAC THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
      ASM_REWRITE_TAC[ARITH_RULE `k + 1 <= n <=> k < n`] THEN
      REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
     `j <= k + 1 ==> j = k + 1 \/ j <= k /\ ~(j = k + 1)`)) THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `p256_tabulates P blocksize tab len tabulation` THEN
    EXPAND_TAC "tabulation" THEN REWRITE_TAC[p256_tabulates] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[ARITH_RULE `i <= 256 DIV b <=> i < 256 DIV b + 1`] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[LE_1; ADD_SUB] THEN
    REWRITE_TAC[bignum_pair_from_memory; BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_RULE `word(8 * 4) = word 32`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[ARITH_RULE `k + 1 <= n <=> k < n`];

    (*** Loop-back for the inner loop ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; bignum_triple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC [1]  THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
    SUBGOAL_THEN `word(2 EXP (blocksize - 1)):int64 = word k <=>
                  k = 2 EXP (blocksize - 1)`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
      REWRITE_TAC[GSYM VAL_EQ] THEN BINOP_TAC THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
      ASM_SIMP_TAC[LE_REFL; LT_IMP_LE] THEN
      REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
      ASM_SIMP_TAC[LT_IMP_NE]];

    ALL_TAC] THEN

  (*** The continuation into the rest of the main loop ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY ABBREV_TAC
   [`t0 = read X0 s0`;
    `t1 = read X1 s0`;
    `t2 = read X2 s0`;
    `t3 = read X3 s0`;
    `t4 = read X4 s0`;
    `t5 = read X5 s0`;
    `t6 = read X6 s0`;
    `t7 = read X7 s0`] THEN
  ARM_ACCSTEPS_TAC P256_SCALARMULBASE_ALT_EXEC [5;7;9;10] (1--17) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; VAL_EQ_0; COND_SWAP]) THEN
  MAP_EVERY ABBREV_TAC
   [`xs = read(memory :> bytes(word_add stackpointer (word 448),8 * 4)) s17`;
    `ys =
     read(memory :> bytes(word_add stackpointer (word 480),8 * 4)) s17`] THEN

  SUBGOAL_THEN
  `!P. ~(j = 0) /\
       P IN group_carrier p256_group /\
       p256_tabulates P blocksize tab len tabulation
       ==> represents2_p256
            (group_zpow p256_group P
              (--(&1) pow (bitval cf') * &2 pow (blocksize * i) * &j))
            (xs,ys)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[GSYM GROUP_NPOW; GSYM INT_OF_NUM_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["xs"; "ys"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[WORD_BITVAL_EQ_0; COND_SWAP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[INT_MUL_LID; GSYM INT_NEG_MINUS1] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS2_P256_NEGATION) THEN
    ASM_SIMP_TAC[GROUP_ZPOW; GROUP_ZPOW_NEG] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
     GEN_REWRITE_RULE I [represents2_p256]) THEN
    SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_EQ_0] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[bignum_of_wordlist; p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Mixed addition operation ***)

  ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (18--21) THEN
  LOCAL_JMIXADD_TAC 22 THEN
  MAP_EVERY ABBREV_TAC
   [`Xo = read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s22`;
    `Yo = read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s22`;
    `Zo = read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s22`]
  THEN BIGNUM_LDIGITIZE_TAC "xo_"
   `read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s22` THEN
  BIGNUM_LDIGITIZE_TAC "yo_"
   `read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s22` THEN
  BIGNUM_LDIGITIZE_TAC "z0_"
   `read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s22` THEN
  BIGNUM_LDIGITIZE_TAC "xi_"
   `read(memory :> bytes(word_add stackpointer (word 256),8 * 4)) s22` THEN
  BIGNUM_LDIGITIZE_TAC "yi_"
   `read(memory :> bytes(word_add stackpointer (word 288),8 * 4)) s22` THEN
  BIGNUM_LDIGITIZE_TAC "zi_"
   `read(memory :> bytes(word_add stackpointer (word 320),8 * 4)) s22` THEN

  (*** Multiplexing away the j = 0 case ***)

  ARM_STEPS_TAC P256_SCALARMULBASE_ALT_EXEC (23--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL; BITVAL_BOUND; GSYM WORD_ADD] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_BOUND; GSYM WORD_ADD]] THEN

  (*** Final mathematics ***)

  SUBGOAL_THEN
   `&n rem &2 pow (blocksize * (i + 1)) =
    &2 pow (blocksize * i) * &bf + &n rem &2 pow (blocksize * i)`
  (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "+" th) THENL
   [EXPAND_TAC "bf" THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
    REWRITE_TAC[GSYM MOD_MULT_MOD] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `b * (i + 1) = b * i + b`];
    ALL_TAC] THEN

  REWRITE_TAC[BITVAL_EQ_0] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [EXPAND_TAC "cf'" THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GE; GT; INT_OF_NUM_REM] THEN
    MATCH_MP_TAC(ARITH_RULE
     `c <= 1 /\ (2 * h <= 2 * b ==> x <= 2 * y)
      ==> h < b + c ==> x <= 2 * (y + z)`) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP); BITVAL_BOUND] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= b ==> SUC(b - 1) = b`] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 * a * b = a * 2 * b`] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `b * (i + 1) = b * i + b`] THEN
    SIMP_TAC[LE_MULT_LCANCEL];
    DISCH_TAC] THEN

  X_GEN_TAC `P:(int#int)option` THEN STRIP_TAC THEN
  REWRITE_TAC[bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[WORD_SUB_0; COND_SWAP] THEN

  DISCARD_STATE_TAC "s54" THEN

  SUBGOAL_THEN `val(word j:int64) = 0 <=> j = 0` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC LET_TRANS `2 EXP (blocksize - 1)` THEN
    ASM_REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `blocksize < 64` THEN ARITH_TAC;
    ALL_TAC] THEN

  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [REPLICATE_TAC 3
     (FIRST_X_ASSUM(K ALL_TAC o SPEC `P:(int#int)option`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC
     `(if cf' then 2 EXP blocksize - (bf + bitval cf) else bf + bitval cf) =
      j` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_SUB] THEN
    REWRITE_TAC[ARITH_RULE `b * (i + 1) = b * i + b`; INT_POW_ADD] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_RING;
    ALL_TAC] THEN

  ASM_CASES_TAC
   `&n rem &2 pow (blocksize * i) - &2 pow (blocksize * i) * &(bitval cf) =
    -- &1 pow bitval cf' * &2 pow (blocksize * i) * &j`
  THENL
   [POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    ASM_CASES_TAC `&n rem &2 pow (blocksize * i) = &0` THENL
     [FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
      ASM_REWRITE_TAC[INT_GE; INT_MUL_RZERO; BITVAL_EQ_0] THEN
      SIMP_TAC[INT_NOT_LE; INT_LT_POW2; BITVAL_CLAUSES] THEN
      DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o SYM) THEN
      REWRITE_TAC[INT_MUL_RZERO; INT_SUB_REFL; INT_ENTIRE] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_POW_EQ_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
      REWRITE_TAC[ARITH_RULE `b * (i + 1) = b * i + b`; INT_POW_ADD] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
        `r - e * x:int = c * e * j ==> e divides r`)) THEN
      REWRITE_TAC[GSYM num_divides; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      REWRITE_TAC[GSYM NOT_LT; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES]];
    ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o SPECL
   [`group_zpow p256_group P
       (&n rem &2 pow (blocksize * i) -
        &2 pow (blocksize * i) * &(bitval cf))`;
    `group_zpow p256_group P
        (-- &1 pow bitval cf' * &2 pow (blocksize * i) * &j)`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `P:(int#int)option`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:(int#int)option`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN

  SUBGOAL_THEN
   `-- &1 pow bitval cf' * &2 pow (blocksize * i) * &j:int =
    (&2 pow (blocksize * i) * (&bf + &(bitval cf))) -
    &2 pow (blocksize * (i + 1)) * &(bitval cf')`
  (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "*" th) THENL
   [UNDISCH_THEN
     `(if cf' then 2 EXP blocksize - (bf + bitval cf) else bf + bitval cf) =
      j` (SUBST1_TAC o SYM) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
    REWRITE_TAC[ARITH_RULE `b * (i + 1) = b * i + b`; INT_POW_ADD] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_RING;
    ASM_SIMP_TAC[GSYM GROUP_ZPOW_ADD]] THEN

  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN CONV_TAC INT_RING] THEN
  ASM_SIMP_TAC[GROUP_ZPOW_EQ; P256_GROUP_ELEMENT_ORDER] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REPRESENTS2_P256_NONZERO) THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_ZPOW_ID] THEN
  DISCH_THEN(K ALL_TAC) THEN

  W(MP_TAC o PART_MATCH (rand o lhand) INT_CONG_IMP_EQ o rand o snd) THEN
  ASM_REWRITE_TAC[TAUT `~(p /\ q) ==> ~q <=> ~(~p /\ q)`] THEN
  REWRITE_TAC[INT_NOT_LT] THEN

  ASM_CASES_TAC `blocksize * (i + 1) <= 256` THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[INT_NOT_LE] THEN
    MATCH_MP_TAC(INT_ARITH
     `!y. (&0 <= x /\ x < e) /\ (&0 <= b * e /\ b * e <= e) /\
          abs(z:int) <= e * y /\ e * (y + &1) < f
          ==> abs(x - e * b - z) < f`) THEN
    EXISTS_TAC `(&2:int) pow (blocksize - 1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES; LE_0; MOD_LT_EQ] THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_CLAUSES; LE_0; bitval] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NEG; INT_ABS_NUM] THEN
      REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN
      SIMP_TAC[INT_LE_LMUL_EQ; INT_LT_POW2] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC(INT_ARITH
     `e * &2 pow 1 <= e * b /\ &3 * e * &2 * b:int < &4 * n
      ==> e * (b + &1) < n`) THEN
    SIMP_TAC[INT_LE_LMUL_EQ; INT_LT_POW2; GSYM(CONJUNCT2 INT_POW)] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_POW_MONO THEN UNDISCH_TAC `2 <= blocksize` THEN
      ARITH_TAC;
      REWRITE_TAC[GSYM INT_POW_ADD]] THEN
    ASM_SIMP_TAC[ARITH_RULE
      `2 <= b ==> b * i + SUC(b - 1) = b * (i + 1)`] THEN
    TRANS_TAC INT_LET_TRANS `(&3:int) * &2 pow 256` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[n_256] THEN INT_ARITH_TAC] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN REWRITE_TAC[INT_POS] THEN
    MATCH_MP_TAC INT_POW_MONO THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN

  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [TAUT `p ==> q <=> q \/ ~p`]) THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    REMOVE_THEN "+" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GE; NOT_LE; INT_OF_NUM_REM] THEN
    MATCH_MP_TAC(ARITH_RULE
     `m MOD n <= m /\ 2 * m < e ==> 2 * m MOD n < e`) THEN
    REWRITE_TAC[MOD_LE] THEN TRANS_TAC LTE_TRANS `2 EXP 257` THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; ARITH_RULE `257 <= a <=> 256 < a`] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[n_256] THEN ARITH_TAC;
    DISCH_THEN(fun th -> SUBST_ALL_TAC(EQF_INTRO th)) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REWRITE_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; CONJUNCT1 INT_POW;
                INT_MUL_LID; INT_SUB_RZERO; INT_ADD_RID] THEN
    STRIP_TAC] THEN

  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  BOOL_CASES_TAC `cf:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; CONJUNCT1 INT_POW;
                INT_MUL_LID; INT_SUB_RZERO; INT_ADD_RID; INT_MUL_RID;
                ARITH_EQ; ADD_CLAUSES] THEN
  STRIP_TAC THENL
   [UNDISCH_THEN
     `&2 pow (blocksize * i) * &j:int = &2 pow (blocksize * i) * (&bf + &1)`
     (K ALL_TAC) THEN
    UNDISCH_THEN `bf + 1 = j` (SUBST_ALL_TAC o SYM);
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[INT_NOT_LE] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0:int <= x /\ abs(y) + x < n ==> abs(x - y) < n`) THEN
    REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NUM] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_POS] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
    UNDISCH_TAC `n < n_256` THEN ARITH_TAC] THEN

  SUBGOAL_THEN `blocksize * i <= 256` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LE_RDIV_EQ; ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `a <= b <=> a < b + 1`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `bi <= 256 ==> bi = 256 \/ bi <= 255`))
  THENL
   [SUBGOAL_THEN `&bf:int = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC
       `&n rem &2 pow (blocksize * (i + 1)) =
        &2 pow (blocksize * i) * &bf + &n rem &2 pow (blocksize * i)` THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE
       `n' < n_256 /\ n_256 < e /\ (e * 1 <= e * b)
        ==> ~(n' = e * b + n)`) THEN
      ASM_SIMP_TAC[LE_MULT_LCANCEL; LE_1; EXP_EQ_0; ARITH_EQ] THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[n_256] THEN ARITH_TAC] THEN
      W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
      UNDISCH_TAC `n < n_256` THEN ARITH_TAC;
      REWRITE_TAC[INT_ADD_LID; INT_MUL_RID]] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[INTEGER_RULE
     `(a - b:int == b) (mod n) <=> (a == &2 * b) (mod n)`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES;
                    GSYM num_congruent] THEN
    SUBGOAL_THEN `n MOD 2 EXP 256 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `n < n_256` THEN
      REWRITE_TAC[n_256] THEN ARITH_TAC;
      ASM_SIMP_TAC[CONG; MOD_LT] THEN DISCH_TAC] THEN
    UNDISCH_TAC
     `&2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)` THEN
    ASM_REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (INTEGER_RULE
   `(l - q:int == q * (b + &1)) (mod n)
    ==> (n - q == q * (b + &1) - l) (mod n)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    INT_CONG_IMP_EQ)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `(&0:int <= x /\ x < n) /\ (&0 <= y /\ y < n) ==> abs(x - y) < n`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INT_SUB_LE] THEN
      TRANS_TAC INT_LE_TRANS `(&2:int) pow 255` THEN
      ASM_SIMP_TAC[INT_POW_MONO; INT_ARITH `&1:int <= &2`] THEN
      REWRITE_TAC[n_256] THEN INT_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `a - b:int < a <=> &0 < b`; INT_LT_POW2];
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; INT_SUB_LE] THEN
      MATCH_MP_TAC(ARITH_RULE `m < e ==> m <= e * (b + 1)`) THEN
      REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    TRANS_TAC INT_LET_TRANS `&n rem &2 pow (blocksize * (i + 1))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC
        `&2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)` THEN
      INT_ARITH_TAC;
      REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
      W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN
      UNDISCH_TAC `n < n_256` THEN ARITH_TAC];
    REWRITE_TAC[INT_ARITH
     `n - q:int = q * (b + &1) - l <=> q * (b + &2) = n + l`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN DISCH_TAC] THEN

  FIRST_ASSUM(MP_TAC o SPEC `2 EXP 256 - n_256` o MATCH_MP (NUMBER_RULE
   `e * b:num = n + x ==> !m. e divides (n + m) ==> (x == m) (mod e)`)) THEN
  REWRITE_TAC[n_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 256`)] THEN
  ASM_SIMP_TAC[DIVIDES_EXP_LE_IMP; ARITH_RULE `i <= 255 ==> i <= 256`] THEN
  REWRITE_TAC[CONG; MOD_MOD_REFL] THEN MATCH_MP_TAC(MESON[]
   `(n MOD 2 EXP 256 MOD e = n MOD e) /\ ~(x = n MOD 2 EXP 256 MOD e)
    ==> ~(x = n MOD e)`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `i <= 255 ==> MIN 256 i = i`];
    CONV_TAC NUM_REDUCE_CONV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[MOD_LE; LE_TRANS]
   `x = a MOD n ==> x <= a`)) THEN
  UNDISCH_TAC
   `&2 * &n rem &2 pow (blocksize * i) >= &2 pow (blocksize * i)` THEN
  REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES; GE] THEN
  MATCH_MP_TAC(ARITH_RULE
   `2 * a < e ==> e <= 2 * x ==> ~(x <= a)`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  TRANS_TAC LTE_TRANS `2 EXP 225` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
  MAP_EVERY UNDISCH_TAC
   [`256 < blocksize * (i + 1)`; `blocksize <= 31`] THEN
  ARITH_TAC);;

let P256_SCALARMULBASE_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar blocksize tab n len tabulation pc stackpointer returnaddress.
        2 <= val blocksize /\ val blocksize <= 31 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
            [(word pc,0x2c84); (res,64); (scalar,32); (tab,len)] /\
        nonoverlapping (res,64) (word pc,0x2c84)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) p256_scalarmulbase_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [res;scalar;blocksize;tab] s /\
                  bignum_from_memory (scalar,4) s = n /\
                  read (memory :> bytes(tab,len)) s = tabulation)
             (\s. read PC s = returnaddress /\
                  !P. P IN group_carrier p256_group /\
                      p256_tabulates P (val blocksize) tab len tabulation
                      ==> affinepointz_p256
                           (bignum_pair_from_memory(res,4) s)
                           (group_pow p256_group P n))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(word_sub stackpointer (word 576),576)])`,
   ARM_ADD_RETURN_STACK_TAC P256_SCALARMULBASE_ALT_EXEC
   P256_SCALARMULBASE_ALT_CORRECT `[X19; X20; X21; X22; X23; X24; X25; X30]`
     576);;
