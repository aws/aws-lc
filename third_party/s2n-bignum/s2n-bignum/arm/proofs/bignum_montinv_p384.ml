(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery inverse modulo p_384, the field characteristic for NIST P-384. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "Divstep/divstep_bounds.ml";;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/p384/bignum_montinv_p384.o";;
 ****)

let bignum_montinv_p384_mc = define_assert_from_elf "bignum_montinv_p384_mc" "arm/p384/bignum_montinv_p384.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10403ff;       (* arm_SUB SP SP (rvalue (word 256)) *)
  0xaa0003f4;       (* arm_MOV X20 X0 *)
  0xb2407fea;       (* arm_MOV X10 (rvalue (word 4294967295)) *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0x9280002c;       (* arm_MOVN X12 (word 1) 0 *)
  0x9280000f;       (* arm_MOVN X15 (word 0) 0 *)
  0xa9002fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0xa9013fec;       (* arm_STP X12 X15 SP (Immediate_Offset (iword (&16))) *)
  0xa9023fef;       (* arm_STP X15 X15 SP (Immediate_Offset (iword (&32))) *)
  0xf9001bff;       (* arm_STR XZR SP (Immediate_Offset (word 48)) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xeb0a004a;       (* arm_SUBS X10 X2 X10 *)
  0xfa0b006b;       (* arm_SBCS X11 X3 X11 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xfa0c008c;       (* arm_SBCS X12 X4 X12 *)
  0xfa0f00ad;       (* arm_SBCS X13 X5 X15 *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xfa0f00ce;       (* arm_SBCS X14 X6 X15 *)
  0xfa0f00ef;       (* arm_SBCS X15 X7 X15 *)
  0x9a8a3042;       (* arm_CSEL X2 X2 X10 Condition_CC *)
  0x9a8b3063;       (* arm_CSEL X3 X3 X11 Condition_CC *)
  0x9a8c3084;       (* arm_CSEL X4 X4 X12 Condition_CC *)
  0x9a8d30a5;       (* arm_CSEL X5 X5 X13 Condition_CC *)
  0x9a8e30c6;       (* arm_CSEL X6 X6 X14 Condition_CC *)
  0x9a8f30e7;       (* arm_CSEL X7 X7 X15 Condition_CC *)
  0xa9040fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&64))) *)
  0xa90517e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&80))) *)
  0xa9061fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&96))) *)
  0xf9003bff;       (* arm_STR XZR SP (Immediate_Offset (word 112)) *)
  0xa9087fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&128))) *)
  0xa9097fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&144))) *)
  0xa90a7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&160))) *)
  0xb2544fec;       (* arm_MOV X12 (rvalue (word 18446726481523507200)) *)
  0xb275018a;       (* arm_ORR X10 X12 (rvalue (word 2048)) *)
  0xa90c2bff;       (* arm_STP XZR X10 SP (Immediate_Offset (iword (&192))) *)
  0xd280ffeb;       (* arm_MOV X11 (rvalue (word 2047)) *)
  0xb254016b;       (* arm_ORR X11 X11 (rvalue (word 17592186044416)) *)
  0xa90d33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&208))) *)
  0xd281000c;       (* arm_MOV X12 (rvalue (word 2048)) *)
  0xa90e33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&224))) *)
  0xd28001f5;       (* arm_MOV X21 (rvalue (word 15)) *)
  0xd2800036;       (* arm_MOV X22 (rvalue (word 1)) *)
  0x140001b9;       (* arm_B (word 1764) *)
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
  0xf94023e8;       (* arm_LDR X8 SP (Immediate_Offset (word 64)) *)
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
  0xf94027e8;       (* arm_LDR X8 SP (Immediate_Offset (word 72)) *)
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
  0xf90023e5;       (* arm_STR X5 SP (Immediate_Offset (word 64)) *)
  0xf9400be7;       (* arm_LDR X7 SP (Immediate_Offset (word 16)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9402be8;       (* arm_LDR X8 SP (Immediate_Offset (word 80)) *)
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
  0xf90027e3;       (* arm_STR X3 SP (Immediate_Offset (word 72)) *)
  0xf9400fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 24)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xf9402fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 88)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c6eca6;       (* arm_EXTR X6 X5 X6 59 *)
  0xf9000be6;       (* arm_STR X6 SP (Immediate_Offset (word 16)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0x93c4ec44;       (* arm_EXTR X4 X2 X4 59 *)
  0xf9002be4;       (* arm_STR X4 SP (Immediate_Offset (word 80)) *)
  0xf94013e7;       (* arm_LDR X7 SP (Immediate_Offset (word 32)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xf94033e8;       (* arm_LDR X8 SP (Immediate_Offset (word 96)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0x93c5ec65;       (* arm_EXTR X5 X3 X5 59 *)
  0xf9000fe5;       (* arm_STR X5 SP (Immediate_Offset (word 24)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0x93c2ecc2;       (* arm_EXTR X2 X6 X2 59 *)
  0xf9002fe2;       (* arm_STR X2 SP (Immediate_Offset (word 88)) *)
  0xf94017e7;       (* arm_LDR X7 SP (Immediate_Offset (word 40)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0xf9401bf7;       (* arm_LDR X23 SP (Immediate_Offset (word 48)) *)
  0xca0e02e2;       (* arm_EOR X2 X23 X14 *)
  0x8a0a0042;       (* arm_AND X2 X2 X10 *)
  0xcb0203e2;       (* arm_NEG X2 X2 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94037e8;       (* arm_LDR X8 SP (Immediate_Offset (word 104)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0xf9403bf8;       (* arm_LDR X24 SP (Immediate_Offset (word 112)) *)
  0xca0f0300;       (* arm_EOR X0 X24 X15 *)
  0x8a0b0000;       (* arm_AND X0 X0 X11 *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0x93c3ec83;       (* arm_EXTR X3 X4 X3 59 *)
  0xf90013e3;       (* arm_STR X3 SP (Immediate_Offset (word 32)) *)
  0x93c4ec44;       (* arm_EXTR X4 X2 X4 59 *)
  0xf90017e4;       (* arm_STR X4 SP (Immediate_Offset (word 40)) *)
  0x937bfc42;       (* arm_ASR X2 X2 59 *)
  0xf9001be2;       (* arm_STR X2 SP (Immediate_Offset (word 48)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0xca1002e4;       (* arm_EOR X4 X23 X16 *)
  0x8a0c0084;       (* arm_AND X4 X4 X12 *)
  0xcb0403e4;       (* arm_NEG X4 X4 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0xca110300;       (* arm_EOR X0 X24 X17 *)
  0x8a0d0000;       (* arm_AND X0 X0 X13 *)
  0xcb000084;       (* arm_SUB X4 X4 X0 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0x93c6eca6;       (* arm_EXTR X6 X5 X6 59 *)
  0xf90033e6;       (* arm_STR X6 SP (Immediate_Offset (word 96)) *)
  0x93c5ec85;       (* arm_EXTR X5 X4 X5 59 *)
  0xf90037e5;       (* arm_STR X5 SP (Immediate_Offset (word 104)) *)
  0x937bfc84;       (* arm_ASR X4 X4 59 *)
  0xf9003be4;       (* arm_STR X4 SP (Immediate_Offset (word 112)) *)
  0xf94043e7;       (* arm_LDR X7 SP (Immediate_Offset (word 128)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94063e8;       (* arm_LDR X8 SP (Immediate_Offset (word 192)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90043e4;       (* arm_STR X4 SP (Immediate_Offset (word 128)) *)
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
  0xf90063e5;       (* arm_STR X5 SP (Immediate_Offset (word 192)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94047e7;       (* arm_LDR X7 SP (Immediate_Offset (word 136)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94067e8;       (* arm_LDR X8 SP (Immediate_Offset (word 200)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90047e2;       (* arm_STR X2 SP (Immediate_Offset (word 136)) *)
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
  0xf90067e3;       (* arm_STR X3 SP (Immediate_Offset (word 200)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf9404be7;       (* arm_LDR X7 SP (Immediate_Offset (word 144)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9406be8;       (* arm_LDR X8 SP (Immediate_Offset (word 208)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf9004be6;       (* arm_STR X6 SP (Immediate_Offset (word 144)) *)
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
  0xf9006be4;       (* arm_STR X4 SP (Immediate_Offset (word 208)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf9404fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 152)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xf9406fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 216)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0xf9004fe5;       (* arm_STR X5 SP (Immediate_Offset (word 152)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf9006fe2;       (* arm_STR X2 SP (Immediate_Offset (word 216)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xf94053e7;       (* arm_LDR X7 SP (Immediate_Offset (word 160)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xf94073e8;       (* arm_LDR X8 SP (Immediate_Offset (word 224)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xf90053e3;       (* arm_STR X3 SP (Immediate_Offset (word 160)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf90073e6;       (* arm_STR X6 SP (Immediate_Offset (word 224)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xf94057e7;       (* arm_LDR X7 SP (Immediate_Offset (word 168)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c2;       (* arm_AND X2 X14 X10 *)
  0xcb0203e2;       (* arm_NEG X2 X2 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94077e8;       (* arm_LDR X8 SP (Immediate_Offset (word 232)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90057e4;       (* arm_STR X4 SP (Immediate_Offset (word 168)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf9005be2;       (* arm_STR X2 SP (Immediate_Offset (word 176)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x8a0c0204;       (* arm_AND X4 X16 X12 *)
  0xcb0403e4;       (* arm_NEG X4 X4 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x8a0d0220;       (* arm_AND X0 X17 X13 *)
  0xcb000084;       (* arm_SUB X4 X4 X0 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0xf90077e5;       (* arm_STR X5 SP (Immediate_Offset (word 232)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf9007be4;       (* arm_STR X4 SP (Immediate_Offset (word 240)) *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa9490fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0xa94a17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&160))) *)
  0xf9405be6;       (* arm_LDR X6 SP (Immediate_Offset (word 176)) *)
  0xd2fc0007;       (* arm_MOVZ X7 (word 57344) 48 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0xb24073e8;       (* arm_MOV X8 (rvalue (word 536870911)) *)
  0xba080021;       (* arm_ADCS X1 X1 X8 *)
  0xb2638be9;       (* arm_MOV X9 (rvalue (word 18446744073172680704)) *)
  0x9242f929;       (* arm_AND X9 X9 (rvalue (word 16140901064495857663)) *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x92fc0007;       (* arm_MOVN X7 (word 57344) 48 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0x8b008000;       (* arm_ADD X0 X0 (Shiftedreg X0 LSL 32) *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bc07ce7;       (* arm_UMULH X7 X7 X0 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0x9b007d09;       (* arm_MUL X9 X8 X0 *)
  0x9bc07d08;       (* arm_UMULH X8 X8 X0 *)
  0xab0900e7;       (* arm_ADDS X7 X7 X9 *)
  0xba000108;       (* arm_ADCS X8 X8 X0 *)
  0x9a9f37e9;       (* arm_CSET X9 Condition_CS *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0xeb070021;       (* arm_SUBS X1 X1 X7 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa090063;       (* arm_SBCS X3 X3 X9 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f0000;       (* arm_SBCS X0 X0 XZR *)
  0xcb0003e0;       (* arm_NEG X0 X0 *)
  0x92407c07;       (* arm_AND X7 X0 (rvalue (word 4294967295)) *)
  0x92607c08;       (* arm_AND X8 X0 (rvalue (word 18446744069414584320)) *)
  0x927ff809;       (* arm_AND X9 X0 (rvalue (word 18446744073709551614)) *)
  0xeb070021;       (* arm_SUBS X1 X1 X7 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa090063;       (* arm_SBCS X3 X3 X9 *)
  0xfa000084;       (* arm_SBCS X4 X4 X0 *)
  0xfa0000a5;       (* arm_SBCS X5 X5 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xa9080be1;       (* arm_STP X1 X2 SP (Immediate_Offset (iword (&128))) *)
  0xa90913e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0xa90a1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa94c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xa94d0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&208))) *)
  0xa94e17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&224))) *)
  0xf9407be6;       (* arm_LDR X6 SP (Immediate_Offset (word 240)) *)
  0xd2fc0007;       (* arm_MOVZ X7 (word 57344) 48 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0xb24073e8;       (* arm_MOV X8 (rvalue (word 536870911)) *)
  0xba080021;       (* arm_ADCS X1 X1 X8 *)
  0xb2638be9;       (* arm_MOV X9 (rvalue (word 18446744073172680704)) *)
  0x9242f929;       (* arm_AND X9 X9 (rvalue (word 16140901064495857663)) *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0x92fc0007;       (* arm_MOVN X7 (word 57344) 48 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0x8b008000;       (* arm_ADD X0 X0 (Shiftedreg X0 LSL 32) *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bc07ce7;       (* arm_UMULH X7 X7 X0 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0x9b007d09;       (* arm_MUL X9 X8 X0 *)
  0x9bc07d08;       (* arm_UMULH X8 X8 X0 *)
  0xab0900e7;       (* arm_ADDS X7 X7 X9 *)
  0xba000108;       (* arm_ADCS X8 X8 X0 *)
  0x9a9f37e9;       (* arm_CSET X9 Condition_CS *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0xeb070021;       (* arm_SUBS X1 X1 X7 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa090063;       (* arm_SBCS X3 X3 X9 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f0000;       (* arm_SBCS X0 X0 XZR *)
  0xcb0003e0;       (* arm_NEG X0 X0 *)
  0x92407c07;       (* arm_AND X7 X0 (rvalue (word 4294967295)) *)
  0x92607c08;       (* arm_AND X8 X0 (rvalue (word 18446744069414584320)) *)
  0x927ff809;       (* arm_AND X9 X0 (rvalue (word 18446744073709551614)) *)
  0xeb070021;       (* arm_SUBS X1 X1 X7 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa090063;       (* arm_SBCS X3 X3 X9 *)
  0xfa000084;       (* arm_SBCS X4 X4 X0 *)
  0xfa0000a5;       (* arm_SBCS X5 X5 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xa90c0be1;       (* arm_STP X1 X2 SP (Immediate_Offset (iword (&192))) *)
  0xa90d13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&208))) *)
  0xa90e1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&224))) *)
  0xaa1603e1;       (* arm_MOV X1 X22 *)
  0xf94003e2;       (* arm_LDR X2 SP (Immediate_Offset (word 0)) *)
  0xf94023e3;       (* arm_LDR X3 SP (Immediate_Offset (word 64)) *)
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
  0x54ff7cc1;       (* arm_BNE (word 2092952) *)
  0xf94003e0;       (* arm_LDR X0 SP (Immediate_Offset (word 0)) *)
  0xf94023e1;       (* arm_LDR X1 SP (Immediate_Offset (word 64)) *)
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
  0xf94043e7;       (* arm_LDR X7 SP (Immediate_Offset (word 128)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94063e8;       (* arm_LDR X8 SP (Immediate_Offset (word 192)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90043e4;       (* arm_STR X4 SP (Immediate_Offset (word 128)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94047e7;       (* arm_LDR X7 SP (Immediate_Offset (word 136)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94067e8;       (* arm_LDR X8 SP (Immediate_Offset (word 200)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90047e2;       (* arm_STR X2 SP (Immediate_Offset (word 136)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xf9404be7;       (* arm_LDR X7 SP (Immediate_Offset (word 144)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9406be8;       (* arm_LDR X8 SP (Immediate_Offset (word 208)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf9004be6;       (* arm_STR X6 SP (Immediate_Offset (word 144)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xf9404fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 152)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xf9406fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 216)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0xf9004fe5;       (* arm_STR X5 SP (Immediate_Offset (word 152)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94053e7;       (* arm_LDR X7 SP (Immediate_Offset (word 160)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xf94073e8;       (* arm_LDR X8 SP (Immediate_Offset (word 224)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xf90053e3;       (* arm_STR X3 SP (Immediate_Offset (word 160)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf94057e7;       (* arm_LDR X7 SP (Immediate_Offset (word 168)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c2;       (* arm_AND X2 X14 X10 *)
  0xcb0203e2;       (* arm_NEG X2 X2 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94077e8;       (* arm_LDR X8 SP (Immediate_Offset (word 232)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90057e4;       (* arm_STR X4 SP (Immediate_Offset (word 168)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf9005be2;       (* arm_STR X2 SP (Immediate_Offset (word 176)) *)
  0xa94803ea;       (* arm_LDP X10 X0 SP (Immediate_Offset (iword (&128))) *)
  0xa9490be1;       (* arm_LDP X1 X2 SP (Immediate_Offset (iword (&144))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xf9405be5;       (* arm_LDR X5 SP (Immediate_Offset (word 176)) *)
  0xd2fc0007;       (* arm_MOVZ X7 (word 57344) 48 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xb24073e8;       (* arm_MOV X8 (rvalue (word 536870911)) *)
  0xba080000;       (* arm_ADCS X0 X0 X8 *)
  0xb2638be9;       (* arm_MOV X9 (rvalue (word 18446744073172680704)) *)
  0x9242f929;       (* arm_AND X9 X9 (rvalue (word 16140901064495857663)) *)
  0xba090021;       (* arm_ADCS X1 X1 X9 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0x92fc0007;       (* arm_MOVN X7 (word 57344) 48 *)
  0x9a0700a5;       (* arm_ADC X5 X5 X7 *)
  0x8b0a814a;       (* arm_ADD X10 X10 (Shiftedreg X10 LSL 32) *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bca7ce7;       (* arm_UMULH X7 X7 X10 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0x9b0a7d09;       (* arm_MUL X9 X8 X10 *)
  0x9bca7d08;       (* arm_UMULH X8 X8 X10 *)
  0xab0900e7;       (* arm_ADDS X7 X7 X9 *)
  0xba0a0108;       (* arm_ADCS X8 X8 X10 *)
  0x9a9f37e9;       (* arm_CSET X9 Condition_CS *)
  0xab0a00a5;       (* arm_ADDS X5 X5 X10 *)
  0x9a9f37ea;       (* arm_CSET X10 Condition_CS *)
  0xeb070000;       (* arm_SUBS X0 X0 X7 *)
  0xfa080021;       (* arm_SBCS X1 X1 X8 *)
  0xfa090042;       (* arm_SBCS X2 X2 X9 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x92407d47;       (* arm_AND X7 X10 (rvalue (word 4294967295)) *)
  0x92607d48;       (* arm_AND X8 X10 (rvalue (word 18446744069414584320)) *)
  0x927ff949;       (* arm_AND X9 X10 (rvalue (word 18446744073709551614)) *)
  0xeb070000;       (* arm_SUBS X0 X0 X7 *)
  0xfa080021;       (* arm_SBCS X1 X1 X8 *)
  0xfa090042;       (* arm_SBCS X2 X2 X9 *)
  0xfa0a0063;       (* arm_SBCS X3 X3 X10 *)
  0xfa0a0084;       (* arm_SBCS X4 X4 X10 *)
  0xda0a00a5;       (* arm_SBC X5 X5 X10 *)
  0xb2407fea;       (* arm_MOV X10 (rvalue (word 4294967295)) *)
  0xeb0a000a;       (* arm_SUBS X10 X0 X10 *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0xfa0b002b;       (* arm_SBCS X11 X1 X11 *)
  0x9280002c;       (* arm_MOVN X12 (word 1) 0 *)
  0xfa0c004c;       (* arm_SBCS X12 X2 X12 *)
  0x9280000f;       (* arm_MOVN X15 (word 0) 0 *)
  0xfa0f006d;       (* arm_SBCS X13 X3 X15 *)
  0xfa0f008e;       (* arm_SBCS X14 X4 X15 *)
  0xfa0f00af;       (* arm_SBCS X15 X5 X15 *)
  0x9a8a3000;       (* arm_CSEL X0 X0 X10 Condition_CC *)
  0x9a8b3021;       (* arm_CSEL X1 X1 X11 Condition_CC *)
  0x9a8c3042;       (* arm_CSEL X2 X2 X12 Condition_CC *)
  0x9a8d3063;       (* arm_CSEL X3 X3 X13 Condition_CC *)
  0x9a8e3084;       (* arm_CSEL X4 X4 X14 Condition_CC *)
  0x9a8f30a5;       (* arm_CSEL X5 X5 X15 Condition_CC *)
  0xa9000680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&0))) *)
  0xa9010e82;       (* arm_STP X2 X3 X20 (Immediate_Offset (iword (&16))) *)
  0xa9021684;       (* arm_STP X4 X5 X20 (Immediate_Offset (iword (&32))) *)
  0x910403ff;       (* arm_ADD SP SP (rvalue (word 256)) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTINV_P384_EXEC = ARM_MK_EXEC_RULE bignum_montinv_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Do the main proof for the core that is sometimes inlined elsewhere        *)
(* ------------------------------------------------------------------------- *)

let CORE_INV_P384_EXEC =
    ARM_MK_EXEC_RULE
     ((GEN_REWRITE_CONV RAND_CONV [bignum_montinv_p384_mc] THENC TRIM_LIST_CONV)
      `TRIM_LIST (16,20) bignum_montinv_p384_mc`);;

(* ------------------------------------------------------------------------- *)
(* A localized form of the word_divstep59 proof, almost identical            *)
(* except for the context and the lack of store back to memory.              *)
(* ------------------------------------------------------------------------- *)

let BIT_1_WORD_ISHR = prove
 (`!x:int64. bit 1 x = bit 0 (word_ishr x 1)`,
  CONV_TAC WORD_BLAST);;

let VAL_WORD_AND_2_ISHR = prove
 (`!x:int64. val(word_and x (word 2)) = 0 <=> ~bit 0 (word_ishr x 1)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `2 = 2 EXP 1`] THEN
  REWRITE_TAC[VAL_WORD_AND_POW2; GSYM BIT_1_WORD_ISHR] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let lemma1,lemma2 = (CONJ_PAIR o prove)
 (`(--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 43
    ==> word_ishr (iword(&2 pow 43 * h + l):int64) 43 = iword h) /\
   (--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 42
    ==> word_ishr (iword(&2 pow 42 * h + l):int64) 42 = iword h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `l:int` THEN ASM_REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_MUL_SYM] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

let divstep_fvec = define
 `divstep_fvec n (d,f,g) =
    divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$2`;;

let divstep_gvec = define
 `divstep_gvec n (d,f,g) =
    divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$2`;;

let divstep_dvec = define
 `divstep_dvec n (d,f,g) =
  divstep_d n (d,f rem &2 pow 20,g rem &2 pow 20)`;;

let DIVSTEP_DVEC_BOUND = prove
 (`!n d f g. abs(divstep_dvec n (d,f,g)) <= abs(d) + &2 * &n`,
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_D; GSYM INT_OF_NUM_SUC] THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_FVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_fvec n (d,f,g) rem &2 =
            divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_fvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_GVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_gvec n (d,f,g) rem &2 =
            divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_gvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_DVEC = prove
 (`(!d f g. divstep_dvec 0 (d,f,g) = d) /\
   (!n t. n <= 20
          ==> divstep_dvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then &2 - divstep_dvec n t else &2 + divstep_dvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_dvec; DIVSTEP_D] THEN
  SIMP_TAC[DIVSTEP_GVEC_PARITY]);;

let DIVSTEP_FVEC = prove
 (`(!d f g. divstep_fvec 0 (d,f,g) = f rem &2 pow 20 - &2 pow 41) /\
   (!n t. n <= 20
          ==> divstep_fvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then divstep_gvec n t else divstep_fvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_fvec; DIVSTEP_F; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[divstep_dvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = (41 - SUC n) + 1`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = (62 - SUC n) + 1`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_GVEC = prove
 (`(!d f g. divstep_gvec 0 (d,f,g) = g rem &2 pow 20 - &2 pow 62) /\
   (!n t. n <= 20
          ==> divstep_gvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then (divstep_gvec n t - divstep_fvec n t) div &2
              else (divstep_gvec n t +
                    divstep_gvec n t rem &2 * divstep_fvec n t) div &2)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_gvec; DIVSTEP_G; divstep_mat] THEN
  REWRITE_TAC[GSYM divstep_gvec] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[divstep_dvec; divstep_fvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = 1 + (41 - SUC n)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = 1 + (62 - SUC n)`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) - (x' - &2 * y' - &2 * z'):int =
    (x - x') + &2 * ((y' + z') - (y + z))`] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) + b * (x' - &2 * y' - &2 * z'):int =
    (x + b * x') + &2 * --(b * (y' + z') + (y + z))`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_OF_NUM_EQ; ARITH_EQ] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_FGVEC_PACK = prove
 (`!d f g. word_or (word_and (iword f) (word 1048575))
                   (word 18446741874686296064):int64 =
           iword(divstep_fvec 0 (d,f,g)) /\
           word_or (word_and (iword g) (word 1048575))
                   (word 13835058055282163712):int64 =
           iword(divstep_gvec 0 (d,f,g))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC;
              DIVSTEP_F; DIVSTEP_G; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  W(MP_TAC o PART_MATCH (rand o rand) WORD_ADD_OR o lhand o snd) THEN
  (ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  REWRITE_TAC[INT_SUB] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[IWORD_INT_ADD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; GSYM(NUM_REDUCE_CONV `2 EXP 20 - 1`)] THEN
  REWRITE_TAC[WORD_IWORD; IWORD_EQ; GSYM INT_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC INT_EQ_IMP_CONG THEN REWRITE_TAC[INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN REWRITE_TAC[VAL_IWORD_CONG] THEN
  REWRITE_TAC[DIMINDEX_64; GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV);;

let IVAL_IWORD_DVEC = prove
 (`!n d f g.
        abs(d) < &2 pow 63 - &2 * &n
        ==> ival(iword(divstep_dvec n (d,f,g)):int64) =
            divstep_dvec n (d,f,g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`n:num`; `d:int`; `f:int`; `g:int`] DIVSTEP_DVEC_BOUND) THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_FVEC_BOUNDS,DIVSTEP_GVEC_BOUNDS = (CONJ_PAIR o prove)
 (`(!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_fvec n (d,f,g) /\
            divstep_fvec n (d,f,g) < &2 pow 62) /\
   (!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_gvec n (d,f,g) /\
            divstep_gvec n (d,f,g) < &2 pow 62)`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN INDUCT_TAC THENL
   [REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC; ARITH] THEN
    MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    INT_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o MATCH_MP
     (ARITH_RULE `SUC n <= 20 ==> n <= 20`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_SIMP_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC] THEN STRIP_TAC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ;  INT_ARITH `(&0:int) < &2`] THEN
  DISJ_CASES_THEN SUBST1_TAC
   (SPEC `divstep_gvec n (d,f,g)` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

let PACKED_DIVSTEP_TAC n shf s =
  let s' = if mem n shf then s+7 else s+8 in
  ARM_STEPS_TAC CORE_INV_P384_EXEC (s--s') THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral(n-1),`n:num`;
           mk_var("s"^string_of_int s',`:armstate`),`s:armstate`]
     `read X1 s = iword(divstep_dvec (SUC n) (d,f,g)) /\
      read X4 s = iword(divstep_fvec (SUC n) (d,f,g)) /\
      read X5 s = iword(divstep_gvec (SUC n) (d,f,g))`)
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB_0; WORD_AND_1_BITVAL] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
    REWRITE_TAC[TAUT `(if p then x else T) <=> p ==> x`] THEN
    REWRITE_TAC[TAUT `(if p then x else F) <=> p /\ x`] THEN
    REWRITE_TAC[INT_SUB_RZERO] THEN
    SIMP_TAC(ARITH::map CONJUNCT2
     [DIVSTEP_DVEC; DIVSTEP_FVEC; DIVSTEP_GVEC]) THEN
    REWRITE_TAC[TAUT `p ==> q <=> ~(~q /\ p)`] THEN
    REWRITE_TAC[COND_SWAP; INT_ARITH `~(x:int < &0) <=> x >= &0`] THEN
    REWRITE_TAC[BIT_LSB_IWORD] THEN
    MP_TAC(ISPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
      IVAL_IWORD_DVEC) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THENL
     [ALL_TAC;
      DISJ_CASES_THEN SUBST1_TAC
       (SPEC(subst [mk_small_numeral(n - 1),`n:num`] `divstep_gvec n (d,f,g)`)
          INT_REM_2_CASES) THEN
      CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID; INT_ADD_RID]] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[word_ishr] THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_ADD_0; INT_POW_1] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_RULE `word_add x (word_neg y) = word_sub x y`] THEN
    REWRITE_TAC[GSYM IWORD_INT_ADD; GSYM IWORD_INT_SUB] THEN
    MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_FVEC_BOUNDS) THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_GVEC_BOUNDS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read X5 s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read X4 s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read X1 s = x`) o concl)) THEN
    RULE_ASSUM_TAC(PURE_REWRITE_RULE [VAL_WORD_AND_2_ISHR]) THEN
    REPLICATE_TAC 3 (DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_SUC_CONV)) THEN
    DISCH_THEN(fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)];;

let RENAME_DFG_TAC d0 f0 g0 =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`f:int`,f0) THEN
  SPEC_TAC(`g:int`,g0) THEN
  SPEC_TAC(`d:int`,d0) THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read X1 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read X2 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read X3 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th));;

let DIVSTEP_MAT_UNPACK_20 = prove
 (`word_sxfrom 20
    (word_subword (word_add (iword(divstep_fvec 20 (d,f,g)):int64)
                            (word 1048576))
                  (21,21)):int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword (divstep_fvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_sxfrom 20
    (word_subword (word_add (iword(divstep_gvec 20 (d,f,g)):int64)
                            (word 1048576))
                  (21,21)):int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword (divstep_gvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  MP_TAC(GENL [`x:int64`; `pos:num`]
   (ISPECL [`x:int64`; `pos:num`; `21`] WORD_SXFROM_SUBWORD_AS_ISHR_SHL)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> SIMP_TAC[th; ARITH]) THEN
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 22 * (l - &2 pow 21 * m - &2 pow 42 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 22 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 21 * m - &2 pow 42 * h + z:int =
    &2 pow 42 * --h + &2 pow 21 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC lemma1 ORELSE MATCH_MP_TAC lemma2) THEN
  MP_TAC(SPECL [`20`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let DIVSTEP_MAT_UNPACK_19 = prove
 (`word_sxfrom 20
    (word_subword (word_add (iword(divstep_fvec 19 (d,f,g)):int64)
                            (word 1048576))
                  (22,21)):int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword(divstep_fvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_sxfrom 20
    (word_subword (word_add (iword(divstep_gvec 19 (d,f,g)):int64)
                            (word 1048576))
                  (22,21)):int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword(divstep_gvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  MP_TAC(GENL [`x:int64`; `pos:num`]
   (ISPECL [`x:int64`; `pos:num`; `21`] WORD_SXFROM_SUBWORD_AS_ISHR_SHL)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> SIMP_TAC[th; ARITH]) THEN
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 21 * (l - &2 pow 22 * m - &2 pow 43 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 21 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 22 * m - &2 pow 43 * h + z:int =
    &2 pow 43 * --h + &2 pow 22 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC lemma1 THEN
  MP_TAC(SPECL [`19`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let LOCAL_WORD_DIVSTEP59_CORRECT = prove
 (`!d f g pc.
       ensures arm
        (\s. aligned_bytes_loaded s (word pc)
                 (TRIM_LIST (16,20) bignum_montinv_p384_mc) /\
             read PC s = word(pc + 0x794) /\
             read X1 s = d /\
             read X2 s = f /\
             read X3 s = g)
        (\s. read PC s = word(pc + 0x1108) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62 ==>
              read X1 s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read X10 s = iword(M$1$1) /\
              read X11 s = iword(M$1$2) /\
              read X12 s = iword(M$2$1) /\
              read X13 s = iword(M$2$2)))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY
    (fun t -> GEN_REWRITE_TAC I [FORALL_IVAL_GEN] THEN
              X_GEN_TAC t THEN STRIP_TAC)
    [`d:int`; `f:int`; `g:int`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`]) THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[SOME_FLAGS] THEN

  (*** Globalize the odd(d), odd(f) and |d| < 2^62 assumption ***)

  ASM_CASES_TAC `d rem &2 = &1 /\ f rem &2 = &1 /\ abs(d:int) < &2 pow 62` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    ARM_QUICKSIM_TAC CORE_INV_P384_EXEC [`read X0 s = x`] (1--605)] THEN

  (*** The first packing ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC CORE_INV_P384_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first block of 20 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (9*n-3)) (1--20) THEN

  (*** The unpacking of the first block ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (185--194) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of first update matrix to f and g ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (195--202) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word(0 + val(iword(--x):int64) * val(iword g:int64)):int64 =
    iword(--(x * g))`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr; GSYM IWORD_INT_ADD]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &40`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d0:int` `f0:int` `g0:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN
   `(divstep_f 20 (d0,f0,g0) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d0,f0,g0) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d0:int`; `f0:int`; `g0:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    REWRITE_TAC[GSYM INT_NEG_ADD] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d0,f0,g0) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The second packing ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (203--207) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The second block of 20 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (9*n+199)) (1--20) THEN

  (*** The unpacking of the second block ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (387--396) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of second update matrix to f and g ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (397--404) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word(0 + val(iword(--x):int64) * val(iword g:int64)):int64 =
    iword(--(x * g))`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr; GSYM IWORD_INT_ADD]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &80`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62 + &40` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d1:int` `f1:int` `g1:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN
   `(divstep_f 20 (d1,f1,g1) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d1,f1,g1) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d1:int`; `f1:int`; `g1:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    REWRITE_TAC[GSYM INT_NEG_ADD] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d1,f1,g1) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The third and final packing ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (405--409) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first 10 of the third block of 19 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (9*n+401)) (1--10) THEN

  (*** The interspersed matrix multiplication ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (500--507) THEN

  (*** The final 9 of the third block of 19 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (9*n+409)) (11--19) THEN

  (*** The final unpacking is a little different as it's 19 not 20 ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (588--597) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_19]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** The final matrix multiplication and writeback ***)

  ARM_STEPS_TAC CORE_INV_P384_EXEC (598--605) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s605" THEN

  (*** The ending mathematics ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[IWORD_IVAL; IWORD_INT_SUB; IWORD_INT_NEG; IWORD_INT_ADD;
           IWORD_INT_MUL; WORD_ADD; WORD_MUL; ADD_CLAUSES; WORD_VAL] THEN
  REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_MUL; GSYM IWORD_INT_ADD;
              GSYM IWORD_INT_SUB; GSYM IWORD_INT_NEG] THEN
  SUBGOAL_THEN
   `divstep_d 59 (d0,f0,g0) = divstep_d 19 (d,f,g) /\
    divstep_mat 59 (d0,f0,g0) =
    imat_mul (divstep_mat 19 (d,f,g))
             (imat_mul (divstep_mat 20 (d1,f1,g1))
                       (divstep_mat 20 (d0,f0,g0)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[ARITH_RULE `59 = 19 + 40`; DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD];
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[imat_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; ISUM_2] THEN
    INT_ARITH_TAC] THEN
  SUBGOAL_THEN
   `divstep_d 40 (d0,f0,g0) = d /\
    (divstep_f 40 (d0,f0,g0) == f) (mod (&2 pow 19)) /\
    (divstep_g 40 (d0,f0,g0) == g) (mod (&2 pow 19)) /\
    divstep_mat 40 (d0,f0,g0) =
    imat_mul (divstep_mat 20 (d1,f1,g1))
             (divstep_mat 20 (d0,f0,g0))`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `59 = 19 + 40`;
                    DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIVSTEP_D_CONGRUENCE;
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE] THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL
   [`40`; `d1:int`; `divstep_f 20 (d0,f0,g0)`; `divstep_g 20 (d0,f0,g0)`;
    `f1:int`; `g1:int`; `20`]
   DIVSTEP_CONGRUENCE_NEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[DIVSTEP_F_ODD]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `40 = 20 + 20`;
                  DIVSTEP_DFG_ADD; DIVSTEP_MAT_ADD] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> (y == z) (mod p) /\ q divides p
    ==> (x == z) (mod q)`)) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(--x:int == y) (mod p) <=> (x == --y) (mod p)`] THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> q divides p ==> (x == y) (mod q)`)) THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT]);;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let PRIME_P384 = time prove
 (`prime p_384`,
  REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "41"; "43"; "47";
   "59"; "61"; "67"; "73"; "79"; "97"; "131"; "139"; "157"; "181"; "211";
   "233"; "263"; "271"; "293"; "599"; "661"; "881"; "937"; "1033"; "1373";
   "1579"; "2213"; "3253"; "3517"; "6317"; "8389"; "21407"; "38557";
   "312289"; "336757"; "363557"; "568151"; "6051631"; "105957871";
   "246608641"; "513928823"; "532247449"; "2862218959"; "53448597593";
   "807145746439"; "44925942675193"; "1357291859799823621";
   "529709925838459440593"; "35581458644053887931343";
   "23964610537191310276190549303"; "862725979338887169942859774909";
   "20705423504133292078628634597817";
   "413244619895455989650825325680172591660047";
   "12397338596863679689524759770405177749801411";
   "19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097"]);;

let IWORD_CASES_ABS = prove
 (`!m. (if m < &0 then word_neg(iword m) else iword m) = iword(abs m)`,
  GEN_TAC THEN REWRITE_TAC[GSYM IWORD_INT_NEG] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ASM_INT_ARITH_TAC);;

let WORD_AND_ISHR_CASES = prove
 (`!x y:int64. word_and (word_ishr x 63) y =
               if ival x < &0 then y else word 0`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:int64` WORD_ISHR_MSB) THEN
  REWRITE_TAC[MSB_IVAL] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_AND_MASK]);;

let TWOS_COMPLEMENT_448 = prove
 (`(&(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6]) == x) (mod (&2 pow 448))
   ==> --(&2 pow 384) <= x /\ x:int < &2 pow 384
       ==> ?b. n6 = word_neg(word(bitval b)) /\
               x = &(bignum_of_wordlist[n0;n1;n2;n3;n4;n5]) -
                   &2 pow 384 * &(bitval b)`,
  REWRITE_TAC[ARITH_RULE `448 = 384 + 64`] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] TWOS_COMPLEMENT_GEN)) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(6,1)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `x:int < &0` THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM VAL_EQ]; CONV_TAC INT_ARITH] THEN
  ASM_REWRITE_TAC[VAL_WORD_MASK; DIMINDEX_64] THEN ARITH_TAC);;

let TWOS_COMPLEMENT_448_WEAK = prove
 (`(&(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6]) == x) (mod (&2 pow 448))
   ==> --(&2 pow 447) <= x /\ x:int < &2 pow 447
       ==> &(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6]) =
           x + &2 pow 448 * &(bitval(bit 63 n6))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] TWOS_COMPLEMENT)) THEN
  ASM_REWRITE_TAC[ARITH_EQ; NUM_REDUCE_CONV `448 - 1`] THEN
  ANTS_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
  SIMP_TAC[EXP; MULT_CLAUSES; INT_EQ_SUB_RADD]);;

let swlemma_alt = WORD_RULE
  `word_add x (word_shl x 32):int64 = word(4294967297 * val x)`;;

let mmlemma_alt = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &18446744069414584321 * &(val(word(4294967297 * val x):int64))
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let CORE_INV_P384_CORRECT = time prove
 (`!z x n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,256))
            [(word pc,0x13bc); (z,8 * 6); (x,8 * 6)] /\
        nonoverlapping (word pc,0x13bc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                   (TRIM_LIST (16,20) bignum_montinv_p384_mc) /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = word (pc + 0x13bc) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17;
                      X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,8 * 6);
                      memory :> bytes(stackpointer,256)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Abbreviate the starting tuple for divstep ***)

  ABBREV_TAC `t:int#int#int = (&1,&p_384,&n rem &p_384)` THEN

  (*** Set up the main loop invariant ***)

  ENSURES_WHILE_UP_TAC `14` `pc + 0x788` `pc + 0x788`
   `\i s.
      read SP s = stackpointer /\
      read X20 s = z /\
      read X21 s = word(15 - i) /\
      read X22 s = iword(divstep_d (59 * i) t) /\
      (&(read (memory :> bytes(stackpointer,8 * 7)) s) ==
       divstep_f (59 * i) t) (mod (&2 pow 448)) /\
      (&(read (memory :> bytes(word_add stackpointer (word 64),8 * 7)) s) ==
       divstep_g (59 * i) t) (mod (&2 pow 448)) /\
      (&2 pow (843 - 5 * i) * divstep_f (59 * i) t ==
       &n * &(read (memory :> bytes(word_add stackpointer (word 128),8 * 6)) s))
      (mod (&p_384)) /\
      (&2 pow (843 - 5 * i) * divstep_g (59 * i) t ==
       &n * &(read (memory :> bytes(word_add stackpointer (word 192),8 * 6)) s))
      (mod (&p_384)) /\
     (p_384 divides n
      ==> p_384 divides
          read(memory :> bytes(word_add stackpointer (word 128),8 * 6)) s)`
  THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    BIGNUM_TERMRANGE_TAC `6` `n:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN
    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [11;12;14;15;17;18] (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[DIVSTEP_D; DIVSTEP_F; DIVSTEP_G; GSYM WORD_IWORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s38" THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES; p_384;
                GSYM INT_REM_EQ] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[DIVIDES_0] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_REM_REM; INT_MUL_RID; GSYM p_384] THEN
    CONJ_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC; REWRITE_TAC[INT_MUL_SYM]] THEN
    REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
     [`64 * 6`; `if n < p_384 then &n else &n - &p_384:real`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      ALL_TAC;
      SIMP_TAC[GSYM NOT_LE; COND_SWAP; REAL_OF_NUM_SUB; GSYM COND_RAND] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
      MATCH_MP_TAC MOD_CASES THEN REWRITE_TAC[p_384] THEN ASM_ARITH_TAC] THEN
    SUBGOAL_THEN `carry_s18 <=> n < p_384` (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `384` THEN
      EXPAND_TAC "n" THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_384;
                  GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(BINOP_CONV(BINOP_CONV REAL_POLY_CONV)) THEN BOUNDER_TAC[];
      EXPAND_TAC "n" THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];

    (*** Main invariant proof ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `f:num` `read (memory :> bytes (stackpointer,8 * 7))` THEN
    GHOST_INTRO_TAC `g:num`
     `read (memory :> bytes (word_add stackpointer (word 64),8 * 7))` THEN
    GHOST_INTRO_TAC `u:num`
     `read (memory :> bytes (word_add stackpointer (word 128),8 * 6))` THEN
    GHOST_INTRO_TAC `v:num`
     `read (memory :> bytes (word_add stackpointer (word 192),8 * 6))` THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY (BIGNUM_TERMRANGE_TAC `7`) [`f:num`; `g:num`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "f_"
     `read (memory :> bytes(stackpointer,8 * 7)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "g_"
     `read (memory :> bytes(word_add stackpointer (word 64),8 * 7)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "u_"
     `read (memory :> bytes(word_add stackpointer (word 128),8 * 6)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "v_"
     `read (memory :> bytes(word_add stackpointer (word 192),8 * 6)) s0` THEN

    ARM_STEPS_TAC CORE_INV_P384_EXEC (1--3) THEN
    MP_TAC(SPECL
     [`iword (divstep_d (59 * i) t):int64`;
      `f_0:int64`; `g_0:int64`; `pc:num`]
     LOCAL_WORD_DIVSTEP59_CORRECT) THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    ARM_BIGSTEP_TAC CORE_INV_P384_EXEC "s4" THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN

    SUBGOAL_THEN `abs(divstep_d (59 * i) t) < &2 pow 62` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN W(MP_TAC o
       PART_MATCH (lhand o rand o lhand) DIVSTEP_D_BOUND o lhand o snd) THEN
      MATCH_MP_TAC(INT_ARITH
       `e:int < &59 * &14
        ==> abs(x - abs(&1)) <= &2 * e ==> x < &2 pow 62`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ival(iword(divstep_d (59 * i) t):int64) = divstep_d (59 * i) t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN

    ANTS_TAC THENL
     [EXPAND_TAC "t" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      TRANS_TAC EQ_TRANS `divstep_f (59 * i) t rem &2` THEN
      EXPAND_TAC "t" THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[INT_REM_EQ];
        MATCH_MP_TAC DIVSTEP_F_ODD THEN REWRITE_TAC[p_384] THEN
        CONV_TAC INT_REDUCE_CONV] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(z:int == y) (mod q)
        ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r)
                ==> (x == y) (mod p)`)) THEN
      EXISTS_TAC `(&2:int) pow 64` THEN REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
      CONJ_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
      REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
      REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      SIMP_TAC[VAL_BOUND_64; MOD_LT];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `divstep_d 59 (divstep_d (59 * i) t,ival(f_0:int64),ival(g_0:int64)) =
      divstep_d (59 * (i + 1)) t`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `59 * (i + 1) = 59 + 59 * i`] THEN
      REWRITE_TAC[DIVSTEP_DFG_ADD] THEN
      MATCH_MP_TAC DIVSTEP_D_CONGRUENCE THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(z:int == y) (mod q)
        ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r)
                ==> (x == y) (mod p)`)) THEN
      EXISTS_TAC `(&2:int) pow 64` THEN REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
      (CONJ_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC]) THEN
      MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
      REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
      REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
      SIMP_TAC[VAL_BOUND_64; MOD_LT];
      ALL_TAC] THEN

    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV let_CONV)) THEN
    MAP_EVERY ABBREV_TAC
     [`mm = divstep_mat 59
             (divstep_d (59 * i) t,ival(f_0:int64),ival(g_0:int64))`;
      `m00 = (mm:int^2^2)$1$1`;
      `m01 = (mm:int^2^2)$1$2`;
      `m10 = (mm:int^2^2)$2$1`;
      `m11 = (mm:int^2^2)$2$2`] THEN
    STRIP_TAC THEN

    (*** The trivial fact that we loop back ***)

    ARM_STEPS_TAC CORE_INV_P384_EXEC (5--7) THEN
    SUBGOAL_THEN
     `word_sub (word (15 - i)) (word 1):int64 = word(15 - (i + 1))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[ARITH_RULE `15 - (i + 1) = (15 - i) - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 14 ==> 1 <= 15 - i`];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word(15 - (i + 1)):int64) = 0)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL
     [VAL_INT64_TAC `15 - (i + 1)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i < 14` THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** Sign-magnitude breakdown of matrix entries ***)

    ARM_STEPS_TAC CORE_INV_P384_EXEC (8--19) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; COND_SWAP]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    SUBGOAL_THEN
     `abs(m00:int) <= &2 pow 59 /\
      abs(m01:int) <= &2 pow 59 /\
      abs(m10:int) <= &2 pow 59 /\
      abs(m11:int) <= &2 pow 59`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m00"; "m01"; "m10"; "m11"; "mm"] THEN
      SIMP_TAC[INT_ABS_BOUNDS; DIVSTEP_MAT_BOUNDS; INT_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ival(iword m00:int64) = m00 /\
      ival(iword m01:int64) = m01 /\
      ival(iword m10:int64) = m10 /\
      ival(iword m11:int64) = m11`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)
    THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[INT_ARITH
       `abs(m:int) <= &2 pow 59 ==> --(&2 pow 63) <= m /\ m < &2 pow 63`];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IWORD_CASES_ABS]) THEN
    SUBGOAL_THEN
     `val(iword(abs m00):int64) <= 2 EXP 59 /\
      val(iword(abs m01):int64) <= 2 EXP 59 /\
      val(iword(abs m10):int64) <= 2 EXP 59 /\
      val(iword(abs m11):int64) <= 2 EXP 59`
    (STRIP_ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THENL
     [REWRITE_TAC[iword] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC VAL_WORD_LE THEN
      SIMP_TAC[GSYM INT_OF_NUM_CLAUSES; INT_OF_NUM_OF_INT; INT_ABS_POS;
               INT_REM_POS_EQ] THEN
      REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC INT_REM_LE THEN
      ASM_REWRITE_TAC[INT_ABS_POS];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `abs(real_of_int m00) = &(val(iword(abs m00):int64)) /\
      abs(real_of_int m01) = &(val(iword(abs m01):int64)) /\
      abs(real_of_int m10) = &(val(iword(abs m10):int64)) /\
      abs(real_of_int m11) = &(val(iword(abs m11):int64))`
    STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN REPEAT CONJ_TAC THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_VAL_IWORD THEN
     REWRITE_TAC[INT_ABS_POS; DIMINDEX_64] THEN
     ASM_SIMP_TAC[INT_ARITH `x:int <= &2 pow 59 ==> x < &2 pow 64`];
     ALL_TAC] THEN

    (*** Starting offset, common to both accumulations ***)

    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC [22;25] (20--25) THEN

    (*** Accumulation of new f and g (then keep 2 accumulations above) ***)

    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [28;30;31;34;36;37;39;41;42;44;46;47;50;52;53;56;58;59;63;
     65;66;68;70;71;76;78;79;82;84;85;89;91;92;94;96;97;102;104;
     105;108;110;111;115;117;118;120;122;123;128;130;131;134;136;137;
     141;143;144;146;148;149;158;160;161;167;168;170;171;182;184;185;
     189;190;192;193] (26--199) THEN

    MAP_EVERY ABBREV_TAC
     [`fup = bignum_of_wordlist
        [sum_s36;sum_s58;sum_s84;sum_s110;sum_s136;sum_s170;sum_s171]`;
      `gup = bignum_of_wordlist
        [sum_s46;sum_s70;sum_s96;sum_s122;sum_s148;sum_s192;sum_s193]`] THEN
    SUBGOAL_THEN
     `(&fup:int ==
       m00 * divstep_f (59 * i) t + m01 * divstep_g (59 * i) t)
      (mod (&2 pow 448)) /\
      (&gup:int ==
       m10 * divstep_f (59 * i) t + m11 * divstep_g (59 * i) t)
      (mod (&2 pow 448))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MAP_EVERY
       (SUBST1_TAC o C SPEC
         (INT_ARITH `!m:int. m = if m < &0 then --(abs m) else abs m`))
       [`m00:int`; `m01:int`; `m10:int`; `m11:int`] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      REPLICATE_TAC 2 (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[WORD_AND_ISHR_CASES; WORD_SUB_LZERO; REAL_VAL_WORD_NOT;
                  VAL_WORD_0; DIMINDEX_64] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `(&f == divstep_f (59 * i) t) (mod (&2 pow 448))` THEN
      UNDISCH_TAC `(&g == divstep_g (59 * i) t) (mod (&2 pow 448))` THEN
      MAP_EVERY EXPAND_TAC ["f"; "g"; "t"] THEN
      (DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_448) THEN ANTS_TAC THENL
       [MATCH_MP_TAC DIVSTEP_G_BOUNDS THEN
        REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV THEN
        REWRITE_TAC[INT_OF_NUM_REM; INT_ARITH `--(&m):int <= &n`] THEN
        REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `gtop:bool`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))] THEN
       DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_448) THEN ANTS_TAC THENL
       [MATCH_MP_TAC DIVSTEP_F_BOUNDS THEN
        REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV THEN
        REWRITE_TAC[INT_OF_NUM_REM; INT_ARITH `--(&m):int <= &n`] THEN
        REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `ftop:bool`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST1_TAC))]) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["fup"; "gup"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK; WORD_NOT_MASK] THEN
      REWRITE_TAC[COND_SWAP] THEN
      MAP_EVERY ASM_CASES_TAC [`ftop:bool`; `gtop:bool`] THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN STRIP_TAC THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      ACCUMULATOR_ASSUM_LIST(fun ths ->
        ASSUM_LIST(fun cths ->
           let tts = filter (is_ratconst o rand o concl)
                            (GEN_DECARRY_RULE cths ths) in
           REWRITE_TAC tts)) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[BIT_WORD_NOT; COND_SWAP; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[REAL_VAL_WORD_NEG; DIMINDEX_64] THEN
      REPEAT(COND_CASES_TAC THEN
        ASM_REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; REAL_VAL_WORD_NEG;
                        BITVAL_CLAUSES; DIMINDEX_64]) THEN
      REAL_INTEGER_TAC;

      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        fst o chop_list 2 o rev) THEN
      STRIP_TAC] THEN

    (*** Accumulation of new u and v values before reduction ***)

    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [202;204;205;208;210;212;214;216;217;219;221;223;226;228;
      229;232;234;236;238;240;241;243;245;247;250;252;253;256;
      258;260;262;264;265;267;269;271;274;276;277;280;282;284;
      286;288;289;291;293;295;298;300;301;304;306;308;310;312;
      313;315;317;319;324;326;327;331;332;334;336;341;343;344;
      347;348;350;352]
     (200--353) THEN

    MAP_EVERY ABBREV_TAC
     [`uup = bignum_of_wordlist
        [sum_s210;sum_s234;sum_s258;sum_s282;sum_s306;sum_s334;sum_s336]`;
      `vup = bignum_of_wordlist
        [sum_s221;sum_s245;sum_s269;sum_s293;sum_s317;sum_s350;sum_s352]`] THEN

    SUBGOAL_THEN
     `(&uup:int == m00 * &u + m01 * &v) (mod (&2 pow 448)) /\
      (&vup:int == m10 * &u + m11 * &v) (mod (&2 pow 448))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MAP_EVERY
       (SUBST1_TAC o C SPEC
         (INT_ARITH `!m:int. m = if m < &0 then --(abs m) else abs m`))
       [`m00:int`; `m01:int`; `m10:int`; `m11:int`] THEN
      REPLICATE_TAC 2 (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[WORD_AND_ISHR_CASES; WORD_SUB_LZERO; REAL_VAL_WORD_NOT;
                  VAL_WORD_0; DIMINDEX_64] THEN
      STRIP_TAC THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["uup"; "vup"; "u"; "v"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      ACCUMULATOR_ASSUM_LIST(fun ths ->
        ASSUM_LIST(fun cths ->
           let tts = filter (is_ratconst o rand o concl)
                            (GEN_DECARRY_RULE cths ths) in
           REWRITE_TAC tts)) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH] THEN
      REWRITE_TAC[BIT_WORD_NOT; COND_SWAP; DIMINDEX_64; ARITH] THEN
      ASM_REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; REAL_VAL_WORD_NEG;
                      BITVAL_CLAUSES; DIMINDEX_64] THEN
      REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Bounds on the updated u and v integers ***)

    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN
     `abs(m00 * &u + m01 * &v:int) <= &2 pow 444 /\
      abs(m10 * &u + m11 * &v:int) <= &2 pow 444`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(INT_ARITH
       `abs(x) <= &2 pow 59 * &2 pow 384 /\
        abs(y) <= &2 pow 59 * &2 pow 384
        ==> abs(x + y:int) <= &2 pow 444`) THEN
      REWRITE_TAC[INT_ABS_MUL] THEN
      CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL2 THEN
      ASM_REWRITE_TAC[INT_ABS_NUM; INT_POS; INT_ABS_POS] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      MAP_EVERY EXPAND_TAC ["u"; "v"] THEN BOUNDER_TAC[];
      ALL_TAC] THEN

    (*** Biasing and Montgomery reduction of u ***)

    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [359;361;364;365;366;367;369] (354--369) THEN
    ABBREV_TAC
     `upos =
      bignum_of_wordlist
       [sum_s359;sum_s361;sum_s364;sum_s365;sum_s366;sum_s367;sum_s369]` THEN
    SUBGOAL_THEN
     `upos < 2 EXP 446 /\ (&upos:int == m00 * &u + m01 * &v) (mod (&p_384))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `&upos:int = (m00 * &u + m01 * &v) + &2 pow 61 * &p_384`
      SUBST1_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[INTEGER_RULE `(x + k * p:int == x) (mod p)`] THEN
        UNDISCH_TAC `abs(m00 * &u + m01 * &v):int <= &2 pow 444` THEN
        REWRITE_TAC[p_384] THEN INT_ARITH_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `upos < 2 EXP 448` MP_TAC THENL
         [EXPAND_TAC "upos" THEN BOUNDER_TAC[];
          UNDISCH_TAC `abs(m00 * &u + m01 * &v):int <= &2 pow 444`] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_384] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(uup:int == uexp) (mod p)
        ==> (upos == uup + c) (mod p)
            ==> (upos == uexp + c) (mod p)`)) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["upos"; "uup"] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; bignum_of_wordlist; p_384;
                  GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
    ARM_STEPS_TAC CORE_INV_P384_EXEC [370] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma_alt]) THEN
    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC [372;374;375] (371--375) THEN
    RULE_ASSUM_TAC(fun th ->
      try MATCH_MP mmlemma_alt th with Failure _ -> th) THEN
    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [376;377;379;381;382;383;384;385;386;387] (376--387) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC (392--397) (388--400) THEN
    SUBGOAL_THEN
     `(&2 pow 64 *
       &(bignum_of_wordlist
          [sum_s392; sum_s393; sum_s394; sum_s395; sum_s396; sum_s397]):int ==
       m00 * &u + m01 * &v) (mod &p_384)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          INT_CONG_TRANS)) THEN
      ABBREV_TAC `w:int64 = word(4294967297 * val(sum_s359:int64))` THEN
      MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC
       `if &upos + &(val(w:int64)) * &p_384:int < &2 pow 448
        then &upos + &(val w) * &p_384:int
        else (&upos + &(val w) * &p_384) - &2 pow 64 * &p_384` THEN
      CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN CONV_TAC INTEGER_RULE] THEN
      MATCH_MP_TAC INT_EQ_IMP_CONG THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
        MATCH_MP_TAC(INT_ARITH
         `&0:int <= x /\ x < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
        REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
         [EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN BOUNDER_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
          EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `2 EXP 64 * bignum_of_wordlist
         [sum_s381;sum_s382;sum_s383;sum_s384;sum_s385;sum_s386;sum_s387] =
        upos + val(w:int64) * p_384`
      ASSUME_TAC THENL
       [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 512` THEN
         REPLICATE_TAC 2 (CONJ_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC]) THEN
        REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
        EXPAND_TAC "upos" THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `val(sum_s387:int64) < 2` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
         `2 EXP 64 * x = y ==> y < 2 * 2 EXP 448 ==> x < 2 * 2 EXP 384`)) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
        REWRITE_TAC[NUM_AS_BITVAL_ALT; VAL_WORD_GALOIS]] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:bool` (SUBST_ALL_TAC o CONJUNCT2)) THEN
      SUBGOAL_THEN
       `&upos + &(val(w:int64)) * &p_384:int < &2 pow 448 <=> ~c`
      SUBST1_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[NOT_LT] THEN BOUNDER_TAC[];
        REWRITE_TAC[COND_SWAP]] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        rev o fst o chop_list 6) THEN
      REWRITE_TAC[WORD_SUB_LZERO; WORD_AND_MASK] THEN
      BOOL_CASES_TAC `c:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist; p_384] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN

    (*** Biasing and Montgomery reduction of v ***)

    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
     [406;408;411;412;413;414;416] (401--416) THEN
    ABBREV_TAC
     `vpos =
      bignum_of_wordlist
       [sum_s406;sum_s408;sum_s411;sum_s412;sum_s413;sum_s414;sum_s416]` THEN
    SUBGOAL_THEN
     `vpos < 2 EXP 446 /\ (&vpos:int == m10 * &u + m11 * &v) (mod (&p_384))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `&vpos:int = (m10 * &u + m11 * &v) + &2 pow 61 * &p_384`
      SUBST1_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[INTEGER_RULE `(x + k * p:int == x) (mod p)`] THEN
        UNDISCH_TAC `abs(m10 * &u + m11 * &v):int <= &2 pow 444` THEN
        REWRITE_TAC[p_384] THEN INT_ARITH_TAC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `vpos < 2 EXP 448` MP_TAC THENL
         [EXPAND_TAC "vpos" THEN BOUNDER_TAC[];
          UNDISCH_TAC `abs(m10 * &u + m11 * &v):int <= &2 pow 444`] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_384] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(vup:int == uexp) (mod p)
        ==> (vpos == vup + c) (mod p)
            ==> (vpos == uexp + c) (mod p)`)) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["vpos"; "vup"] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; bignum_of_wordlist; p_384;
                  GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
    ARM_STEPS_TAC CORE_INV_P384_EXEC [417] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swlemma_alt]) THEN
    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC [419;421;422] (418--422) THEN
    RULE_ASSUM_TAC(fun th ->
      try MATCH_MP mmlemma_alt th with Failure _ -> th) THEN
    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
      [423;424;426;428;429;430;431;432;433;434] (423--434) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
    ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC (439--444) (435--447) THEN
    SUBGOAL_THEN
     `(&2 pow 64 *
       &(bignum_of_wordlist
          [sum_s439; sum_s440; sum_s441; sum_s442; sum_s443; sum_s444]):int ==
       m10 * &u + m11 * &v) (mod &p_384)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          INT_CONG_TRANS)) THEN
      ABBREV_TAC `w:int64 = word(4294967297 * val(sum_s406:int64))` THEN
      MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC
       `if &vpos + &(val(w:int64)) * &p_384:int < &2 pow 448
        then &vpos + &(val w) * &p_384:int
        else (&vpos + &(val w) * &p_384) - &2 pow 64 * &p_384` THEN
      CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN CONV_TAC INTEGER_RULE] THEN
      MATCH_MP_TAC INT_EQ_IMP_CONG THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
        MATCH_MP_TAC(INT_ARITH
         `&0:int <= x /\ x < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
        REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
         [EXPAND_TAC "vpos" THEN REWRITE_TAC[p_384] THEN BOUNDER_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
          EXPAND_TAC "vpos" THEN REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `2 EXP 64 * bignum_of_wordlist
         [sum_s428;sum_s429;sum_s430;sum_s431;sum_s432;sum_s433;sum_s434] =
        vpos + val(w:int64) * p_384`
      ASSUME_TAC THENL
       [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 512` THEN
         REPLICATE_TAC 2 (CONJ_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC]) THEN
        REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
        EXPAND_TAC "vpos" THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `val(sum_s434:int64) < 2` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
         `2 EXP 64 * x = y ==> y < 2 * 2 EXP 448 ==> x < 2 * 2 EXP 384`)) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
        REWRITE_TAC[NUM_AS_BITVAL_ALT; VAL_WORD_GALOIS]] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:bool` (SUBST_ALL_TAC o CONJUNCT2)) THEN
      SUBGOAL_THEN
       `&vpos + &(val(w:int64)) * &p_384:int < &2 pow 448 <=> ~c`
      SUBST1_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[NOT_LT] THEN BOUNDER_TAC[];
        REWRITE_TAC[COND_SWAP]] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        rev o fst o chop_list 6) THEN
      REWRITE_TAC[WORD_SUB_LZERO; WORD_AND_MASK] THEN
      BOOL_CASES_TAC `c:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist; p_384] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN

    (*** Finish the simulation before proceeding ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s443" THEN

    (*** Stepping mathematics for divstep ***)

    REWRITE_TAC[ARITH_RULE `59 * (i + 1) = 59 + 59 * i`] THEN
    REWRITE_TAC[DIVSTEP_DFG_ADD] THEN

    MP_TAC(SPECL
     [`divstep_d (59 * i) t`; `divstep_f (59 * i) t`; `divstep_g (59 * i) t`;
      `59`] DIVSTEP_MAT) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_F_ODD THEN
      REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV;
      GEN_REWRITE_TAC LAND_CONV [CART_EQ]] THEN
    SIMP_TAC[DIMINDEX_2; FORALL_2; imat_vmul; VECTOR_2;
             ISUM_2; LAMBDA_BETA; ARITH] THEN

    MP_TAC(SPECL
     [`divstep_d (59 * i) t`; `divstep_f (59 * i) t`; `divstep_g (59 * i) t`;
      `ival(f_0:int64)`; `ival(g_0:int64)`; `59`]
     DIVSTEP_MAT_CONGRUENCE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
       `(x:int == d) (mod p)
        ==> q divides p /\ (x == x') (mod q) ==> (d == x') (mod q)`)) THEN
      SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
      MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
      ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `(f':int == f) (mod e) /\ p divides e
        ==> (f + e * x == f') (mod p)`) THEN
      SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; IVAL_VAL_CONG];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN

    (*** The two right-shifts are easy now ***)

    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP
       (MESON[INT_DIV_MUL; INT_POW_EQ_0; INT_REDUCE_CONV `&2:int = &0`]
         `&2 pow 59 * x = y ==> x = y div &2 pow 59`))) THEN
      MAP_EVERY UNDISCH_TAC
       [`(&fup:int ==
          m00 * divstep_f (59 * i) t + m01 * divstep_g (59 * i) t)
         (mod (&2 pow 448))`;
        `(&gup:int ==
          m10 * divstep_f (59 * i) t + m11 * divstep_g (59 * i) t)
         (mod (&2 pow 448))`] THEN
      MAP_EVERY EXPAND_TAC ["fup"; "gup"] THEN
      REPLICATE_TAC 2
       (DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_448_WEAK) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC(INT_ARITH
           `abs(a * x) <= &2 pow 59 * &2 pow 384 /\
            abs(b * y) <= &2 pow 59 * &2 pow 384
            ==> --(&2 pow 447):int <= a * x + b * y /\
                a * x + b * y < &2 pow 447`) THEN
          SUBGOAL_THEN
           `(--(&2 pow 384) <= divstep_f (59 * i) t /\
             divstep_f (59 * i) t < &2 pow 384) /\
            (--(&2 pow 384) <= divstep_g (59 * i) t /\
             divstep_g (59 * i) t < &2 pow 384)`
          STRIP_ASSUME_TAC THENL
           [EXPAND_TAC "t" THEN CONJ_TAC THENL
             [MATCH_MP_TAC DIVSTEP_F_BOUNDS;
              MATCH_MP_TAC DIVSTEP_G_BOUNDS] THEN
            REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV THEN
            REWRITE_TAC[INT_OF_NUM_REM; INT_ARITH `--(&m):int <= &n`] THEN
            REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC;
            REWRITE_TAC[INT_ABS_MUL] THEN CONJ_TAC THEN
            MATCH_MP_TAC INT_LE_MUL2 THEN
            ASM_REWRITE_TAC[INT_ABS_POS; INT_ABS_BOUNDS] THEN
            ASM_SIMP_TAC[INT_LT_IMP_LE]];
          DISCH_THEN(SUBST1_TAC o MATCH_MP (INT_ARITH
           `a:int = b + c ==> b = a - c`))]) THEN
      REWRITE_TAC[INT_ARITH
       `x - &2 pow 448 * b:int =
        x + &2 pow 59 * (&2 pow 389 * --b)`] THEN
      SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[INTEGER_RULE
       `(a:int == b + c * --d) (mod n) <=> (a + c * d == b) (mod n)`] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; GSYM num_congruent] THEN
      CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 59 * 2 EXP 5`] THEN
      SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; ARITH_EQ; EXP_EQ_0] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN
      CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN

    (*** Final stepping mathematics ***)

    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [num_divides] THEN
    REWRITE_TAC[GSYM INT_CONG_0_DIVIDES] THEN
    SUBGOAL_THEN
     `!x y:int. (x == y) (mod &p_384) <=>
                (&2 pow 64 * x == &2 pow 64 * y) (mod &p_384)`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
       `!e:int. coprime(e,p)
                ==> ((x == y) (mod p) <=> (e * x == e * y) (mod p))`) THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_coprime; COPRIME_LEXP] THEN
      REWRITE_TAC[COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:int. &2 pow 64 * &2 pow (843 - 5 * (i + 1)) * x =
              &2 pow (843 - 5 * i) * &2 pow 59 * x`
    (fun th -> REWRITE_TAC[th]) THENL
      [ASM_SIMP_TAC[INT_POW_ADD; ARITH_RULE
        `i < 14 ==> 843 - 5 * i = (843 - 5 * (i + 1)) + 5`] THEN
       INT_ARITH_TAC;
       ASM_REWRITE_TAC[INT_MUL_RZERO]] THEN
    ONCE_REWRITE_TAC[INT_ARITH
     `&2 pow 64 * x * y:int = x * &2 pow 64 * y`] THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(&2 pow 64 * x:int == &0) (mod p) <=>
      (&0 == &1 * &2 pow 64 * x) (mod p)`] THEN
    REPEAT(FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o
      MATCH_MP (INTEGER_RULE
        `(&2 pow 64 * x:int == y) (mod p)
         ==> !z. ((z == e * &2 pow 64 * x) (mod p) <=>
                 (z == e * y) (mod p))`))) THEN
    ASM_SIMP_TAC[INTEGER_RULE
     `(e * f:int == n * f') (mod p) /\ (e * g == n * g') (mod p)
      ==> (e * (a * f + b * g) == n * (a * f' + b * g')) (mod p)`] THEN
    DISCH_TAC THEN MATCH_MP_TAC(INTEGER_RULE
     `p divides u /\ b = &0
      ==> (&0:int == &1 * (a * u + b * v)) (mod p)`) THEN
    ASM_SIMP_TAC[GSYM num_divides] THEN
    SUBST1_TAC(SYM(ASSUME `(mm:int^2^2)$1$2 = m01`)) THEN EXPAND_TAC "mm" THEN
    MATCH_MP_TAC DIVSTEP_MAT_DIAGONAL_1 THEN
    SUBGOAL_THEN `g = 0` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_EQ];
      EXPAND_TAC "g" THEN
      SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL; IVAL_WORD_0]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[INT_CONG_IMP_EQ;INT_SUB_RZERO]
      `(x == y) (mod n) ==> y:int = &0 /\ abs(x) < n ==> x = &0`)) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_G_ZERO THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0; GSYM num_divides];
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "g" THEN BOUNDER_TAC[]];

    (*** Because of the peculiar loop structure, completely trivial ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ARM_SIM_TAC CORE_INV_P384_EXEC [] THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (*** Start on the tail computation, with similar divstep reasoning ***)

  CONV_TAC(DEPTH_CONV NUM_SUB_CONV) THEN
  REWRITE_TAC[ARITH_RULE `59 * 14 = 826`] THEN
  GHOST_INTRO_TAC `f:num` `read (memory :> bytes (stackpointer,8 * 7))` THEN
  GHOST_INTRO_TAC `g:num`
   `read (memory :> bytes (word_add stackpointer (word 64),8 * 7))` THEN
  GHOST_INTRO_TAC `u:num`
   `read (memory :> bytes (word_add stackpointer (word 128),8 * 6))` THEN
  GHOST_INTRO_TAC `v:num`
   `read (memory :> bytes (word_add stackpointer (word 192),8 * 6))` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `7`) [`f:num`; `g:num`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "f_"
   `read (memory :> bytes(stackpointer,8 * 7)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "g_"
   `read (memory :> bytes(word_add stackpointer (word 64),8 * 7)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "u_"
   `read (memory :> bytes(word_add stackpointer (word 128),8 * 6)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "v_"
   `read (memory :> bytes(word_add stackpointer (word 192),8 * 6)) s0` THEN
  ARM_STEPS_TAC CORE_INV_P384_EXEC (1--3) THEN
  MP_TAC(SPECL
   [`iword (divstep_d 826 t):int64`;
    `f_0:int64`; `g_0:int64`; `pc:num`]
   LOCAL_WORD_DIVSTEP59_CORRECT) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC CORE_INV_P384_EXEC "s4" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN

  SUBGOAL_THEN `abs(divstep_d 826 t) < &2 pow 62` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN W(MP_TAC o
     PART_MATCH (lhand o rand o lhand) DIVSTEP_D_BOUND o lhand o snd) THEN
    MATCH_MP_TAC(INT_ARITH
     `e:int < &827
      ==> abs(x - abs(&1)) <= &2 * e ==> x < &2 pow 62`) THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(iword(divstep_d 826 t):int64) = divstep_d 826 t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN

  ANTS_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    TRANS_TAC EQ_TRANS `divstep_f 826 t rem &2` THEN
    EXPAND_TAC "t" THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[INT_REM_EQ];
      MATCH_MP_TAC DIVSTEP_F_ODD THEN REWRITE_TAC[p_384] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(z:int == y) (mod q)
      ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r)
              ==> (x == y) (mod p)`)) THEN
    EXISTS_TAC `(&2:int) pow 64` THEN REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
    CONJ_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
    REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
    REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    SIMP_TAC[VAL_BOUND_64; MOD_LT];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `divstep_d 59 (divstep_d 826 t,ival(f_0:int64),ival(g_0:int64)) =
    divstep_d 885 t`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `885 = 59 + 826`] THEN
    REWRITE_TAC[DIVSTEP_DFG_ADD] THEN
    MATCH_MP_TAC DIVSTEP_D_CONGRUENCE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(z:int == y) (mod q)
      ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r)
              ==> (x == y) (mod p)`)) THEN
    EXISTS_TAC `(&2:int) pow 64` THEN REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
    (CONJ_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC]) THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
    REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
    REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    SIMP_TAC[VAL_BOUND_64; MOD_LT];
    ALL_TAC] THEN

  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV let_CONV)) THEN
  MAP_EVERY ABBREV_TAC
   [`mm = divstep_mat 59
           (divstep_d 826 t,ival(f_0:int64),ival(g_0:int64))`;
    `m00 = (mm:int^2^2)$1$1`;
    `m01 = (mm:int^2^2)$1$2`;
    `m10 = (mm:int^2^2)$2$1`;
    `m11 = (mm:int^2^2)$2$2`] THEN
  STRIP_TAC THEN

  (*** Complete all the simulation first ***)

  ARM_ACCSTEPS_TAC CORE_INV_P384_EXEC
   [31;34;36;37;40;42;44;47;49;50;53;55;57;60;62;63;66;68;
    70;73;75;76;79;81;83;86;88;89;92;94;96;101;103;104;108;109;111;
    113;120;122;125;126;127;128;130;133;135;137;138;140;142;143;
    144;145;146;147;148;153;154;155;156;157;158;160;162;164;166;167;168]
   (5--177) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s177" THEN

  (*** Deploy the divstep bound to deduce g = 0 ***)

  MP_TAC(SPECL [`&p_384:int`; `&n rem &p_384`; `384`; `885`]
        IDIVSTEP_ENDTOEND_BITS_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
    STRIP_TAC] THEN

  (*** Sign-magnitude breakdown of matrix entries ***)

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; COND_SWAP]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  SUBGOAL_THEN
   `abs(m00:int) <= &2 pow 59 /\
    abs(m01:int) <= &2 pow 59 /\
    abs(m10:int) <= &2 pow 59 /\
    abs(m11:int) <= &2 pow 59`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m00"; "m01"; "m10"; "m11"; "mm"] THEN
    SIMP_TAC[INT_ABS_BOUNDS; DIVSTEP_MAT_BOUNDS; INT_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(iword m00:int64) = m00 /\
    ival(iword m01:int64) = m01 /\
    ival(iword m10:int64) = m10 /\
    ival(iword m11:int64) = m11`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)
  THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_ARITH
     `abs(m:int) <= &2 pow 59 ==> --(&2 pow 63) <= m /\ m < &2 pow 63`];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IWORD_CASES_ABS]) THEN
  SUBGOAL_THEN
   `val(iword(abs m00):int64) <= 2 EXP 59 /\
    val(iword(abs m01):int64) <= 2 EXP 59 /\
    val(iword(abs m10):int64) <= 2 EXP 59 /\
    val(iword(abs m11):int64) <= 2 EXP 59`
  (STRIP_ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THENL
   [REWRITE_TAC[iword] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC VAL_WORD_LE THEN
    SIMP_TAC[GSYM INT_OF_NUM_CLAUSES; INT_OF_NUM_OF_INT; INT_ABS_POS;
             INT_REM_POS_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC INT_REM_LE THEN
    ASM_REWRITE_TAC[INT_ABS_POS];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `abs(real_of_int m00) = &(val(iword(abs m00):int64)) /\
    abs(real_of_int m01) = &(val(iword(abs m01):int64)) /\
    abs(real_of_int m10) = &(val(iword(abs m10):int64)) /\
    abs(real_of_int m11) = &(val(iword(abs m11):int64))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN REPEAT CONJ_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_VAL_IWORD THEN
    REWRITE_TAC[INT_ABS_POS; DIMINDEX_64] THEN
    ASM_SIMP_TAC[INT_ARITH `x:int <= &2 pow 59 ==> x < &2 pow 64`];
    ALL_TAC] THEN

  (*** Stepping mathematics for divstep ***)

  MP_TAC(SPECL
     [`divstep_d 826 t`; `divstep_f 826 t`; `divstep_g 826 t`;
      `59`] DIVSTEP_MAT) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_F_ODD THEN
    REWRITE_TAC[p_384] THEN CONV_TAC INT_REDUCE_CONV;
    GEN_REWRITE_TAC LAND_CONV [CART_EQ]] THEN
  SIMP_TAC[DIMINDEX_2; FORALL_2; imat_vmul; VECTOR_2;
           ISUM_2; LAMBDA_BETA; ARITH] THEN
  SUBGOAL_THEN
   `divstep_mat 59 (divstep_d 826 t,divstep_f 826 t,divstep_g 826 t) = mm`
  SUBST1_TAC THENL
   [EXPAND_TAC "mm" THEN
    MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(z:int == y) (mod q)
      ==> !r. (p divides q /\ p divides r) /\ (z == x) (mod r)
              ==> (y == x) (mod p)`)) THEN
    EXISTS_TAC `(&2:int) pow 64` THEN REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
    (CONJ_TAC THENL [CONV_TAC INT_REDUCE_CONV; ALL_TAC]) THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD] THEN
    REWRITE_TAC[GSYM DIMINDEX_64; GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG] THEN
    REWRITE_TAC[DIMINDEX_64; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    SIMP_TAC[VAL_BOUND_64; MOD_LT];
    ASM_REWRITE_TAC[GSYM DIVSTEP_DFG_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC] THEN

  (*** Final f sign in non-degenerate case ***)

  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  MP_TAC(GEN `x:int64` (ISPEC `x:int64` WORD_ISHR_MSB)) THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ABBREV_TAC
   `bsgn <=> bit 63 (word
     (val(word(val(f_0:int64) * val(iword m00:int64)):int64) +
      val(g_0:int64) * val(iword m01:int64)):int64)` THEN

  (*** Accumulation of pre-reduction u value ***)

  ABBREV_TAC
   `uup = bignum_of_wordlist
           [sum_s42;sum_s55;sum_s68;sum_s81;sum_s94;sum_s111;sum_s113]` THEN
  SUBGOAL_THEN
   `(&uup:int ==
     --(&1) pow bitval bsgn *
     (m00 * &u + m01 * &v)) (mod (&2 pow 448))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INT_POW_NEG; EVEN_BITVAL; COND_SWAP; INT_POW_ONE] THEN
    MAP_EVERY
     (SUBST1_TAC o C SPEC
       (INT_ARITH `!m:int. m = if m < &0 then --(abs m) else abs m`))
     [`m00:int`; `m01:int`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev o
        snd o chop_list 31) THEN
    REPLICATE_TAC 3 (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK; WORD_NOT_MASK] THEN
    REWRITE_TAC[WORD_AND_ISHR_CASES; WORD_SUB_LZERO; REAL_VAL_WORD_NOT;
      WORD_NEG_0; WORD_NEG_NEG; WORD_SUB_0; VAL_WORD_0; DIMINDEX_64] THEN
    STRIP_TAC THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
    MAP_EVERY EXPAND_TAC ["uup"; "u"; "v"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(fun ths ->
      ASSUM_LIST(fun cths ->
         let tts = filter (is_ratconst o rand o concl)
                          (GEN_DECARRY_RULE cths ths) in
         REWRITE_TAC tts)) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH] THEN
    REWRITE_TAC[BIT_WORD_NOT; COND_SWAP; DIMINDEX_64; ARITH] THEN
    ASM_REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; REAL_VAL_WORD_NEG;
                    BITVAL_CLAUSES; DIMINDEX_64] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev o
      fst o chop_list 31) THEN
    STRIP_TAC] THEN

  (*** Bound on the updated u value ***)

  ABBREV_TAC `fsgn:int = -- &1 pow bitval bsgn` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SUBGOAL_THEN `abs(fsgn * (m00 * &u + m01 * &v):int) <= &2 pow 444`
  ASSUME_TAC THENL
   [EXPAND_TAC "fsgn" THEN
    REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NEG; INT_POW_ONE;
                INT_ABS_NUM; INT_MUL_LID] THEN
    MATCH_MP_TAC(INT_ARITH
     `abs(x) <= &2 pow 59 * &2 pow 384 /\
      abs(y) <= &2 pow 59 * &2 pow 384
      ==> abs(x + y:int) <= &2 pow 444`) THEN
    REWRITE_TAC[INT_ABS_MUL] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL2 THEN
    ASM_REWRITE_TAC[INT_ABS_NUM; INT_POS; INT_ABS_POS] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    MAP_EVERY EXPAND_TAC ["u"; "v"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Biasing and Montgomery reduction of u ***)

  ABBREV_TAC
   `upos =
     bignum_of_wordlist
       [sum_s120;sum_s122;sum_s125;sum_s126;sum_s127;sum_s128;sum_s130]` THEN
  SUBGOAL_THEN
   `upos < 2 EXP 446 /\
    (&upos:int == fsgn * (m00 * &u + m01 * &v)) (mod (&p_384))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN
     `&upos:int = fsgn * (m00 * &u + m01 * &v) + &2 pow 61 * &p_384`
    SUBST1_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[INTEGER_RULE `(x + k * p:int == x) (mod p)`] THEN
      UNDISCH_TAC `abs(fsgn * (m00 * &u + m01 * &v)):int <= &2 pow 444` THEN
      REWRITE_TAC[p_384] THEN INT_ARITH_TAC] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `upos < 2 EXP 448` MP_TAC THENL
       [EXPAND_TAC "upos" THEN BOUNDER_TAC[];
        UNDISCH_TAC `abs(fsgn * (m00 * &u + m01 * &v)):int <= &2 pow 444`] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_384] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(uup:int == uexp) (mod p)
      ==> (upos == uup + c) (mod p)
          ==> (upos == uexp + c) (mod p)`)) THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
    MAP_EVERY EXPAND_TAC ["upos"; "uup"] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        fst o chop_list 7 o rev) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; bignum_of_wordlist; p_384;
                GSYM REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  RULE_ASSUM_TAC(REWRITE_RULE[swlemma_alt]) THEN
  RULE_ASSUM_TAC(fun th ->
    try MATCH_MP mmlemma_alt th with Failure _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(&2 pow 64 *
     &(bignum_of_wordlist
        [sum_s153;sum_s154;sum_s155;sum_s156;sum_s157;sum_s158]):int ==
     fsgn * (m00 * &u + m01 * &v)) (mod &p_384)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        INT_CONG_TRANS)) THEN
    ABBREV_TAC `w:int64 = word(4294967297 * val(sum_s120:int64))` THEN
    MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC
     `if &upos + &(val(w:int64)) * &p_384:int < &2 pow 448
      then &upos + &(val w) * &p_384:int
      else (&upos + &(val w) * &p_384) - &2 pow 64 * &p_384` THEN
    CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN CONV_TAC INTEGER_RULE] THEN
    MATCH_MP_TAC INT_EQ_IMP_CONG THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 448` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(INT_ARITH
       `&0:int <= x /\ x < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN BOUNDER_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [POP_ASSUM MP_TAC THEN REWRITE_TAC[p_384] THEN INT_ARITH_TAC;
        EXPAND_TAC "upos" THEN REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * bignum_of_wordlist
       [sum_s142;sum_s143;sum_s144;sum_s145;sum_s146;sum_s147;sum_s148] =
      upos + val(w:int64) * p_384`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 512` THEN
       REPLICATE_TAC 2 (CONJ_TAC THENL
       [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC]) THEN
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      EXPAND_TAC "upos" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           snd o chop_list 7 o rev) THEN
      STRIP_TAC THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; p_384]) THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(sum_s148:int64) < 2` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `2 EXP 64 * x = y ==> y < 2 * 2 EXP 448 ==> x < 2 * 2 EXP 384`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[p_384] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
      REWRITE_TAC[NUM_AS_BITVAL_ALT; VAL_WORD_GALOIS]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:bool` (SUBST_ALL_TAC o CONJUNCT2)) THEN
    SUBGOAL_THEN
     `&upos + &(val(w:int64)) * &p_384:int < &2 pow 448 <=> ~c`
    SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[NOT_LT] THEN BOUNDER_TAC[];
      REWRITE_TAC[COND_SWAP]] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      fst o chop_list 6 o rev o fst o chop_list 12) THEN
    REWRITE_TAC[WORD_SUB_LZERO; WORD_AND_MASK] THEN
    BOOL_CASES_TAC `c:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES; bignum_of_wordlist; p_384] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `pra = bignum_of_wordlist
           [sum_s153; sum_s154; sum_s155; sum_s156; sum_s157; sum_s158]` THEN
  TRANS_TAC EQ_TRANS `&(pra MOD p_384):int` THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
     [`64 * 6`; `if pra < p_384 then &pra else &pra - &p_384:real`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      ALL_TAC;
      SIMP_TAC[GSYM NOT_LE; COND_SWAP; REAL_OF_NUM_SUB; GSYM COND_RAND] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
      MATCH_MP_TAC MOD_CASES THEN REWRITE_TAC[p_384] THEN
      EXPAND_TAC "pra" THEN BOUNDER_TAC[]] THEN
    SUBGOAL_THEN `carry_s168 <=> pra < p_384` (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `384` THEN
      EXPAND_TAC "pra" THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; p_384;
                  GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
        rev o fst o chop_list 6) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(BINOP_CONV(BINOP_CONV REAL_POLY_CONV)) THEN BOUNDER_TAC[];
      EXPAND_TAC "pra" THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE o
        rev o fst o chop_list 6) THEN
      REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES]] THEN

  (*** Now finally handle the degenerate case ***)

  ASM_CASES_TAC `p_384 divides n` THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM DIVIDES_MOD; num_divides] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(e * x:int == f * (a * u + b * v)) (mod p)
      ==> p divides u /\ b = &0 /\ coprime(p,e)
          ==> p divides x`)) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides; GSYM num_coprime;
                    COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM p_384] THEN
    SUBST1_TAC(SYM(ASSUME `(mm:int^2^2)$1$2 = m01`)) THEN EXPAND_TAC "mm" THEN
    MATCH_MP_TAC DIVSTEP_MAT_DIAGONAL_1 THEN
    SUBGOAL_THEN `g = 0` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_EQ];
      EXPAND_TAC "g" THEN
      SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL; IVAL_WORD_0]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[INT_CONG_IMP_EQ;INT_SUB_RZERO]
      `(x == y) (mod n) ==> y:int = &0 /\ abs(x) < n ==> x = &0`)) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_G_ZERO THEN
      ASM_REWRITE_TAC[INT_REM_EQ_0; GSYM num_divides];
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "g" THEN BOUNDER_TAC[]];
    ASM_REWRITE_TAC[]] THEN

  (*** Deploy non-triviality ***)

  SUBGOAL_THEN `coprime(p_384,n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P384]; ALL_TAC] THEN
  SUBGOAL_THEN `gcd(&p_384,&n rem &p_384) = &1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM INT_COPRIME_GCD; INT_COPRIME_RREM] THEN
    ASM_SIMP_TAC[GSYM num_coprime];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(val(word(val(word(val(f_0:int64) * val(iword m00:int64)):int64) +
                val(g_0:int64) * val(iword m01:int64)):int64)) ==
     &2 pow 59 * divstep_f 885 t) (mod (&2 pow 64))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_64; GSYM IWORD_EQ] THEN
    CONV_TAC WORD_VAL_CONG_CONV THEN REWRITE_TAC[DIMINDEX_64] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [INT_MUL_SYM] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MATCH_MP_TAC INT_CONG_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INT_CONG_LMUL THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (INTEGER_RULE
       `(f:int == df) (mod q)
        ==> p divides q /\ (f == f0) (mod p) ==> (f0 == df) (mod p)`)) THEN
    SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC NUMBER_RULE;
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        TWOS_COMPLEMENT))] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VAL_BOUND_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `abs (divstep_f 885 t) = &1` THEN INT_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; GSYM MSB_VAL] THEN
  ASM_REWRITE_TAC[DIMINDEX_64; NUM_SUB_CONV `64 - 1`] THEN
  REWRITE_TAC[INT_ARITH `&2 pow 59 * x < &0 <=> x:int < &0`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN

  (*** Final part of mathematics ***)

  REWRITE_TAC[GSYM CONG; GSYM(NUM_EXP_CONV `2 EXP 768`)] THEN
  MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `n:num` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(n * i == 1) (mod p) /\ (n * pra == x) (mod p)
    ==> (n * pra == n * x * i) (mod p)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; num_congruent] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `!f f'. (e * pra:int == x) (mod p)
    ==> coprime(e,p) /\ f' * f = &1 /\
        (n * x == q * f' * f * e) (mod p)
        ==> (n * pra == q) (mod p)`)) THEN
  MAP_EVERY EXISTS_TAC [`fsgn:int`; `divstep_f 885 t`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_coprime] THEN
    REWRITE_TAC[COPRIME_LEXP; COPRIME_2; p_384] THEN CONV_TAC NUM_REDUCE_CONV;
    EXPAND_TAC "fsgn" THEN UNDISCH_TAC `abs(divstep_f 885 t) = &1` THEN
    REWRITE_TAC[INT_ARITH `abs x:int = &1 <=> x = &1 \/ x = --(&1)`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC INT_REDUCE_CONV;
    MATCH_MP_TAC(INTEGER_RULE
     `(a * n * u + b * n * v:int == q * x * y) (mod p)
      ==> (n * f * (a * u + b * v) == q * x * f * y) (mod p)`)] THEN
  REWRITE_TAC[INT_ARITH `(x:int) * &2 pow 64 = &2 pow 5 * &2 pow 59 * x`] THEN
  FIRST_X_ASSUM(fun th ->
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[ARITH_RULE
   `e * (a * u + b * v):int = a * e * u + b * e * v`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  MATCH_MP_TAC INT_CONG_ADD THEN CONJ_TAC THEN MATCH_MP_TAC INT_CONG_LMUL THEN
  ONCE_REWRITE_TAC[INT_CONG_SYM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NUM_REDUCE_CONV `843 - 5 * 14`]) THEN
  REWRITE_TAC[INT_MUL_ASSOC; GSYM INT_POW_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let BIGNUM_MONTINV_P384_CORRECT = time prove
 (`!z x n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,256))
            [(word pc,0x13e0); (z,8 * 6); (x,8 * 6)] /\
        nonoverlapping (word pc,0x13e0) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montinv_p384_mc /\
                  read PC s = word(pc + 0x10) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = word (pc + 0x13cc) /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17;
                      X19; X20; X21; X22; X23; X24] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,8 * 6);
                      memory :> bytes(stackpointer,256)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  ARM_SUBROUTINE_SIM_TAC
      (bignum_montinv_p384_mc,BIGNUM_MONTINV_P384_EXEC,0x10,
       (GEN_REWRITE_CONV RAND_CONV [bignum_montinv_p384_mc] THENC TRIM_LIST_CONV)
       `TRIM_LIST (16,20) bignum_montinv_p384_mc`,
       CORE_INV_P384_CORRECT)
      [`read X0 s`; `read X1 s`;
       `read (memory :> bytes(read X1 s,8 * 6)) s`;
       `pc + 0x10`; `stackpointer:int64`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_MONTINV_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 304),304))
            [word pc,0x13e0; z,8 * 6; x,8 * 6] /\
        nonoverlapping (word pc,0x13e0) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montinv_p384_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,6) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,6) s =
                  (if p_384 divides n then 0
                   else (2 EXP 768 * inverse_mod p_384 n) MOD p_384))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                    memory :> bytes(word_sub stackpointer (word 304),304)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTINV_P384_EXEC BIGNUM_MONTINV_P384_CORRECT
   `[X19;X20;X21;X22;X23;X24]` 304);;
