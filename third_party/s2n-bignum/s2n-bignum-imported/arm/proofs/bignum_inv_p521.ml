(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inversion modulo p_521, the field characteristic for NIST P-521.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "Divstep/divstep_bounds.ml";;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/p521/bignum_inv_p521.o";;
 ****)

let bignum_inv_p521_mc =  define_assert_from_elf
 "bignum_inv_p521_mc" "arm/p521/bignum_inv_p521.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10483ff;       (* arm_SUB SP SP (rvalue (word 288)) *)
  0xaa0003f4;       (* arm_MOV X20 X0 *)
  0x9280000a;       (* arm_MOVN X10 (word 0) 0 *)
  0xa9002bea;       (* arm_STP X10 X10 SP (Immediate_Offset (iword (&0))) *)
  0xa9012bea;       (* arm_STP X10 X10 SP (Immediate_Offset (iword (&16))) *)
  0xa9022bea;       (* arm_STP X10 X10 SP (Immediate_Offset (iword (&32))) *)
  0xa9032bea;       (* arm_STP X10 X10 SP (Immediate_Offset (iword (&48))) *)
  0xd2803feb;       (* arm_MOV X11 (rvalue (word 511)) *)
  0xf90023eb;       (* arm_STR X11 SP (Immediate_Offset (word 64)) *)
  0xf9402028;       (* arm_LDR X8 X1 (Immediate_Offset (word 64)) *)
  0xd349fd09;       (* arm_LSR X9 X8 9 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9402c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&0))) *)
  0xba09015f;       (* arm_ADCS XZR X10 X9 *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xa941342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&16))) *)
  0x8a0d0187;       (* arm_AND X7 X12 X13 *)
  0xba1f00ff;       (* arm_ADCS XZR X7 XZR *)
  0xa9423c2e;       (* arm_LDP X14 X15 X1 (Immediate_Offset (iword (&32))) *)
  0x8a0f01c7;       (* arm_AND X7 X14 X15 *)
  0xba1f00ff;       (* arm_ADCS XZR X7 XZR *)
  0xa9434430;       (* arm_LDP X16 X17 X1 (Immediate_Offset (iword (&48))) *)
  0x8a110207;       (* arm_AND X7 X16 X17 *)
  0xba1f00ff;       (* arm_ADCS XZR X7 XZR *)
  0xb277d907;       (* arm_ORR X7 X8 (rvalue (word 18446744073709551104)) *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba09014a;       (* arm_ADCS X10 X10 X9 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0x92402108;       (* arm_AND X8 X8 (rvalue (word 511)) *)
  0xa904afea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&72))) *)
  0xa905b7ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&88))) *)
  0xa906bfee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&104))) *)
  0xa907c7f0;       (* arm_STP X16 X17 SP (Immediate_Offset (iword (&120))) *)
  0xf90047e8;       (* arm_STR X8 SP (Immediate_Offset (word 136)) *)
  0xa9097fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&144))) *)
  0xa90a7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&160))) *)
  0xa90b7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&176))) *)
  0xa90c7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&192))) *)
  0xf9006bff;       (* arm_STR XZR SP (Immediate_Offset (word 208)) *)
  0xd280020a;       (* arm_MOV X10 (rvalue (word 16)) *)
  0xa90dffff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&216))) *)
  0xa90effff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&232))) *)
  0xa90fabff;       (* arm_STP XZR X10 SP (Immediate_Offset (iword (&248))) *)
  0xa910ffff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&264))) *)
  0xf9008fff;       (* arm_STR XZR SP (Immediate_Offset (word 280)) *)
  0xd28002b5;       (* arm_MOV X21 (rvalue (word 21)) *)
  0xd2800036;       (* arm_MOV X22 (rvalue (word 1)) *)
  0x14000213;       (* arm_B (word 2124) *)
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
  0xf94027e8;       (* arm_LDR X8 SP (Immediate_Offset (word 72)) *)
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
  0xf9402be8;       (* arm_LDR X8 SP (Immediate_Offset (word 80)) *)
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
  0xf90027e5;       (* arm_STR X5 SP (Immediate_Offset (word 72)) *)
  0xf9400be7;       (* arm_LDR X7 SP (Immediate_Offset (word 16)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9402fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 88)) *)
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
  0xf9002be3;       (* arm_STR X3 SP (Immediate_Offset (word 80)) *)
  0xf9400fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 24)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xf94033e8;       (* arm_LDR X8 SP (Immediate_Offset (word 96)) *)
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
  0xf9002fe4;       (* arm_STR X4 SP (Immediate_Offset (word 88)) *)
  0xf94013e7;       (* arm_LDR X7 SP (Immediate_Offset (word 32)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xf94037e8;       (* arm_LDR X8 SP (Immediate_Offset (word 104)) *)
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
  0xf90033e2;       (* arm_STR X2 SP (Immediate_Offset (word 96)) *)
  0xf94017e7;       (* arm_LDR X7 SP (Immediate_Offset (word 40)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf9403be8;       (* arm_LDR X8 SP (Immediate_Offset (word 112)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0x93c3ec83;       (* arm_EXTR X3 X4 X3 59 *)
  0xf90013e3;       (* arm_STR X3 SP (Immediate_Offset (word 32)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c6eca6;       (* arm_EXTR X6 X5 X6 59 *)
  0xf90037e6;       (* arm_STR X6 SP (Immediate_Offset (word 104)) *)
  0xf9401be7;       (* arm_LDR X7 SP (Immediate_Offset (word 48)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf9403fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 120)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0x93c4ec44;       (* arm_EXTR X4 X2 X4 59 *)
  0xf90017e4;       (* arm_STR X4 SP (Immediate_Offset (word 40)) *)
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
  0xf9003be5;       (* arm_STR X5 SP (Immediate_Offset (word 112)) *)
  0xf9401fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 56)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf94043e8;       (* arm_LDR X8 SP (Immediate_Offset (word 128)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0x93c2ecc2;       (* arm_EXTR X2 X6 X2 59 *)
  0xf9001be2;       (* arm_STR X2 SP (Immediate_Offset (word 48)) *)
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
  0xf9003fe3;       (* arm_STR X3 SP (Immediate_Offset (word 120)) *)
  0xf94023e7;       (* arm_LDR X7 SP (Immediate_Offset (word 64)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x937ffc23;       (* arm_ASR X3 X1 63 *)
  0x8a0a0063;       (* arm_AND X3 X3 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94047e8;       (* arm_LDR X8 SP (Immediate_Offset (word 136)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x937ffc20;       (* arm_ASR X0 X1 63 *)
  0x8a0b0000;       (* arm_AND X0 X0 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c6eca6;       (* arm_EXTR X6 X5 X6 59 *)
  0xf9001fe6;       (* arm_STR X6 SP (Immediate_Offset (word 56)) *)
  0x93c5ec65;       (* arm_EXTR X5 X3 X5 59 *)
  0xf90023e5;       (* arm_STR X5 SP (Immediate_Offset (word 64)) *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x937ffc25;       (* arm_ASR X5 X1 63 *)
  0x8a0c00a5;       (* arm_AND X5 X5 X12 *)
  0xcb0503e5;       (* arm_NEG X5 X5 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x937ffc20;       (* arm_ASR X0 X1 63 *)
  0x8a0d0000;       (* arm_AND X0 X0 X13 *)
  0xcb0000a5;       (* arm_SUB X5 X5 X0 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0x93c4ec44;       (* arm_EXTR X4 X2 X4 59 *)
  0xf90043e4;       (* arm_STR X4 SP (Immediate_Offset (word 128)) *)
  0x93c2eca2;       (* arm_EXTR X2 X5 X2 59 *)
  0xf90047e2;       (* arm_STR X2 SP (Immediate_Offset (word 136)) *)
  0xf9404be7;       (* arm_LDR X7 SP (Immediate_Offset (word 144)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf9406fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 216)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf9004be4;       (* arm_STR X4 SP (Immediate_Offset (word 144)) *)
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
  0xf9006fe5;       (* arm_STR X5 SP (Immediate_Offset (word 216)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9404fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 152)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94073e8;       (* arm_LDR X8 SP (Immediate_Offset (word 224)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf9004fe2;       (* arm_STR X2 SP (Immediate_Offset (word 152)) *)
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
  0xf90073e3;       (* arm_STR X3 SP (Immediate_Offset (word 224)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf94053e7;       (* arm_LDR X7 SP (Immediate_Offset (word 160)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf94077e8;       (* arm_LDR X8 SP (Immediate_Offset (word 232)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf90053e6;       (* arm_STR X6 SP (Immediate_Offset (word 160)) *)
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
  0xf90077e4;       (* arm_STR X4 SP (Immediate_Offset (word 232)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94057e7;       (* arm_LDR X7 SP (Immediate_Offset (word 168)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xf9407be8;       (* arm_LDR X8 SP (Immediate_Offset (word 240)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0xf90057e5;       (* arm_STR X5 SP (Immediate_Offset (word 168)) *)
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
  0xf9007be2;       (* arm_STR X2 SP (Immediate_Offset (word 240)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xf9405be7;       (* arm_LDR X7 SP (Immediate_Offset (word 176)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xf9407fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 248)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xf9005be3;       (* arm_STR X3 SP (Immediate_Offset (word 176)) *)
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
  0xf9007fe6;       (* arm_STR X6 SP (Immediate_Offset (word 248)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xf9405fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 184)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94083e8;       (* arm_LDR X8 SP (Immediate_Offset (word 256)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf9005fe4;       (* arm_STR X4 SP (Immediate_Offset (word 184)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xca1000e1;       (* arm_EOR X1 X7 X16 *)
  0x9b0c7c20;       (* arm_MUL X0 X1 X12 *)
  0x9bcc7c21;       (* arm_UMULH X1 X1 X12 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xca110101;       (* arm_EOR X1 X8 X17 *)
  0x9b0d7c20;       (* arm_MUL X0 X1 X13 *)
  0x9bcd7c21;       (* arm_UMULH X1 X1 X13 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0xf90083e5;       (* arm_STR X5 SP (Immediate_Offset (word 256)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94063e7;       (* arm_LDR X7 SP (Immediate_Offset (word 192)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94087e8;       (* arm_LDR X8 SP (Immediate_Offset (word 264)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90063e2;       (* arm_STR X2 SP (Immediate_Offset (word 192)) *)
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
  0xf90087e3;       (* arm_STR X3 SP (Immediate_Offset (word 264)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf94067e7;       (* arm_LDR X7 SP (Immediate_Offset (word 200)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9408be8;       (* arm_LDR X8 SP (Immediate_Offset (word 272)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf90067e6;       (* arm_STR X6 SP (Immediate_Offset (word 200)) *)
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
  0xf9008be4;       (* arm_STR X4 SP (Immediate_Offset (word 272)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf9406be7;       (* arm_LDR X7 SP (Immediate_Offset (word 208)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c3;       (* arm_AND X3 X14 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9408fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 280)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c52466;       (* arm_EXTR X6 X3 X5 9 *)
  0xa94907e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&144))) *)
  0x8b83fcc6;       (* arm_ADD X6 X6 (Shiftedreg X3 ASR 63) *)
  0xcb0624a5;       (* arm_SUB X5 X5 (Shiftedreg X6 LSL 9) *)
  0xab060000;       (* arm_ADDS X0 X0 X6 *)
  0x937ffcc6;       (* arm_ASR X6 X6 63 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa90907e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&144))) *)
  0xa94a07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xba060000;       (* arm_ADCS X0 X0 X6 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa90a07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa94b07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&176))) *)
  0xba060000;       (* arm_ADCS X0 X0 X6 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa90b07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&176))) *)
  0xa94c07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0xba060000;       (* arm_ADCS X0 X0 X6 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa90c07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&192))) *)
  0x9a0600a5;       (* arm_ADC X5 X5 X6 *)
  0xf9006be5;       (* arm_STR X5 SP (Immediate_Offset (word 208)) *)
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
  0x93c224a6;       (* arm_EXTR X6 X5 X2 9 *)
  0xa94d87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&216))) *)
  0x8b85fcc6;       (* arm_ADD X6 X6 (Shiftedreg X5 ASR 63) *)
  0xcb062442;       (* arm_SUB X2 X2 (Shiftedreg X6 LSL 9) *)
  0xab060000;       (* arm_ADDS X0 X0 X6 *)
  0x937ffcc6;       (* arm_ASR X6 X6 63 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa90d87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&216))) *)
  0xa94e87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&232))) *)
  0xba060000;       (* arm_ADCS X0 X0 X6 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa90e87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&232))) *)
  0xa94f87e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&248))) *)
  0xba060000;       (* arm_ADCS X0 X0 X6 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa90f87e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&248))) *)
  0xa95087e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&264))) *)
  0xba060000;       (* arm_ADCS X0 X0 X6 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0xa91087e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&264))) *)
  0x9a060042;       (* arm_ADC X2 X2 X6 *)
  0xf9008fe2;       (* arm_STR X2 SP (Immediate_Offset (word 280)) *)
  0xaa1603e1;       (* arm_MOV X1 X22 *)
  0xf94003e2;       (* arm_LDR X2 SP (Immediate_Offset (word 0)) *)
  0xf94027e3;       (* arm_LDR X3 SP (Immediate_Offset (word 72)) *)
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
  0x54ff7181;       (* arm_BNE (word 2092592) *)
  0xf94003e0;       (* arm_LDR X0 SP (Immediate_Offset (word 0)) *)
  0xf94027e1;       (* arm_LDR X1 SP (Immediate_Offset (word 72)) *)
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
  0xf9404be7;       (* arm_LDR X7 SP (Immediate_Offset (word 144)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf9406fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 216)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf9004be4;       (* arm_STR X4 SP (Immediate_Offset (word 144)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf9404fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 152)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94073e8;       (* arm_LDR X8 SP (Immediate_Offset (word 224)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf9004fe2;       (* arm_STR X2 SP (Immediate_Offset (word 152)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xf94053e7;       (* arm_LDR X7 SP (Immediate_Offset (word 160)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf94077e8;       (* arm_LDR X8 SP (Immediate_Offset (word 232)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf90053e6;       (* arm_STR X6 SP (Immediate_Offset (word 160)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xf94057e7;       (* arm_LDR X7 SP (Immediate_Offset (word 168)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a0103e3;       (* arm_ADC X3 XZR X1 *)
  0xf9407be8;       (* arm_LDR X8 SP (Immediate_Offset (word 240)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0xf90057e5;       (* arm_STR X5 SP (Immediate_Offset (word 168)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9405be7;       (* arm_LDR X7 SP (Immediate_Offset (word 176)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0x9a0103e4;       (* arm_ADC X4 XZR X1 *)
  0xf9407fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 248)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000063;       (* arm_ADDS X3 X3 X0 *)
  0xf9005be3;       (* arm_STR X3 SP (Immediate_Offset (word 176)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf9405fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 184)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94083e8;       (* arm_LDR X8 SP (Immediate_Offset (word 256)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf9005fe4;       (* arm_STR X4 SP (Immediate_Offset (word 184)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94063e7;       (* arm_LDR X7 SP (Immediate_Offset (word 192)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94087e8;       (* arm_LDR X8 SP (Immediate_Offset (word 264)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90063e2;       (* arm_STR X2 SP (Immediate_Offset (word 192)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xf94067e7;       (* arm_LDR X7 SP (Immediate_Offset (word 200)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9408be8;       (* arm_LDR X8 SP (Immediate_Offset (word 272)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf90067e6;       (* arm_STR X6 SP (Immediate_Offset (word 200)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xf9406be7;       (* arm_LDR X7 SP (Immediate_Offset (word 208)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c3;       (* arm_AND X3 X14 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9408fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 280)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c52466;       (* arm_EXTR X6 X3 X5 9 *)
  0xa9492fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&144))) *)
  0x8b83fcc6;       (* arm_ADD X6 X6 (Shiftedreg X3 ASR 63) *)
  0xcb0624a5;       (* arm_SUB X5 X5 (Shiftedreg X6 LSL 9) *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0x937ffcc6;       (* arm_ASR X6 X6 63 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0xa94a37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0xa94b3fee;       (* arm_LDP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0xba0601ef;       (* arm_ADCS X15 X15 X6 *)
  0xa94c47f0;       (* arm_LDP X16 X17 SP (Immediate_Offset (iword (&192))) *)
  0xba060210;       (* arm_ADCS X16 X16 X6 *)
  0xba060231;       (* arm_ADCS X17 X17 X6 *)
  0x9a0600b3;       (* arm_ADC X19 X5 X6 *)
  0xb1000540;       (* arm_ADDS X0 X10 (rvalue (word 1)) *)
  0xba1f0161;       (* arm_ADCS X1 X11 XZR *)
  0xba1f0182;       (* arm_ADCS X2 X12 XZR *)
  0xba1f01a3;       (* arm_ADCS X3 X13 XZR *)
  0xba1f01c4;       (* arm_ADCS X4 X14 XZR *)
  0xba1f01e5;       (* arm_ADCS X5 X15 XZR *)
  0xba1f0206;       (* arm_ADCS X6 X16 XZR *)
  0xba1f0227;       (* arm_ADCS X7 X17 XZR *)
  0xd2803fe8;       (* arm_MOV X8 (rvalue (word 511)) *)
  0xfa080268;       (* arm_SBCS X8 X19 X8 *)
  0x9a8a2000;       (* arm_CSEL X0 X0 X10 Condition_CS *)
  0x9a8b2021;       (* arm_CSEL X1 X1 X11 Condition_CS *)
  0x9a8c2042;       (* arm_CSEL X2 X2 X12 Condition_CS *)
  0x9a8d2063;       (* arm_CSEL X3 X3 X13 Condition_CS *)
  0x9a8e2084;       (* arm_CSEL X4 X4 X14 Condition_CS *)
  0x9a8f20a5;       (* arm_CSEL X5 X5 X15 Condition_CS *)
  0x9a9020c6;       (* arm_CSEL X6 X6 X16 Condition_CS *)
  0x9a9120e7;       (* arm_CSEL X7 X7 X17 Condition_CS *)
  0x9a932108;       (* arm_CSEL X8 X8 X19 Condition_CS *)
  0xa9000680;       (* arm_STP X0 X1 X20 (Immediate_Offset (iword (&0))) *)
  0xa9010e82;       (* arm_STP X2 X3 X20 (Immediate_Offset (iword (&16))) *)
  0xa9021684;       (* arm_STP X4 X5 X20 (Immediate_Offset (iword (&32))) *)
  0xa9031e86;       (* arm_STP X6 X7 X20 (Immediate_Offset (iword (&48))) *)
  0xf9002288;       (* arm_STR X8 X20 (Immediate_Offset (word 64)) *)
  0x910483ff;       (* arm_ADD SP SP (rvalue (word 288)) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_INV_P521_EXEC = ARM_MK_EXEC_RULE bignum_inv_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Do the main proof for the core that is sometimes inlined elsewhere        *)
(* ------------------------------------------------------------------------- *)

let CORE_INV_P521_EXEC =
    ARM_MK_EXEC_RULE
     ((GEN_REWRITE_CONV RAND_CONV [bignum_inv_p521_mc] THENC TRIM_LIST_CONV)
      `TRIM_LIST (12,16) bignum_inv_p521_mc`);;

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
  ARM_STEPS_TAC CORE_INV_P521_EXEC (s--s') THEN
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
                 (TRIM_LIST (12,16) bignum_inv_p521_mc) /\
             read PC s = word(pc + 0x92c) /\
             read X1 s = d /\
             read X2 s = f /\
             read X3 s = g)
        (\s. read PC s = word(pc + 0x12a0) /\
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
    ARM_QUICKSIM_TAC CORE_INV_P521_EXEC [`read X0 s = x`] (1--605)] THEN

  (*** The first packing ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC CORE_INV_P521_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first block of 20 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (9*n-3)) (1--20) THEN

  (*** The unpacking of the first block ***)

  ARM_STEPS_TAC CORE_INV_P521_EXEC (185--194) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of first update matrix to f and g ***)

  ARM_STEPS_TAC CORE_INV_P521_EXEC (195--202) THEN
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

  ARM_STEPS_TAC CORE_INV_P521_EXEC (203--207) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The second block of 20 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (9*n+199)) (1--20) THEN

  (*** The unpacking of the second block ***)

  ARM_STEPS_TAC CORE_INV_P521_EXEC (387--396) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of second update matrix to f and g ***)

  ARM_STEPS_TAC CORE_INV_P521_EXEC (397--404) THEN
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

  ARM_STEPS_TAC CORE_INV_P521_EXEC (405--409) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first 10 of the third block of 19 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (9*n+401)) (1--10) THEN

  (*** The interspersed matrix multiplication ***)

  ARM_STEPS_TAC CORE_INV_P521_EXEC (500--507) THEN

  (*** The final 9 of the third block of 19 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (9*n+409)) (11--19) THEN

  (*** The final unpacking is a little different as it's 19 not 20 ***)

  ARM_STEPS_TAC CORE_INV_P521_EXEC (588--597) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_19]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** The final matrix multiplication and writeback ***)

  ARM_STEPS_TAC CORE_INV_P521_EXEC (598--605) THEN
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

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let PRIME_P521 = time prove
 (`prime p_521`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONV_TAC o PRIME_RULE)
  ["2"; "3"; "5"; "7"; "11"; "13"; "17"; "19"; "23"; "29"; "31"; "37"; "41";
   "43"; "53"; "59"; "61"; "79"; "89"; "103"; "109"; "113"; "131"; "151";
   "157"; "173"; "179"; "223"; "227"; "257"; "277"; "317"; "347"; "397";
   "521"; "683"; "1051"; "1237"; "1381"; "1433"; "1613"; "1663"; "2437";
   "2731"; "3191"; "8191"; "23609"; "28793"; "42641"; "49481"; "51481";
   "61681"; "409891"; "858001"; "2995763"; "5746001"; "7623851"; "8620289";
   "9211861"; "34110701"; "308761441"; "2400573761"; "2534364967";
   "24098228377"; "65427463921"; "674750394557"; "108140989558681";
   "145295143558111"; "361725589517273017"; "173308343918874810521923841"]);;

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

let TWOS_COMPLEMENT_576 = prove
 (`(&(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8]) == x) (mod (&2 pow 576))
   ==> --(&2 pow 575) <= x /\ x:int < &2 pow 575
       ==> x = &(bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8]) -
               &2 pow 576 * &(bitval(bit 63 n8))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] TWOS_COMPLEMENT)) THEN
  ASM_REWRITE_TAC[ARITH_EQ; NUM_RED_CONV `576 - 1`] THEN
  ANTS_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  MP_TAC(SYM(ISPEC `n8:int64` BITVAL_MSB)) THEN
  REWRITE_TAC[DIMINDEX_64; NUM_RED_CONV `64 - 1`] THEN MESON_TAC[]);;

let p521signedredlemma = prove
 (`!n:int.
        abs(n) <= &2 pow 582
        ==> let q = n div &2 pow 521 in
            let q' = if n < &0 then q - &1 else q in
            abs(q') < &2 pow 62 /\
            &0 <= n - q' * &p_521 /\
            n - q' * &p_521 < &2 * &p_521`,
  REWRITE_TAC[p_521; LET_DEF; LET_END_DEF] THEN INT_ARITH_TAC);;

let CORE_INV_P521_CORRECT = time prove
 (`!z x n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,288))
            [(word pc,0x1590); (z,8 * 9); (x,8 * 9)] /\
        nonoverlapping (word pc,0x1590) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                   (TRIM_LIST (12,16) bignum_inv_p521_mc) /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0x1590) /\
                  bignum_from_memory(z,9) s =
                  (if p_521 divides n then 0 else inverse_mod p_521 n))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17;
                      X19; X20; X21; X22] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,8 * 9);
                      memory :> bytes(stackpointer,288)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Abbreviate the starting tuple for divstep ***)

  ABBREV_TAC `t:int#int#int = (&1,&p_521,&n rem &p_521)` THEN

  (*** Set up the main loop invariant ***)

  ENSURES_WHILE_UP_TAC `20` `pc + 0x920` `pc + 0x920`
   `\i s.
      read SP s = stackpointer /\
      read X20 s = z /\
      read X21 s = word(21 - i) /\
      read X22 s = iword(divstep_d (59 * i) t) /\
      (&(read (memory :> bytes(stackpointer,8 * 9)) s) ==
       divstep_f (59 * i) t) (mod (&2 pow 576)) /\
      (&(read (memory :> bytes(word_add stackpointer (word 72),8 * 9)) s) ==
       divstep_g (59 * i) t) (mod (&2 pow 576)) /\
      read (memory :> bytes(word_add stackpointer (word 144),8 * 9)) s <
      2 * p_521 /\
      read (memory :> bytes(word_add stackpointer (word 216),8 * 9)) s <
      2 * p_521 /\
      (divstep_f (59 * i) t ==
       &n * &2 pow (59 * (21 - i)) *
       &(read (memory :> bytes(word_add stackpointer (word 144),8 * 9)) s))
      (mod (&p_521)) /\
      (divstep_g (59 * i) t ==
       &n * &2 pow (59 * (21 - i)) *
       &(read (memory :> bytes(word_add stackpointer (word 216),8 * 9)) s))
      (mod (&p_521)) /\
     (p_521 divides n
      ==> read (memory :> bytes(word_add stackpointer (word 144),8 * 9)) s = 0)`
  THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)
    (*** Latter part is more or less a copy of bignum_mod_p521_9 proof ***)

    BIGNUM_TERMRANGE_TAC `9` `n:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
    ARM_ACCSTEPS_TAC CORE_INV_P521_EXEC
     [13;14;17;20;23;25;26;27;28;29;30;31;32;33;34] (1--54) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[DIVSTEP_D; DIVSTEP_F; DIVSTEP_G; GSYM WORD_IWORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s54" THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES; p_521;
                GSYM INT_REM_EQ] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_REM_REM; INT_MUL_RID; GSYM p_521] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    SUBGOAL_THEN `n MOD p_521 = (n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [ARITH_RULE `n = 2 EXP 521 * n DIV 2 EXP 521 + n MOD 2 EXP 521`] THEN
      REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
       `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
      REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `n DIV 2 EXP 521 < 2 EXP 55 /\ n MOD 2 EXP 521 < 2 EXP 521`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; ARITH_RULE
       `n DIV 2 EXP 521 < 2 EXP 55 <=> n < 2 EXP (64 * 9)`] THEN
      EXPAND_TAC "n" THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
      `l = bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7;
                              word_and n_8 (word 511)]` THEN
    ABBREV_TAC `h:int64 = word_ushr n_8 9` THEN
    SUBGOAL_THEN
     `n DIV 2 EXP 521 = val(h:int64) /\ n MOD 2 EXP 521 = l`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["n"; "h"; "l"] THEN CONJ_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
        REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD];
        REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
        REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
        REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
        SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD;
                 ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
                 MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; ADD_CLAUSES] THEN
        REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
        REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ADD_CLAUSES] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `carry_s25 <=> p_521 <= val(h:int64) + l` SUBST_ALL_TAC THENL
     [TRANS_TAC EQ_TRANS
       `2 EXP 329 <=
        bignum_of_wordlist [n_0; n_1; word_and n_2 n_3; word_and n_4 n_5;
                            word_and n_6 n_7; word_and n_8 (word 511)] +
        val(h:int64) + 1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        SUBGOAL_THEN
         `&(val(word_or n_8 (word 18446744073709551104):int64)):real =
           &2 pow 9 * (&2 pow 55 - &1) + &(val(word_and n_8 (word 511)))`
        SUBST1_TAC THENL
         [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
           `word_or a b = word_or b (word_and a (word_not b))`] THEN
          SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
           `word_and x (word_and y (word_not x)) = word 0`] THEN
          CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          REWRITE_TAC[REAL_OF_NUM_ADD];
          DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
        EXPAND_TAC "l"] THEN
      REWRITE_TAC[bignum_of_wordlist] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      MP_TAC(ARITH_RULE `val(n_8:int64) MOD 2 EXP 9 < 2 EXP 9`) THEN
      SPEC_TAC(`val(n_8:int64) MOD 2 EXP 9`,`n8:num`) THEN GEN_TAC THEN
      UNDISCH_TAC `val(h:int64) < 2 EXP 55` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MP_TAC(ISPECL [`n_2:int64`; `n_3:int64`] VAL_WORD_AND_EQ_MAX) THEN
      MP_TAC(ISPECL [`n_4:int64`; `n_5:int64`] VAL_WORD_AND_EQ_MAX) THEN
      MP_TAC(ISPECL [`n_6:int64`; `n_7:int64`] VAL_WORD_AND_EQ_MAX) THEN
      REWRITE_TAC[TAUT
       `(p <=> q /\ r) <=> ~p /\ (~q \/ ~r) \/ p /\ q /\ r`] THEN
      SIMP_TAC[VAL_BOUND; ARITH_RULE
       `n < e ==> (~(n = e - 1) <=> n < e - 1)`] THEN
      MAP_EVERY (MP_TAC o C SPEC VAL_BOUND_64)
       [`n_0:int64`; `n_1:int64`; `n_2:int64`; `n_3:int64`;
        `n_4:int64`; `n_5:int64`; `n_6:int64`; `n_7:int64`;
        `word_and n_2 n_3:int64`;
        `word_and n_4 n_5:int64`;
        `word_and n_6 n_7:int64`] THEN
      REWRITE_TAC[DIMINDEX_64; p_521] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY ASM_ARITH_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o MATCH_MP
       (ARITH_RULE `n < 2 EXP 9 ==> n = 2 EXP 9 - 1 \/ n < 2 EXP 9 - 1`)) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`521`;
      `if val(h:int64) + l < p_521
       then &(val(h:int64) + l) else &(val(h:int64) + l) - &p_521`] THEN
    REPEAT CONJ_TAC THENL
     [BOUNDER_TAC[];
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      ALL_TAC;
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`l < 2 EXP 521`; `val(h:int64) < 2 EXP 55`] THEN
        REWRITE_TAC[p_521] THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
    ABBREV_TAC `bb <=> val(h:int64) + l < p_521` THEN
    EXPAND_TAC "l" THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_MOD; p_521] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;

    (*** Main invariant proof ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `f:num` `read (memory :> bytes (stackpointer,8 * 9))` THEN
    GHOST_INTRO_TAC `g:num`
     `read (memory :> bytes (word_add stackpointer (word 72),8 * 9))` THEN
    GHOST_INTRO_TAC `u:num`
     `read (memory :> bytes (word_add stackpointer (word 144),8 * 9))` THEN
    GHOST_INTRO_TAC `v:num`
     `read (memory :> bytes (word_add stackpointer (word 216),8 * 9))` THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY (BIGNUM_TERMRANGE_TAC `9`) [`f:num`; `g:num`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "f_"
     `read (memory :> bytes(stackpointer,8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "g_"
     `read (memory :> bytes(word_add stackpointer (word 72),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "u_"
     `read (memory :> bytes(word_add stackpointer (word 144),8 * 9)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "v_"
     `read (memory :> bytes(word_add stackpointer (word 216),8 * 9)) s0` THEN

    ARM_STEPS_TAC CORE_INV_P521_EXEC (1--3) THEN
    MP_TAC(SPECL
     [`iword (divstep_d (59 * i) t):int64`;
      `f_0:int64`; `g_0:int64`; `pc:num`]
     LOCAL_WORD_DIVSTEP59_CORRECT) THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    ARM_BIGSTEP_TAC CORE_INV_P521_EXEC "s4" THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN

    SUBGOAL_THEN `abs(divstep_d (59 * i) t) < &2 pow 62` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN W(MP_TAC o
       PART_MATCH (lhand o rand o lhand) DIVSTEP_D_BOUND o lhand o snd) THEN
      MATCH_MP_TAC(INT_ARITH
       `e:int < &59 * &20
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
        MATCH_MP_TAC DIVSTEP_F_ODD THEN REWRITE_TAC[p_521] THEN
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

    ARM_STEPS_TAC CORE_INV_P521_EXEC (5--7) THEN
    SUBGOAL_THEN
     `word_sub (word (21 - i)) (word 1):int64 = word(21 - (i + 1))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[ARITH_RULE `21 - (i + 1) = (21 - i) - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 20 ==> 1 <= 21 - i`];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word(21 - (i + 1)):int64) = 0)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL
     [VAL_INT64_TAC `21 - (i + 1)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i < 20` THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** Sign-magnitude breakdown of matrix entries ***)

    ARM_STEPS_TAC CORE_INV_P521_EXEC (8--19) THEN
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

    ARM_ACCSTEPS_TAC CORE_INV_P521_EXEC [22;25] (20--25) THEN

    (*** Accumulation of new f and g (then keep 2 accumulations above) ***)

    ARM_ACCSTEPS_TAC CORE_INV_P521_EXEC
     [28;30;31;34;36;37;39;41;42;44;46;47;50;52;53;56;58;59;63;
      65;66;68;70;71;76;78;79;82;84;85;89;91;92;94;96;97;102;
      104;105;108;110;111;115;117;118;120;122;123;128;130;131;134;
      136;137;141;143;144;146;148;149;154;156;157;160;162;163;167;
      169;170;172;174;175;180;182;183;186;188;189;193;195;196;198;
      200;201;206;208;209;212;214;215;219;221;222;224;226;227;235;
      237;238;243;244;246;247;256;258;259;263;264;266;267]
     (26--271) THEN
    MAP_EVERY ABBREV_TAC
     [`fup = bignum_of_wordlist
        [sum_s36;sum_s58;sum_s84;sum_s110;sum_s136;
         sum_s162;sum_s188;sum_s214;sum_s246;sum_s247]`;
      `gup = bignum_of_wordlist
        [sum_s46;sum_s70;sum_s96;sum_s122;sum_s148;
         sum_s174;sum_s200;sum_s226;sum_s266;sum_s267]`] THEN
    SUBGOAL_THEN
     `(&fup:int ==
       m00 * divstep_f (59 * i) t + m01 * divstep_g (59 * i) t)
      (mod (&2 pow 640)) /\
      (&gup:int ==
       m10 * divstep_f (59 * i) t + m11 * divstep_g (59 * i) t)
      (mod (&2 pow 640))`
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
      UNDISCH_TAC `(&f == divstep_f (59 * i) t) (mod (&2 pow 576))` THEN
      UNDISCH_TAC `(&g == divstep_g (59 * i) t) (mod (&2 pow 576))` THEN
      MAP_EVERY EXPAND_TAC ["f"; "g"; "t"] THEN
      (DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_576) THEN ANTS_TAC THENL
       [MATCH_MP_TAC DIVSTEP_G_BOUNDS THEN
        REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV THEN
        REWRITE_TAC[INT_OF_NUM_REM; INT_ARITH `--(&m):int <= &n`] THEN
        REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
       DISCH_THEN(MP_TAC o MATCH_MP TWOS_COMPLEMENT_576) THEN ANTS_TAC THENL
       [MATCH_MP_TAC DIVSTEP_F_BOUNDS THEN
        REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV THEN
        REWRITE_TAC[INT_OF_NUM_REM; INT_ARITH `--(&m):int <= &n`] THEN
        REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_OF_NUM_EQ] THEN
      MAP_EVERY EXPAND_TAC ["fup"; "gup"] THEN
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
      REPEAT(COND_CASES_TAC THEN
        ASM_REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; REAL_VAL_WORD_NEG;
                        BITVAL_CLAUSES; DIMINDEX_64]) THEN
      REAL_INTEGER_TAC;

      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        fst o chop_list 2 o rev) THEN
      STRIP_TAC] THEN

    (*** Accumulation of new u and v values before reduction ***)
    (*** Keep all the accumulations for the modular reductions ***)

    ARM_ACCSTEPS_TAC CORE_INV_P521_EXEC
     [274;276;277;280;282;284;286;288;289;291;293;295;298;300;301;
      304;306;308;310;312;313;315;317;319;322;324;325;328;330;332;
      334;336;337;339;341;343;346;348;349;352;354;356;358;360;361;
      363;365;367;370;372;373;376;378;380;382;384;385;387;389;391;
      394;396;397;400;402;404;406;408;409;411;413;415;418;420;421;
      424;426;428;430;432;433;435;437;439;442;444;445;448;450;452;
      454;456;457;459;461;463;468;470;471;475;476;478;479;483;484;
      486;489;490;493;494;497;498;500;505;507;508;511;512;514;515;
      519;520;522;525;526;529;530;533;534;536]
     (272--537) THEN
    MAP_EVERY ABBREV_TAC
     [`uup = bignum_of_wordlist
              [sum_s282;sum_s306;sum_s330;sum_s354;sum_s378;
               sum_s402;sum_s426;sum_s450;sum_s478;sum_s479]`;
      `vup = bignum_of_wordlist
              [sum_s293;sum_s317;sum_s341;sum_s365;sum_s389;
               sum_s413;sum_s437;sum_s461;sum_s514;sum_s515]`] THEN
    SUBGOAL_THEN
     `(&uup:int == m00 * &u + m01 * &v) (mod (&2 pow 640)) /\
      (&vup:int == m10 * &u + m11 * &v) (mod (&2 pow 640))`
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
      ALL_TAC] THEN

    (*** Finish the simulation before proceeding ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s535" THEN

    (*** Stepping mathematics for divstep ***)

    REWRITE_TAC[ARITH_RULE `59 * (i + 1) = 59 + 59 * i`] THEN
    REWRITE_TAC[DIVSTEP_DFG_ADD] THEN

    MP_TAC(SPECL
     [`divstep_d (59 * i) t`; `divstep_f (59 * i) t`; `divstep_g (59 * i) t`;
      `59`] DIVSTEP_MAT) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_F_ODD THEN
      REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV;
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
      CONJ_TAC THEN MATCH_MP_TAC INT_CONG_TRANS THENL
       [EXISTS_TAC `&fup div &2 pow 59`;
        EXISTS_TAC `&gup div &2 pow 59`] THEN
      (CONJ_TAC THENL
        [REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_DIV; INT_OF_NUM_CLAUSES];
         MATCH_MP_TAC INT_CONG_DIV2 THEN
         FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
           INT_CONG_INT_DIVIDES_MODULUS)) THEN
         REWRITE_TAC[GSYM INT_POW_ADD] THEN
         SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH]]) THEN
      REWRITE_TAC[GSYM num_congruent] THEN
      MAP_EVERY EXPAND_TAC ["fup"; "gup"] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [bignum_of_wordlist] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 59 * 2 EXP 5`] THEN
      SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; ARITH_EQ; EXP_EQ_0] THEN
      SIMP_TAC[bignum_of_wordlist; VAL_WORD_SUBWORD_JOIN_64;
               ARITH_LE; ARITH_LT] THEN
      CONV_TAC(DEPTH_CONV NUM_SUB_CONV) THEN
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
      REAL_INTEGER_TAC;
      ALL_TAC] THEN

    (*** The basic modular reduction mathematics ***)

    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN
     `abs(m00 * &u + m01 * &v:int) <= &2 pow 582 /\
      abs(m10 * &u + m11 * &v:int) <= &2 pow 582`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(INT_ARITH
       `abs(x) <= &2 pow 59 * &2 pow 522 /\
        abs(y) <= &2 pow 59 * &2 pow 522
        ==> abs(x + y:int) <= &2 pow 582`) THEN
      REWRITE_TAC[INT_ABS_MUL] THEN
      CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL2 THEN
      ASM_REWRITE_TAC[INT_ABS_NUM; INT_POS; INT_ABS_POS] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      MAP_EVERY UNDISCH_TAC [`u < 2 * p_521`; `v < 2 * p_521`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPEC `m10 * &u + m11 * &v:int` p521signedredlemma)) THEN
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPEC `m00 * &u + m01 * &v:int` p521signedredlemma)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`usgn <=> m00 * &u + m01 * &v:int < &0`;
      `vsgn <=> m10 * &u + m11 * &v:int < &0`;
      `uq = (m00 * &u + m01 * &v) div &2 pow 521`;
      `vq = (m10 * &u + m11 * &v) div &2 pow 521`;
      `uq':int = if usgn then uq - &1 else uq`;
      `vq':int = if vsgn then vq - &1 else vq`] THEN
    STRIP_TAC THEN STRIP_TAC THEN

    SUBGOAL_THEN
     `&(bignum_of_wordlist
          [sum_s484; sum_s486; sum_s489; sum_s490; sum_s493;
           sum_s494; sum_s497; sum_s498; sum_s500]):int =
      (m00 * &u + m01 * &v) - uq' * &p_521 /\
      &(bignum_of_wordlist
          [sum_s520; sum_s522; sum_s525; sum_s526; sum_s529;
           sum_s530; sum_s533; sum_s534; sum_s536]):int =
      (m10 * &u + m11 * &v) - vq' * &p_521`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
         `e * f:int = x
          ==> coprime(e,p) /\
              (f' * n * e * t == x) (mod p)
          ==> (f == n * t * (f' - q * p)) (mod p)`)) THEN
        (CONJ_TAC THENL
          [REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_coprime] THEN
           REWRITE_TAC[COPRIME_LEXP; p_521; ARITH_EQ] THEN
           CONV_TAC COPRIME_CONV;
           REWRITE_TAC[GSYM INT_POW_ADD]]) THEN
        ASM_SIMP_TAC[ARITH_RULE
         `i < 20 ==> (59 + 59 * (21 - (i + 1))) = 59 * (21 - i)`] THEN
        MAP_EVERY UNDISCH_TAC
         [`(divstep_f (59 * i) t == &n * &2 pow (59 * (21 - i)) * &u)
           (mod &p_521)`;
          `(divstep_g (59 * i) t == &n * &2 pow (59 * (21 - i)) * &v)
           (mod &p_521)`] THEN
        CONV_TAC INTEGER_RULE;
        ALL_TAC] THEN
      DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["uq'"; "uq"; "usgn"] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `m01:int = &0` SUBST1_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `(mm:int^2^2)$1$2 = m01`));
        REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; p_521] THEN
        INT_ARITH_TAC] THEN
      EXPAND_TAC "mm" THEN MATCH_MP_TAC DIVSTEP_MAT_DIAGONAL_1 THEN
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
        EXPAND_TAC "g" THEN BOUNDER_TAC[]]] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN
    EXISTS_TAC `(&2:int) pow 576` THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC(INT_ARITH
        `&x:int < p /\ &0 <= y /\ y < p ==> abs(&x - y) < p`) THEN
       CONJ_TAC THENL
        [REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN BOUNDER_TAC[]; ALL_TAC] THEN
       ASM_REWRITE_TAC[] THEN
       TRANS_TAC INT_LTE_TRANS `&2 * &p_521:int` THEN
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[p_521] THEN INT_ARITH_TAC;
       ALL_TAC]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(y':int == y) (mod q) ==>  p divides q /\ (x == y' - z) (mod p)
      ==> (x == y - z) (mod p)`)) THEN
    SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THENL

    (*** The two actual modular reductions ***)

     [ABBREV_TAC `qu:int64 =
        word_add (word_subword
                  ((word_join:int64->int64->int128) sum_s479 sum_s478) (9,64))
                 (word_ishr sum_s479 63)` THEN

      SUBGOAL_THEN
       `word_subword ((word_join:int64->int64->int128) sum_s479 sum_s478)
                     (9,64):int64 =
        word(uup DIV 2 EXP 521)`
      SUBST_ALL_TAC THENL
       [EXPAND_TAC "uup" THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[word_subword; VAL_WORD_JOIN; WORD_EQ] THEN
        REWRITE_TAC[CONG; DIMINDEX_64; DIMINDEX_128; MOD_MOD_REFL] THEN
        SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
         `v < 2 EXP 64 /\ w < 2 EXP 64 ==> 2 EXP 64 * v + w < 2 EXP 128`] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `word_ishr (sum_s479:int64) 63 = word_neg(word(bitval usgn))`
      SUBST_ALL_TAC THENL
       [REWRITE_TAC[ARITH_RULE `63 = 64 - 1`; GSYM DIMINDEX_64;
                    WORD_ISHR_MSB] THEN
        REPLICATE_TAC 3 AP_TERM_TAC THEN REWRITE_TAC[MSB_VAL] THEN
        MP_TAC(SPECL [`640`; `uup:num`; `m00 * &u + m01 * &v:int`]
            TWOS_COMPLEMENT) THEN
        ASM_REWRITE_TAC[ARITH_EQ; DIMINDEX_64] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
        REWRITE_TAC[ARITH_RULE
         `2 EXP 639 <= n <=> ~(n DIV 2 EXP 639 = 0)`] THEN
        EXPAND_TAC "uup" THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [BOUNDER_TAC []; ALL_TAC] THEN
          UNDISCH_TAC `abs(m00 * &u + m01 * &v:int) <= &2 pow 582` THEN
          CONV_TAC INT_ARITH;
          SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0; NOT_LT]];
        ALL_TAC] THEN
      SUBGOAL_THEN `word(uup DIV 2 EXP 521):int64 = iword uq`
      SUBST_ALL_TAC THENL
       [EXPAND_TAC "uq" THEN
        REWRITE_TAC[WORD_IWORD; GSYM INT_OF_NUM_DIV;
                    GSYM INT_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[IWORD_EQ] THEN MATCH_MP_TAC INT_CONG_DIV2 THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] INT_CONG_INT_DIVIDES_MODULUS)) THEN
        REWRITE_TAC[GSYM INT_POW_ADD; DIMINDEX_64] THEN
        MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `word_add (iword uq) (word_neg (word (bitval usgn))):int64 =
        iword uq'`
      SUBST_ALL_TAC THENL
       [EXPAND_TAC "uq'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC WORD_RULE;
        FIRST_ASSUM(MP_TAC o AP_TERM `ival:int64->int`)] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
        ASM_SIMP_TAC[INT_ARITH
         `abs(x:int) < &2 pow 62 ==> --(&2 pow 63) <= x /\ x < &2 pow 63`];
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[IVAL_VAL] THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ;
                  INT_POW_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN EXPAND_TAC "uup" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        fst o chop_list 10 o snd o chop_list 105 o rev) THEN
      MP_TAC(ISPEC `qu:int64` WORD_ISHR_MSB) THEN
      REWRITE_TAC[DIMINDEX_64; p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_VAL_WORD_MASK] THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[VAL_WORD_SHL; GSYM REAL_OF_NUM_CLAUSES;
                  REAL_OF_NUM_MOD; DIMINDEX_64; REAL_VAL_WORD_MASK] THEN
      REAL_INTEGER_TAC;

      ABBREV_TAC `qv:int64 =
        word_add (word_subword
                  ((word_join:int64->int64->int128) sum_s515 sum_s514) (9,64))
                 (word_ishr sum_s515 63)` THEN

      SUBGOAL_THEN
       `word_subword ((word_join:int64->int64->int128) sum_s515 sum_s514)
                     (9,64):int64 =
        word(vup DIV 2 EXP 521)`
      SUBST_ALL_TAC THENL
       [EXPAND_TAC "vup" THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[word_subword; VAL_WORD_JOIN; WORD_EQ] THEN
        REWRITE_TAC[CONG; DIMINDEX_64; DIMINDEX_128; MOD_MOD_REFL] THEN
        SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
         `v < 2 EXP 64 /\ w < 2 EXP 64 ==> 2 EXP 64 * v + w < 2 EXP 128`] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `word_ishr (sum_s515:int64) 63 = word_neg(word(bitval vsgn))`
      SUBST_ALL_TAC THENL
       [REWRITE_TAC[ARITH_RULE `63 = 64 - 1`; GSYM DIMINDEX_64;
                    WORD_ISHR_MSB] THEN
        REPLICATE_TAC 3 AP_TERM_TAC THEN REWRITE_TAC[MSB_VAL] THEN
        MP_TAC(SPECL [`640`; `vup:num`; `m10 * &u + m11 * &v:int`]
            TWOS_COMPLEMENT) THEN
        ASM_REWRITE_TAC[ARITH_EQ; DIMINDEX_64] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
        REWRITE_TAC[ARITH_RULE
         `2 EXP 639 <= n <=> ~(n DIV 2 EXP 639 = 0)`] THEN
        EXPAND_TAC "vup" THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [BOUNDER_TAC []; ALL_TAC] THEN
          UNDISCH_TAC `abs(m10 * &u + m11 * &v:int) <= &2 pow 582` THEN
          CONV_TAC INT_ARITH;
          SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0; NOT_LT]];
        ALL_TAC] THEN
      SUBGOAL_THEN `word(vup DIV 2 EXP 521):int64 = iword vq`
      SUBST_ALL_TAC THENL
       [EXPAND_TAC "vq" THEN
        REWRITE_TAC[WORD_IWORD; GSYM INT_OF_NUM_DIV;
                    GSYM INT_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[IWORD_EQ] THEN MATCH_MP_TAC INT_CONG_DIV2 THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] INT_CONG_INT_DIVIDES_MODULUS)) THEN
        REWRITE_TAC[GSYM INT_POW_ADD; DIMINDEX_64] THEN
        MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `word_add (iword vq) (word_neg (word (bitval vsgn))):int64 =
        iword vq'`
      SUBST_ALL_TAC THENL
       [EXPAND_TAC "vq'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC WORD_RULE;
        FIRST_ASSUM(MP_TAC o AP_TERM `ival:int64->int`)] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
        ASM_SIMP_TAC[INT_ARITH
         `abs(x:int) < &2 pow 62 ==> --(&2 pow 63) <= x /\ x < &2 pow 63`];
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[IVAL_VAL] THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ;
                  INT_POW_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN EXPAND_TAC "vup" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        rev o fst o chop_list 10) THEN
      MP_TAC(ISPEC `qv:int64` WORD_ISHR_MSB) THEN
      REWRITE_TAC[DIMINDEX_64; p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_VAL_WORD_MASK] THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[VAL_WORD_SHL; GSYM REAL_OF_NUM_CLAUSES;
                  REAL_OF_NUM_MOD; DIMINDEX_64; REAL_VAL_WORD_MASK] THEN
      REAL_INTEGER_TAC];

    (*** Because of the peculiar loop structure, completely trivial ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ARM_SIM_TAC CORE_INV_P521_EXEC [] THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (*** Start on the tail computation, with similar divstep reasoning ***)

  CONV_TAC(DEPTH_CONV NUM_SUB_CONV) THEN
  REWRITE_TAC[ARITH_RULE `59 * 20 = 1180`] THEN
  GHOST_INTRO_TAC `f:num` `read (memory :> bytes (stackpointer,8 * 9))` THEN
  GHOST_INTRO_TAC `g:num`
   `read (memory :> bytes (word_add stackpointer (word 72),8 * 9))` THEN
  GHOST_INTRO_TAC `u:num`
   `read (memory :> bytes (word_add stackpointer (word 144),8 * 9))` THEN
  GHOST_INTRO_TAC `v:num`
   `read (memory :> bytes (word_add stackpointer (word 216),8 * 9))` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `9`) [`f:num`; `g:num`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "f_"
   `read (memory :> bytes(stackpointer,8 * 9)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "g_"
   `read (memory :> bytes(word_add stackpointer (word 72),8 * 9)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "u_"
   `read (memory :> bytes(word_add stackpointer (word 144),8 * 9)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "v_"
   `read (memory :> bytes(word_add stackpointer (word 216),8 * 9)) s0` THEN
  ARM_STEPS_TAC CORE_INV_P521_EXEC (1--3) THEN
  MP_TAC(SPECL
   [`iword (divstep_d 1180 t):int64`;
    `f_0:int64`; `g_0:int64`; `pc:num`]
   LOCAL_WORD_DIVSTEP59_CORRECT) THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC CORE_INV_P521_EXEC "s4" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN

  SUBGOAL_THEN `abs(divstep_d 1180 t) < &2 pow 62` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN W(MP_TAC o
     PART_MATCH (lhand o rand o lhand) DIVSTEP_D_BOUND o lhand o snd) THEN
    MATCH_MP_TAC(INT_ARITH
     `e:int < &1181
      ==> abs(x - abs(&1)) <= &2 * e ==> x < &2 pow 62`) THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(iword(divstep_d 1180 t):int64) = divstep_d 1180 t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN

  ANTS_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[DIVSTEP_D_PARITY] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    TRANS_TAC EQ_TRANS `divstep_f 1180 t rem &2` THEN
    EXPAND_TAC "t" THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[INT_REM_EQ];
      MATCH_MP_TAC DIVSTEP_F_ODD THEN REWRITE_TAC[p_521] THEN
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
   `divstep_d 59 (divstep_d 1180 t,ival(f_0:int64),ival(g_0:int64)) =
    divstep_d 1239 t`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1239 = 59 + 1180`] THEN
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
           (divstep_d 1180 t,ival(f_0:int64),ival(g_0:int64))`;
    `m00 = (mm:int^2^2)$1$1`;
    `m01 = (mm:int^2^2)$1$2`;
    `m10 = (mm:int^2^2)$2$1`;
    `m11 = (mm:int^2^2)$2$2`] THEN
  STRIP_TAC THEN

  (*** Complete all the simulation first ***)

  ARM_ACCSTEPS_TAC CORE_INV_P521_EXEC
   [31;34;36;37;40;42;44;47;49;50;53;55;57;60;62;63;66;
    68;70;73;75;76;79;81;83;86;88;89;92;94;96;99;101;102;
    105;107;109;112;114;115;118;120;122;125;127;128;131;133;
    135;140;142;143;147;148;150;151;155;156;158;160;161;163;
    164;166;167;168;169;170;171;172;173;174;175;176;178]
   (5--192) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s192" THEN

  (*** Deploy the divstep bound to deduce g = 0 ***)

  MP_TAC(SPECL [`&p_521:int`; `&n rem &p_521`; `521`; `1239`]
        IDIVSTEP_ENDTOEND_BITS_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[p_521] THEN INT_ARITH_TAC;
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
     [`divstep_d 1180 t`; `divstep_f 1180 t`; `divstep_g 1180 t`;
      `59`] DIVSTEP_MAT) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC DIVSTEP_F_ODD THEN
    REWRITE_TAC[p_521] THEN CONV_TAC INT_REDUCE_CONV;
    GEN_REWRITE_TAC LAND_CONV [CART_EQ]] THEN
  SIMP_TAC[DIMINDEX_2; FORALL_2; imat_vmul; VECTOR_2;
           ISUM_2; LAMBDA_BETA; ARITH] THEN
  SUBGOAL_THEN
   `divstep_mat 59 (divstep_d 1180 t,divstep_f 1180 t,divstep_g 1180 t) = mm`
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
      [sum_s42;sum_s55;sum_s68;sum_s81;sum_s94;sum_s107;sum_s120;
       sum_s133;sum_s150;sum_s151]` THEN
  SUBGOAL_THEN
   `(&uup:int ==
     --(&1) pow bitval bsgn *
     (m00 * &u + m01 * &v)) (mod (&2 pow 640))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INT_POW_NEG; EVEN_BITVAL; COND_SWAP; INT_POW_ONE] THEN
    MAP_EVERY
     (SUBST1_TAC o C SPEC
       (INT_ARITH `!m:int. m = if m < &0 then --(abs m) else abs m`))
     [`m00:int`; `m01:int`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev o
        snd o chop_list 19) THEN
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
      fst o chop_list 19) THEN
    STRIP_TAC] THEN

  (*** The basic modular reduction mathematics ***)

  ABBREV_TAC `fsgn:int = -- &1 pow bitval bsgn` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SUBGOAL_THEN `abs(fsgn * (m00 * &u + m01 * &v):int) <= &2 pow 582`
  ASSUME_TAC THENL
   [EXPAND_TAC "fsgn" THEN
    REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NEG; INT_POW_ONE;
                INT_ABS_NUM; INT_MUL_LID] THEN
    MATCH_MP_TAC(INT_ARITH
     `abs(x) <= &2 pow 59 * &2 pow 522 /\
      abs(y) <= &2 pow 59 * &2 pow 522
      ==> abs(x + y:int) <= &2 pow 582`) THEN
    REWRITE_TAC[INT_ABS_MUL] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL2 THEN
    ASM_REWRITE_TAC[INT_ABS_NUM; INT_POS; INT_ABS_POS] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    MAP_EVERY UNDISCH_TAC [`u < 2 * p_521`; `v < 2 * p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (SPEC `fsgn * (m00 * &u + m01 * &v):int` p521signedredlemma)) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
   [`usgn <=> fsgn * (m00 * &u + m01 * &v):int < &0`;
    `uq = (fsgn * (m00 * &u + m01 * &v)) div &2 pow 521`;
    `uq':int = if usgn then uq - &1 else uq`] THEN
  STRIP_TAC THEN

  SUBGOAL_THEN
   `word_subword ((word_join:int64->int64->int128) sum_s151 sum_s150)
                 (9,64):int64 =
    word(uup DIV 2 EXP 521)`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "uup" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[word_subword; VAL_WORD_JOIN; WORD_EQ] THEN
    REWRITE_TAC[CONG; DIMINDEX_64; DIMINDEX_128; MOD_MOD_REFL] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
     `v < 2 EXP 64 /\ w < 2 EXP 64 ==> 2 EXP 64 * v + w < 2 EXP 128`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `bit 63 (sum_s151:int64) <=> usgn` SUBST_ALL_TAC THENL
   [REWRITE_TAC[ARITH_RULE `63 = 64 - 1`; GSYM DIMINDEX_64; MSB_VAL] THEN
    MP_TAC(SPECL [`640`; `uup:num`; `fsgn * (m00 * &u + m01 * &v):int`]
        TWOS_COMPLEMENT) THEN
    ASM_REWRITE_TAC[ARITH_EQ; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    REWRITE_TAC[ARITH_RULE
     `2 EXP 639 <= n <=> ~(n DIV 2 EXP 639 = 0)`] THEN
    EXPAND_TAC "uup" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [BOUNDER_TAC []; ALL_TAC] THEN
      UNDISCH_TAC `abs(fsgn * (m00 * &u + m01 * &v):int) <= &2 pow 582` THEN
      CONV_TAC INT_ARITH;
      SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0; NOT_LT]];
    ALL_TAC] THEN

  SUBGOAL_THEN `word(uup DIV 2 EXP 521):int64 = iword uq`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "uq" THEN
    REWRITE_TAC[WORD_IWORD; GSYM INT_OF_NUM_DIV;
                GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[IWORD_EQ] THEN MATCH_MP_TAC INT_CONG_DIV2 THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] INT_CONG_INT_DIVIDES_MODULUS)) THEN
    REWRITE_TAC[GSYM INT_POW_ADD; DIMINDEX_64] THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  ABBREV_TAC
   `qu:int64 = word_add (iword uq) (word_neg (word (bitval usgn)))` THEN
  SUBGOAL_THEN
   `word_add (iword uq) (word_neg (word (bitval usgn))):int64 =
    iword uq'`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "uq'" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_RULE;
    FIRST_ASSUM(MP_TAC o AP_TERM `ival:int64->int`)] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    ASM_SIMP_TAC[INT_ARITH
     `abs(x:int) < &2 pow 62 ==> --(&2 pow 63) <= x /\ x < &2 pow 63`];
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST_ALL_TAC] THEN

  MP_TAC(SPEC `fsgn * (m00 * &u + m01 * &v) - ival(qu:int64) * &p_521`
        INT_OF_NUM_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `r:num` THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist
      [sum_s156; sum_s158; sum_s160; sum_s161; sum_s163;
       sum_s164; sum_s166;sum_s167; sum_s168] = r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 576` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      TRANS_TAC INT_LTE_TRANS `&2 * &p_521:int` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[p_521] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_congruent] THEN FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(y':int == y) (mod q) ==>  p divides q /\ (x == y' - z) (mod p)
      ==> (x == y - z) (mod p)`)) THEN
    SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[IVAL_VAL] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ;
                INT_POW_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN EXPAND_TAC "uup" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    MP_TAC(ISPEC `qu:int64` WORD_ISHR_MSB) THEN
    REWRITE_TAC[DIMINDEX_64; p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_VAL_WORD_MASK] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VAL_WORD_SHL; GSYM REAL_OF_NUM_CLAUSES;
                REAL_OF_NUM_MOD; DIMINDEX_64; REAL_VAL_WORD_MASK] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev o
      fst o chop_list 9) THEN
    STRIP_TAC] THEN

  TRANS_TAC EQ_TRANS `&(r MOD p_521):int` THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_CLAUSES; COND_SWAP] THEN RULE_ASSUM_TAC(REWRITE_RULE
     [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    SUBGOAL_THEN `carry_s178 <=> r < p_521` SUBST_ALL_TAC  THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
      EXPAND_TAC "r" THEN
      REWRITE_TAC[p_521; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN

    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 576` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&r:int < &2 * &p_521` THEN UNDISCH_TAC `p_521 <= r` THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; p_521] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN EXPAND_TAC "r" THEN
    REWRITE_TAC[bignum_of_wordlist; p_521; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Now finally handle the degenerate case ***)

  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      MP_TAC th THEN EXPAND_TAC "u" THEN SUBST_ALL_TAC th) THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         STRIP_ASSUME_TAC th) THEN
    SUBGOAL_THEN `m01:int = &0` SUBST_ALL_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(mm:int^2^2)$1$2 = m01`)) THEN
      EXPAND_TAC "mm" THEN MATCH_MP_TAC DIVSTEP_MAT_DIAGONAL_1 THEN
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
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_IWORD])] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[INT_REM_EQ_0] THEN INTEGER_TAC;
    ALL_TAC] THEN

  (*** Deploy non-triviality ***)

  SUBGOAL_THEN `coprime(p_521,n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P521]; ALL_TAC] THEN
  SUBGOAL_THEN `gcd(&p_521,&n rem &p_521) = &1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM INT_COPRIME_GCD; INT_COPRIME_RREM] THEN
    ASM_SIMP_TAC[GSYM num_coprime];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(&(val(word(val(word(val(f_0:int64) * val(iword m00:int64)):int64) +
                val(g_0:int64) * val(iword m01:int64)):int64)) ==
     &2 pow 59 * divstep_f 1239 t) (mod (&2 pow 64))`
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
    UNDISCH_TAC `abs (divstep_f 1239 t) = &1` THEN INT_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; GSYM MSB_VAL] THEN
  ASM_REWRITE_TAC[DIMINDEX_64; NUM_SUB_CONV `64 - 1`] THEN
  REWRITE_TAC[INT_ARITH `&2 pow 59 * x < &0 <=> x:int < &0`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN

  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&p_521:int` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `(&0 <= x /\ x < p) /\ (&0 <= y /\ y < p)
      ==> abs(x - y:int) < p`) THEN
    REWRITE_TAC[INT_LT_REM_EQ; INT_REM_POS_EQ; INT_POS] THEN
    REWRITE_TAC[INT_OF_NUM_LT; INVERSE_MOD_BOUND] THEN
    REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ]] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - q * p) (mod p) <=> (x == y) (mod p)`] THEN
  MATCH_MP_TAC INT_CONG_MUL_RCANCEL THEN EXISTS_TAC `&n:int` THEN
  REWRITE_TAC[GSYM num_coprime; INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC `&1:int` THEN
  ASM_REWRITE_TAC[GSYM num_congruent; INVERSE_MOD_LMUL_EQ] THEN

  SUBGOAL_THEN
   `(m00 * divstep_f 1180 t + m01 * divstep_g 1180 t ==
     m00 * &n * &2 pow (59 * 1) * &u +
     m01 * &n * &2 pow (59 * 1) * &v) (mod &p_521)`
  MP_TAC THENL
   [MATCH_MP_TAC INT_CONG_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC INT_CONG_LMUL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(e * d:int == m0 * n * e * u + m1 * n * e * v) (mod p)
    ==> coprime(e,p) ==> (d == (m0 * u + m1 * v) * n) (mod p)`)) THEN
  REWRITE_TAC[INT_COPRIME_LPOW; GSYM num_coprime; ARITH_EQ] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p_521] THEN CONV_TAC COPRIME_CONV; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (INT_ARITH
   `abs(x:int) = &1 ==> x = if x < &0 then -- &1 else &1`)) THEN
  EXPAND_TAC "fsgn" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  INTEGER_TAC);;

let BIGNUM_INV_P521_CORRECT = time prove
 (`!z x n pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,288))
            [(word pc,0x15ac); (z,8 * 9); (x,8 * 9)] /\
        nonoverlapping (word pc,0x15ac) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_inv_p521_mc /\
                  read PC s = word(pc + 0xc) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0x159c) /\
                  bignum_from_memory(z,9) s =
                  (if p_521 divides n then 0 else inverse_mod p_521 n))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17;
                      X19; X20; X21; X22] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(z,8 * 9);
                      memory :> bytes(stackpointer,288)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  ARM_SUBROUTINE_SIM_TAC
      (bignum_inv_p521_mc,BIGNUM_INV_P521_EXEC,0xc,
       (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p521_mc] THENC TRIM_LIST_CONV)
       `TRIM_LIST (12,16) bignum_inv_p521_mc`,
       CORE_INV_P521_CORRECT)
      [`read X0 s`; `read X1 s`;
       `read (memory :> bytes(read X1 s,8 * 9)) s`;
       `pc + 0xc`; `stackpointer:int64`] 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_INV_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 320),320))
            [word pc,0x15ac; z,8 * 9; x,8 * 9] /\
        nonoverlapping (word pc,0x15ac) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_inv_p521_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,9) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,9) s =
                  (if p_521 divides n then 0 else inverse_mod p_521 n))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                    memory :> bytes(word_sub stackpointer (word 320),320)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_INV_P521_EXEC BIGNUM_INV_P521_CORRECT
   `[X19;X20;X21;X22]` 320);;
