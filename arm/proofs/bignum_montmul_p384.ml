(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication modulo p_384.                                   *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/p384/bignum_montmul_p384.o";;
 ****)

let bignum_montmul_p384_mc =
  define_assert_from_elf "bignum_montmul_p384_mc" "arm/p384/bignum_montmul_p384.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xa9422027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&32))) *)
  0xa9402849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&0))) *)
  0xa941304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&16))) *)
  0xa942384d;       (* arm_LDP X13 X14 X2 (Immediate_Offset (iword (&32))) *)
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
  0xd3607df7;       (* arm_LSL X23 X15 (rvalue (word 32)) *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 (rvalue (word 32)) *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 (rvalue (word 32)) *)
  0xd360fed6;       (* arm_LSR X22 X22 (rvalue (word 32)) *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 (rvalue (word 32)) *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 (rvalue (word 32)) *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 (rvalue (word 32)) *)
  0xd360fed6;       (* arm_LSR X22 X22 (rvalue (word 32)) *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 (rvalue (word 32)) *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 (rvalue (word 32)) *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 (rvalue (word 32)) *)
  0xd360fed6;       (* arm_LSR X22 X22 (rvalue (word 32)) *)
  0xab1102d6;       (* arm_ADDS X22 X22 X17 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170273;       (* arm_SUBS X19 X19 X23 *)
  0xfa160294;       (* arm_SBCS X20 X20 X22 *)
  0xfa150021;       (* arm_SBCS X1 X1 X21 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xa9005013;       (* arm_STP X19 X20 X0 (Immediate_Offset (iword (&0))) *)
  0xa9013c01;       (* arm_STP X1 X15 X0 (Immediate_Offset (iword (&16))) *)
  0xa9024410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&32))) *)
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
  0xa9405815;       (* arm_LDP X21 X22 X0 (Immediate_Offset (iword (&0))) *)
  0xab1501ef;       (* arm_ADDS X15 X15 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xa9415815;       (* arm_LDP X21 X22 X0 (Immediate_Offset (iword (&16))) *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xa9425815;       (* arm_LDP X21 X22 X0 (Immediate_Offset (iword (&32))) *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0xba160021;       (* arm_ADCS X1 X1 X22 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xa900400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&0))) *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
  0xa9020414;       (* arm_STP X20 X1 X0 (Immediate_Offset (iword (&32))) *)
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
  0xa9401003;       (* arm_LDP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9411805;       (* arm_LDP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xa9422007;       (* arm_LDP X7 X8 X0 (Immediate_Offset (iword (&32))) *)
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
  0xd3607df7;       (* arm_LSL X23 X15 (rvalue (word 32)) *)
  0x8b0f02ef;       (* arm_ADD X15 X23 X15 *)
  0xd360fdf7;       (* arm_LSR X23 X15 (rvalue (word 32)) *)
  0xeb0f02f7;       (* arm_SUBS X23 X23 X15 *)
  0xda1f01f6;       (* arm_SBC X22 X15 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 (rvalue (word 32)) *)
  0xd360fed6;       (* arm_LSR X22 X22 (rvalue (word 32)) *)
  0xab0f02d6;       (* arm_ADDS X22 X22 X15 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170210;       (* arm_SUBS X16 X16 X23 *)
  0xfa160231;       (* arm_SBCS X17 X17 X22 *)
  0xfa150273;       (* arm_SBCS X19 X19 X21 *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e17;       (* arm_LSL X23 X16 (rvalue (word 32)) *)
  0x8b1002f0;       (* arm_ADD X16 X23 X16 *)
  0xd360fe17;       (* arm_LSR X23 X16 (rvalue (word 32)) *)
  0xeb1002f7;       (* arm_SUBS X23 X23 X16 *)
  0xda1f0216;       (* arm_SBC X22 X16 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 (rvalue (word 32)) *)
  0xd360fed6;       (* arm_LSR X22 X22 (rvalue (word 32)) *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9a1f03f5;       (* arm_ADC X21 XZR XZR *)
  0xeb170231;       (* arm_SUBS X17 X17 X23 *)
  0xfa160273;       (* arm_SBCS X19 X19 X22 *)
  0xfa150294;       (* arm_SBCS X20 X20 X21 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e37;       (* arm_LSL X23 X17 (rvalue (word 32)) *)
  0x8b1102f1;       (* arm_ADD X17 X23 X17 *)
  0xd360fe37;       (* arm_LSR X23 X17 (rvalue (word 32)) *)
  0xeb1102f7;       (* arm_SUBS X23 X23 X17 *)
  0xda1f0236;       (* arm_SBC X22 X17 XZR *)
  0x93d782d7;       (* arm_EXTR X23 X22 X23 (rvalue (word 32)) *)
  0xd360fed6;       (* arm_LSR X22 X22 (rvalue (word 32)) *)
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
  0xd3607ed5;       (* arm_LSL X21 X22 (rvalue (word 32)) *)
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
  0xa9005013;       (* arm_STP X19 X20 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012401;       (* arm_STP X1 X9 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_P384_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

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

let BIGNUM_MONTMUL_P384_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x600) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_mc /\
                  read PC s = word(pc + 0xc) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + 0x5f0) /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTMUL_P384_EXEC (1--377)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN

 (*** First ADK block multiplying lower halves.
  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** the three Montgomery steps on the low half ***)

  montred_tac BIGNUM_MONTMUL_P384_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 68 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 83 THEN
  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 98 THEN

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_EXEC (114--116) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** First absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Second absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Collective sign-magnitude representation  of middle product ***)

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_EXEC [201] THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC (202--214) (202--214) THEN
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Third and final ADK block computing the mid-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Big net accumulation computation absorbing cases over sign ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    BOOL_CASES_TAC `msgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_XOR_NOT; WORD_XOR_0;
                SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Last three Montgomery steps to get the pre-reduced result ***)

  montred_tac BIGNUM_MONTMUL_P384_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 303 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 318 THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 333 THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC (349--352) (349--352) THEN

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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC (357--362) (353--362) THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
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

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_EXEC [363] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM NOT_LT; COND_SWAP; GSYM WORD_MASK;
    SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN

  (*** The final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTMUL_P384_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x600) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x600); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
           (\s. read PC s = returnaddress /\
                (a * b <= 2 EXP 384 * p_384
                 ==> bignum_from_memory (z,6) s =
                     (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_EXEC BIGNUM_MONTMUL_P384_CORRECT
   `[X19;X20;X21;X22;X23;X24]` 48);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 384 bits, may then not be fully reduced mod p_384.  *)
(* ------------------------------------------------------------------------- *)

let p384genshortredlemma = prove
 (`!n. n < 3 * 2 EXP 384
       ==> let q = (n DIV 2 EXP 384) + 1 in
           q <= 3 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let BIGNUM_AMONTMUL_P384_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x600) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_mc /\
                  read PC s = word(pc + 0xc) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + 0x5f0) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN

 (*** First ADK block multiplying lower halves.
  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** the three Montgomery steps on the low half ***)

  montred_tac BIGNUM_MONTMUL_P384_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 68 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 83 THEN
  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 98 THEN

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_EXEC (114--116) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** First absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Second absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Collective sign-magnitude representation  of middle product ***)

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_EXEC [201] THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC (202--214) (202--214) THEN
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Third and final ADK block computing the mid-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o
      DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Big net accumulation computation absorbing cases over sign ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    BOOL_CASES_TAC `msgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_XOR_NOT; WORD_XOR_0;
                SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Last three Montgomery steps to get the pre-reduced result ***)

  montred_tac BIGNUM_MONTMUL_P384_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 303 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 318 THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 333 THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC (349--352) (349--352) THEN

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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  SUBGOAL_THEN
   `t < 3 * 2 EXP 384 /\ (2 EXP 384 * t == a * b) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
    MATCH_MP_TAC(ARITH_RULE
     `2 EXP 384 * x < 2 EXP 768 * 3 ==> x < 3 * 2 EXP 384`) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Quotient approximation computation and main property ***)

  ABBREV_TAC `h = t DIV 2 EXP 384` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 3 * 2 EXP 384` THEN EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s352:int64 = word h` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "t"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:num` p384genshortredlemma) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC (357--362) (353--362) THEN
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
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
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

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_EXEC [363] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM NOT_LT; COND_SWAP; GSYM WORD_MASK;
    SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN

  (*** The final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_EXEC
   [366;368;371;372;373;374] (364--377) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[CONG; MOD_MOD_REFL]
    `x = y MOD n ==> (x == y) (mod n)`) THEN
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
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTMUL_P384_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x600) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x600); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
           (\s. read PC s = returnaddress /\
                (bignum_from_memory (z,6) s ==
                 inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_EXEC BIGNUM_AMONTMUL_P384_CORRECT
   `[X19;X20;X21;X22;X23;X24]` 48);;
