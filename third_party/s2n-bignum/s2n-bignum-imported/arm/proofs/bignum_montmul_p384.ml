(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication modulo p_384.                                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(**** print_literal_from_elf "arm/p384/unopt/bignum_montmul_p384_base.o";;
 ****)

let bignum_montmul_p384_unopt_mc =
  define_assert_from_elf "bignum_montmul_p384_unopt_mc" "arm/p384/unopt/bignum_montmul_p384_base.o"
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

let BIGNUM_MONTMUL_P384_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p384_unopt_mc;;

(* bignum_montmul_p384_unopt_mc without ret. *)
let bignum_montmul_p384_unopt_core_mc_def,
    bignum_montmul_p384_unopt_core_mc,
    BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p384_unopt_core_mc"
    bignum_montmul_p384_unopt_mc
    (`12`,`LENGTH bignum_montmul_p384_unopt_mc - 28`)
    (fst BIGNUM_MONTMUL_P384_UNOPT_EXEC);;

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

let BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_unopt_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_unopt_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p384_unopt_core_mc) /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (1--377)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN

 (*** First ADK block multiplying lower halves.
  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  montred_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 68 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 83 THEN
  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 98 THEN

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (114--116) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC [201] THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (202--214) (202--214) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  montred_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 303 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 318 THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 333 THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (349--352) (349--352) THEN

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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (357--362) (353--362) THEN
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

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC [363] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM NOT_LT; COND_SWAP; GSYM WORD_MASK;
    SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN

  (*** The final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

let BIGNUM_MONTMUL_P384_UNOPT_CORRECT = time prove(
  `!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_unopt_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_unopt_mc /\
                  read PC s = word (pc+12) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + (12+LENGTH bignum_montmul_p384_unopt_core_mc)) /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT
    bignum_montmul_p384_unopt_core_mc_def
    [fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC;fst BIGNUM_MONTMUL_P384_UNOPT_EXEC]);;

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

let BIGNUM_AMONTMUL_P384_UNOPT_CORE_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_unopt_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_unopt_core_mc /\
                  read PC s = word(pc) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p384_unopt_core_mc) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN

 (*** First ADK block multiplying lower halves.
  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  montred_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 68 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 83 THEN
  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 98 THEN

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (114--116) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC [201] THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (202--214) (202--214) THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

  montred_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X15;X1;X20;X19;X17;X16;X15; X21;X22;X23]` 303 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X16;X15;X1;X20;X19;X17;X16; X21;X22;X23]` 318 THEN

  montred_subst_tac BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
   `[X17;X16;X15;X1;X20;X19;X17; X21;X22;X23]` 333 THEN

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (349--352) (349--352) THEN

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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC (357--362) (353--362) THEN
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

  ARM_STEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC [363] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM NOT_LT; COND_SWAP; GSYM WORD_MASK;
    SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN

  (*** The final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
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

let BIGNUM_AMONTMUL_P384_UNOPT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_unopt_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_unopt_mc /\
                  read PC s = word(pc + 12) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + (12 + LENGTH bignum_montmul_p384_unopt_core_mc)) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTMUL_P384_UNOPT_CORE_CORRECT
      bignum_montmul_p384_unopt_core_mc_def
      [fst BIGNUM_MONTMUL_P384_UNOPT_EXEC;fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC]);;


(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-scheduled program
******************************************************************************)

(* This is the intermediate program that is equivalent to both
   bignum_montmul_p384_base and bignum_montmul_p384. This is a vectorized
   version of bignum_montmul_p384_base but instructions are unscheduled. *)

let bignum_montmul_p384_interm1_ops:int list = [
  0xa9bf53f3; (* stp    x19, x20, [sp, #-16]! *)
  0xa9bf5bf5; (* stp    x21, x22, [sp, #-16]! *)
  0xa9bf63f7; (* stp    x23, x24, [sp, #-16]! *)
  0xa9405423; (* ldp    x3, x21, [x1] *)
  0x3dc0003e; (* ldr    q30, [x1] *)
  0xa9416028; (* ldp    x8, x24, [x1, #16] *)
  0xa9422825; (* ldp    x5, x10, [x1, #32] *)
  0xa9405c4d; (* ldp    x13, x23, [x2] *)
  0x3dc00053; (* ldr    q19, [x2] *)
  0xa9413846; (* ldp    x6, x14, [x2, #16] *)
  0xa942444f; (* ldp    x15, x17, [x2, #32] *)
  0x3dc00821; (* ldr    q1, [x1, #32] *)
  0x3dc0085c; (* ldr    q28, [x2, #32] *)
  0x4e9e1a65; (* uzp1   v5.4s, v19.4s, v30.4s *)
  0x4ea00a73; (* rev64  v19.4s, v19.4s *)
  0x4e9e1bc0; (* uzp1   v0.4s, v30.4s, v30.4s *)
  0x4ebe9e75; (* mul    v21.4s, v19.4s, v30.4s *)
  0x6ea02ab3; (* uaddlp v19.2d, v21.4s *)
  0x4f605673; (* shl    v19.2d, v19.2d, #32 *)
  0x2ea58013; (* umlal  v19.2d, v0.2s, v5.2s *)
  0x4e083e6c; (* mov    x12, v19.d[0] *)
  0x4e183e70; (* mov    x16, v19.d[1] *)
  0x9b067d14; (* mul    x20, x8, x6 *)
  0x9bcd7c64; (* umulh  x4, x3, x13 *)
  0x9bd77ea1; (* umulh  x1, x21, x23 *)
  0x9bc67d02; (* umulh  x2, x8, x6 *)
  0xab100084; (* adds   x4, x4, x16 *)
  0xba140033; (* adcs   x19, x1, x20 *)
  0x9a1f0054; (* adc    x20, x2, xzr *)
  0xab0c008b; (* adds   x11, x4, x12 *)
  0xba040270; (* adcs   x16, x19, x4 *)
  0xba130281; (* adcs   x1, x20, x19 *)
  0x9a1f0282; (* adc    x2, x20, xzr *)
  0xab0c0207; (* adds   x7, x16, x12 *)
  0xba040024; (* adcs   x4, x1, x4 *)
  0xba130049; (* adcs   x9, x2, x19 *)
  0x9a1f0293; (* adc    x19, x20, xzr *)
  0xeb150062; (* subs   x2, x3, x21 *)
  0xda822454; (* cneg   x20, x2, cc  // cc = lo, ul, last *)
  0xda9f23f0; (* csetm  x16, cc  // cc = lo, ul, last *)
  0xeb0d02e2; (* subs   x2, x23, x13 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e81; (* mul    x1, x20, x2 *)
  0x9bc27e82; (* umulh  x2, x20, x2 *)
  0xda902210; (* cinv   x16, x16, cc  // cc = lo, ul, last *)
  0xca100021; (* eor    x1, x1, x16 *)
  0xca100042; (* eor    x2, x2, x16 *)
  0xb100061f; (* cmn    x16, #0x1 *)
  0xba01016b; (* adcs   x11, x11, x1 *)
  0xba0200e7; (* adcs   x7, x7, x2 *)
  0xba100084; (* adcs   x4, x4, x16 *)
  0xba100129; (* adcs   x9, x9, x16 *)
  0x9a100273; (* adc    x19, x19, x16 *)
  0xeb080062; (* subs   x2, x3, x8 *)
  0xda822454; (* cneg   x20, x2, cc  // cc = lo, ul, last *)
  0xda9f23f0; (* csetm  x16, cc  // cc = lo, ul, last *)
  0xeb0d00c2; (* subs   x2, x6, x13 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e81; (* mul    x1, x20, x2 *)
  0x9bc27e82; (* umulh  x2, x20, x2 *)
  0xda902210; (* cinv   x16, x16, cc  // cc = lo, ul, last *)
  0xca100021; (* eor    x1, x1, x16 *)
  0xca100042; (* eor    x2, x2, x16 *)
  0xb100061f; (* cmn    x16, #0x1 *)
  0xba0100e7; (* adcs   x7, x7, x1 *)
  0xba020084; (* adcs   x4, x4, x2 *)
  0xba100129; (* adcs   x9, x9, x16 *)
  0x9a100273; (* adc    x19, x19, x16 *)
  0xeb0802a2; (* subs   x2, x21, x8 *)
  0xda822454; (* cneg   x20, x2, cc  // cc = lo, ul, last *)
  0xda9f23f0; (* csetm  x16, cc  // cc = lo, ul, last *)
  0xeb1700c2; (* subs   x2, x6, x23 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e81; (* mul    x1, x20, x2 *)
  0x9bc27e82; (* umulh  x2, x20, x2 *)
  0xda902210; (* cinv   x16, x16, cc  // cc = lo, ul, last *)
  0xca100021; (* eor    x1, x1, x16 *)
  0xca100042; (* eor    x2, x2, x16 *)
  0xb100061f; (* cmn    x16, #0x1 *)
  0xba010084; (* adcs   x4, x4, x1 *)
  0xba020134; (* adcs   x20, x9, x2 *)
  0x9a100270; (* adc    x16, x19, x16 *)
  0xd3607d82; (* lsl    x2, x12, #32 *)
  0x8b0c0053; (* add    x19, x2, x12 *)
  0xd360fe62; (* lsr    x2, x19, #32 *)
  0xeb130041; (* subs   x1, x2, x19 *)
  0xda1f0262; (* sbc    x2, x19, xzr *)
  0x93c18041; (* extr   x1, x2, x1, #32 *)
  0xd360fc42; (* lsr    x2, x2, #32 *)
  0xab13004c; (* adds   x12, x2, x19 *)
  0x9a1f03e2; (* adc    x2, xzr, xzr *)
  0xeb010161; (* subs   x1, x11, x1 *)
  0xfa0c00e7; (* sbcs   x7, x7, x12 *)
  0xfa020084; (* sbcs   x4, x4, x2 *)
  0xfa1f0294; (* sbcs   x20, x20, xzr *)
  0xfa1f0210; (* sbcs   x16, x16, xzr *)
  0xda1f0269; (* sbc    x9, x19, xzr *)
  0xd3607c22; (* lsl    x2, x1, #32 *)
  0x8b010053; (* add    x19, x2, x1 *)
  0xd360fe62; (* lsr    x2, x19, #32 *)
  0xeb130041; (* subs   x1, x2, x19 *)
  0xda1f0262; (* sbc    x2, x19, xzr *)
  0x93c18041; (* extr   x1, x2, x1, #32 *)
  0xd360fc42; (* lsr    x2, x2, #32 *)
  0xab13004c; (* adds   x12, x2, x19 *)
  0x9a1f03e2; (* adc    x2, xzr, xzr *)
  0xeb0100e1; (* subs   x1, x7, x1 *)
  0xfa0c0084; (* sbcs   x4, x4, x12 *)
  0xfa020294; (* sbcs   x20, x20, x2 *)
  0xfa1f0210; (* sbcs   x16, x16, xzr *)
  0xfa1f0127; (* sbcs   x7, x9, xzr *)
  0xda1f0269; (* sbc    x9, x19, xzr *)
  0xd3607c22; (* lsl    x2, x1, #32 *)
  0x8b010053; (* add    x19, x2, x1 *)
  0xd360fe62; (* lsr    x2, x19, #32 *)
  0xeb130041; (* subs   x1, x2, x19 *)
  0xda1f0262; (* sbc    x2, x19, xzr *)
  0x93c1804c; (* extr   x12, x2, x1, #32 *)
  0xd360fc42; (* lsr    x2, x2, #32 *)
  0xab130041; (* adds   x1, x2, x19 *)
  0x9a1f03e2; (* adc    x2, xzr, xzr *)
  0xeb0c0084; (* subs   x4, x4, x12 *)
  0xfa010294; (* sbcs   x20, x20, x1 *)
  0xfa020210; (* sbcs   x16, x16, x2 *)
  0xfa1f00ec; (* sbcs   x12, x7, xzr *)
  0xfa1f0121; (* sbcs   x1, x9, xzr *)
  0xda1f0262; (* sbc    x2, x19, xzr *)
  0xa9005004; (* stp    x4, x20, [x0] *)
  0xa9013010; (* stp    x16, x12, [x0, #16] *)
  0xa9020801; (* stp    x1, x2, [x0, #32] *)
  0x9b0e7f16; (* mul    x22, x24, x14 *)
  0x6f00e5ff; (* movi   v31.2d, #0xffffffff *)
  0x4e9c5b90; (* uzp2   v16.4s, v28.4s, v28.4s *)
  0x0ea12826; (* xtn    v6.2s, v1.2d *)
  0x0ea12b9e; (* xtn    v30.2s, v28.2d *)
  0x4ea00b9c; (* rev64  v28.4s, v28.4s *)
  0x2ebec0c5; (* umull  v5.2d, v6.2s, v30.2s *)
  0x2eb0c0c0; (* umull  v0.2d, v6.2s, v16.2s *)
  0x4e815833; (* uzp2   v19.4s, v1.4s, v1.4s *)
  0x4ea19f94; (* mul    v20.4s, v28.4s, v1.4s *)
  0x6f6014a0; (* usra   v0.2d, v5.2d, #32 *)
  0x2eb0c261; (* umull  v1.2d, v19.2s, v16.2s *)
  0x6ea02a98; (* uaddlp v24.2d, v20.4s *)
  0x4e3f1c05; (* and    v5.16b, v0.16b, v31.16b *)
  0x2ebe8265; (* umlal  v5.2d, v19.2s, v30.2s *)
  0x4f605713; (* shl    v19.2d, v24.2d, #32 *)
  0x6f601401; (* usra   v1.2d, v0.2d, #32 *)
  0x2ebe80d3; (* umlal  v19.2d, v6.2s, v30.2s *)
  0x6f6014a1; (* usra   v1.2d, v5.2d, #32 *)
  0x4e083e74; (* mov    x20, v19.d[0] *)
  0x4e183e70; (* mov    x16, v19.d[1] *)
  0x9bce7f0c; (* umulh  x12, x24, x14 *)
  0x4e083c21; (* mov    x1, v1.d[0] *)
  0x4e183c22; (* mov    x2, v1.d[1] *)
  0xab140184; (* adds   x4, x12, x20 *)
  0xba100034; (* adcs   x20, x1, x16 *)
  0x9a1f0050; (* adc    x16, x2, xzr *)
  0xab160087; (* adds   x7, x4, x22 *)
  0xba04028c; (* adcs   x12, x20, x4 *)
  0xba140201; (* adcs   x1, x16, x20 *)
  0x9a1f0202; (* adc    x2, x16, xzr *)
  0xab160189; (* adds   x9, x12, x22 *)
  0xba040033; (* adcs   x19, x1, x4 *)
  0xba140044; (* adcs   x4, x2, x20 *)
  0x9a1f0214; (* adc    x20, x16, xzr *)
  0xeb050302; (* subs   x2, x24, x5 *)
  0xda822450; (* cneg   x16, x2, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm  x12, cc  // cc = lo, ul, last *)
  0xeb0e01e2; (* subs   x2, x15, x14 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e01; (* mul    x1, x16, x2 *)
  0x9bc27e02; (* umulh  x2, x16, x2 *)
  0xda8c218c; (* cinv   x12, x12, cc  // cc = lo, ul, last *)
  0xca0c0021; (* eor    x1, x1, x12 *)
  0xca0c0042; (* eor    x2, x2, x12 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xba0100eb; (* adcs   x11, x7, x1 *)
  0xba020129; (* adcs   x9, x9, x2 *)
  0xba0c0273; (* adcs   x19, x19, x12 *)
  0xba0c0084; (* adcs   x4, x4, x12 *)
  0x9a0c0294; (* adc    x20, x20, x12 *)
  0xeb0a0302; (* subs   x2, x24, x10 *)
  0xda822450; (* cneg   x16, x2, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm  x12, cc  // cc = lo, ul, last *)
  0xeb0e0222; (* subs   x2, x17, x14 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e01; (* mul    x1, x16, x2 *)
  0x9bc27e02; (* umulh  x2, x16, x2 *)
  0xda8c218c; (* cinv   x12, x12, cc  // cc = lo, ul, last *)
  0xca0c0021; (* eor    x1, x1, x12 *)
  0xca0c0042; (* eor    x2, x2, x12 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xba010127; (* adcs   x7, x9, x1 *)
  0xba020273; (* adcs   x19, x19, x2 *)
  0xba0c0084; (* adcs   x4, x4, x12 *)
  0x9a0c0294; (* adc    x20, x20, x12 *)
  0xeb0a00a2; (* subs   x2, x5, x10 *)
  0xda822450; (* cneg   x16, x2, cc  // cc = lo, ul, last *)
  0xda9f23ec; (* csetm  x12, cc  // cc = lo, ul, last *)
  0xeb0f0222; (* subs   x2, x17, x15 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027e01; (* mul    x1, x16, x2 *)
  0x9bc27e02; (* umulh  x2, x16, x2 *)
  0xda8c2190; (* cinv   x16, x12, cc  // cc = lo, ul, last *)
  0xca100021; (* eor    x1, x1, x16 *)
  0xca100042; (* eor    x2, x2, x16 *)
  0xb100061f; (* cmn    x16, #0x1 *)
  0xba010273; (* adcs   x19, x19, x1 *)
  0xba02008c; (* adcs   x12, x4, x2 *)
  0x9a100281; (* adc    x1, x20, x16 *)
  0xeb030302; (* subs   x2, x24, x3 *)
  0xfa1500b8; (* sbcs   x24, x5, x21 *)
  0xfa080155; (* sbcs   x21, x10, x8 *)
  0xda1f03e5; (* ngc    x5, xzr *)
  0xb10004bf; (* cmn    x5, #0x1 *)
  0xca050042; (* eor    x2, x2, x5 *)
  0xba1f0044; (* adcs   x4, x2, xzr *)
  0xca050302; (* eor    x2, x24, x5 *)
  0xba1f0054; (* adcs   x20, x2, xzr *)
  0xca0502a2; (* eor    x2, x21, x5 *)
  0x9a1f0050; (* adc    x16, x2, xzr *)
  0xeb0e01a2; (* subs   x2, x13, x14 *)
  0xfa0f02f8; (* sbcs   x24, x23, x15 *)
  0xfa1100c8; (* sbcs   x8, x6, x17 *)
  0xda1f03f5; (* ngc    x21, xzr *)
  0xb10006bf; (* cmn    x21, #0x1 *)
  0xca150042; (* eor    x2, x2, x21 *)
  0xba1f004f; (* adcs   x15, x2, xzr *)
  0xca150302; (* eor    x2, x24, x21 *)
  0xba1f004e; (* adcs   x14, x2, xzr *)
  0xca150102; (* eor    x2, x8, x21 *)
  0x9a1f0046; (* adc    x6, x2, xzr *)
  0xca1500a9; (* eor    x9, x5, x21 *)
  0xa9400815; (* ldp    x21, x2, [x0] *)
  0xab1502ca; (* adds   x10, x22, x21 *)
  0xba020165; (* adcs   x5, x11, x2 *)
  0xa9410815; (* ldp    x21, x2, [x0, #16] *)
  0xba1500f8; (* adcs   x24, x7, x21 *)
  0xba020268; (* adcs   x8, x19, x2 *)
  0xa9420815; (* ldp    x21, x2, [x0, #32] *)
  0xba150195; (* adcs   x21, x12, x21 *)
  0xba020022; (* adcs   x2, x1, x2 *)
  0x9a1f03f3; (* adc    x19, xzr, xzr *)
  0xa900140a; (* stp    x10, x5, [x0] *)
  0xa9012018; (* stp    x24, x8, [x0, #16] *)
  0xa9020815; (* stp    x21, x2, [x0, #32] *)
  0x9b0f7c8c; (* mul    x12, x4, x15 *)
  0x9b0e7e85; (* mul    x5, x20, x14 *)
  0x9b067e18; (* mul    x24, x16, x6 *)
  0x9bcf7c88; (* umulh  x8, x4, x15 *)
  0x9bce7e95; (* umulh  x21, x20, x14 *)
  0x9bc67e02; (* umulh  x2, x16, x6 *)
  0xab05010a; (* adds   x10, x8, x5 *)
  0xba1802a5; (* adcs   x5, x21, x24 *)
  0x9a1f0058; (* adc    x24, x2, xzr *)
  0xab0c0157; (* adds   x23, x10, x12 *)
  0xba0a00a8; (* adcs   x8, x5, x10 *)
  0xba050315; (* adcs   x21, x24, x5 *)
  0x9a1f0302; (* adc    x2, x24, xzr *)
  0xab0c010d; (* adds   x13, x8, x12 *)
  0xba0a02a1; (* adcs   x1, x21, x10 *)
  0xba05004a; (* adcs   x10, x2, x5 *)
  0x9a1f0305; (* adc    x5, x24, xzr *)
  0xeb140082; (* subs   x2, x4, x20 *)
  0xda822458; (* cneg   x24, x2, cc  // cc = lo, ul, last *)
  0xda9f23e8; (* csetm  x8, cc  // cc = lo, ul, last *)
  0xeb0f01c2; (* subs   x2, x14, x15 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027f15; (* mul    x21, x24, x2 *)
  0x9bc27f02; (* umulh  x2, x24, x2 *)
  0xda882108; (* cinv   x8, x8, cc  // cc = lo, ul, last *)
  0xca0802b5; (* eor    x21, x21, x8 *)
  0xca080042; (* eor    x2, x2, x8 *)
  0xb100051f; (* cmn    x8, #0x1 *)
  0xba1502f7; (* adcs   x23, x23, x21 *)
  0xba0201ad; (* adcs   x13, x13, x2 *)
  0xba080021; (* adcs   x1, x1, x8 *)
  0xba08014a; (* adcs   x10, x10, x8 *)
  0x9a0800a5; (* adc    x5, x5, x8 *)
  0xeb100082; (* subs   x2, x4, x16 *)
  0xda822458; (* cneg   x24, x2, cc  // cc = lo, ul, last *)
  0xda9f23e8; (* csetm  x8, cc  // cc = lo, ul, last *)
  0xeb0f00c2; (* subs   x2, x6, x15 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027f15; (* mul    x21, x24, x2 *)
  0x9bc27f02; (* umulh  x2, x24, x2 *)
  0xda882108; (* cinv   x8, x8, cc  // cc = lo, ul, last *)
  0xca0802b5; (* eor    x21, x21, x8 *)
  0xca080042; (* eor    x2, x2, x8 *)
  0xb100051f; (* cmn    x8, #0x1 *)
  0xba1501a4; (* adcs   x4, x13, x21 *)
  0xba02002d; (* adcs   x13, x1, x2 *)
  0xba080141; (* adcs   x1, x10, x8 *)
  0x9a0800aa; (* adc    x10, x5, x8 *)
  0xeb100282; (* subs   x2, x20, x16 *)
  0xda822458; (* cneg   x24, x2, cc  // cc = lo, ul, last *)
  0xda9f23e8; (* csetm  x8, cc  // cc = lo, ul, last *)
  0xeb0e00c2; (* subs   x2, x6, x14 *)
  0xda822442; (* cneg   x2, x2, cc  // cc = lo, ul, last *)
  0x9b027f15; (* mul    x21, x24, x2 *)
  0x9bc27f02; (* umulh  x2, x24, x2 *)
  0xda882105; (* cinv   x5, x8, cc  // cc = lo, ul, last *)
  0xca0502b5; (* eor    x21, x21, x5 *)
  0xca050042; (* eor    x2, x2, x5 *)
  0xb10004bf; (* cmn    x5, #0x1 *)
  0xba1501b8; (* adcs   x24, x13, x21 *)
  0xba020028; (* adcs   x8, x1, x2 *)
  0x9a050155; (* adc    x21, x10, x5 *)
  0xa9404014; (* ldp    x20, x16, [x0] *)
  0xa9413c11; (* ldp    x17, x15, [x0, #16] *)
  0xa942180e; (* ldp    x14, x6, [x0, #32] *)
  0xb100053f; (* cmn    x9, #0x1 *)
  0xca090182; (* eor    x2, x12, x9 *)
  0xba14004c; (* adcs   x12, x2, x20 *)
  0xca0902e2; (* eor    x2, x23, x9 *)
  0xba100057; (* adcs   x23, x2, x16 *)
  0xca090082; (* eor    x2, x4, x9 *)
  0xba11004d; (* adcs   x13, x2, x17 *)
  0xca090302; (* eor    x2, x24, x9 *)
  0xba0f004a; (* adcs   x10, x2, x15 *)
  0xca090102; (* eor    x2, x8, x9 *)
  0xba0e0045; (* adcs   x5, x2, x14 *)
  0xca0902a2; (* eor    x2, x21, x9 *)
  0xba060058; (* adcs   x24, x2, x6 *)
  0xba130121; (* adcs   x1, x9, x19 *)
  0xba1f0128; (* adcs   x8, x9, xzr *)
  0xba1f0135; (* adcs   x21, x9, xzr *)
  0x9a1f0122; (* adc    x2, x9, xzr *)
  0xab14014a; (* adds   x10, x10, x20 *)
  0xba1000a5; (* adcs   x5, x5, x16 *)
  0xba110318; (* adcs   x24, x24, x17 *)
  0xba0f0031; (* adcs   x17, x1, x15 *)
  0xba0e010f; (* adcs   x15, x8, x14 *)
  0xba0602ae; (* adcs   x14, x21, x6 *)
  0x9a130046; (* adc    x6, x2, x19 *)
  0xd3607d82; (* lsl    x2, x12, #32 *)
  0x8b0c0041; (* add    x1, x2, x12 *)
  0xd360fc22; (* lsr    x2, x1, #32 *)
  0xeb010055; (* subs   x21, x2, x1 *)
  0xda1f0022; (* sbc    x2, x1, xzr *)
  0x93d58055; (* extr   x21, x2, x21, #32 *)
  0xd360fc42; (* lsr    x2, x2, #32 *)
  0xab010048; (* adds   x8, x2, x1 *)
  0x9a1f03e2; (* adc    x2, xzr, xzr *)
  0xeb1502f5; (* subs   x21, x23, x21 *)
  0xfa0801b7; (* sbcs   x23, x13, x8 *)
  0xfa02014a; (* sbcs   x10, x10, x2 *)
  0xfa1f00a5; (* sbcs   x5, x5, xzr *)
  0xfa1f0318; (* sbcs   x24, x24, xzr *)
  0xda1f002d; (* sbc    x13, x1, xzr *)
  0xd3607ea2; (* lsl    x2, x21, #32 *)
  0x8b150041; (* add    x1, x2, x21 *)
  0xd360fc22; (* lsr    x2, x1, #32 *)
  0xeb010055; (* subs   x21, x2, x1 *)
  0xda1f0022; (* sbc    x2, x1, xzr *)
  0x93d58055; (* extr   x21, x2, x21, #32 *)
  0xd360fc42; (* lsr    x2, x2, #32 *)
  0xab010048; (* adds   x8, x2, x1 *)
  0x9a1f03e2; (* adc    x2, xzr, xzr *)
  0xeb1502f5; (* subs   x21, x23, x21 *)
  0xfa08014a; (* sbcs   x10, x10, x8 *)
  0xfa0200a5; (* sbcs   x5, x5, x2 *)
  0xfa1f0318; (* sbcs   x24, x24, xzr *)
  0xfa1f01b7; (* sbcs   x23, x13, xzr *)
  0xda1f002d; (* sbc    x13, x1, xzr *)
  0xd3607ea2; (* lsl    x2, x21, #32 *)
  0x8b150041; (* add    x1, x2, x21 *)
  0xd360fc22; (* lsr    x2, x1, #32 *)
  0xeb010055; (* subs   x21, x2, x1 *)
  0xda1f0022; (* sbc    x2, x1, xzr *)
  0x93d58048; (* extr   x8, x2, x21, #32 *)
  0xd360fc42; (* lsr    x2, x2, #32 *)
  0xab010055; (* adds   x21, x2, x1 *)
  0x9a1f03e2; (* adc    x2, xzr, xzr *)
  0xeb08014a; (* subs   x10, x10, x8 *)
  0xfa1500a5; (* sbcs   x5, x5, x21 *)
  0xfa020318; (* sbcs   x24, x24, x2 *)
  0xfa1f02e8; (* sbcs   x8, x23, xzr *)
  0xfa1f01b5; (* sbcs   x21, x13, xzr *)
  0xda1f0022; (* sbc    x2, x1, xzr *)
  0xab080237; (* adds   x23, x17, x8 *)
  0xba1501ed; (* adcs   x13, x15, x21 *)
  0xba0201c1; (* adcs   x1, x14, x2 *)
  0x9a1f00c2; (* adc    x2, x6, xzr *)
  0x91000448; (* add    x8, x2, #0x1 *)
  0xd3607d02; (* lsl    x2, x8, #32 *)
  0xeb020115; (* subs   x21, x8, x2 *)
  0xda1f0042; (* sbc    x2, x2, xzr *)
  0xab15014a; (* adds   x10, x10, x21 *)
  0xba0200a5; (* adcs   x5, x5, x2 *)
  0xba080318; (* adcs   x24, x24, x8 *)
  0xba1f02e8; (* adcs   x8, x23, xzr *)
  0xba1f01b5; (* adcs   x21, x13, xzr *)
  0xba1f002d; (* adcs   x13, x1, xzr *)
  0xda9f23e1; (* csetm  x1, cc  // cc = lo, ul, last *)
  0xb2407fe2; (* mov    x2, #0xffffffff                 // #4294967295 *)
  0x8a010042; (* and    x2, x2, x1 *)
  0xab02014a; (* adds   x10, x10, x2 *)
  0xca010042; (* eor    x2, x2, x1 *)
  0xba0200a5; (* adcs   x5, x5, x2 *)
  0x92800022; (* mov    x2, #0xfffffffffffffffe         // #-2 *)
  0x8a010042; (* and    x2, x2, x1 *)
  0xba020318; (* adcs   x24, x24, x2 *)
  0xba010108; (* adcs   x8, x8, x1 *)
  0xba0102b5; (* adcs   x21, x21, x1 *)
  0x9a0101a2; (* adc    x2, x13, x1 *)
  0xa900140a; (* stp    x10, x5, [x0] *)
  0xa9012018; (* stp    x24, x8, [x0, #16] *)
  0xa9020815; (* stp    x21, x2, [x0, #32] *)
  0xa8c163f7; (* ldp    x23, x24, [sp], #16 *)
  0xa8c15bf5; (* ldp    x21, x22, [sp], #16 *)
  0xa8c153f3; (* ldp    x19, x20, [sp], #16 *)
  0xd65f03c0; (* ret *)
];;

let bignum_montmul_p384_interm1_mc =
  define_mc_from_intlist "bignum_montmul_p384_interm1_mc" bignum_montmul_p384_interm1_ops;;

let BIGNUM_MONTMUL_P384_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p384_interm1_mc;;

let bignum_montmul_p384_interm1_core_mc_def,
    bignum_montmul_p384_interm1_core_mc,
    BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p384_interm1_core_mc"
    bignum_montmul_p384_interm1_mc
    (`12`,`LENGTH bignum_montmul_p384_interm1_mc - 28`)
    (fst BIGNUM_MONTMUL_P384_INTERM1_EXEC);;

let montmul_p384_eqin = new_definition
  `!s1 s1' x y z.
    (montmul_p384_eqin:(armstate#armstate)->int64->int64->int64->bool) (s1,s1') x y z <=>
    (C_ARGUMENTS [z; x; y] s1 /\
     C_ARGUMENTS [z; x; y] s1' /\
     ?a. bignum_from_memory (x,6) s1 = a /\
         bignum_from_memory (x,6) s1' = a /\
      (?b. bignum_from_memory (y,6) s1 = b /\
           bignum_from_memory (y,6) s1' = b))`;;

let montmul_p384_eqout = new_definition
  `!s1 s1' z.
    (montmul_p384_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,6) s1 = a /\
      bignum_from_memory (z,6) s1' = a)`;;

(* This diff is generated by tools/gen-actions.py.
   To get this diff you will need an 'original register name'
   version of the bignum_montmul_p384_interm1_mc. *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 4, 2, 5);
  ("insert", 4, 4, 5, 6);
  ("equal", 4, 6, 6, 8);
  ("replace", 6, 8, 8, 19);
  ("equal", 8, 117, 19, 128);
  ("replace", 117, 119, 128, 148);
  ("equal", 119, 120, 148, 149);
  ("replace", 120, 122, 149, 151);
  ("equal", 122, 377, 151, 406);
];;

let actions = break_equal_loads actions
    (snd BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC) 0x0;;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montmul_p384_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p384_interm1_core_mc)]`
    montmul_p384_eqin
    montmul_p384_eqout
    bignum_montmul_p384_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montmul_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;


let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTMUL_P384_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC;
    fst BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p384_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
    BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,6) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV;;


(******************************************************************************
  The second program equivalence between the core part of intermediate
  program and fully optimized program
******************************************************************************)

let bignum_montmul_p384_mc =
  define_from_elf "bignum_montmul_p384_mc"
    "arm/p384/bignum_montmul_p384.o";;

let BIGNUM_MONTMUL_P384_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p384_mc;;

let bignum_montmul_p384_core_mc_def,
    bignum_montmul_p384_core_mc,
    BIGNUM_MONTMUL_P384_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p384_core_mc"
    bignum_montmul_p384_mc
    (`12`,`LENGTH bignum_montmul_p384_mc - 28`)
    (fst BIGNUM_MONTMUL_P384_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montmul_p384_interm1_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p384_core_mc)]`
    montmul_p384_eqin
    montmul_p384_eqout
    bignum_montmul_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montmul_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;


(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)

let inst_map = [
  2;6;5;1;12;11;21;14;13;10;3;35;9;129;37;22;133;130;36;38;131;132;39;7;137;15;42;40;136;135;16;17;20;139;51;134;52;23;19;43;18;53;138;24;25;41;26;144;27;141;28;140;29;142;30;31;143;32;33;44;34;54;55;58;45;56;46;47;48;57;49;50;66;67;59;68;69;70;145;71;73;61;146;62;60;63;64;80;72;74;8;81;65;4;82;75;83;84;76;77;85;86;78;79;87;149;88;89;90;91;95;96;92;128;93;97;94;98;99;100;101;102;103;104;105;106;110;111;107;112;108;109;113;114;115;116;117;118;119;147;120;121;125;122;123;126;150;124;163;148;164;165;166;151;170;167;127;168;152;153;154;155;169;156;171;157;158;159;160;161;162;173;172;174;175;176;177;178;179;180;181;182;186;183;208;209;184;210;211;194;187;196;195;197;201;198;219;220;215;199;221;213;222;185;212;202;214;216;217;218;228;200;223;224;226;225;227;229;189;188;190;247;191;192;203;231;193;204;205;234;246;206;207;237;232;245;233;230;235;241;236;244;238;242;239;240;277;249;243;278;279;248;292;310;293;294;280;281;284;261;283;262;263;264;268;282;265;295;296;299;250;266;251;252;253;254;267;255;256;257;258;259;298;269;260;271;272;270;312;273;285;274;297;301;275;276;287;288;398;286;289;300;290;291;302;306;307;303;316;304;305;309;311;308;314;333;313;315;320;317;318;319;321;322;323;334;335;324;325;336;337;326;327;338;339;328;329;330;331;393;332;340;341;342;343;348;349;344;345;350;346;347;351;352;353;354;355;356;357;358;363;359;364;360;365;361;362;366;367;369;368;370;371;372;373;374;375;376;377;378;379;380;381;382;383;384;385;386;387;388;389;390;391;392;399;394;395;396;397;400;404;401;402;405;403;406
];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTMUL_P384_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTMUL_P384_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p384_eqin THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MONTMUL_P384_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,6) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(******************************************************************************
  Use transitivity of two program equivalences to prove end-to-end
  correctness
******************************************************************************)

let equiv_goal = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montmul_p384_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montmul_p384_core_mc)]`
    montmul_p384_eqin
    montmul_p384_eqout
    bignum_montmul_p384_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montmul_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

let montmul_p384_eqout_TRANS = prove(
  `!s s2 s'
    z. montmul_p384_eqout (s,s') z /\ montmul_p384_eqout (s',s2) z
    ==> montmul_p384_eqout (s,s2) z`,
  MESON_TAC[montmul_p384_eqout]);;

let BIGNUM_MONTMUL_P384_CORE_EQUIV = time prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc:int64,LENGTH bignum_montmul_p384_unopt_core_mc);
        (word pc3:int64,LENGTH bignum_montmul_p384_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc3:int64,LENGTH bignum_montmul_p384_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montmul_p384_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montmul_p384_interm1_core_mc))
        [x,8 * 6; y,8 * 6] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTMUL_P384_CORE_EXEC;
       fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTMUL_P384_CORE_EQUIV1,BIGNUM_MONTMUL_P384_CORE_EQUIV2)
    (montmul_p384_eqin,montmul_p384_eqin,montmul_p384_eqin)
    montmul_p384_eqout_TRANS
    (BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P384_INTERM1_CORE_EXEC,
     BIGNUM_MONTMUL_P384_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MONTMUL_P384_SUBROUTINE_CORRECT
          from BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64, LENGTH
        (APPEND bignum_montmul_p384_unopt_core_mc barrier_inst_bytes))
      (z:int64,8 * 6)`
    [`z:int64`;`x:int64`;`y:int64`] bignum_montmul_p384_unopt_core_mc
    `\s0. C_ARGUMENTS [z;x;y] s0`;;

let BIGNUM_MONTMUL_P384_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montmul_p384_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC]
    THEN CONV_TAC NUM_DIVIDES_CONV
    THEN NO_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC);;


let BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTMUL_P384_UNOPT_EXEC
    BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
    BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT
    BIGNUM_MONTMUL_P384_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montmul_p384_unopt_core_mc replaced with
    bignum_montmul_p384_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_MONTMUL_P384_CORE_CORRECT = time prove(
  `!z x y a b pc2.
      nonoverlapping (word pc2,LENGTH bignum_montmul_p384_core_mc) (z,8 * 6)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p384_core_mc /\
                read PC s = word (pc2) /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
            (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p384_core_mc) /\
                (a * b <= 2 EXP 384 * p_384
                  ==> bignum_from_memory (z,6) s =
                      (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17; X19;
                        X20; X21; X22; X23; X24] ,,
             MAYCHANGE MODIFIABLE_SIMD_REGS ,,
             MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_unopt_core_mc barrier_inst_bytes)) (y:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P384_CORE_EQUIV BIGNUM_MONTMUL_P384_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P384_CORE_EXEC)
    (montmul_p384_eqin,montmul_p384_eqout));;

let BIGNUM_MONTMUL_P384_CORRECT = time prove(
  `!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_mc /\
                  read PC s = word (pc+12) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word ((pc + 12) + LENGTH bignum_montmul_p384_core_mc) /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P384_CORE_CORRECT
      bignum_montmul_p384_core_mc_def
      [fst BIGNUM_MONTMUL_P384_EXEC;
       fst BIGNUM_MONTMUL_P384_CORE_EXEC]);;

let BIGNUM_MONTMUL_P384_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p384_mc) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,LENGTH bignum_montmul_p384_mc); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
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
  REWRITE_TAC[fst BIGNUM_MONTMUL_P384_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_EXEC
   (let th = REWRITE_RULE [fst BIGNUM_MONTMUL_P384_CORE_EXEC;
        fst BIGNUM_MONTMUL_P384_EXEC;GSYM ADD_ASSOC]
      BIGNUM_MONTMUL_P384_CORRECT in
    CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
   `[X19;X20;X21;X22;X23;X24]` 48);;


(******************************************************************************
          Inducing BIGNUM_AMONTMUL_P384_SUBROUTINE_CORRECT
          from BIGNUM_AMONTMUL_P384_UNOPT_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTMUL_P384_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTMUL_P384_UNOPT_EXEC
    BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC
    BIGNUM_AMONTMUL_P384_UNOPT_CORE_CORRECT
    BIGNUM_MONTMUL_P384_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_AMONTMUL_P384_UNOPT_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montmul_p384_unopt_core_mc with
    bignum_montmul_p384_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_AMONTMUL_P384_CORE_CORRECT = time prove(
  `!z x y a b pc2.
      nonoverlapping (word pc2,LENGTH bignum_montmul_p384_core_mc) (z,8 * 6)
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p384_core_mc /\
                read PC s = word (pc2) /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
            (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p384_core_mc) /\
                (bignum_from_memory (z,6) s ==
                  inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17; X19;
                        X20; X21; X22; X23; X24] ,,
             MAYCHANGE MODIFIABLE_SIMD_REGS ,,
             MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montmul_p384_unopt_core_mc barrier_inst_bytes)) (y:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P384_CORE_EQUIV BIGNUM_AMONTMUL_P384_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P384_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P384_CORE_EXEC)
    (montmul_p384_eqin,montmul_p384_eqout));;

let BIGNUM_AMONTMUL_P384_CORRECT = time prove(
  `!z x y a b pc.
        nonoverlapping (word pc,LENGTH bignum_montmul_p384_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_mc /\
                  read PC s = word (pc+12) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + (12 + LENGTH bignum_montmul_p384_core_mc)) /\
                  (bignum_from_memory (z,6) s ==
                       inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                        X10; X11; X12; X13; X14; X15; X16; X17; X19;
                        X20; X21; X22; X23; X24] ,,
             MAYCHANGE MODIFIABLE_SIMD_REGS ,,
             MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTMUL_P384_CORE_CORRECT
      bignum_montmul_p384_core_mc_def
      [fst BIGNUM_MONTMUL_P384_EXEC;
       fst BIGNUM_MONTMUL_P384_CORE_EXEC]);;


let BIGNUM_AMONTMUL_P384_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,LENGTH bignum_montmul_p384_mc) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,LENGTH bignum_montmul_p384_mc); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
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
  REWRITE_TAC[fst BIGNUM_MONTMUL_P384_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_EXEC
   (let th = REWRITE_RULE [fst BIGNUM_MONTMUL_P384_CORE_EXEC;
        fst BIGNUM_MONTMUL_P384_EXEC;GSYM ADD_ASSOC]
      BIGNUM_AMONTMUL_P384_CORRECT in
    CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) th)
   `[X19;X20;X21;X22;X23;X24]` 48);;
