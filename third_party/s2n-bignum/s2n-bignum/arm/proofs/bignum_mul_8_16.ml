(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 8x8 -> 16 multiply (pure Karatsuba and then ADK for the 4x4 bits).        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(* ------------------------------------------------------------------------- *)
(* Prove the functional correctness of unopt/bignum_mul_8_16_base first.     *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/fastmul/bignum_mul_8_16_base.o";;
 ****)

let bignum_mul_8_16_unopt_mc = define_assert_from_elf "bignum_mul_8_16_unopt_mc" "arm/fastmul/unopt/bignum_mul_8_16_base.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
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
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0xa900300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&0))) *)
  0xa9422047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&32))) *)
  0xa901380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&16))) *)
  0xa9431825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&48))) *)
  0xa902400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&32))) *)
  0xa9432849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&48))) *)
  0xa9034c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&48))) *)
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
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_8_16_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_mul_8_16_unopt_mc;;

(* bignum_mul_8_16 without callee-save register spilling. *)
let bignum_mul_8_16_unopt_core_mc_def,
    bignum_mul_8_16_unopt_core_mc,
    BIGNUM_MUL_8_16_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_mul_8_16_unopt_core_mc"
    bignum_mul_8_16_unopt_mc
    (`12`,`LENGTH bignum_mul_8_16_unopt_mc - 28`)
    (fst BIGNUM_MUL_8_16_UNOPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas to halve the number of case splits, useful for efficiency.         *)
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

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

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

let BIGNUM_MUL_8_16_UNOPT_CORE_CORRECT = prove
 (`!z x y a b pc.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc,LENGTH bignum_mul_8_16_unopt_core_mc); (x,8 * 8); (y,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_mul_8_16_unopt_core_mc /\
                 read PC s = word(pc) /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,8) s = a /\
                 bignum_from_memory (y,8) s = b)
          (\s. read PC s = word (pc + LENGTH bignum_mul_8_16_unopt_core_mc) /\
               bignum_from_memory (z,16) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
                        X9; X10; X11; X12; X13; X14; X15; X16;
                        X17; X19; X20; X21; X22; X23; X24] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,8) s0` THEN

  (*** First ADK block multiplying the lower halves ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC
   [5;6;7;8;10;12;14;16;17;18;19;20;21;22;23;24;25;
    26;27;33;38;40;41;47;52;54;55;56;57;58;59;65;70;
    72;73;74;80;85;87;88;89;90;91;97;102;104;105;106;
    107;113;118;120;121;122;123] (1--123) THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = bignum_of_wordlist[mullo_s5;sum_s52;sum_s85;sum_s118]`;
    `q1 = bignum_of_wordlist[sum_s120;sum_s121;sum_s122;sum_s123]`] THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC
   [132;133;134;135;137;139;141;143;144;145;146;147;
    148;149;150;151;152;153;154;156;157;159;160;161;
    162;163;164;170;175;177;178;184;189;191;192;193;
    194;195;196;202;207;209;210;211;217;222;224;225;
    226;227;228;234;239;241;242;243;244;250;255;257;
    258;259;260]
   (124--260) THEN

  MAP_EVERY ABBREV_TAC
   [`q2 = bignum_of_wordlist[sum_s156; sum_s189; sum_s222; sum_s255]`;
    `q3 = bignum_of_wordlist[sum_s257; sum_s258; sum_s259; sum_s260]`] THEN
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC
   [262;263;265;266; 270;271;273;274;
    278;280;282;284; 287;289;291;293]
   (261--294) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN

  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s274 <=> carry_s266)`;
   `xd = bignum_of_wordlist[sum_s278;sum_s280;sum_s282;sum_s284]`;
   `yd = bignum_of_wordlist[sum_s287;sum_s289;sum_s291;sum_s293]`] THEN

  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_4;x_5;x_6;x_7]) -
     &(bignum_of_wordlist[x_0;x_1;x_2;x_3])) *
    (&(bignum_of_wordlist[y_0;y_1;y_2;y_3]) -
     &(bignum_of_wordlist[y_4;y_5;y_6;y_7])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s266 * &xd) *
      (--(&1) pow bitval carry_s274 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s266 <=>
       bignum_of_wordlist[x_4;x_5;x_6;x_7] <
       bignum_of_wordlist[x_0;x_1;x_2;x_3]) /\
      (carry_s274 <=>
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC
   [296;297;298;299;301;303;305;307;308;309;310;311;312;313;314;315;
    316;317;318;324;329;331;332;338;343;345;346;347;348;349;350;356;
    361;363;364;365;371;376;378;379;380;381;382;388;393;395;396;397;
    398;404;409;411;412;413;414]
   (295--414) THEN

  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist
       [mullo_s296; sum_s343; sum_s376; sum_s409;
        sum_s411; sum_s412; sum_s413;  sum_s414])`
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC
   [417;418;421;422;424;425;427;428;429;430;433;435;436;437;439;
    441;443;445;447;448;449;450;451]
   (415--457) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s457" THEN
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
     `&(bitval carry_s429):real = &(bitval carry_s430)`
    SUBST1_TAC THENL [ALL_TAC; REAL_INTEGER_TAC] THEN
    POP_ASSUM MP_TAC THEN BOOL_CASES_TAC `carry_s429:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[REAL_RAT_REDUCE_CONV `(&2 pow 64 - &1) * &1 + &0`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o
    filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MUL_8_16_UNOPT_CORRECT = prove(
  `!z x y a b pc.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc,LENGTH bignum_mul_8_16_unopt_mc); (x,8 * 8); (y,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_mul_8_16_unopt_mc /\
                 read PC s = word(pc + 0xc) /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,8) s = a /\
                 bignum_from_memory (y,8) s = b)
          (\s. read PC s = word (pc + 0xc + LENGTH bignum_mul_8_16_unopt_core_mc) /\
               bignum_from_memory (z,16) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
                        X9; X10; X11; X12; X13; X14; X15; X16;
                        X17; X19; X20; X21; X22; X23; X24] ,,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MUL_8_16_UNOPT_CORE_CORRECT
      bignum_mul_8_16_unopt_core_mc_def
      [fst BIGNUM_MUL_8_16_UNOPT_EXEC;fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC]);;


(* ------------------------------------------------------------------------- *)
(* Prove program equivalence and use it to prove full functional correctness *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/fastmul/bignum_mul_8_16.o";;
 ****)

let bignum_mul_8_16_mc = define_assert_from_elf "bignum_mul_8_16_mc" "arm/fastmul/bignum_mul_8_16.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
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
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_8_16_EXEC = ARM_MK_EXEC_RULE bignum_mul_8_16_mc;;

(* bignum_mul_8_16_mc without callee-save register spilling. *)
let bignum_mul_8_16_core_mc_def,
    bignum_mul_8_16_core_mc,
    BIGNUM_MUL_8_16_CORE_EXEC =
  mk_sublist_of_mc "bignum_mul_8_16_core_mc"
    bignum_mul_8_16_mc
    (`12`,`LENGTH bignum_mul_8_16_mc - 28`)
    (fst BIGNUM_MUL_8_16_EXEC);;

(** Define equivalence relations at the begin and end of the two programs
    (after stack push/pops stripped) **)

(** s1, s1' are program states of the 'left' program and 'right' program.
    x, y are memory addresses of input buffers, z is an address of output buffer.
    The input and output buffers must not overlap, and this constraint is defined
    outside this equivalence relation definition.
**)
let bignum_mul_8_16_equiv_input_states = new_definition
  `!s1 s1' x y z.
    (bignum_mul_8_16_equiv_input_states:(armstate#armstate)->int64->int64->int64->bool) (s1,s1') x y z <=>
    (?a b.
      C_ARGUMENTS [z; x; y] s1 /\
      C_ARGUMENTS [z; x; y] s1' /\
      bignum_from_memory (x,8) s1 = a /\
      bignum_from_memory (x,8) s1' = a /\
      bignum_from_memory (y,8) s1 = b /\
      bignum_from_memory (y,8) s1' = b)`;;

let bignum_mul_8_16_equiv_output_states = new_definition
  `!s1 s1' x y z.
    (bignum_mul_8_16_equiv_output_states:(armstate#armstate)->int64->int64->int64->bool) (s1,s1') x y z <=>
    (?a b c.
      bignum_from_memory (x,8) s1 = a /\
      bignum_from_memory (x,8) s1' = a /\
      bignum_from_memory (y,8) s1 = b /\
      bignum_from_memory (y,8) s1' = b /\
      bignum_from_memory (z,16) s1 = c /\
      bignum_from_memory (z,16) s1' = c)`;;

let equiv_goal = mk_equiv_statement_simple
  `ALL (nonoverlapping (z,8 * 16)) [
      (word pc:int64,LENGTH bignum_mul_8_16_unopt_core_mc);
      (word pc2:int64,LENGTH bignum_mul_8_16_core_mc);
      (x,8 * 8); (y,8 * 8)]`
  bignum_mul_8_16_equiv_input_states
  bignum_mul_8_16_equiv_output_states
  bignum_mul_8_16_unopt_core_mc
  `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
              X9; X10; X11; X12; X13; X14; X15; X16;
              X17; X19; X20; X21; X22; X23; X24] ,,
   MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
  bignum_mul_8_16_core_mc
  `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
              X9; X10; X11; X12; X13; X14; X15; X16;
              X17; X19; X20; X21; X22; X23; X24] ,,
   MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
   MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
   MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I
    [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
     WORD_SQR64_HI; WORD_SQR64_LO]] @ (!extra_word_CONV);;

(* This diff is generated by
  'python3 gen-actions.py bignum_mul_8_16_base.S bignum_mul_8_16.S'
  where the two files are the disassemblied outputs from objdump.
*)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 2);
  ("equal", 1, 2, 2, 3);
  ("insert", 2, 2, 3, 4);
  ("equal", 2, 3, 4, 5);
  ("insert", 3, 3, 5, 6);
  ("equal", 3, 4, 6, 7);
  ("replace", 4, 8, 7, 30);
  ("equal", 8, 15, 30, 37);
  ("insert", 15, 15, 37, 44);
  ("equal", 15, 131, 44, 160);
  ("replace", 131, 135, 160, 171);
  ("equal", 135, 457, 171, 493);
];;

let actions = break_equal_loads actions
    (snd BIGNUM_MUL_8_16_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MUL_8_16_CORE_EXEC) 0x0;;

let BIGNUM_MUL_8_16_CORE_EQUIV = time prove(
  equiv_goal,

  REWRITE_TAC[SOME_FLAGS;ALL;NONOVERLAPPING_CLAUSES;
      fst BIGNUM_MUL_8_16_CORE_EXEC;
      fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC bignum_mul_8_16_equiv_input_states THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* The main simulation part *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MUL_8_16_UNOPT_CORE_EXEC BIGNUM_MUL_8_16_CORE_EXEC THEN

  (* We finished simulation of the programs. Prove postconditions *)
  ENSURES_N_FINAL_STATE_TAC THEN ENSURES_N_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[bignum_mul_8_16_equiv_output_states;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,8) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[BIGNUM_EXPAND_CONV `bignum_from_memory (p,16) st`];

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV;;

(** Now we will prove that bignum_mul_8_16 is correct using
    BIGNUM_MUL_8_16_CORE_EQUIV and BIGNUM_MUL_8_16_UNOPT_CORE_CORRECT.

    In order to do this, we need an updated version of
    BIGNUM_MUL_8_16_UNOPT_CORE_CORRECT that has # instructions to step.

    Proving the updated version consists of two steps:

    (1) A proof stating that, after a specified amount of steps,
        a postcondition will be satisfied at the end of bignum_mul_8_16_unopt_core_mc
        thanks to the explicit description of PC.
**)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
  `ALL (nonoverlapping (z,8 * 16)) [
      (word pc:int64,
       LENGTH (APPEND bignum_mul_8_16_unopt_core_mc barrier_inst_bytes));
      (x:int64,8 * 8); (y:int64,8 * 8)]`
  [`z:int64`;`x:int64`;`y:int64`] bignum_mul_8_16_unopt_core_mc
  `(\s0. C_ARGUMENTS [z;x;y] s0)`;;

let BIGNUM_MUL_8_16_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,
  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_mul_8_16_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC]) THENL [
        REWRITE_TAC[fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
        ALL_TAC] THEN
  REPEAT_N 4 GEN_TAC THEN
  (* nonoverlapping *)
  STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN
  STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC);;

(**
    (2) An updated 'ensures_n' that has an imaginary 'barrier' instruction
        attached at the end of the core, and is given 'n' which is the
        number of small steps needed to reach at its postcondition.

        This needs BIGNUM_MUL_8_16_EVENTUALLY_N_AT_PC.
**)

let BIGNUM_MUL_8_16_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MUL_8_16_UNOPT_EXEC
    BIGNUM_MUL_8_16_UNOPT_CORE_EXEC
    BIGNUM_MUL_8_16_UNOPT_CORE_CORRECT
    BIGNUM_MUL_8_16_EVENTUALLY_N_AT_PC;;

let BIGNUM_MUL_8_16_CORE_CORRECT = prove(
  `!z x y a b pc2.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc2,LENGTH bignum_mul_8_16_core_mc); (x,8 * 8); (y,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_mul_8_16_core_mc /\
                 read PC s = word(pc2) /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,8) s = a /\
                 bignum_from_memory (y,8) s = b)
          (\s. read PC s = word (pc2 + LENGTH bignum_mul_8_16_core_mc) /\
               bignum_from_memory (z,16) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
                        X9; X10; X11; X12; X13; X14; X15; X16;
                        X17; X19; X20; X21; X22; X23; X24] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5],,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  let mc_lengths_th =
    map fst [BIGNUM_MUL_8_16_UNOPT_CORE_EXEC; BIGNUM_MUL_8_16_CORE_EXEC] in
  REPEAT GEN_TAC THEN

  (* Prepare pc for the 'left' program. The left program must not have overwritten x and y. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (z:int64,8 * 16) (word pc,
        LENGTH (APPEND bignum_mul_8_16_unopt_core_mc barrier_inst_bytes)) /\
      ALL (nonoverlapping (word pc,
          LENGTH (APPEND bignum_mul_8_16_unopt_core_mc barrier_inst_bytes)))
          [(x:int64,8 * 8); (y:int64,8 * 8)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC;NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN

  (* massage nonoverlapping assumptions *)
  REPEAT_N 2 STRIP_TAC THEN

  VCGEN_EQUIV_TAC BIGNUM_MUL_8_16_CORE_EQUIV BIGNUM_MUL_8_16_UNOPT_CORE_CORRECT_N
    [fst BIGNUM_MUL_8_16_UNOPT_CORE_EXEC; fst BIGNUM_MUL_8_16_CORE_EXEC] THEN

  (* unravel definitions that may block reasonings *)
  RULE_ASSUM_TAC (REWRITE_RULE([ALL;NONOVERLAPPING_CLAUSES] @ mc_lengths_th)) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[bignum_mul_8_16_equiv_input_states] THEN
    EXISTS_TAC
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND bignum_mul_8_16_unopt_core_mc barrier_inst_bytes)))
          (APPEND bignum_mul_8_16_unopt_core_mc barrier_inst_bytes)
          (write PC (word pc) s2)` THEN
    PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC THEN
    (* Now has only one subgoal: the equivalence! *)
    REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
    MAP_EVERY EXISTS_TAC [`a:num`;`b:num`] THEN
    PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_MUL_8_16_UNOPT_CORE_EXEC;

    (** SUBGOAL 2. Postcond **)
    MESON_TAC[bignum_mul_8_16_equiv_output_states;BIGNUM_FROM_MEMORY_BYTES;
      fst BIGNUM_MUL_8_16_CORE_EXEC];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[]
  ]);;

let BIGNUM_MUL_8_16_CORRECT = prove(
  `!z x y a b pc2.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc2,LENGTH bignum_mul_8_16_mc); (x,8 * 8); (y,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc2) bignum_mul_8_16_mc /\
                 read PC s = word(pc2 + 0xc) /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,8) s = a /\
                 bignum_from_memory (y,8) s = b)
          (\s. read PC s = word (pc2 + 0xc + LENGTH bignum_mul_8_16_core_mc) /\
               bignum_from_memory (z,16) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
                        X9; X10; X11; X12; X13; X14; X15; X16;
                        X17; X19; X20; X21; X22; X23; X24] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5],,
             MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MUL_8_16_CORE_CORRECT
      bignum_mul_8_16_core_mc_def
      [fst BIGNUM_MUL_8_16_EXEC;
       fst BIGNUM_MUL_8_16_CORE_EXEC]);;

let BIGNUM_MUL_8_16_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 16) (word_sub stackpointer (word 48),48) /\
        ALLPAIRS nonoverlapping
          [(z,8 * 16); (word_sub stackpointer (word 48),48)]
          [(word pc,2000); (x,8 * 8); (y,8 * 8)]
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_mul_8_16_mc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [z; x; y] s /\
                 bignum_from_memory (x,8) s = a /\
                 bignum_from_memory (y,8) s = b)
          (\s. read PC s = returnaddress /\
               bignum_from_memory (z,16) s = a * b)
            (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8;
                        X9; X10; X11; X12; X13; X14; X15; X16; X17] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5],,
             MAYCHANGE [memory :> bytes(z,8 * 16);
                     memory :> bytes(word_sub stackpointer (word 48),48)] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_8_16_EXEC
   ((CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o REWRITE_RULE
     [fst BIGNUM_MUL_8_16_EXEC;fst BIGNUM_MUL_8_16_CORE_EXEC]) BIGNUM_MUL_8_16_CORRECT)
   `[X19;X20;X21;X22;X23;X24]` 48);;
