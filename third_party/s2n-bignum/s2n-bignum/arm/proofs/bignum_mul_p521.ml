(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_521.                                              *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(**** print_literal_from_elf "arm/p521/unopt/bignum_mul_p521_base.o";;
 ****)

let bignum_mul_p521_unopt_mc =
  define_assert_from_elf "bignum_mul_p521_unopt_mc" "arm/p521/unopt/bignum_mul_p521_base.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10143ff;       (* arm_SUB SP SP (rvalue (word 80)) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
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
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba170210;       (* arm_ADCS X16 X16 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070116;       (* arm_SUBS X22 X8 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba17018c;       (* arm_ADCS X12 X12 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080156;       (* arm_SUBS X22 X10 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070136;       (* arm_SUBS X22 X9 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070156;       (* arm_SUBS X22 X10 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080136;       (* arm_SUBS X22 X9 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xd377d975;       (* arm_LSL X21 X11 9 *)
  0x93cbdd8b;       (* arm_EXTR X11 X12 X11 55 *)
  0x93ccddac;       (* arm_EXTR X12 X13 X12 55 *)
  0x93cdddcd;       (* arm_EXTR X13 X14 X13 55 *)
  0xd377fdce;       (* arm_LSR X14 X14 55 *)
  0xa90043ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&0))) *)
  0xa9014ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&16))) *)
  0xa9022ff5;       (* arm_STP X21 X11 SP (Immediate_Offset (iword (&32))) *)
  0xa90337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&48))) *)
  0xf90023ee;       (* arm_STR X14 SP (Immediate_Offset (word 64)) *)
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0xa9431825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&48))) *)
  0xa9422047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&32))) *)
  0xa9432849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&48))) *)
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
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba170210;       (* arm_ADCS X16 X16 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070116;       (* arm_SUBS X22 X8 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba17018c;       (* arm_ADCS X12 X12 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080156;       (* arm_SUBS X22 X10 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070136;       (* arm_SUBS X22 X9 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070156;       (* arm_SUBS X22 X10 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080136;       (* arm_SUBS X22 X9 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xa9405bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&0))) *)
  0xab17016b;       (* arm_ADDS X11 X11 X23 *)
  0xba16018c;       (* arm_ADCS X12 X12 X22 *)
  0xa90033eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&0))) *)
  0xa9415bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&16))) *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xa9013bed;       (* arm_STP X13 X14 SP (Immediate_Offset (iword (&16))) *)
  0xa9425bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&32))) *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xa90243ef;       (* arm_STP X15 X16 SP (Immediate_Offset (iword (&32))) *)
  0xa9435bf7;       (* arm_LDP X23 X22 SP (Immediate_Offset (iword (&48))) *)
  0xba170231;       (* arm_ADCS X17 X17 X23 *)
  0xba160273;       (* arm_ADCS X19 X19 X22 *)
  0xa9034ff1;       (* arm_STP X17 X19 SP (Immediate_Offset (iword (&48))) *)
  0xf94023f5;       (* arm_LDR X21 SP (Immediate_Offset (word 64)) *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xf90023f5;       (* arm_STR X21 SP (Immediate_Offset (word 64)) *)
  0xa9405837;       (* arm_LDP X23 X22 X1 (Immediate_Offset (iword (&0))) *)
  0xeb170063;       (* arm_SUBS X3 X3 X23 *)
  0xfa160084;       (* arm_SBCS X4 X4 X22 *)
  0xa9415837;       (* arm_LDP X23 X22 X1 (Immediate_Offset (iword (&16))) *)
  0xfa1700a5;       (* arm_SBCS X5 X5 X23 *)
  0xfa1600c6;       (* arm_SBCS X6 X6 X22 *)
  0xda9f23f8;       (* arm_CSETM X24 Condition_CC *)
  0xa9405857;       (* arm_LDP X23 X22 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0702e7;       (* arm_SUBS X7 X23 X7 *)
  0xfa0802c8;       (* arm_SBCS X8 X22 X8 *)
  0xa9415857;       (* arm_LDP X23 X22 X2 (Immediate_Offset (iword (&16))) *)
  0xfa0902e9;       (* arm_SBCS X9 X23 X9 *)
  0xfa0a02ca;       (* arm_SBCS X10 X22 X10 *)
  0xda9f23f9;       (* arm_CSETM X25 Condition_CC *)
  0xca180063;       (* arm_EOR X3 X3 X24 *)
  0xeb180063;       (* arm_SUBS X3 X3 X24 *)
  0xca180084;       (* arm_EOR X4 X4 X24 *)
  0xfa180084;       (* arm_SBCS X4 X4 X24 *)
  0xca1800a5;       (* arm_EOR X5 X5 X24 *)
  0xfa1800a5;       (* arm_SBCS X5 X5 X24 *)
  0xca1800c6;       (* arm_EOR X6 X6 X24 *)
  0xda1800c6;       (* arm_SBC X6 X6 X24 *)
  0xca1900e7;       (* arm_EOR X7 X7 X25 *)
  0xeb1900e7;       (* arm_SUBS X7 X7 X25 *)
  0xca190108;       (* arm_EOR X8 X8 X25 *)
  0xfa190108;       (* arm_SBCS X8 X8 X25 *)
  0xca190129;       (* arm_EOR X9 X9 X25 *)
  0xfa190129;       (* arm_SBCS X9 X9 X25 *)
  0xca19014a;       (* arm_EOR X10 X10 X25 *)
  0xda19014a;       (* arm_SBC X10 X10 X25 *)
  0xca180339;       (* arm_EOR X25 X25 X24 *)
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
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb090156;       (* arm_SUBS X22 X10 X9 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba170210;       (* arm_ADCS X16 X16 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160231;       (* arm_ADCS X17 X17 X22 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb040078;       (* arm_SUBS X24 X3 X4 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070116;       (* arm_SUBS X22 X8 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba17018c;       (* arm_ADCS X12 X12 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ad;       (* arm_ADCS X13 X13 X22 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060098;       (* arm_SUBS X24 X4 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080156;       (* arm_SUBS X22 X10 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ef;       (* arm_ADCS X15 X15 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba160210;       (* arm_ADCS X16 X16 X22 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050078;       (* arm_SUBS X24 X3 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070136;       (* arm_SUBS X22 X9 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ad;       (* arm_ADCS X13 X13 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ce;       (* arm_ADCS X14 X14 X22 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb060078;       (* arm_SUBS X24 X3 X6 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb070156;       (* arm_SUBS X22 X10 X7 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xeb050098;       (* arm_SUBS X24 X4 X5 *)
  0xda982718;       (* arm_CNEG X24 X24 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0xeb080136;       (* arm_SUBS X22 X9 X8 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0x9b167f17;       (* arm_MUL X23 X24 X22 *)
  0x9bd67f16;       (* arm_UMULH X22 X24 X22 *)
  0xda9522b5;       (* arm_CINV X21 X21 Condition_CC *)
  0xb10006bf;       (* arm_CMN X21 (rvalue (word 1)) *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xba1701ce;       (* arm_ADCS X14 X14 X23 *)
  0xca1502d6;       (* arm_EOR X22 X22 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba150210;       (* arm_ADCS X16 X16 X21 *)
  0xba150231;       (* arm_ADCS X17 X17 X21 *)
  0x9a150273;       (* arm_ADC X19 X19 X21 *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xca19016b;       (* arm_EOR X11 X11 X25 *)
  0xab03016b;       (* arm_ADDS X11 X11 X3 *)
  0xca19018c;       (* arm_EOR X12 X12 X25 *)
  0xba04018c;       (* arm_ADCS X12 X12 X4 *)
  0xca1901ad;       (* arm_EOR X13 X13 X25 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xca1901ce;       (* arm_EOR X14 X14 X25 *)
  0xba0601ce;       (* arm_ADCS X14 X14 X6 *)
  0xca1901ef;       (* arm_EOR X15 X15 X25 *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0xa9432be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0xf94023f4;       (* arm_LDR X20 SP (Immediate_Offset (word 64)) *)
  0xba0701ef;       (* arm_ADCS X15 X15 X7 *)
  0xca190210;       (* arm_EOR X16 X16 X25 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0xca190231;       (* arm_EOR X17 X17 X25 *)
  0xba090231;       (* arm_ADCS X17 X17 X9 *)
  0xca190273;       (* arm_EOR X19 X19 X25 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a1f0295;       (* arm_ADC X21 X20 XZR *)
  0xab0301ef;       (* arm_ADDS X15 X15 X3 *)
  0xba040210;       (* arm_ADCS X16 X16 X4 *)
  0xba050231;       (* arm_ADCS X17 X17 X5 *)
  0xba060273;       (* arm_ADCS X19 X19 X6 *)
  0x92402339;       (* arm_AND X25 X25 (rvalue (word 511)) *)
  0xd377d978;       (* arm_LSL X24 X11 9 *)
  0xaa190318;       (* arm_ORR X24 X24 X25 *)
  0xba1800e7;       (* arm_ADCS X7 X7 X24 *)
  0x93cbdd98;       (* arm_EXTR X24 X12 X11 55 *)
  0xba180108;       (* arm_ADCS X8 X8 X24 *)
  0x93ccddb8;       (* arm_EXTR X24 X13 X12 55 *)
  0xba180129;       (* arm_ADCS X9 X9 X24 *)
  0x93cdddd8;       (* arm_EXTR X24 X14 X13 55 *)
  0xba18014a;       (* arm_ADCS X10 X10 X24 *)
  0xd377fdd8;       (* arm_LSR X24 X14 55 *)
  0x9a140314;       (* arm_ADC X20 X24 X20 *)
  0xf9402046;       (* arm_LDR X6 X2 (Immediate_Offset (word 64)) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0x9240cc77;       (* arm_AND X23 X3 (rvalue (word 4503599627370495)) *)
  0x9b177cd7;       (* arm_MUL X23 X6 X23 *)
  0xf940202e;       (* arm_LDR X14 X1 (Immediate_Offset (word 64)) *)
  0xa940304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&0))) *)
  0x9240cd78;       (* arm_AND X24 X11 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0x93c3d098;       (* arm_EXTR X24 X4 X3 52 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0x93cbd198;       (* arm_EXTR X24 X12 X11 52 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d732d8;       (* arm_EXTR X24 X22 X23 12 *)
  0xab1801ef;       (* arm_ADDS X15 X15 X24 *)
  0xa9410c25;       (* arm_LDP X5 X3 X1 (Immediate_Offset (iword (&16))) *)
  0xa9412c4d;       (* arm_LDP X13 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x93c4a0b8;       (* arm_EXTR X24 X5 X4 40 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cca1b8;       (* arm_EXTR X24 X13 X12 40 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374ced6;       (* arm_LSL X22 X22 12 *)
  0x93d662f8;       (* arm_EXTR X24 X23 X22 24 *)
  0xba180210;       (* arm_ADCS X16 X16 X24 *)
  0x93c57078;       (* arm_EXTR X24 X3 X5 28 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0x93cd7178;       (* arm_EXTR X24 X11 X13 28 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d792d8;       (* arm_EXTR X24 X22 X23 36 *)
  0xba180231;       (* arm_ADCS X17 X17 X24 *)
  0x8a11021a;       (* arm_AND X26 X16 X17 *)
  0xa9421424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&32))) *)
  0xa942344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&32))) *)
  0x93c34098;       (* arm_EXTR X24 X4 X3 16 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cb4198;       (* arm_EXTR X24 X12 X11 16 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd3503eb5;       (* arm_LSL X21 X21 48 *)
  0x8b1502f7;       (* arm_ADD X23 X23 X21 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374ced6;       (* arm_LSL X22 X22 12 *)
  0x93d6c2f8;       (* arm_EXTR X24 X23 X22 48 *)
  0xba180273;       (* arm_ADCS X19 X19 X24 *)
  0x8a13035a;       (* arm_AND X26 X26 X19 *)
  0xd344fc98;       (* arm_LSR X24 X4 4 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0xd344fd98;       (* arm_LSR X24 X12 4 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d7f2d9;       (* arm_EXTR X25 X22 X23 60 *)
  0x93c4e0b8;       (* arm_EXTR X24 X5 X4 56 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cce1b8;       (* arm_EXTR X24 X13 X12 56 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd378df39;       (* arm_LSL X25 X25 8 *)
  0x93d922f8;       (* arm_EXTR X24 X23 X25 8 *)
  0xba1800e7;       (* arm_ADCS X7 X7 X24 *)
  0x8a07035a;       (* arm_AND X26 X26 X7 *)
  0xa9431023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&48))) *)
  0xa943304b;       (* arm_LDP X11 X12 X2 (Immediate_Offset (iword (&48))) *)
  0x93c5b078;       (* arm_EXTR X24 X3 X5 44 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0x93cdb178;       (* arm_EXTR X24 X11 X13 44 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d752d8;       (* arm_EXTR X24 X22 X23 20 *)
  0xba180108;       (* arm_ADCS X8 X8 X24 *)
  0x8a08035a;       (* arm_AND X26 X26 X8 *)
  0x93c38098;       (* arm_EXTR X24 X4 X3 32 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187cd7;       (* arm_MUL X23 X6 X24 *)
  0x93cb8198;       (* arm_EXTR X24 X12 X11 32 *)
  0x9240cf18;       (* arm_AND X24 X24 (rvalue (word 4503599627370495)) *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374fed8;       (* arm_LSR X24 X22 52 *)
  0x8b1802f7;       (* arm_ADD X23 X23 X24 *)
  0xd374ced6;       (* arm_LSL X22 X22 12 *)
  0x93d682f8;       (* arm_EXTR X24 X23 X22 32 *)
  0xba180129;       (* arm_ADCS X9 X9 X24 *)
  0x8a09035a;       (* arm_AND X26 X26 X9 *)
  0xd354fc98;       (* arm_LSR X24 X4 20 *)
  0x9b187cd6;       (* arm_MUL X22 X6 X24 *)
  0xd354fd98;       (* arm_LSR X24 X12 20 *)
  0x9b187dd8;       (* arm_MUL X24 X14 X24 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374fef8;       (* arm_LSR X24 X23 52 *)
  0x8b1802d6;       (* arm_ADD X22 X22 X24 *)
  0xd374cef7;       (* arm_LSL X23 X23 12 *)
  0x93d7b2d8;       (* arm_EXTR X24 X22 X23 44 *)
  0xba18014a;       (* arm_ADCS X10 X10 X24 *)
  0x8a0a035a;       (* arm_AND X26 X26 X10 *)
  0x9b0e7cd8;       (* arm_MUL X24 X6 X14 *)
  0xd36cfed6;       (* arm_LSR X22 X22 44 *)
  0x8b160318;       (* arm_ADD X24 X24 X22 *)
  0x9a180294;       (* arm_ADC X20 X20 X24 *)
  0xd349fe96;       (* arm_LSR X22 X20 9 *)
  0xb277da94;       (* arm_ORR X20 X20 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba1601ff;       (* arm_ADCS XZR X15 X22 *)
  0xba1f035f;       (* arm_ADCS XZR X26 XZR *)
  0xba1f029f;       (* arm_ADCS XZR X20 XZR *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0273;       (* arm_ADCS X19 X19 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x924021f6;       (* arm_AND X22 X15 (rvalue (word 511)) *)
  0x93cf260f;       (* arm_EXTR X15 X16 X15 9 *)
  0x93d02630;       (* arm_EXTR X16 X17 X16 9 *)
  0xa900400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&0))) *)
  0x93d12671;       (* arm_EXTR X17 X19 X17 9 *)
  0x93d324f3;       (* arm_EXTR X19 X7 X19 9 *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
  0x93c72507;       (* arm_EXTR X7 X8 X7 9 *)
  0x93c82528;       (* arm_EXTR X8 X9 X8 9 *)
  0xa9022007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&32))) *)
  0x93c92549;       (* arm_EXTR X9 X10 X9 9 *)
  0x93ca268a;       (* arm_EXTR X10 X20 X10 9 *)
  0xa9032809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&48))) *)
  0xf9002016;       (* arm_STR X22 X0 (Immediate_Offset (word 64)) *)
  0x910143ff;       (* arm_ADD SP SP (rvalue (word 80)) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_P521_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_mul_p521_unopt_mc;;

(* bignum_mul_p521_unopt_mc without callee-save register spills + ret. *)
let bignum_mul_p521_unopt_core_mc_def,
    bignum_mul_p521_unopt_core_mc,
    BIGNUM_MUL_P521_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_mul_p521_unopt_core_mc"
    bignum_mul_p521_unopt_mc
    (`20`,`LENGTH bignum_mul_p521_unopt_mc - 44`)
    (fst BIGNUM_MUL_P521_UNOPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_521_AS_WORDLIST = prove
 (`p_521 =
   bignum_of_wordlist
    [word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word(0x1FF)]`,
  REWRITE_TAC[p_521; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_EQ_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] = p_521 <=>
   (!i. i < 64
        ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
            bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
   (!i. i < 9 ==> bit i n8) /\ (!i. i < 64 ==> 9 <= i ==> ~bit i n8)`,
  REWRITE_TAC[P_521_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let BIGNUM_FROM_MEMORY_LE_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] <= p_521 <=>
   !i. i < 64 ==> 9 <= i ==> ~bit i n8`,
  SIMP_TAC[P_521; ARITH_RULE `p_521 = 2 EXP 521 - 1 ==>
    (n <= p_521 <=> n DIV 2 EXP (8 * 64) < 2 EXP 9)`] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `8`; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV; EXP; DIV_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; GSYM UPPER_BITS_ZERO] THEN
  MP_TAC(ISPEC `n8:int64` BIT_TRIVIAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MESON_TAC[NOT_LE]);;

let BIGNUM_FROM_MEMORY_LT_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] < p_521 <=>
   (!i. i < 64 ==> 9 <= i ==> ~bit i n8) /\
   ~((!i. i < 64
          ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
              bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
     (!i. i < 9 ==> bit i n8))`,
  GEN_REWRITE_TAC LAND_CONV [LT_LE] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_P521; BIGNUM_FROM_MEMORY_LE_P521] THEN
  MESON_TAC[]);;

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

let BIGNUM_MUL_P521_UNOPT_CORE_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_mul_p521_unopt_core_mc); (z,8 * 9); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_mul_p521_unopt_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p521_unopt_core_mc /\
                  read PC s = word(pc) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_mul_p521_unopt_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                         memory :> bytes(stackpointer,80)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC (1--624)] THEN

  (*** Digitize, deduce the bound on the top words ***)

  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `bignum_from_memory (y,9) s0` THEN
  SUBGOAL_THEN
   `a DIV 2 EXP 512 < 2 EXP 9 /\ b DIV 2 EXP 512 < 2 EXP 9`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a < p_521`; `b < p_521`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    STRIP_TAC] THEN

  (*** 4x4 multiplication of the low portions and its rebasing ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [5; 6; 7; 8; 10; 12; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25;
    26; 27; 33; 38; 40; 41; 47; 52; 54; 55; 56; 57; 58; 59; 65; 70;
    72; 73; 74; 80; 85; 87; 88; 89; 90; 91; 97; 102; 104; 105; 106;
    107; 113; 118; 120; 121; 122; 123]
   (1--133) THEN
  ABBREV_TAC
   `l = bignum_of_wordlist
         [sum_s120; sum_s121; sum_s122; sum_s123; word_shl mullo_s5 9;
          word_subword
           ((word_join:int64->int64->int128) sum_s52 mullo_s5) (55,64);
          word_subword
           ((word_join:int64->int64->int128) sum_s85 sum_s52) (55,64);
          word_subword
           ((word_join:int64->int64->int128) sum_s118 sum_s85) (55,64);
          word_ushr sum_s118 55]` THEN
  SUBGOAL_THEN
   `l < 2 EXP 521 /\
    (2 EXP 256 * l ==
     bignum_of_wordlist[x_0;x_1;x_2;x_3] *
     bignum_of_wordlist[y_0;y_1;y_2;y_3]) (mod p_521)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; VAL_WORD_USHR] THEN
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) /\ y < 2 EXP 9
        ==> x + 2 EXP 512 * y < 2 EXP 521`) THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 55 * 2 EXP 9 = 2 EXP 64`] THEN
      REWRITE_TAC[VAL_BOUND_64] THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `bignum_of_wordlist[x_0;x_1;x_2;x_3] *
      bignum_of_wordlist[y_0;y_1;y_2;y_3] =
      bignum_of_wordlist[mullo_s5;sum_s52;sum_s85;sum_s118;
                         sum_s120;sum_s121;sum_s122;sum_s123]`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ADK_48_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR;
                BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** 4x4 multiplication of the high portions ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [138; 139; 140; 141; 143; 145; 147; 149; 150; 151; 152; 153;
    154; 155; 156; 157; 158; 159; 160; 166; 171; 173; 174; 180;
    185; 187; 188; 189; 190; 191; 192; 198; 203; 205; 206; 207;
    213; 218; 220; 221; 222; 223; 224; 230; 235; 237; 238; 239;
    240; 246; 251; 253; 254; 255; 256]
   (134--256) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [mullo_s138; sum_s185; sum_s218; sum_s251;
      sum_s253; sum_s254; sum_s255; sum_s256] =
    bignum_of_wordlist[x_4;x_5;x_6;x_7] *
    bignum_of_wordlist[y_4;y_5;y_6;y_7]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Addition combining high and low parts into hl ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [258; 259; 262; 263; 266; 267; 270; 271; 274]
   (257--275) THEN
  ABBREV_TAC
   `hl = bignum_of_wordlist
          [sum_s258; sum_s259; sum_s262; sum_s263;
           sum_s266; sum_s267; sum_s270; sum_s271; sum_s274]` THEN
  SUBGOAL_THEN
   `hl < 2 EXP 522 /\
    (2 EXP 256 * hl ==
     2 EXP 256 * bignum_of_wordlist[x_4;x_5;x_6;x_7] *
                 bignum_of_wordlist[y_4;y_5;y_6;y_7] +
     bignum_of_wordlist[x_0;x_1;x_2;x_3] *
     bignum_of_wordlist[y_0;y_1;y_2;y_3]) (mod p_521)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `!y:num. y < e /\ P y /\ (y < e ==> y = x)
              ==> x < e /\ P x`) THEN
    EXISTS_TAC
     `bignum_of_wordlist
       [mullo_s138; sum_s185; sum_s218; sum_s251; sum_s253; sum_s254;
        sum_s255; sum_s256] + l` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) /\ y < 2 EXP 521
        ==> x + y < 2 EXP 522`) THEN
      CONJ_TAC THENL [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; CONG_ADD_LCANCEL_EQ];
      DISCH_THEN(fun th ->
        MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 9)` THEN
        CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; ALL_TAC]) THEN
      MAP_EVERY EXPAND_TAC ["hl"; "l"] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
     ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
     REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `l:num` o concl)))] THEN

  (*** The sign-magnitude difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [277; 278; 280; 281; 284; 285; 287; 288;
    291; 293; 295; 297; 299; 301; 303; 305]
   (276--306) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; WORD_XOR_MASKS]) THEN
  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s288 <=> carry_s281)`;
   `xd = bignum_of_wordlist[sum_s291; sum_s293; sum_s295; sum_s297]`;
   `yd = bignum_of_wordlist[sum_s299; sum_s301; sum_s303; sum_s305]`] THEN
  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_4;x_5;x_6;x_7]) -
     &(bignum_of_wordlist[x_0;x_1;x_2;x_3])) *
    (&(bignum_of_wordlist[y_0;y_1;y_2;y_3]) -
     &(bignum_of_wordlist[y_4;y_5;y_6;y_7])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s281 * &xd) *
      (--(&1) pow bitval carry_s288 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s281 <=>
       bignum_of_wordlist[x_4;x_5;x_6;x_7] <
       bignum_of_wordlist[x_0;x_1;x_2;x_3]) /\
      (carry_s288 <=>
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

  (*** One more 4x4 multiplication of the cross-terms ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [307; 308; 309; 310; 312; 314; 316; 318; 319; 320; 321; 322;
    323; 324; 325; 326; 327; 328; 329; 335; 340; 342; 343; 349;
    354; 356; 357; 358; 359; 360; 361; 367; 372; 374; 375; 376;
    382; 387; 389; 390; 391; 392; 393; 399; 404; 406; 407; 408;
    409; 415; 420; 422; 423; 424; 425]
   (307--425) THEN
  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist
      [mullo_s307; sum_s354; sum_s387; sum_s420; sum_s422; sum_s423; sum_s424;
       sum_s425])`
  SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN
  MP_TAC(ASSUME `hl < 2 EXP 522`) THEN
  REWRITE_TAC[ARITH_RULE
   `n < 2 EXP 522 <=> n DIV 2 EXP 512 < 2 EXP 10`] THEN
  EXPAND_TAC "hl" THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
  DISCH_TAC THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [429; 431; 433; 435; 440; 442; 444; 446]
   (426--447) THEN
  ABBREV_TAC
   `hlm = bignum_of_wordlist
     [sum_s429; sum_s431; sum_s433; sum_s435;
      sum_s440; sum_s442; sum_s444; sum_s446;
      word_and (word_neg(word(bitval sgn))) (word 511)]` THEN
  SUBGOAL_THEN
   `(&hl +
     --(&1) pow bitval sgn *
     &(bignum_of_wordlist
       [mullo_s307; sum_s354; sum_s387; sum_s420; sum_s422; sum_s423;
        sum_s424; sum_s425]):int ==
     &2 pow 512 * &(val(sum_s274:int64) + bitval carry_s446) + &hlm)
    (mod &p_521)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hl"; "hlm"] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; p_521; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_add_th; int_sub_th; int_mul_th; int_pow_th;
                int_neg_th; int_of_num_th; bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN
    BOOL_CASES_TAC `sgn:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ABBREV_TAC `topcar:int64 = word_add sum_s274 (word(bitval carry_s446))` THEN
  SUBGOAL_THEN
   `val(sum_s274:int64) + bitval carry_s446 = val(topcar:int64) /\
    val(topcar:int64) <= 2 EXP 10`
  (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [MATCH_MP_TAC(ARITH_RULE
     `c <= 1 /\ s < 2 EXP 10 /\
      (s + c < 2 EXP 64 ==> y = s + c)
      ==> s + c = y /\ y <= 2 EXP 10`) THEN
    ASM_REWRITE_TAC[BITVAL_BOUND] THEN EXPAND_TAC "topcar" THEN
    SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64; VAL_WORD_BITVAL; MOD_LT];
    ALL_TAC] THEN
  ABBREV_TAC
   `hlm' = bignum_of_wordlist
     [sum_s440; sum_s442; sum_s444; sum_s446;
      word_or (word_shl sum_s429 9)
              (word_and (word_neg (word (bitval sgn))) (word 511));
      word_subword ((word_join:int64->int64->int128) sum_s431 sum_s429) (55,64);
      word_subword ((word_join:int64->int64->int128) sum_s433 sum_s431) (55,64);
      word_subword ((word_join:int64->int64->int128) sum_s435 sum_s433) (55,64);
      word_ushr sum_s435 55]` THEN
  SUBGOAL_THEN `(2 EXP 256 * hlm' == hlm) (mod p_521)` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hlm"; "hlm'"] THEN
    REWRITE_TAC[REAL_CONGRUENCE; p_521; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
     REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_USHR; BIT_WORD_MASK;
      BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN
    REAL_INTEGER_TAC;
    FIRST_X_ASSUM(MP_TAC o
     check(can (term_match [] `(x:int == y) (mod n)` o concl))) THEN
    REWRITE_TAC[num_congruent; IMP_IMP] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (INTEGER_RULE
     `(x:int == a + y) (mod n) /\ (y' == y) (mod n)
      ==> (x == a + y') (mod n)`))] THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [448; 449; 450; 451; 455; 457; 459; 461]
   (448--463) THEN
  ABBREV_TAC
   `newtop:int64 =
    word_add (word_add (word_ushr sum_s435 55) sum_s274)
             (word (bitval carry_s461))` THEN
  SUBGOAL_THEN
   `val(word_ushr (sum_s435:int64) 55) +
    val(sum_s274:int64) + bitval carry_s461 =
    val(newtop:int64) /\
    val(newtop:int64) <= 2 EXP 11`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `u < 2 EXP 9 /\ c <= 1 /\ s < 2 EXP 10 /\
      (u + s + c < 2 EXP 64 ==> y = u + s + c)
      ==> u + s + c = y /\ y <= 2 EXP 11`) THEN
    ASM_REWRITE_TAC[BITVAL_BOUND] THEN CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD_USHR] THEN
      MP_TAC(SPEC `sum_s435:int64` VAL_BOUND_64) THEN ARITH_TAC;
      EXPAND_TAC "newtop" THEN
      REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; VAL_WORD_BITVAL] THEN
      CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[ADD_ASSOC; MOD_LT]];
    ALL_TAC] THEN
  ABBREV_TAC
   `topsum = bignum_of_wordlist
     [sum_s448; sum_s449; sum_s450; sum_s451;
      sum_s455; sum_s457; sum_s459; sum_s461; newtop]` THEN
  SUBGOAL_THEN
   `(2 EXP 512 * (2 EXP 256 * val(topcar:int64) + topsum) ==
     bignum_of_wordlist [x_0; x_1; x_2; x_3; x_4; x_5; x_6; x_7] *
     bignum_of_wordlist [y_0; y_1; y_2; y_3; y_4; y_5; y_6; y_7])
    (mod p_521)`
  MP_TAC THENL
   [REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,4)] THEN
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_ARITH
     `(l + &2 pow 256 * h) * (l' + &2 pow 256 * h'):int =
      (&1 + &2 pow 256) * (&2 pow 256 * h * h' + l * l') +
      &2 pow 256 * (h - l) * (l' - h')`] THEN
    FIRST_X_ASSUM(MP_TAC o
     check(can (term_match [] `x:real = a pow n * y`) o concl)) THEN
    REWRITE_TAC[GSYM int_of_num_th; GSYM int_pow_th; GSYM int_mul_th;
                GSYM int_sub_th; GSYM int_add_th; GSYM int_neg_th] THEN
    REWRITE_TAC[GSYM int_eq] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN MATCH_MP_TAC(INTEGER_RULE
     `(a:int == b * x' + c) (mod n)
      ==> (x' == x) (mod n)
          ==> (a == b * x + c) (mod n)`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(hl + m:int == tc + e * hlm) (mod n)
      ==> (x == e * e * hl + e * tc + e * e * hlm) (mod n)
          ==> (x == (&1 + e) * e * hl + e * m) (mod n)`)) THEN
    REWRITE_TAC[INT_ARITH `(&2:int) pow 512 = &2 pow 256 * &2 pow 256`] THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC; GSYM INT_ADD_LDISTRIB] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `hl + hlm:int = s
      ==> (e * e * (tc + s) == e * e * (hl + tc + hlm)) (mod n)`) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN EXPAND_TAC "topsum" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
    MAP_EVERY EXPAND_TAC ["hl"; "hlm'"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`(a:int == b) (mod n)`; `(a:num == b) (mod n)`; `x:real = y`;
      `a:num = b * c`; `word_add a b = c`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `hl:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `hlm':num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `sgn:bool` o concl))) THEN
    DISCH_TAC] THEN

  (*** The intricate augmentation of the product with top words ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC
   [484; 498; 510; 527; 551; 566; 579; 590; 595]
   (464--595) THEN
  SUBGOAL_THEN
   `(a * b) MOD p_521 =
    (2 EXP 512 *
     (2 EXP 512 * val(x_8:int64) * val(y_8:int64) +
      val x_8 * bignum_of_wordlist[y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7] +
      val y_8 * bignum_of_wordlist[x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] +
      2 EXP 256 * val(topcar:int64) + topsum)) MOD p_521`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE
     `e * (e * h + x + y + z):num = e * (e * h + x + y) + e * z`] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [CONG]) THEN
    CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [CONG])] THEN
  SUBGOAL_THEN
   `2 EXP 512 * val(x_8:int64) * val(y_8:int64) +
    val x_8 * bignum_of_wordlist[y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7] +
    val y_8 * bignum_of_wordlist[x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] +
    2 EXP 256 * val(topcar:int64) + topsum =
    bignum_of_wordlist
     [sum_s484; sum_s498; sum_s510; sum_s527;
      sum_s551; sum_s566; sum_s579; sum_s590; sum_s595]`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      MATCH_MP_TAC(ARITH_RULE
       `c2 <= 2 EXP 9 * 2 EXP 9 /\
        x <= 2 EXP 9 * 2 EXP 512 /\ y <= 2 EXP 9 * 2 EXP 512 /\
        c <= 2 EXP 256 * 2 EXP 64 /\
        s < 2 EXP 512 * 2 EXP 11 + 2 EXP 512
        ==> 2 EXP 512 * c2 + x + y + c + s < 2 EXP 576`) THEN
      REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC LE_MULT2 THEN
          ASM_SIMP_TAC[LT_IMP_LE; LE_REFL; VAL_BOUND_64] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
          BOUNDER_TAC[]) THEN
      EXPAND_TAC "topsum" THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      MATCH_MP_TAC(ARITH_RULE
       `c <= 2 EXP 11 /\ s < 2 EXP 512
        ==> s + 2 EXP 512 * c < 2 EXP 512 * 2 EXP 11 + 2 EXP 512`) THEN
      ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 52 - 1`)) THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word(val(x:int64) * val(d:int64)))
               (word(val(y:int64) * val(e:int64))):int64 =
      word(val x * val d + val y * val e)`] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word x) (word_shl c 48):int64 =
      word(2 EXP 48 * val c + x)`] THEN
    MAP_EVERY ABBREV_TAC
     [`dx0:int64 = word_and x_0 (word (2 EXP 52 - 1))`;
      `dx1:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_1 x_0) (52,64))
                           (word (2 EXP 52 - 1))`;
      `dx2:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_2 x_1) (40,64))
                           (word (2 EXP 52 - 1))`;
      `dx3:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_3 x_2) (28,64))
                           (word (2 EXP 52 - 1))`;
      `dx4:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_4 x_3) (16,64))
                           (word (2 EXP 52 - 1))`;
      `dx5:int64 = word_and (word_ushr x_4 4) (word (2 EXP 52 - 1))`;
      `dx6:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_5 x_4) (56,64))
                           (word (2 EXP 52 - 1))`;
      `dx7:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_6 x_5) (44,64))
                           (word (2 EXP 52 - 1))`;
      `dx8:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) x_7 x_6) (32,64))
                           (word (2 EXP 52 - 1))`;
      `dx9:int64 = word_ushr x_7 20`;
      `dy0:int64 = word_and y_0 (word (2 EXP 52 - 1))`;
      `dy1:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_1 y_0) (52,64))
                           (word (2 EXP 52 - 1))`;
      `dy2:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_2 y_1) (40,64))
                           (word (2 EXP 52 - 1))`;
      `dy3:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_3 y_2) (28,64))
                           (word (2 EXP 52 - 1))`;
      `dy4:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_4 y_3) (16,64))
                           (word (2 EXP 52 - 1))`;
      `dy5:int64 = word_and (word_ushr y_4 4) (word (2 EXP 52 - 1))`;
      `dy6:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_5 y_4) (56,64))
                           (word (2 EXP 52 - 1))`;
      `dy7:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_6 y_5) (44,64))
                           (word (2 EXP 52 - 1))`;
      `dy8:int64 = word_and
        (word_subword ((word_join:int64->int64->int128) y_7 y_6) (32,64))
                           (word (2 EXP 52 - 1))`;
      `dy9:int64 = word_ushr y_7 20`;
      `e0:int64 = word(val(y_8:int64) * val(dx0:int64) +
                       val(x_8:int64) * val(dy0:int64))`;
      `e1:int64 =
       word_add (word(val(y_8:int64) * val(dx1:int64) +
                      val(x_8:int64) * val(dy1:int64)))
                (word_ushr e0 52)`;
      `e2:int64 =
       word_add (word(val(y_8:int64) * val(dx2:int64) +
                      val(x_8:int64) * val(dy2:int64)))
                (word_ushr e1 52)`;
      `e3:int64 =
       word_add (word(val(y_8:int64) * val(dx3:int64) +
                      val(x_8:int64) * val(dy3:int64)))
                (word_ushr e2 52)`;
      `e4:int64 =
       word_add (word(2 EXP 48 * val(topcar:int64) +
                      val(y_8:int64) * val(dx4:int64) +
                      val(x_8:int64) * val(dy4:int64)))
                (word_ushr e3 52)`;
      `e5:int64 =
       word_add (word(val(y_8:int64) * val(dx5:int64) +
                      val(x_8:int64) * val(dy5:int64)))
                (word_ushr e4 52)`;
      `e6:int64 =
       word_add (word(val(y_8:int64) * val(dx6:int64) +
                      val(x_8:int64) * val(dy6:int64)))
                (word_ushr e5 52)`;
      `e7:int64 =
       word_add (word(val(y_8:int64) * val(dx7:int64) +
                      val(x_8:int64) * val(dy7:int64)))
                (word_ushr e6 52)`;
      `e8:int64 =
       word_add (word(val(y_8:int64) * val(dx8:int64) +
                      val(x_8:int64) * val(dy8:int64)))
                (word_ushr e7 52)`;
      `e9:int64 =
       word_add (word(val(y_8:int64) * val(dx9:int64) +
                      val(x_8:int64) * val(dy9:int64)))
                (word_ushr e8 52)`;
      `f0:int64 = word_subword
       ((word_join:int64->int64->int128) e1 (word_shl e0 12)) (12,64)`;
      `f1:int64 = word_subword
       ((word_join:int64->int64->int128) e2 (word_shl e1 12)) (24,64)`;
      `f2:int64 = word_subword
       ((word_join:int64->int64->int128) e3 (word_shl e2 12)) (36,64)`;
      `f3:int64 = word_subword
       ((word_join:int64->int64->int128) e4 (word_shl e3 12)) (48,64)`;
      `f4:int64 = word_subword
        ((word_join:int64->int64->int128) e6
        (word_shl (word_subword ((word_join:int64->int64->int128) e5
              (word_shl e4 12)) (60,64)) 8)) (8,64)`;
      `f5:int64 = word_subword
       ((word_join:int64->int64->int128) e7 (word_shl e6 12)) (20,64)`;
      `f6:int64 = word_subword
        ((word_join:int64->int64->int128) e8 (word_shl e7 12)) (32,64)`;
      `f7:int64 = word_subword
        ((word_join:int64->int64->int128) e9 (word_shl e8 12)) (44,64)`;
      `f8:int64 = word_ushr e9 44`] THEN
    SUBGOAL_THEN
     `val(x_8:int64) * bignum_of_wordlist [y_0;y_1;y_2;y_3;y_4;y_5;y_6;y_7] +
      val(y_8:int64) * bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] +
      2 EXP 256 * val(topcar:int64) + topsum =
      bignum_of_wordlist[f0;f1;f2;f3;f4;f5;f6;f7;f8] + topsum`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `bignum_of_wordlist[x_0; x_1; x_2; x_3; x_4; x_5; x_6; x_7] =
        ITLIST (\(h:int64) t. val h + 2 EXP 52 * t)
               [dx0;dx1;dx2;dx3;dx4;dx5;dx6;dx7;dx8;dx9] 0 /\
        bignum_of_wordlist[y_0; y_1; y_2; y_3; y_4; y_5; y_6; y_7] =
        ITLIST (\(h:int64) t. val h + 2 EXP 52 * t)
               [dy0;dy1;dy2;dy3;dy4;dy5;dy6;dy7;dy8;dy9] 0 /\
        bignum_of_wordlist[f0; f1; f2; f3; f4; f5; f6; f7; f8] =
        2 EXP 520 * val(e9:int64) DIV 2 EXP 52 +
        ITLIST (\(h:int64) t. val h MOD 2 EXP 52 + 2 EXP 52 * t)
               [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9] 0`
      (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[ITLIST; ADD_CLAUSES; MULT_CLAUSES; bignum_of_wordlist] THEN
        REWRITE_TAC[GSYM VAL_WORD_USHR; GSYM VAL_WORD_AND_MASK_WORD] THEN
        REPEAT CONJ_TAC THENL
         [MAP_EVERY EXPAND_TAC
           ["dx0";"dx1";"dx2";"dx3";"dx4";"dx5";"dx6";"dx7";"dx8";"dx9"];
          MAP_EVERY EXPAND_TAC
           ["dy0";"dy1";"dy2";"dy3";"dy4";"dy5";"dy6";"dy7";"dy8";"dy9"];
          MAP_EVERY EXPAND_TAC
           ["f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8"]] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `val(y_8:int64) * val(dx0:int64) + val(x_8:int64) * val(dy0:int64) =
        val (e0:int64) /\
        val(y_8:int64) * val(dx1:int64) + val(x_8:int64) * val(dy1:int64) +
        val e0 DIV 2 EXP 52 = val(e1:int64) /\
        val(y_8:int64) * val(dx2:int64) + val(x_8:int64) * val(dy2:int64) +
        val e1 DIV 2 EXP 52 = val(e2:int64) /\
        val(y_8:int64) * val(dx3:int64) + val(x_8:int64) * val(dy3:int64) +
        val e2 DIV 2 EXP 52 = val(e3:int64) /\
        2 EXP 48 * val(topcar:int64) +
        val(y_8:int64) * val(dx4:int64) + val(x_8:int64) * val(dy4:int64) +
        val e3 DIV 2 EXP 52 = val(e4:int64) /\
        val(y_8:int64) * val(dx5:int64) + val(x_8:int64) * val(dy5:int64) +
        val e4 DIV 2 EXP 52 = val(e5:int64) /\
        val(y_8:int64) * val(dx6:int64) + val(x_8:int64) * val(dy6:int64) +
        val e5 DIV 2 EXP 52 = val(e6:int64) /\
        val(y_8:int64) * val(dx7:int64) + val(x_8:int64) * val(dy7:int64) +
        val e6 DIV 2 EXP 52 = val(e7:int64) /\
        val(y_8:int64) * val(dx8:int64) + val(x_8:int64) * val(dy8:int64) +
        val e7 DIV 2 EXP 52 = val(e8:int64) /\
        val(y_8:int64) * val(dx9:int64) + val(x_8:int64) * val(dy9:int64) +
        val e8 DIV 2 EXP 52 = val(e9:int64)`
      MP_TAC THENL [ALL_TAC; REWRITE_TAC[ITLIST] THEN ARITH_TAC] THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; VAL_WORD_USHR; DIMINDEX_64] THEN
      CONV_TAC SYM_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN MATCH_MP_TAC MOD_LT THEN
      (MATCH_MP_TAC(ARITH_RULE
        `c <= 2 EXP 10 /\ x < 2 EXP 63 ==> 2 EXP 48 * c + x < 2 EXP 64`) ORELSE
       MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 63 ==> x < 2 EXP 64`)) THEN
      ASM_REWRITE_TAC[] THEN
      (MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 /\
         m * e <= 2 EXP 9 * 2 EXP 52 /\
         f < 2 EXP 64
         ==> n * d + m * e + f DIV 2 EXP 52 < 2 EXP 63`) ORELSE
       MATCH_MP_TAC(ARITH_RULE
        `n * d <= 2 EXP 9 * 2 EXP 52 /\
         m * e <= 2 EXP 9 * 2 EXP 52
         ==> n * d + m * e < 2 EXP 63`)) THEN
      REWRITE_TAC[VAL_BOUND_64] THEN CONJ_TAC THEN
      MATCH_MP_TAC LE_MULT2 THEN
      CONJ_TAC THEN MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC
       ["dx0";"dx1";"dx2";"dx3";"dx4";"dx5";"dx6";"dx7";"dx8";"dx9";
        "dy0";"dy1";"dy2";"dy3";"dy4";"dy5";"dy6";"dy7";"dy8";"dy9"] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN TRY ARITH_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR] THEN MATCH_MP_TAC
       (ARITH_RULE `n < 2 EXP 64 ==> n DIV 2 EXP 20 < 2 EXP 52`) THEN
      MATCH_ACCEPT_TAC VAL_BOUND_64;
      ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    EXPAND_TAC "topsum" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o rev o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final modular reduction ***)

  ABBREV_TAC
   `n = bignum_of_wordlist
         [sum_s484; sum_s498; sum_s510; sum_s527; sum_s551; sum_s566;
          sum_s579; sum_s590; sum_s595]` THEN

  SUBGOAL_THEN `n < 2 EXP 576` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  SUBGOAL_THEN `n MOD p_521 = (n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `n = 2 EXP 521 * n DIV 2 EXP 521 + n MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n DIV 2 EXP 521 < 2 EXP 64 /\ n MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `n < 2 EXP 576` THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC (596--598) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s595 9`;
    `d:int64 = word_or sum_s595 (word 18446744073709551104)`;
    `dd:int64 =
      word_and sum_s498 (word_and sum_s510 (word_and sum_s527
       (word_and sum_s551 (word_and sum_s566
         (word_and sum_s579 sum_s590)))))`] THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC (599--601) (599--601) THEN
  SUBGOAL_THEN
   `carry_s601 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(sum_s484:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC (602--610) (602--610) THEN
  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s595:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s595:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [sum_s484; sum_s498; sum_s510; sum_s527;
      sum_s551; sum_s566; sum_s579; sum_s590] =
    n MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s601`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s601" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s498; sum_s510; sum_s527; sum_s551; sum_s566; sum_s579; sum_s590] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `sum_s484:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN SUBST1_TAC(SYM(ASSUME
     `word_and sum_s498 (word_and sum_s510 (word_and sum_s527
      (word_and sum_s551 (word_and sum_s566 (word_and sum_s579 sum_s590))))) =
      (dd:int64)`)) THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s595:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s595:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `sum_s484:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN
  SUBGOAL_THEN `val(h:int64) = n DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_ushr sum_s595 9 = (h:int64)`)) THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN
    MATCH_MP_TAC(ARITH_RULE
     `m DIV 2 EXP 512 = x ==> x DIV 2 EXP 9 = m DIV 2 EXP 521`) THEN
    EXPAND_TAC "n" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + n DIV 2 EXP 521 + 1 <=>
    p_521 <= n DIV 2 EXP 521 + n MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521 < p_521`
  MP_TAC THENL [REWRITE_TAC[MOD_LT_EQ; p_521] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521 =
    bignum_of_wordlist
     [sum_s602; sum_s603; sum_s604; sum_s605; sum_s606;
      sum_s607; sum_s608; sum_s609; word_and sum_s610 (word(2 EXP 9 - 1))]`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`521`;
      `if n DIV 2 EXP 521 + n MOD 2 EXP 521 < p_521
       then &(n DIV 2 EXP 521 + n MOD 2 EXP 521)
       else &(n DIV 2 EXP 521 + n MOD 2 EXP 521) - &p_521`] THEN
    REPEAT CONJ_TAC THENL
     [BOUNDER_TAC[];
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      ALL_TAC;
      W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `n < 2 EXP 576` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
    ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
    REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** The rotation to shift from the 512 position ***)

  ARM_STEPS_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC (611--624) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC MOD_DOWN_CONV THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[MOD_UNIQUE] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
   UNDISCH_TAC
   `bignum_of_wordlist
     [sum_s602; sum_s603; sum_s604; sum_s605; sum_s606;
      sum_s607; sum_s608; sum_s609; word_and sum_s610 (word(2 EXP 9 - 1))]
    < p_521` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_LT_P521; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[DIMINDEX_64; BIT_WORD_AND; BIT_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN (LABEL_TAC "*" o CONV_RULE(RAND_CONV CONJ_CANON_CONV)) THEN
  REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
  REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_AND; BIT_WORD;
              BIT_WORD_USHR; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV CONJ_CANON_CONV))) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MUL_P521_UNOPT_CORRECT = time prove
   (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_mul_p521_unopt_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_mul_p521_unopt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p521_unopt_mc /\
                  read PC s = word(pc + 20) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + 20 + LENGTH bignum_mul_p521_unopt_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                         memory :> bytes(stackpointer,80)])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MUL_P521_UNOPT_CORE_CORRECT
    bignum_mul_p521_unopt_core_mc_def
    [fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC;fst BIGNUM_MUL_P521_UNOPT_EXEC] THEN

  REPEAT (POP_ASSUM MP_TAC) THEN
  REWRITE_TAC([fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC;fst BIGNUM_MUL_P521_UNOPT_EXEC;ALL;
               NONOVERLAPPING_CLAUSES]) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC);;


(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-scheduled program
******************************************************************************)

(* This is the intermediate program that is equivalent to the core parts of
   bignum_mul_p521_base and bignum_mul_p521. This is a vectorized
   version of core of bignum_mul_p521_base but instructions are unscheduled. *)

let bignum_mul_p521_interm1_ops:int list = [
  0xa940542f; (* ldp    x15, x21, [x1] *)
  0xa941442a; (* ldp    x10, x17, [x1, #16] *)
  0xa940404d; (* ldp    x13, x16, [x2] *)
  0x3dc00032; (* ldr    q18, [x1] *)
  0x3dc0005c; (* ldr    q28, [x2] *)
  0xa9415045; (* ldp    x5, x20, [x2, #16] *)
  0x6f00e5f0; (* movi   v16.2d, #0xffffffff *)
  0x4e9c5b87; (* uzp2   v7.4s, v28.4s, v28.4s *)
  0x0ea12a44; (* xtn    v4.2s, v18.2d *)
  0x0ea12b81; (* xtn    v1.2s, v28.2d *)
  0x4ea00b9b; (* rev64  v27.4s, v28.4s *)
  0x2ea1c095; (* umull  v21.2d, v4.2s, v1.2s *)
  0x2ea7c09c; (* umull  v28.2d, v4.2s, v7.2s *)
  0x4e925a45; (* uzp2   v5.4s, v18.4s, v18.4s *)
  0x4eb29f72; (* mul    v18.4s, v27.4s, v18.4s *)
  0x6f6016bc; (* usra   v28.2d, v21.2d, #32 *)
  0x2ea7c0bd; (* umull  v29.2d, v5.2s, v7.2s *)
  0x6ea02a52; (* uaddlp v18.2d, v18.4s *)
  0x4e301f90; (* and    v16.16b, v28.16b, v16.16b *)
  0x2ea180b0; (* umlal  v16.2d, v5.2s, v1.2s *)
  0x4f605652; (* shl    v18.2d, v18.2d, #32 *)
  0x6f60179d; (* usra   v29.2d, v28.2d, #32 *)
  0x2ea18092; (* umlal  v18.2d, v4.2s, v1.2s *)
  0x6f60161d; (* usra   v29.2d, v16.2d, #32 *)
  0x4e083e48; (* mov    x8, v18.d[0] *)
  0x4e183e49; (* mov    x9, v18.d[1] *)
  0x9b057d46; (* mul    x6, x10, x5 *)
  0x9b147e33; (* mul    x19, x17, x20 *)
  0x4e083fae; (* mov    x14, v29.d[0] *)
  0xab0e0129; (* adds   x9, x9, x14 *)
  0x4e183fae; (* mov    x14, v29.d[1] *)
  0xba0e00c6; (* adcs   x6, x6, x14 *)
  0x9bc57d4e; (* umulh  x14, x10, x5 *)
  0xba0e0273; (* adcs   x19, x19, x14 *)
  0x9bd47e2e; (* umulh  x14, x17, x20 *)
  0x9a1f01ce; (* adc    x14, x14, xzr *)
  0xab08012b; (* adds   x11, x9, x8 *)
  0xba0900c9; (* adcs   x9, x6, x9 *)
  0xba060266; (* adcs   x6, x19, x6 *)
  0xba1301d3; (* adcs   x19, x14, x19 *)
  0x9a0e03ee; (* adc    x14, xzr, x14 *)
  0xab080123; (* adds   x3, x9, x8 *)
  0xba0b00d8; (* adcs   x24, x6, x11 *)
  0xba090269; (* adcs   x9, x19, x9 *)
  0xba0601c6; (* adcs   x6, x14, x6 *)
  0xba1303f3; (* adcs   x19, xzr, x19 *)
  0x9a0e03ee; (* adc    x14, xzr, x14 *)
  0xeb110144; (* subs   x4, x10, x17 *)
  0xda842484; (* cneg   x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm  x7, cc  // cc = lo, ul, last *)
  0xeb050297; (* subs   x23, x20, x5 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul    x22, x4, x23 *)
  0x9bd77c84; (* umulh  x4, x4, x23 *)
  0xda8720e7; (* cinv   x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xca0702d7; (* eor    x23, x22, x7 *)
  0xba1700c6; (* adcs   x6, x6, x23 *)
  0xca070084; (* eor    x4, x4, x7 *)
  0xba040273; (* adcs   x19, x19, x4 *)
  0x9a0701ce; (* adc    x14, x14, x7 *)
  0xeb1501e4; (* subs   x4, x15, x21 *)
  0xda842484; (* cneg   x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm  x7, cc  // cc = lo, ul, last *)
  0xeb0d0217; (* subs   x23, x16, x13 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul    x22, x4, x23 *)
  0x9bd77c84; (* umulh  x4, x4, x23 *)
  0xda8720e7; (* cinv   x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xca0702d7; (* eor    x23, x22, x7 *)
  0xba17016b; (* adcs   x11, x11, x23 *)
  0xca070084; (* eor    x4, x4, x7 *)
  0xba040063; (* adcs   x3, x3, x4 *)
  0xba070318; (* adcs   x24, x24, x7 *)
  0xba070129; (* adcs   x9, x9, x7 *)
  0xba0700c6; (* adcs   x6, x6, x7 *)
  0xba070273; (* adcs   x19, x19, x7 *)
  0x9a0701ce; (* adc    x14, x14, x7 *)
  0xeb1102a4; (* subs   x4, x21, x17 *)
  0xda842484; (* cneg   x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm  x7, cc  // cc = lo, ul, last *)
  0xeb100297; (* subs   x23, x20, x16 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul    x22, x4, x23 *)
  0x9bd77c84; (* umulh  x4, x4, x23 *)
  0xda8720e7; (* cinv   x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xca0702d7; (* eor    x23, x22, x7 *)
  0xba170129; (* adcs   x9, x9, x23 *)
  0xca070084; (* eor    x4, x4, x7 *)
  0xba0400c6; (* adcs   x6, x6, x4 *)
  0xba070273; (* adcs   x19, x19, x7 *)
  0x9a0701ce; (* adc    x14, x14, x7 *)
  0xeb0a01e4; (* subs   x4, x15, x10 *)
  0xda842484; (* cneg   x4, x4, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm  x7, cc  // cc = lo, ul, last *)
  0xeb0d00b7; (* subs   x23, x5, x13 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0x9b177c96; (* mul    x22, x4, x23 *)
  0x9bd77c84; (* umulh  x4, x4, x23 *)
  0xda8720e7; (* cinv   x7, x7, cc  // cc = lo, ul, last *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xca0702d7; (* eor    x23, x22, x7 *)
  0xba170063; (* adcs   x3, x3, x23 *)
  0xca070084; (* eor    x4, x4, x7 *)
  0xba040318; (* adcs   x24, x24, x4 *)
  0xba070129; (* adcs   x9, x9, x7 *)
  0xba0700c6; (* adcs   x6, x6, x7 *)
  0xba070273; (* adcs   x19, x19, x7 *)
  0x9a0701ce; (* adc    x14, x14, x7 *)
  0xeb1101f1; (* subs   x17, x15, x17 *)
  0xda912631; (* cneg   x17, x17, cc  // cc = lo, ul, last *)
  0xda9f23e4; (* csetm  x4, cc  // cc = lo, ul, last *)
  0xeb0d028d; (* subs   x13, x20, x13 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e34; (* mul    x20, x17, x13 *)
  0x9bcd7e31; (* umulh  x17, x17, x13 *)
  0xda84208d; (* cinv   x13, x4, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn    x13, #0x1 *)
  0xca0d0294; (* eor    x20, x20, x13 *)
  0xba140314; (* adcs   x20, x24, x20 *)
  0xca0d0231; (* eor    x17, x17, x13 *)
  0xba110131; (* adcs   x17, x9, x17 *)
  0xba0d00c9; (* adcs   x9, x6, x13 *)
  0xba0d0266; (* adcs   x6, x19, x13 *)
  0x9a0d01cd; (* adc    x13, x14, x13 *)
  0xeb0a02b5; (* subs   x21, x21, x10 *)
  0xda9526b5; (* cneg   x21, x21, cc  // cc = lo, ul, last *)
  0xda9f23ea; (* csetm  x10, cc  // cc = lo, ul, last *)
  0xeb1000b0; (* subs   x16, x5, x16 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0x9b107ea5; (* mul    x5, x21, x16 *)
  0x9bd07eb5; (* umulh  x21, x21, x16 *)
  0xda8a214a; (* cinv   x10, x10, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn    x10, #0x1 *)
  0xca0a00b0; (* eor    x16, x5, x10 *)
  0xba100290; (* adcs   x16, x20, x16 *)
  0xca0a02b5; (* eor    x21, x21, x10 *)
  0xba150235; (* adcs   x21, x17, x21 *)
  0xba0a0131; (* adcs   x17, x9, x10 *)
  0xba0a00c5; (* adcs   x5, x6, x10 *)
  0x9a0a01aa; (* adc    x10, x13, x10 *)
  0xd377d90d; (* lsl    x13, x8, #9 *)
  0x93c8dd74; (* extr   x20, x11, x8, #55 *)
  0x93cbdc68; (* extr   x8, x3, x11, #55 *)
  0x93c3de09; (* extr   x9, x16, x3, #55 *)
  0xd377fe10; (* lsr    x16, x16, #55 *)
  0xa90047f5; (* stp    x21, x17, [sp] *)
  0xa9012be5; (* stp    x5, x10, [sp, #16] *)
  0xa90253ed; (* stp    x13, x20, [sp, #32] *)
  0xa90327e8; (* stp    x8, x9, [sp, #48] *)
  0xf90023f0; (* str    x16, [sp, #64] *)
  0xa9422835; (* ldp    x21, x10, [x1, #32] *)
  0xa9433431; (* ldp    x17, x13, [x1, #48] *)
  0xa9421450; (* ldp    x16, x5, [x2, #32] *)
  0x3dc00832; (* ldr    q18, [x1, #32] *)
  0x3dc0085c; (* ldr    q28, [x2, #32] *)
  0xa9432054; (* ldp    x20, x8, [x2, #48] *)
  0x6f00e5f0; (* movi   v16.2d, #0xffffffff *)
  0x4e9c5b87; (* uzp2   v7.4s, v28.4s, v28.4s *)
  0x0ea12a44; (* xtn    v4.2s, v18.2d *)
  0x0ea12b81; (* xtn    v1.2s, v28.2d *)
  0x4ea00b9c; (* rev64  v28.4s, v28.4s *)
  0x2ea1c09b; (* umull  v27.2d, v4.2s, v1.2s *)
  0x2ea7c09d; (* umull  v29.2d, v4.2s, v7.2s *)
  0x4e925a55; (* uzp2   v21.4s, v18.4s, v18.4s *)
  0x4eb29f9c; (* mul    v28.4s, v28.4s, v18.4s *)
  0x6f60177d; (* usra   v29.2d, v27.2d, #32 *)
  0x2ea7c2b2; (* umull  v18.2d, v21.2s, v7.2s *)
  0x6ea02b9c; (* uaddlp v28.2d, v28.4s *)
  0x4e301fb0; (* and    v16.16b, v29.16b, v16.16b *)
  0x2ea182b0; (* umlal  v16.2d, v21.2s, v1.2s *)
  0x4f60579c; (* shl    v28.2d, v28.2d, #32 *)
  0x6f6017b2; (* usra   v18.2d, v29.2d, #32 *)
  0x2ea1809c; (* umlal  v28.2d, v4.2s, v1.2s *)
  0x6f601612; (* usra   v18.2d, v16.2d, #32 *)
  0x4e083f89; (* mov    x9, v28.d[0] *)
  0x4e183f86; (* mov    x6, v28.d[1] *)
  0x9b147e33; (* mul    x19, x17, x20 *)
  0x9b087dae; (* mul    x14, x13, x8 *)
  0x4e083e4b; (* mov    x11, v18.d[0] *)
  0xab0b00c6; (* adds   x6, x6, x11 *)
  0x4e183e4b; (* mov    x11, v18.d[1] *)
  0xba0b0273; (* adcs   x19, x19, x11 *)
  0x9bd47e2b; (* umulh  x11, x17, x20 *)
  0xba0b01ce; (* adcs   x14, x14, x11 *)
  0x9bc87dab; (* umulh  x11, x13, x8 *)
  0x9a1f016b; (* adc    x11, x11, xzr *)
  0xab0900c3; (* adds   x3, x6, x9 *)
  0xba060266; (* adcs   x6, x19, x6 *)
  0xba1301d3; (* adcs   x19, x14, x19 *)
  0xba0e016e; (* adcs   x14, x11, x14 *)
  0x9a0b03eb; (* adc    x11, xzr, x11 *)
  0xab0900d8; (* adds   x24, x6, x9 *)
  0xba030264; (* adcs   x4, x19, x3 *)
  0xba0601c6; (* adcs   x6, x14, x6 *)
  0xba130173; (* adcs   x19, x11, x19 *)
  0xba0e03ee; (* adcs   x14, xzr, x14 *)
  0x9a0b03eb; (* adc    x11, xzr, x11 *)
  0xeb0d0227; (* subs   x7, x17, x13 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm  x23, cc  // cc = lo, ul, last *)
  0xeb140116; (* subs   x22, x8, x20 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul    x12, x7, x22 *)
  0x9bd67ce7; (* umulh  x7, x7, x22 *)
  0xda9722f7; (* cinv   x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn    x23, #0x1 *)
  0xca170196; (* eor    x22, x12, x23 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0xca1700e7; (* eor    x7, x7, x23 *)
  0xba0701ce; (* adcs   x14, x14, x7 *)
  0x9a17016b; (* adc    x11, x11, x23 *)
  0xeb0a02a7; (* subs   x7, x21, x10 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm  x23, cc  // cc = lo, ul, last *)
  0xeb1000b6; (* subs   x22, x5, x16 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul    x12, x7, x22 *)
  0x9bd67ce7; (* umulh  x7, x7, x22 *)
  0xda9722f7; (* cinv   x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn    x23, #0x1 *)
  0xca170196; (* eor    x22, x12, x23 *)
  0xba160063; (* adcs   x3, x3, x22 *)
  0xca1700e7; (* eor    x7, x7, x23 *)
  0xba070318; (* adcs   x24, x24, x7 *)
  0xba170084; (* adcs   x4, x4, x23 *)
  0xba1700c6; (* adcs   x6, x6, x23 *)
  0xba170273; (* adcs   x19, x19, x23 *)
  0xba1701ce; (* adcs   x14, x14, x23 *)
  0x9a17016b; (* adc    x11, x11, x23 *)
  0xeb0d0147; (* subs   x7, x10, x13 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm  x23, cc  // cc = lo, ul, last *)
  0xeb050116; (* subs   x22, x8, x5 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul    x12, x7, x22 *)
  0x9bd67ce7; (* umulh  x7, x7, x22 *)
  0xda9722f7; (* cinv   x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn    x23, #0x1 *)
  0xca170196; (* eor    x22, x12, x23 *)
  0xba1600c6; (* adcs   x6, x6, x22 *)
  0xca1700e7; (* eor    x7, x7, x23 *)
  0xba070273; (* adcs   x19, x19, x7 *)
  0xba1701ce; (* adcs   x14, x14, x23 *)
  0x9a17016b; (* adc    x11, x11, x23 *)
  0xeb1102a7; (* subs   x7, x21, x17 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm  x23, cc  // cc = lo, ul, last *)
  0xeb100296; (* subs   x22, x20, x16 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul    x12, x7, x22 *)
  0x9bd67ce7; (* umulh  x7, x7, x22 *)
  0xda9722f7; (* cinv   x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn    x23, #0x1 *)
  0xca170196; (* eor    x22, x12, x23 *)
  0xba160318; (* adcs   x24, x24, x22 *)
  0xca1700e7; (* eor    x7, x7, x23 *)
  0xba070084; (* adcs   x4, x4, x7 *)
  0xba1700c6; (* adcs   x6, x6, x23 *)
  0xba170273; (* adcs   x19, x19, x23 *)
  0xba1701ce; (* adcs   x14, x14, x23 *)
  0x9a17016b; (* adc    x11, x11, x23 *)
  0xeb0d02a7; (* subs   x7, x21, x13 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm  x23, cc  // cc = lo, ul, last *)
  0xeb100116; (* subs   x22, x8, x16 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul    x12, x7, x22 *)
  0x9bd67ce7; (* umulh  x7, x7, x22 *)
  0xda9722f7; (* cinv   x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn    x23, #0x1 *)
  0xca170196; (* eor    x22, x12, x23 *)
  0xba160084; (* adcs   x4, x4, x22 *)
  0xca1700e7; (* eor    x7, x7, x23 *)
  0xba0700c6; (* adcs   x6, x6, x7 *)
  0xba170273; (* adcs   x19, x19, x23 *)
  0xba1701ce; (* adcs   x14, x14, x23 *)
  0x9a17016b; (* adc    x11, x11, x23 *)
  0xeb110147; (* subs   x7, x10, x17 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23f7; (* csetm  x23, cc  // cc = lo, ul, last *)
  0xeb050296; (* subs   x22, x20, x5 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167cec; (* mul    x12, x7, x22 *)
  0x9bd67ce7; (* umulh  x7, x7, x22 *)
  0xda9722f7; (* cinv   x23, x23, cc  // cc = lo, ul, last *)
  0xb10006ff; (* cmn    x23, #0x1 *)
  0xca170196; (* eor    x22, x12, x23 *)
  0xba160084; (* adcs   x4, x4, x22 *)
  0xca1700e7; (* eor    x7, x7, x23 *)
  0xba0700c6; (* adcs   x6, x6, x7 *)
  0xba170273; (* adcs   x19, x19, x23 *)
  0xba1701ce; (* adcs   x14, x14, x23 *)
  0x9a17016b; (* adc    x11, x11, x23 *)
  0xa9405fe7; (* ldp    x7, x23, [sp] *)
  0xab070129; (* adds   x9, x9, x7 *)
  0xba170063; (* adcs   x3, x3, x23 *)
  0xa9000fe9; (* stp    x9, x3, [sp] *)
  0xa9410fe9; (* ldp    x9, x3, [sp, #16] *)
  0xba090309; (* adcs   x9, x24, x9 *)
  0xba030083; (* adcs   x3, x4, x3 *)
  0xa9010fe9; (* stp    x9, x3, [sp, #16] *)
  0xa9420fe9; (* ldp    x9, x3, [sp, #32] *)
  0xba0900c9; (* adcs   x9, x6, x9 *)
  0xba030266; (* adcs   x6, x19, x3 *)
  0xa9021be9; (* stp    x9, x6, [sp, #32] *)
  0xa9431be9; (* ldp    x9, x6, [sp, #48] *)
  0xba0901c9; (* adcs   x9, x14, x9 *)
  0xba060166; (* adcs   x6, x11, x6 *)
  0xa9031be9; (* stp    x9, x6, [sp, #48] *)
  0xf94023e9; (* ldr    x9, [sp, #64] *)
  0x9a1f0129; (* adc    x9, x9, xzr *)
  0xf90023e9; (* str    x9, [sp, #64] *)
  0xa9401829; (* ldp    x9, x6, [x1] *)
  0xeb0902b5; (* subs   x21, x21, x9 *)
  0xfa06014a; (* sbcs   x10, x10, x6 *)
  0xa9411829; (* ldp    x9, x6, [x1, #16] *)
  0xfa090231; (* sbcs   x17, x17, x9 *)
  0xfa0601ad; (* sbcs   x13, x13, x6 *)
  0xda9f23e9; (* csetm  x9, cc  // cc = lo, ul, last *)
  0xa9404c46; (* ldp    x6, x19, [x2] *)
  0xeb1000d0; (* subs   x16, x6, x16 *)
  0xfa050265; (* sbcs   x5, x19, x5 *)
  0xa9414c46; (* ldp    x6, x19, [x2, #16] *)
  0xfa1400d4; (* sbcs   x20, x6, x20 *)
  0xfa080268; (* sbcs   x8, x19, x8 *)
  0xda9f23e6; (* csetm  x6, cc  // cc = lo, ul, last *)
  0xca0902b5; (* eor    x21, x21, x9 *)
  0xeb0902b5; (* subs   x21, x21, x9 *)
  0xca09014a; (* eor    x10, x10, x9 *)
  0xfa09014a; (* sbcs   x10, x10, x9 *)
  0xca090231; (* eor    x17, x17, x9 *)
  0xfa090231; (* sbcs   x17, x17, x9 *)
  0xca0901ad; (* eor    x13, x13, x9 *)
  0xda0901ad; (* sbc    x13, x13, x9 *)
  0xca060210; (* eor    x16, x16, x6 *)
  0xeb060210; (* subs   x16, x16, x6 *)
  0xca0600a5; (* eor    x5, x5, x6 *)
  0xfa0600a5; (* sbcs   x5, x5, x6 *)
  0xca060294; (* eor    x20, x20, x6 *)
  0xfa060294; (* sbcs   x20, x20, x6 *)
  0xca060108; (* eor    x8, x8, x6 *)
  0xda060108; (* sbc    x8, x8, x6 *)
  0xca0900c9; (* eor    x9, x6, x9 *)
  0x9b107ea6; (* mul    x6, x21, x16 *)
  0x9b057d53; (* mul    x19, x10, x5 *)
  0x9b147e2e; (* mul    x14, x17, x20 *)
  0x9b087dab; (* mul    x11, x13, x8 *)
  0x9bd07ea3; (* umulh  x3, x21, x16 *)
  0xab030273; (* adds   x19, x19, x3 *)
  0x9bc57d43; (* umulh  x3, x10, x5 *)
  0xba0301ce; (* adcs   x14, x14, x3 *)
  0x9bd47e23; (* umulh  x3, x17, x20 *)
  0xba03016b; (* adcs   x11, x11, x3 *)
  0x9bc87da3; (* umulh  x3, x13, x8 *)
  0x9a1f0063; (* adc    x3, x3, xzr *)
  0xab060278; (* adds   x24, x19, x6 *)
  0xba1301d3; (* adcs   x19, x14, x19 *)
  0xba0e016e; (* adcs   x14, x11, x14 *)
  0xba0b006b; (* adcs   x11, x3, x11 *)
  0x9a0303e3; (* adc    x3, xzr, x3 *)
  0xab060264; (* adds   x4, x19, x6 *)
  0xba1801c7; (* adcs   x7, x14, x24 *)
  0xba130173; (* adcs   x19, x11, x19 *)
  0xba0e006e; (* adcs   x14, x3, x14 *)
  0xba0b03eb; (* adcs   x11, xzr, x11 *)
  0x9a0303e3; (* adc    x3, xzr, x3 *)
  0xeb0d0237; (* subs   x23, x17, x13 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb14010c; (* subs   x12, x8, x20 *)
  0xda8c258c; (* cneg   x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul    x15, x23, x12 *)
  0x9bcc7ef7; (* umulh  x23, x23, x12 *)
  0xda9622d6; (* cinv   x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn    x22, #0x1 *)
  0xca1601ec; (* eor    x12, x15, x22 *)
  0xba0c01ce; (* adcs   x14, x14, x12 *)
  0xca1602f7; (* eor    x23, x23, x22 *)
  0xba17016b; (* adcs   x11, x11, x23 *)
  0x9a160063; (* adc    x3, x3, x22 *)
  0xeb0a02b7; (* subs   x23, x21, x10 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb1000ac; (* subs   x12, x5, x16 *)
  0xda8c258c; (* cneg   x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul    x15, x23, x12 *)
  0x9bcc7ef7; (* umulh  x23, x23, x12 *)
  0xda9622d6; (* cinv   x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn    x22, #0x1 *)
  0xca1601ec; (* eor    x12, x15, x22 *)
  0xba0c0318; (* adcs   x24, x24, x12 *)
  0xca1602f7; (* eor    x23, x23, x22 *)
  0xba170084; (* adcs   x4, x4, x23 *)
  0xba1600e7; (* adcs   x7, x7, x22 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0xba1601ce; (* adcs   x14, x14, x22 *)
  0xba16016b; (* adcs   x11, x11, x22 *)
  0x9a160063; (* adc    x3, x3, x22 *)
  0xeb0d0157; (* subs   x23, x10, x13 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb05010c; (* subs   x12, x8, x5 *)
  0xda8c258c; (* cneg   x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul    x15, x23, x12 *)
  0x9bcc7ef7; (* umulh  x23, x23, x12 *)
  0xda9622d6; (* cinv   x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn    x22, #0x1 *)
  0xca1601ec; (* eor    x12, x15, x22 *)
  0xba0c0273; (* adcs   x19, x19, x12 *)
  0xca1602f7; (* eor    x23, x23, x22 *)
  0xba1701ce; (* adcs   x14, x14, x23 *)
  0xba16016b; (* adcs   x11, x11, x22 *)
  0x9a160063; (* adc    x3, x3, x22 *)
  0xeb1102b7; (* subs   x23, x21, x17 *)
  0xda9726f7; (* cneg   x23, x23, cc  // cc = lo, ul, last *)
  0xda9f23f6; (* csetm  x22, cc  // cc = lo, ul, last *)
  0xeb10028c; (* subs   x12, x20, x16 *)
  0xda8c258c; (* cneg   x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7eef; (* mul    x15, x23, x12 *)
  0x9bcc7ef7; (* umulh  x23, x23, x12 *)
  0xda9622d6; (* cinv   x22, x22, cc  // cc = lo, ul, last *)
  0xb10006df; (* cmn    x22, #0x1 *)
  0xca1601ec; (* eor    x12, x15, x22 *)
  0xba0c0084; (* adcs   x4, x4, x12 *)
  0xca1602f7; (* eor    x23, x23, x22 *)
  0xba1700e7; (* adcs   x7, x7, x23 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0xba1601ce; (* adcs   x14, x14, x22 *)
  0xba16016b; (* adcs   x11, x11, x22 *)
  0x9a160063; (* adc    x3, x3, x22 *)
  0xeb0d02b5; (* subs   x21, x21, x13 *)
  0xda9526b5; (* cneg   x21, x21, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm  x13, cc  // cc = lo, ul, last *)
  0xeb100110; (* subs   x16, x8, x16 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0x9b107ea8; (* mul    x8, x21, x16 *)
  0x9bd07eb5; (* umulh  x21, x21, x16 *)
  0xda8d21ad; (* cinv   x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn    x13, #0x1 *)
  0xca0d0110; (* eor    x16, x8, x13 *)
  0xba1000f0; (* adcs   x16, x7, x16 *)
  0xca0d02b5; (* eor    x21, x21, x13 *)
  0xba150275; (* adcs   x21, x19, x21 *)
  0xba0d01c8; (* adcs   x8, x14, x13 *)
  0xba0d0173; (* adcs   x19, x11, x13 *)
  0x9a0d006d; (* adc    x13, x3, x13 *)
  0xeb11014a; (* subs   x10, x10, x17 *)
  0xda8a254a; (* cneg   x10, x10, cc  // cc = lo, ul, last *)
  0xda9f23f1; (* csetm  x17, cc  // cc = lo, ul, last *)
  0xeb050285; (* subs   x5, x20, x5 *)
  0xda8524a5; (* cneg   x5, x5, cc  // cc = lo, ul, last *)
  0x9b057d54; (* mul    x20, x10, x5 *)
  0x9bc57d4a; (* umulh  x10, x10, x5 *)
  0xda912231; (* cinv   x17, x17, cc  // cc = lo, ul, last *)
  0xb100063f; (* cmn    x17, #0x1 *)
  0xca110285; (* eor    x5, x20, x17 *)
  0xba050210; (* adcs   x16, x16, x5 *)
  0xca11014a; (* eor    x10, x10, x17 *)
  0xba0a02b5; (* adcs   x21, x21, x10 *)
  0xba11010a; (* adcs   x10, x8, x17 *)
  0xba110265; (* adcs   x5, x19, x17 *)
  0x9a1101b1; (* adc    x17, x13, x17 *)
  0xa94053ed; (* ldp    x13, x20, [sp] *)
  0xa9414fe8; (* ldp    x8, x19, [sp, #16] *)
  0xca0900c6; (* eor    x6, x6, x9 *)
  0xab0d00c6; (* adds   x6, x6, x13 *)
  0xca09030e; (* eor    x14, x24, x9 *)
  0xba1401ce; (* adcs   x14, x14, x20 *)
  0xca09008b; (* eor    x11, x4, x9 *)
  0xba08016b; (* adcs   x11, x11, x8 *)
  0xca090210; (* eor    x16, x16, x9 *)
  0xba130210; (* adcs   x16, x16, x19 *)
  0xca0902b5; (* eor    x21, x21, x9 *)
  0xa94263e3; (* ldp    x3, x24, [sp, #32] *)
  0xa9431fe4; (* ldp    x4, x7, [sp, #48] *)
  0xf94023f7; (* ldr    x23, [sp, #64] *)
  0xba0302b5; (* adcs   x21, x21, x3 *)
  0xca09014a; (* eor    x10, x10, x9 *)
  0xba18014a; (* adcs   x10, x10, x24 *)
  0xca0900a5; (* eor    x5, x5, x9 *)
  0xba0400a5; (* adcs   x5, x5, x4 *)
  0xca090231; (* eor    x17, x17, x9 *)
  0xba070231; (* adcs   x17, x17, x7 *)
  0x9a1f02f6; (* adc    x22, x23, xzr *)
  0xab0d02b5; (* adds   x21, x21, x13 *)
  0xba14014a; (* adcs   x10, x10, x20 *)
  0xba0800ad; (* adcs   x13, x5, x8 *)
  0xba130231; (* adcs   x17, x17, x19 *)
  0x92402125; (* and    x5, x9, #0x1ff *)
  0xd377d8d4; (* lsl    x20, x6, #9 *)
  0xaa050285; (* orr    x5, x20, x5 *)
  0xba050065; (* adcs   x5, x3, x5 *)
  0x93c6ddd4; (* extr   x20, x14, x6, #55 *)
  0xba140314; (* adcs   x20, x24, x20 *)
  0x93cedd68; (* extr   x8, x11, x14, #55 *)
  0xba080088; (* adcs   x8, x4, x8 *)
  0x93cbde09; (* extr   x9, x16, x11, #55 *)
  0xba0900e9; (* adcs   x9, x7, x9 *)
  0xd377fe10; (* lsr    x16, x16, #55 *)
  0x9a170210; (* adc    x16, x16, x23 *)
  0xf9402046; (* ldr    x6, [x2, #64] *)
  0xa9403833; (* ldp    x19, x14, [x1] *)
  0x9240ce6b; (* and    x11, x19, #0xfffffffffffff *)
  0x9b0b7ccb; (* mul    x11, x6, x11 *)
  0xf9402023; (* ldr    x3, [x1, #64] *)
  0xa9401058; (* ldp    x24, x4, [x2] *)
  0x9240cf07; (* and    x7, x24, #0xfffffffffffff *)
  0x9b077c67; (* mul    x7, x3, x7 *)
  0x8b07016b; (* add    x11, x11, x7 *)
  0x93d3d1d3; (* extr   x19, x14, x19, #52 *)
  0x9240ce73; (* and    x19, x19, #0xfffffffffffff *)
  0x9b137cd3; (* mul    x19, x6, x19 *)
  0x93d8d098; (* extr   x24, x4, x24, #52 *)
  0x9240cf18; (* and    x24, x24, #0xfffffffffffff *)
  0x9b187c78; (* mul    x24, x3, x24 *)
  0x8b180273; (* add    x19, x19, x24 *)
  0xd374fd78; (* lsr    x24, x11, #52 *)
  0x8b180273; (* add    x19, x19, x24 *)
  0xd374cd6b; (* lsl    x11, x11, #12 *)
  0x93cb326b; (* extr   x11, x19, x11, #12 *)
  0xab0b02b5; (* adds   x21, x21, x11 *)
  0xa941602b; (* ldp    x11, x24, [x1, #16] *)
  0xa9415c47; (* ldp    x7, x23, [x2, #16] *)
  0x93cea16e; (* extr   x14, x11, x14, #40 *)
  0x9240cdce; (* and    x14, x14, #0xfffffffffffff *)
  0x9b0e7cce; (* mul    x14, x6, x14 *)
  0x93c4a0e4; (* extr   x4, x7, x4, #40 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047c64; (* mul    x4, x3, x4 *)
  0x8b0401ce; (* add    x14, x14, x4 *)
  0xd374fe64; (* lsr    x4, x19, #52 *)
  0x8b0401ce; (* add    x14, x14, x4 *)
  0xd374ce73; (* lsl    x19, x19, #12 *)
  0x93d361d3; (* extr   x19, x14, x19, #24 *)
  0xba13014a; (* adcs   x10, x10, x19 *)
  0x93cb7313; (* extr   x19, x24, x11, #28 *)
  0x9240ce73; (* and    x19, x19, #0xfffffffffffff *)
  0x9b137cd3; (* mul    x19, x6, x19 *)
  0x93c772eb; (* extr   x11, x23, x7, #28 *)
  0x9240cd6b; (* and    x11, x11, #0xfffffffffffff *)
  0x9b0b7c6b; (* mul    x11, x3, x11 *)
  0x8b0b0273; (* add    x19, x19, x11 *)
  0xd374fdcb; (* lsr    x11, x14, #52 *)
  0x8b0b0273; (* add    x19, x19, x11 *)
  0xd374cdce; (* lsl    x14, x14, #12 *)
  0x93ce926e; (* extr   x14, x19, x14, #36 *)
  0xba0e01ad; (* adcs   x13, x13, x14 *)
  0x8a0d014e; (* and    x14, x10, x13 *)
  0xa942102b; (* ldp    x11, x4, [x1, #32] *)
  0xa9423047; (* ldp    x7, x12, [x2, #32] *)
  0x93d84178; (* extr   x24, x11, x24, #16 *)
  0x9240cf18; (* and    x24, x24, #0xfffffffffffff *)
  0x9b187cd8; (* mul    x24, x6, x24 *)
  0x93d740f7; (* extr   x23, x7, x23, #16 *)
  0x9240cef7; (* and    x23, x23, #0xfffffffffffff *)
  0x9b177c77; (* mul    x23, x3, x23 *)
  0x8b170318; (* add    x24, x24, x23 *)
  0xd3503ed7; (* lsl    x23, x22, #48 *)
  0x8b170318; (* add    x24, x24, x23 *)
  0xd374fe77; (* lsr    x23, x19, #52 *)
  0x8b170318; (* add    x24, x24, x23 *)
  0xd374ce73; (* lsl    x19, x19, #12 *)
  0x93d3c313; (* extr   x19, x24, x19, #48 *)
  0xba130231; (* adcs   x17, x17, x19 *)
  0x8a1101d3; (* and    x19, x14, x17 *)
  0xd344fd6e; (* lsr    x14, x11, #4 *)
  0x9240cdce; (* and    x14, x14, #0xfffffffffffff *)
  0x9b0e7cce; (* mul    x14, x6, x14 *)
  0xd344fcf7; (* lsr    x23, x7, #4 *)
  0x9240cef7; (* and    x23, x23, #0xfffffffffffff *)
  0x9b177c77; (* mul    x23, x3, x23 *)
  0x8b1701ce; (* add    x14, x14, x23 *)
  0xd374ff17; (* lsr    x23, x24, #52 *)
  0x8b1701ce; (* add    x14, x14, x23 *)
  0xd374cf18; (* lsl    x24, x24, #12 *)
  0x93d8f1d8; (* extr   x24, x14, x24, #60 *)
  0x93cbe08b; (* extr   x11, x4, x11, #56 *)
  0x9240cd6b; (* and    x11, x11, #0xfffffffffffff *)
  0x9b0b7ccb; (* mul    x11, x6, x11 *)
  0x93c7e187; (* extr   x7, x12, x7, #56 *)
  0x9240cce7; (* and    x7, x7, #0xfffffffffffff *)
  0x9b077c67; (* mul    x7, x3, x7 *)
  0x8b07016b; (* add    x11, x11, x7 *)
  0xd374fdce; (* lsr    x14, x14, #52 *)
  0x8b0e016e; (* add    x14, x11, x14 *)
  0xd378df0b; (* lsl    x11, x24, #8 *)
  0x93cb21cb; (* extr   x11, x14, x11, #8 *)
  0xba0b00a5; (* adcs   x5, x5, x11 *)
  0x8a050273; (* and    x19, x19, x5 *)
  0xa943602b; (* ldp    x11, x24, [x1, #48] *)
  0xa9431c42; (* ldp    x2, x7, [x2, #48] *)
  0x93c4b164; (* extr   x4, x11, x4, #44 *)
  0x9240cc84; (* and    x4, x4, #0xfffffffffffff *)
  0x9b047cc4; (* mul    x4, x6, x4 *)
  0x93ccb057; (* extr   x23, x2, x12, #44 *)
  0x9240cef7; (* and    x23, x23, #0xfffffffffffff *)
  0x9b177c77; (* mul    x23, x3, x23 *)
  0x8b170084; (* add    x4, x4, x23 *)
  0xd374fdd7; (* lsr    x23, x14, #52 *)
  0x8b170084; (* add    x4, x4, x23 *)
  0xd374cdce; (* lsl    x14, x14, #12 *)
  0x93ce508e; (* extr   x14, x4, x14, #20 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0x8a140273; (* and    x19, x19, x20 *)
  0x93cb830e; (* extr   x14, x24, x11, #32 *)
  0x9240cdce; (* and    x14, x14, #0xfffffffffffff *)
  0x9b0e7cce; (* mul    x14, x6, x14 *)
  0x93c280e2; (* extr   x2, x7, x2, #32 *)
  0x9240cc42; (* and    x2, x2, #0xfffffffffffff *)
  0x9b027c62; (* mul    x2, x3, x2 *)
  0x8b0201c2; (* add    x2, x14, x2 *)
  0xd374fc8e; (* lsr    x14, x4, #52 *)
  0x8b0e0042; (* add    x2, x2, x14 *)
  0xd374cc8e; (* lsl    x14, x4, #12 *)
  0x93ce804e; (* extr   x14, x2, x14, #32 *)
  0xba0e0108; (* adcs   x8, x8, x14 *)
  0x8a080273; (* and    x19, x19, x8 *)
  0xd354ff0e; (* lsr    x14, x24, #20 *)
  0x9b0e7cce; (* mul    x14, x6, x14 *)
  0xd354fceb; (* lsr    x11, x7, #20 *)
  0x9b0b7c6b; (* mul    x11, x3, x11 *)
  0x8b0b01ce; (* add    x14, x14, x11 *)
  0xd374fc4b; (* lsr    x11, x2, #52 *)
  0x8b0b01ce; (* add    x14, x14, x11 *)
  0xd374cc42; (* lsl    x2, x2, #12 *)
  0x93c2b1c2; (* extr   x2, x14, x2, #44 *)
  0xba020129; (* adcs   x9, x9, x2 *)
  0x8a090262; (* and    x2, x19, x9 *)
  0x9b037cc6; (* mul    x6, x6, x3 *)
  0xd36cfdd3; (* lsr    x19, x14, #44 *)
  0x8b1300c6; (* add    x6, x6, x19 *)
  0x9a060210; (* adc    x16, x16, x6 *)
  0xd349fe06; (* lsr    x6, x16, #9 *)
  0xb277da10; (* orr    x16, x16, #0xfffffffffffffe00 *)
  0xeb1f03ff; (* cmp    xzr, xzr *)
  0xba0602bf; (* adcs   xzr, x21, x6 *)
  0xba1f005f; (* adcs   xzr, x2, xzr *)
  0xba1f021f; (* adcs   xzr, x16, xzr *)
  0xba0602b5; (* adcs   x21, x21, x6 *)
  0xba1f014a; (* adcs   x10, x10, xzr *)
  0xba1f01ad; (* adcs   x13, x13, xzr *)
  0xba1f0231; (* adcs   x17, x17, xzr *)
  0xba1f00a5; (* adcs   x5, x5, xzr *)
  0xba1f0294; (* adcs   x20, x20, xzr *)
  0xba1f0108; (* adcs   x8, x8, xzr *)
  0xba1f0129; (* adcs   x9, x9, xzr *)
  0x9a1f0210; (* adc    x16, x16, xzr *)
  0x924022a2; (* and    x2, x21, #0x1ff *)
  0x93d52555; (* extr   x21, x10, x21, #9 *)
  0x93ca25aa; (* extr   x10, x13, x10, #9 *)
  0xa9002815; (* stp    x21, x10, [x0] *)
  0x93cd2635; (* extr   x21, x17, x13, #9 *)
  0x93d124aa; (* extr   x10, x5, x17, #9 *)
  0xa9012815; (* stp    x21, x10, [x0, #16] *)
  0x93c52695; (* extr   x21, x20, x5, #9 *)
  0x93d4250a; (* extr   x10, x8, x20, #9 *)
  0xa9022815; (* stp    x21, x10, [x0, #32] *)
  0x93c82535; (* extr   x21, x9, x8, #9 *)
  0x93c9260a; (* extr   x10, x16, x9, #9 *)
  0xa9032815; (* stp    x21, x10, [x0, #48] *)
  0xf9002002; (* str    x2, [x0, #64] *)
];;

let bignum_mul_p521_interm1_core_mc =
  define_mc_from_intlist "bignum_mul_p521_interm1_core_mc" bignum_mul_p521_interm1_ops;;

let BIGNUM_MUL_P521_INTERM1_CORE_EXEC =
  ARM_MK_EXEC_RULE bignum_mul_p521_interm1_core_mc;;

let mul_p521_eqin = new_definition
  `!s1 s1' x y z stackpointer.
    (mul_p521_eqin:(armstate#armstate)->int64->int64->int64->int64->bool)
        (s1,s1') x y z stackpointer <=>
    (C_ARGUMENTS [z; x; y] s1 /\
     C_ARGUMENTS [z; x; y] s1' /\
     read SP s1 = stackpointer /\
     read SP s1' = stackpointer /\
     ?a. bignum_from_memory (x,9) s1 = a /\
         bignum_from_memory (x,9) s1' = a /\
     (?b. bignum_from_memory (y,9) s1 = b /\
          bignum_from_memory (y,9) s1' = b))`;;

let mul_p521_eqout = new_definition
  `!s1 s1' z stackpointer.
    (mul_p521_eqout:(armstate#armstate)->int64->int64->bool)
        (s1,s1') z stackpointer <=>
    (?a.
      read SP s1 = stackpointer /\
      read SP s1' = stackpointer /\
      bignum_from_memory (z,9) s1 = a /\
      bignum_from_memory (z,9) s1' = a)`;;

let actions = [
  ("equal", 0, 3, 0, 3);
  ("insert", 3, 3, 3, 5);
  ("equal", 3, 4, 5, 6);
  ("replace", 4, 6, 6, 26);
  ("equal", 6, 8, 26, 28);
  ("replace", 8, 9, 28, 29);
  ("equal", 9, 10, 29, 30);
  ("replace", 10, 11, 30, 31);
  ("equal", 11, 136, 31, 156);
  ("insert", 136, 136, 156, 158);
  ("equal", 136, 137, 158, 159);
  ("replace", 137, 139, 159, 179);
  ("equal", 139, 141, 179, 181);
  ("replace", 141, 142, 181, 182);
  ("equal", 142, 143, 182, 183);
  ("replace", 143, 144, 183, 184);
  ("equal", 144, 624, 184, 664);
];;

(* Vectorization loads a same memory location using one ldp to a pair of X
   registers and one ldr to one Q register. If one of these loads is abbreviated,
   then we lose the fact that ldr to Q is word_join of the ldp Xs. *)
let actions = break_equal_loads actions
    (snd BIGNUM_MUL_P521_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MUL_P521_INTERM1_CORE_EXEC) 0x0;;


let equiv_goal1 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_mul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_mul_p521_interm1_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_mul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_mul_p521_interm1_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    mul_p521_eqin
    mul_p521_eqout
    bignum_mul_p521_unopt_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_mul_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
                       WORD_SQR64_HI; WORD_SQR128_DIGIT0]]
  @ (!extra_word_CONV);;

let BIGNUM_MUL_P521_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC;
    fst BIGNUM_MUL_P521_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC mul_p521_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MUL_P521_UNOPT_CORE_EXEC
    BIGNUM_MUL_P521_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[mul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,9) state`;
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

let bignum_mul_p521_mc =
  define_from_elf "bignum_mul_p521_mc"
    "arm/p521/bignum_mul_p521.o";;

let BIGNUM_MUL_P521_EXEC =
    ARM_MK_EXEC_RULE bignum_mul_p521_mc;;

let bignum_mul_p521_core_mc_def,
    bignum_mul_p521_core_mc,
    BIGNUM_MUL_P521_CORE_EXEC =
  mk_sublist_of_mc "bignum_mul_p521_core_mc"
    bignum_mul_p521_mc
    (`20`,`LENGTH bignum_mul_p521_mc - 44`)
    (fst BIGNUM_MUL_P521_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_mul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_mul_p521_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_mul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_mul_p521_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    mul_p521_eqin
    mul_p521_eqout
    bignum_mul_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_mul_p521_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;


(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws. *)

let inst_map = [5;2;4;158;6;157;7;8;11;1;10;9;48;15;50;164;163;3;27;161;18;49;62;162;168;21;28;12;14;13;167;63;64;35;16;171;65;23;66;174;165;166;69;67;176;17;68;169;51;19;55;26;52;22;20;53;170;160;73;172;24;33;175;173;29;54;31;177;30;25;32;34;36;37;38;39;57;40;71;41;59;42;43;44;45;46;47;56;58;60;61;80;81;82;83;84;87;70;72;85;74;75;86;76;77;78;145;79;112;114;113;115;144;89;116;118;119;95;97;151;96;117;98;99;102;100;128;130;129;131;101;135;132;88;90;91;92;121;93;133;104;94;103;105;159;106;107;134;155;108;109;110;123;180;111;120;122;124;188;125;126;137;127;136;138;139;179;140;147;186;184;148;141;182;142;153;146;143;201;152;150;203;202;181;204;149;154;208;205;178;207;183;156;185;187;189;190;191;206;192;193;212;194;215;217;216;218;219;222;195;210;196;220;197;198;221;199;200;209;211;224;213;214;233;234;235;226;236;240;237;223;225;238;227;228;239;229;230;242;231;232;244;248;249;250;251;255;252;241;243;253;245;246;247;254;265;257;266;267;268;269;272;256;259;258;270;260;261;262;271;263;264;274;276;273;275;323;326;277;278;279;280;324;316;325;319;327;328;329;317;338;318;340;344;320;321;322;281;282;283;284;332;285;342;330;288;286;339;341;334;343;336;345;331;287;333;335;292;290;355;337;289;291;293;297;294;351;295;296;298;346;299;300;301;353;305;302;350;303;309;306;304;348;307;308;313;310;311;349;314;312;352;315;357;354;356;347;358;370;371;372;373;377;374;359;360;375;361;362;376;363;364;379;365;366;367;368;381;369;384;385;386;387;391;388;378;380;389;382;383;402;390;403;404;393;395;392;394;396;397;398;399;400;401;417;418;419;405;406;409;434;435;436;407;437;441;408;438;420;421;424;411;410;413;412;422;414;415;470;416;423;450;451;426;452;453;454;457;425;439;428;427;492;429;440;472;468;430;431;432;433;455;442;505;443;456;444;445;446;459;447;513;506;448;514;449;458;460;461;466;462;474;476;467;463;481;477;464;465;504;469;493;483;494;485;471;507;478;473;475;480;479;496;482;484;498;486;487;488;500;502;489;515;490;509;508;491;495;497;499;510;525;501;516;503;511;517;527;528;539;526;518;540;512;561;520;522;529;530;519;541;521;542;552;531;523;543;524;532;554;555;544;553;533;580;556;569;557;545;558;581;534;559;570;535;536;546;537;538;548;547;582;560;549;550;565;562;563;594;564;571;583;566;584;611;593;612;576;585;598;572;573;599;608;595;574;609;578;596;623;597;567;586;575;621;577;579;600;587;588;589;590;604;613;591;610;551;568;601;602;624;603;605;617;606;592;614;607;622;625;632;615;616;626;618;628;627;619;629;620;633;630;634;635;636;638;631;637;639;640;641;642;651;643;652;664;644;653;645;655;654;646;656;647;658;657;648;659;649;660;661;650;662;663];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MUL_P521_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MUL_P521_INTERM1_CORE_EXEC;
    fst BIGNUM_MUL_P521_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC mul_p521_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC BIGNUM_MUL_P521_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MUL_P521_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[mul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,9) state`;
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
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_mul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_mul_p521_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_mul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_mul_p521_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    mul_p521_eqin
    mul_p521_eqout
    bignum_mul_p521_unopt_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_mul_p521_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;

let mul_p521_eqout_TRANS = prove(
  `!s s2 s' z stackpointer.
    mul_p521_eqout (s,s') z stackpointer/\
    mul_p521_eqout (s',s2) z stackpointer
    ==> mul_p521_eqout (s,s2) z stackpointer`,
  MESON_TAC[mul_p521_eqout]);;

let BIGNUM_MUL_P521_CORE_EQUIV = time prove(equiv_goal,
  REPEAT STRIP_TAC THEN
  (* To prove the goal, show that there exists an empty slot in the memory
     which can locate bignum_mul_p521_interm1_core_mc. *)
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc:int64,LENGTH bignum_mul_p521_unopt_core_mc);
        (word pc3:int64,LENGTH bignum_mul_p521_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc3:int64,LENGTH bignum_mul_p521_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_mul_p521_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_mul_p521_interm1_core_mc))
        [x,8 * 9; y,8 * 9; stackpointer,80] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    REPEAT (FIRST_X_ASSUM MP_TAC) THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MUL_P521_INTERM1_CORE_EXEC;
       fst BIGNUM_MUL_P521_CORE_EXEC;
       fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MUL_P521_CORE_EQUIV1,BIGNUM_MUL_P521_CORE_EQUIV2)
    (mul_p521_eqin,mul_p521_eqin,mul_p521_eqin)
    mul_p521_eqout_TRANS
    (BIGNUM_MUL_P521_UNOPT_CORE_EXEC,BIGNUM_MUL_P521_INTERM1_CORE_EXEC,
     BIGNUM_MUL_P521_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MUL_P521_SUBROUTINE_CORRECT
          from BIGNUM_MUL_P521_UNOPT_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MUL_P521_UNOPT_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `ALL (nonoverlapping
      (word pc:int64, LENGTH
        (APPEND bignum_mul_p521_unopt_core_mc barrier_inst_bytes)))
      [(z:int64,8 * 9); (stackpointer:int64,80)] /\
     aligned 16 stackpointer`
    [`z:int64`;`x:int64`;`y:int64`] bignum_mul_p521_unopt_core_mc
    `\s0. C_ARGUMENTS [z;x;y] s0 /\ read SP s0 = stackpointer`;;

let BIGNUM_MUL_P521_EVENTUALLY_N_AT_PC = time prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_mul_p521_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC]
    THEN CONV_TAC NUM_DIVIDES_CONV
    THEN NO_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MUL_P521_UNOPT_CORE_EXEC);;


let BIGNUM_MUL_P521_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MUL_P521_UNOPT_EXEC
    BIGNUM_MUL_P521_UNOPT_CORE_EXEC
    BIGNUM_MUL_P521_UNOPT_CORE_CORRECT
    BIGNUM_MUL_P521_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_MUL_P521_UNOPT_CORE_CORRECT with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_mul_p521_unopt_core_mc replaced with
    bignum_mul_p521_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_MUL_P521_CORE_CORRECT = prove
 (`!z x y a b pc2 stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc2,LENGTH bignum_mul_p521_core_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc2,LENGTH bignum_mul_p521_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_mul_p521_core_mc /\
                  read PC s = word(pc2) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc2 + LENGTH bignum_mul_p521_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                          memory :> bytes(stackpointer,80)])`,
  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      ALL (nonoverlapping (word pc,
        LENGTH (APPEND bignum_mul_p521_unopt_core_mc barrier_inst_bytes)))
      [(stackpointer:int64,80);(z:int64,8*9);(x:int64,8 * 9);(y:int64,8 * 9)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MUL_P521_UNOPT_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    time FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MUL_P521_CORE_EQUIV BIGNUM_MUL_P521_UNOPT_CORE_CORRECT_N
    (BIGNUM_MUL_P521_UNOPT_CORE_EXEC,BIGNUM_MUL_P521_CORE_EXEC)
    (mul_p521_eqin,mul_p521_eqout));;


let BIGNUM_MUL_P521_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_mul_p521_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_mul_p521_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p521_mc /\
                  read PC s = word(pc+20) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + (20 + LENGTH bignum_mul_p521_core_mc)) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                          memory :> bytes(stackpointer,80)])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MUL_P521_CORE_CORRECT
      bignum_mul_p521_core_mc_def
      [fst BIGNUM_MUL_P521_EXEC;
       fst BIGNUM_MUL_P521_CORE_EXEC]);;


let BIGNUM_MUL_P521_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_mul_p521_mc) /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [(word pc,LENGTH bignum_mul_p521_mc); (x,8 * 9); (y,8 * 9);
             (z,8 * 9)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p521_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = returnaddress /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 144),144)])`,
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)
    (REWRITE_RULE [fst BIGNUM_MUL_P521_CORE_EXEC;
                   fst BIGNUM_MUL_P521_EXEC]
     BIGNUM_MUL_P521_CORRECT) in
  REWRITE_TAC[fst BIGNUM_MUL_P521_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_P521_EXEC th
   `[X19;X20;X21;X22;X23;X24;X25;X26]` 144);;
