(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_521.                                              *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/p521/bignum_mul_p521.o";;
 ****)

let bignum_mul_p521_mc =
  define_assert_from_elf "bignum_mul_p521_mc" "arm/p521/bignum_mul_p521.o"
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

let BIGNUM_MUL_P521_EXEC = ARM_MK_EXEC_RULE bignum_mul_p521_mc;;

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

let BIGNUM_MUL_P521_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,0x9ec); (z,8 * 9); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,0x9ec)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p521_mc /\
                  read PC s = word(pc + 0x14) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + 0x9d4) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s = (a * b) MOD p_521))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,9);
                         memory :> bytes(stackpointer,80)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC BIGNUM_MUL_P521_EXEC (1--624)] THEN

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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC
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
        CONV_TAC NUM_RING;
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
  ARM_STEPS_TAC BIGNUM_MUL_P521_EXEC (596--598) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s595 9`;
    `d:int64 = word_or sum_s595 (word 18446744073709551104)`;
    `dd:int64 =
      word_and sum_s498 (word_and sum_s510 (word_and sum_s527
       (word_and sum_s551 (word_and sum_s566
         (word_and sum_s579 sum_s590)))))`] THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC (599--601) (599--601) THEN
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
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P521_EXEC (602--610) (602--610) THEN
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

  ARM_STEPS_TAC BIGNUM_MUL_P521_EXEC (611--624) THEN
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

let BIGNUM_MUL_P521_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 9) (word pc,0x9ec) /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [(word pc,0x9ec); (x,8 * 9); (y,8 * 9); (z,8 * 9)]
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
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MUL_P521_EXEC BIGNUM_MUL_P521_CORRECT
   `[X19;X20;X21;X22;X23;X24;X25;X26]` 144);;
