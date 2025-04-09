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

(**** print_literal_from_elf "arm/p521/unopt/bignum_montmul_p521_base.o";;
 ****)

let bignum_montmul_p521_unopt_mc =
  define_assert_from_elf "bignum_montmul_p521_unopt_mc" "arm/p521/unopt/bignum_montmul_p521_base.o"
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
  0xa9004410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c13;       (* arm_STP X19 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xd377d9f6;       (* arm_LSL X22 X15 9 *)
  0x92402294;       (* arm_AND X20 X20 (rvalue (word 511)) *)
  0xaa160294;       (* arm_ORR X20 X20 X22 *)
  0xa903500a;       (* arm_STP X10 X20 X0 (Immediate_Offset (iword (&48))) *)
  0xd377fdef;       (* arm_LSR X15 X15 55 *)
  0xf900200f;       (* arm_STR X15 X0 (Immediate_Offset (word 64)) *)
  0x910143ff;       (* arm_ADD SP SP (rvalue (word 80)) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_P521_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p521_unopt_mc;;

(* bignum_montmul_p521_unopt_mc without callee-save register spills + ret. *)
let bignum_montmul_p521_unopt_core_mc_def,
    bignum_montmul_p521_unopt_core_mc,
    BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p521_unopt_core_mc"
    bignum_montmul_p521_unopt_mc
    (`20`,`LENGTH bignum_montmul_p521_unopt_mc - 44`)
    (fst BIGNUM_MONTMUL_P521_UNOPT_EXEC);;

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

let BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_montmul_p521_unopt_core_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_montmul_p521_unopt_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_unopt_core_mc /\
                  read PC s = word(pc) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + LENGTH bignum_montmul_p521_unopt_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
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
              fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 /\ b < p_521 assumption for simplicity ***)

  ASM_CASES_TAC `a < p_521 /\ b < p_521` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    ARM_SIM_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC (1--619)] THEN

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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
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
  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
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
  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
   [484; 498; 510; 527; 551; 566; 579; 590; 595]
   (464--595) THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
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
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_ASSOC] THEN

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
  ARM_STEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC (596--598) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_ushr sum_s595 9`;
    `d:int64 = word_or sum_s595 (word 18446744073709551104)`;
    `dd:int64 =
      word_and sum_s498 (word_and sum_s510 (word_and sum_s527
       (word_and sum_s551 (word_and sum_s566
         (word_and sum_s579 sum_s590)))))`] THEN
  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC (599--601) (599--601) THEN
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
  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC (602--610) (602--610) THEN
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

  ARM_STEPS_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC (611--619) THEN
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
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_AND; BIT_WORD_OR;
       BIT_WORD; BIT_WORD_USHR; BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV CONJ_CANON_CONV))) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC(NUMBER_RULE
  `!e. (e * i == 1) (mod p) /\ (e * x == n) (mod p)
       ==> (i * n == x) (mod p)`) THEN
  EXISTS_TAC `2 EXP 576` THEN
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 576`); INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MONTMUL_P521_UNOPT_CORRECT = time prove
   (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_montmul_p521_unopt_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_montmul_p521_unopt_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_unopt_mc /\
                  read PC s = word(pc + 20) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + 20 + LENGTH bignum_montmul_p521_unopt_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                         memory :> bytes(stackpointer,80)])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT
    bignum_montmul_p521_unopt_core_mc_def
    [fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC;fst BIGNUM_MONTMUL_P521_UNOPT_EXEC] THEN

  REPEAT (POP_ASSUM MP_TAC) THEN
  REWRITE_TAC([fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC;fst BIGNUM_MONTMUL_P521_UNOPT_EXEC;ALL;
               NONOVERLAPPING_CLAUSES]) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC);;


(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-scheduled program
******************************************************************************)

(* This is the intermediate program that is equivalent to both
   bignum_montmul_p521_base and bignum_montmul_p521. This is a vectorized
   version of bignum_montmul_p521 but instructions are unscheduled. *)

let bignum_montmul_p521_interm1_ops:int list = [
  0xa9401c2e; (* ldp    x14, x7, [x1] *)
  0xa9416423; (* ldp    x3, x25, [x1, #16] *)
  0xa940604a; (* ldp    x10, x24, [x2] *)
  0x3dc00020; (* ldr    q0, [x1] *)
  0x3dc00059; (* ldr    q25, [x2] *)
  0xa941184c; (* ldp    x12, x6, [x2, #16] *)
  0x6f00e5f2; (* movi   v18.2d, #0xffffffff *)
  0x4e995b23; (* uzp2   v3.4s, v25.4s, v25.4s *)
  0x0ea1281a; (* xtn    v26.2s, v0.2d *)
  0x0ea12b36; (* xtn    v22.2s, v25.2d *)
  0x4ea00b38; (* rev64  v24.4s, v25.4s *)
  0x2eb6c353; (* umull  v19.2d, v26.2s, v22.2s *)
  0x2ea3c359; (* umull  v25.2d, v26.2s, v3.2s *)
  0x4e805814; (* uzp2   v20.4s, v0.4s, v0.4s *)
  0x4ea09f00; (* mul    v0.4s, v24.4s, v0.4s *)
  0x6f601679; (* usra   v25.2d, v19.2d, #32 *)
  0x2ea3c286; (* umull  v6.2d, v20.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e321f32; (* and    v18.16b, v25.16b, v18.16b *)
  0x2eb68292; (* umlal  v18.2d, v20.2s, v22.2s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x6f601726; (* usra   v6.2d, v25.2d, #32 *)
  0x2eb68340; (* umlal  v0.2d, v26.2s, v22.2s *)
  0x6f601646; (* usra   v6.2d, v18.2d, #32 *)
  0x4e083c17; (* mov    x23, v0.d[0] *)
  0x4e183c10; (* mov    x16, v0.d[1] *)
  0x9b0c7c65; (* mul    x5, x3, x12 *)
  0x9b067f35; (* mul    x21, x25, x6 *)
  0x4e083cd3; (* mov    x19, v6.d[0] *)
  0xab130210; (* adds   x16, x16, x19 *)
  0x4e183cd3; (* mov    x19, v6.d[1] *)
  0xba1300a5; (* adcs   x5, x5, x19 *)
  0x9bcc7c73; (* umulh  x19, x3, x12 *)
  0xba1302b5; (* adcs   x21, x21, x19 *)
  0x9bc67f33; (* umulh  x19, x25, x6 *)
  0x9a1f0273; (* adc    x19, x19, xzr *)
  0xab170208; (* adds   x8, x16, x23 *)
  0xba1000b0; (* adcs   x16, x5, x16 *)
  0xba0502a5; (* adcs   x5, x21, x5 *)
  0xba150275; (* adcs   x21, x19, x21 *)
  0x9a1303f3; (* adc    x19, xzr, x19 *)
  0xab17020b; (* adds   x11, x16, x23 *)
  0xba0800af; (* adcs   x15, x5, x8 *)
  0xba1002b0; (* adcs   x16, x21, x16 *)
  0xba050265; (* adcs   x5, x19, x5 *)
  0xba1503f5; (* adcs   x21, xzr, x21 *)
  0x9a1303f3; (* adc    x19, xzr, x19 *)
  0xeb190074; (* subs   x20, x3, x25 *)
  0xda942694; (* cneg   x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm  x9, cc  // cc = lo, ul, last *)
  0xeb0c00cd; (* subs   x13, x6, x12 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul    x26, x20, x13 *)
  0x9bcd7e94; (* umulh  x20, x20, x13 *)
  0xda892129; (* cinv   x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn    x9, #0x1 *)
  0xca09034d; (* eor    x13, x26, x9 *)
  0xba0d00a5; (* adcs   x5, x5, x13 *)
  0xca090294; (* eor    x20, x20, x9 *)
  0xba1402b5; (* adcs   x21, x21, x20 *)
  0x9a090273; (* adc    x19, x19, x9 *)
  0xeb0701d4; (* subs   x20, x14, x7 *)
  0xda942694; (* cneg   x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm  x9, cc  // cc = lo, ul, last *)
  0xeb0a030d; (* subs   x13, x24, x10 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul    x26, x20, x13 *)
  0x9bcd7e94; (* umulh  x20, x20, x13 *)
  0xda892129; (* cinv   x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn    x9, #0x1 *)
  0xca09034d; (* eor    x13, x26, x9 *)
  0xba0d0108; (* adcs   x8, x8, x13 *)
  0xca090294; (* eor    x20, x20, x9 *)
  0xba14016b; (* adcs   x11, x11, x20 *)
  0xba0901ef; (* adcs   x15, x15, x9 *)
  0xba090210; (* adcs   x16, x16, x9 *)
  0xba0900a5; (* adcs   x5, x5, x9 *)
  0xba0902b5; (* adcs   x21, x21, x9 *)
  0x9a090273; (* adc    x19, x19, x9 *)
  0xeb1900f4; (* subs   x20, x7, x25 *)
  0xda942694; (* cneg   x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm  x9, cc  // cc = lo, ul, last *)
  0xeb1800cd; (* subs   x13, x6, x24 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul    x26, x20, x13 *)
  0x9bcd7e94; (* umulh  x20, x20, x13 *)
  0xda892129; (* cinv   x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn    x9, #0x1 *)
  0xca09034d; (* eor    x13, x26, x9 *)
  0xba0d0210; (* adcs   x16, x16, x13 *)
  0xca090294; (* eor    x20, x20, x9 *)
  0xba1400a5; (* adcs   x5, x5, x20 *)
  0xba0902b5; (* adcs   x21, x21, x9 *)
  0x9a090273; (* adc    x19, x19, x9 *)
  0xeb0301d4; (* subs   x20, x14, x3 *)
  0xda942694; (* cneg   x20, x20, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm  x9, cc  // cc = lo, ul, last *)
  0xeb0a018d; (* subs   x13, x12, x10 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7e9a; (* mul    x26, x20, x13 *)
  0x9bcd7e94; (* umulh  x20, x20, x13 *)
  0xda892129; (* cinv   x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn    x9, #0x1 *)
  0xca09034d; (* eor    x13, x26, x9 *)
  0xba0d016b; (* adcs   x11, x11, x13 *)
  0xca090294; (* eor    x20, x20, x9 *)
  0xba1401ef; (* adcs   x15, x15, x20 *)
  0xba090210; (* adcs   x16, x16, x9 *)
  0xba0900a5; (* adcs   x5, x5, x9 *)
  0xba0902b5; (* adcs   x21, x21, x9 *)
  0x9a090273; (* adc    x19, x19, x9 *)
  0xeb1901d9; (* subs   x25, x14, x25 *)
  0xda992739; (* cneg   x25, x25, cc  // cc = lo, ul, last *)
  0xda9f23f4; (* csetm  x20, cc  // cc = lo, ul, last *)
  0xeb0a00ca; (* subs   x10, x6, x10 *)
  0xda8a254a; (* cneg   x10, x10, cc  // cc = lo, ul, last *)
  0x9b0a7f26; (* mul    x6, x25, x10 *)
  0x9bca7f39; (* umulh  x25, x25, x10 *)
  0xda94228a; (* cinv   x10, x20, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn    x10, #0x1 *)
  0xca0a00c6; (* eor    x6, x6, x10 *)
  0xba0601e6; (* adcs   x6, x15, x6 *)
  0xca0a0339; (* eor    x25, x25, x10 *)
  0xba190219; (* adcs   x25, x16, x25 *)
  0xba0a00b0; (* adcs   x16, x5, x10 *)
  0xba0a02a5; (* adcs   x5, x21, x10 *)
  0x9a0a026a; (* adc    x10, x19, x10 *)
  0xeb0300e7; (* subs   x7, x7, x3 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23e3; (* csetm  x3, cc  // cc = lo, ul, last *)
  0xeb180198; (* subs   x24, x12, x24 *)
  0xda982718; (* cneg   x24, x24, cc  // cc = lo, ul, last *)
  0x9b187cec; (* mul    x12, x7, x24 *)
  0x9bd87ce7; (* umulh  x7, x7, x24 *)
  0xda832063; (* cinv   x3, x3, cc  // cc = lo, ul, last *)
  0xb100047f; (* cmn    x3, #0x1 *)
  0xca030198; (* eor    x24, x12, x3 *)
  0xba1800d8; (* adcs   x24, x6, x24 *)
  0xca0300e7; (* eor    x7, x7, x3 *)
  0xba070327; (* adcs   x7, x25, x7 *)
  0xba030219; (* adcs   x25, x16, x3 *)
  0xba0300ac; (* adcs   x12, x5, x3 *)
  0x9a030143; (* adc    x3, x10, x3 *)
  0xd377daea; (* lsl    x10, x23, #9 *)
  0x93d7dd06; (* extr   x6, x8, x23, #55 *)
  0x93c8dd77; (* extr   x23, x11, x8, #55 *)
  0x93cbdf10; (* extr   x16, x24, x11, #55 *)
  0xd377ff18; (* lsr    x24, x24, #55 *)
  0xa90067e7; (* stp    x7, x25, [sp] *)
  0xa9010fec; (* stp    x12, x3, [sp, #16] *)
  0xa9021bea; (* stp    x10, x6, [sp, #32] *)
  0xa90343f7; (* stp    x23, x16, [sp, #48] *)
  0xf90023f8; (* str    x24, [sp, #64] *)
  0xa9420c27; (* ldp    x7, x3, [x1, #32] *)
  0x3dc00820; (* ldr    q0, [x1, #32] *)
  0xa9432839; (* ldp    x25, x10, [x1, #48] *)
  0xa9423058; (* ldp    x24, x12, [x2, #32] *)
  0x3dc00859; (* ldr    q25, [x2, #32] *)
  0xa9435c46; (* ldp    x6, x23, [x2, #48] *)
  0x3dc00c32; (* ldr    q18, [x1, #48] *)
  0x3dc00c43; (* ldr    q3, [x2, #48] *)
  0x4e801b3a; (* uzp1   v26.4s, v25.4s, v0.4s *)
  0x4ea00b39; (* rev64  v25.4s, v25.4s *)
  0x4e801816; (* uzp1   v22.4s, v0.4s, v0.4s *)
  0x4ea09f20; (* mul    v0.4s, v25.4s, v0.4s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x2eba82c0; (* umlal  v0.2d, v22.2s, v26.2s *)
  0x4e083c10; (* mov    x16, v0.d[0] *)
  0x4e183c05; (* mov    x5, v0.d[1] *)
  0x6f00e5e0; (* movi   v0.2d, #0xffffffff *)
  0x4e835879; (* uzp2   v25.4s, v3.4s, v3.4s *)
  0x0ea12a5a; (* xtn    v26.2s, v18.2d *)
  0x0ea12876; (* xtn    v22.2s, v3.2d *)
  0x4ea00878; (* rev64  v24.4s, v3.4s *)
  0x2eb6c353; (* umull  v19.2d, v26.2s, v22.2s *)
  0x2eb9c343; (* umull  v3.2d, v26.2s, v25.2s *)
  0x4e925a54; (* uzp2   v20.4s, v18.4s, v18.4s *)
  0x4eb29f12; (* mul    v18.4s, v24.4s, v18.4s *)
  0x6f601663; (* usra   v3.2d, v19.2d, #32 *)
  0x2eb9c286; (* umull  v6.2d, v20.2s, v25.2s *)
  0x6ea02a59; (* uaddlp v25.2d, v18.4s *)
  0x4e201c60; (* and    v0.16b, v3.16b, v0.16b *)
  0x2eb68280; (* umlal  v0.2d, v20.2s, v22.2s *)
  0x4f605739; (* shl    v25.2d, v25.2d, #32 *)
  0x6f601466; (* usra   v6.2d, v3.2d, #32 *)
  0x2eb68359; (* umlal  v25.2d, v26.2s, v22.2s *)
  0x6f601406; (* usra   v6.2d, v0.2d, #32 *)
  0x4e083f35; (* mov    x21, v25.d[0] *)
  0x4e183f33; (* mov    x19, v25.d[1] *)
  0x9bd87ce8; (* umulh  x8, x7, x24 *)
  0xab0800a5; (* adds   x5, x5, x8 *)
  0x9bcc7c68; (* umulh  x8, x3, x12 *)
  0xba0802b5; (* adcs   x21, x21, x8 *)
  0x4e083cc8; (* mov    x8, v6.d[0] *)
  0xba080273; (* adcs   x19, x19, x8 *)
  0x4e183cc8; (* mov    x8, v6.d[1] *)
  0x9a1f0108; (* adc    x8, x8, xzr *)
  0xab1000ab; (* adds   x11, x5, x16 *)
  0xba0502a5; (* adcs   x5, x21, x5 *)
  0xba150275; (* adcs   x21, x19, x21 *)
  0xba130113; (* adcs   x19, x8, x19 *)
  0x9a0803e8; (* adc    x8, xzr, x8 *)
  0xab1000af; (* adds   x15, x5, x16 *)
  0xba0b02b4; (* adcs   x20, x21, x11 *)
  0xba050265; (* adcs   x5, x19, x5 *)
  0xba150115; (* adcs   x21, x8, x21 *)
  0xba1303f3; (* adcs   x19, xzr, x19 *)
  0x9a0803e8; (* adc    x8, xzr, x8 *)
  0xeb0a0329; (* subs   x9, x25, x10 *)
  0xda892529; (* cneg   x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm  x13, cc  // cc = lo, ul, last *)
  0xeb0602fa; (* subs   x26, x23, x6 *)
  0xda9a275a; (* cneg   x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul    x22, x9, x26 *)
  0x9bda7d29; (* umulh  x9, x9, x26 *)
  0xda8d21ad; (* cinv   x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn    x13, #0x1 *)
  0xca0d02da; (* eor    x26, x22, x13 *)
  0xba1a02b5; (* adcs   x21, x21, x26 *)
  0xca0d0129; (* eor    x9, x9, x13 *)
  0xba090273; (* adcs   x19, x19, x9 *)
  0x9a0d0108; (* adc    x8, x8, x13 *)
  0xeb0300e9; (* subs   x9, x7, x3 *)
  0xda892529; (* cneg   x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm  x13, cc  // cc = lo, ul, last *)
  0xeb18019a; (* subs   x26, x12, x24 *)
  0xda9a275a; (* cneg   x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul    x22, x9, x26 *)
  0x9bda7d29; (* umulh  x9, x9, x26 *)
  0xda8d21ad; (* cinv   x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn    x13, #0x1 *)
  0xca0d02da; (* eor    x26, x22, x13 *)
  0xba1a016b; (* adcs   x11, x11, x26 *)
  0xca0d0129; (* eor    x9, x9, x13 *)
  0xba0901ef; (* adcs   x15, x15, x9 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba0d00a5; (* adcs   x5, x5, x13 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0x9a0d0108; (* adc    x8, x8, x13 *)
  0xeb0a0069; (* subs   x9, x3, x10 *)
  0xda892529; (* cneg   x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm  x13, cc  // cc = lo, ul, last *)
  0xeb0c02fa; (* subs   x26, x23, x12 *)
  0xda9a275a; (* cneg   x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul    x22, x9, x26 *)
  0x9bda7d29; (* umulh  x9, x9, x26 *)
  0xda8d21ad; (* cinv   x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn    x13, #0x1 *)
  0xca0d02da; (* eor    x26, x22, x13 *)
  0xba1a00a5; (* adcs   x5, x5, x26 *)
  0xca0d0129; (* eor    x9, x9, x13 *)
  0xba0902ae; (* adcs   x14, x21, x9 *)
  0xba0d0275; (* adcs   x21, x19, x13 *)
  0x9a0d0113; (* adc    x19, x8, x13 *)
  0xeb1900e9; (* subs   x9, x7, x25 *)
  0xda892528; (* cneg   x8, x9, cc  // cc = lo, ul, last *)
  0xda9f23e9; (* csetm  x9, cc  // cc = lo, ul, last *)
  0xeb1800cd; (* subs   x13, x6, x24 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0x9b0d7d1a; (* mul    x26, x8, x13 *)
  0x9bcd7d08; (* umulh  x8, x8, x13 *)
  0xda892129; (* cinv   x9, x9, cc  // cc = lo, ul, last *)
  0xb100053f; (* cmn    x9, #0x1 *)
  0xca09034d; (* eor    x13, x26, x9 *)
  0xba0d01ef; (* adcs   x15, x15, x13 *)
  0xca090108; (* eor    x8, x8, x9 *)
  0xba080288; (* adcs   x8, x20, x8 *)
  0xba0900a5; (* adcs   x5, x5, x9 *)
  0xba0901d4; (* adcs   x20, x14, x9 *)
  0xba0902b5; (* adcs   x21, x21, x9 *)
  0x9a090273; (* adc    x19, x19, x9 *)
  0xeb0a00e9; (* subs   x9, x7, x10 *)
  0xda892529; (* cneg   x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm  x13, cc  // cc = lo, ul, last *)
  0xeb1802fa; (* subs   x26, x23, x24 *)
  0xda9a275a; (* cneg   x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul    x22, x9, x26 *)
  0x9bda7d29; (* umulh  x9, x9, x26 *)
  0xda8d21ad; (* cinv   x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn    x13, #0x1 *)
  0xca0d02da; (* eor    x26, x22, x13 *)
  0xba1a0108; (* adcs   x8, x8, x26 *)
  0xca0d0129; (* eor    x9, x9, x13 *)
  0xba0900a5; (* adcs   x5, x5, x9 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0x9a0d0273; (* adc    x19, x19, x13 *)
  0xeb190069; (* subs   x9, x3, x25 *)
  0xda892529; (* cneg   x9, x9, cc  // cc = lo, ul, last *)
  0xda9f23ed; (* csetm  x13, cc  // cc = lo, ul, last *)
  0xeb0c00da; (* subs   x26, x6, x12 *)
  0xda9a275a; (* cneg   x26, x26, cc  // cc = lo, ul, last *)
  0x9b1a7d36; (* mul    x22, x9, x26 *)
  0x9bda7d29; (* umulh  x9, x9, x26 *)
  0xda8d21ad; (* cinv   x13, x13, cc  // cc = lo, ul, last *)
  0xb10005bf; (* cmn    x13, #0x1 *)
  0xca0d02da; (* eor    x26, x22, x13 *)
  0xba1a0108; (* adcs   x8, x8, x26 *)
  0xca0d0129; (* eor    x9, x9, x13 *)
  0xba0900a5; (* adcs   x5, x5, x9 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0x9a0d0273; (* adc    x19, x19, x13 *)
  0xa94037e9; (* ldp    x9, x13, [sp] *)
  0xab090210; (* adds   x16, x16, x9 *)
  0xba0d016b; (* adcs   x11, x11, x13 *)
  0xa9002ff0; (* stp    x16, x11, [sp] *)
  0xa9412ff0; (* ldp    x16, x11, [sp, #16] *)
  0xba1001f0; (* adcs   x16, x15, x16 *)
  0xba0b0108; (* adcs   x8, x8, x11 *)
  0xa90123f0; (* stp    x16, x8, [sp, #16] *)
  0xa94223f0; (* ldp    x16, x8, [sp, #32] *)
  0xba1000b0; (* adcs   x16, x5, x16 *)
  0xba080285; (* adcs   x5, x20, x8 *)
  0xa90217f0; (* stp    x16, x5, [sp, #32] *)
  0xa94317f0; (* ldp    x16, x5, [sp, #48] *)
  0xba1002b0; (* adcs   x16, x21, x16 *)
  0xba050265; (* adcs   x5, x19, x5 *)
  0xa90317f0; (* stp    x16, x5, [sp, #48] *)
  0xf94023f0; (* ldr    x16, [sp, #64] *)
  0x9a1f0210; (* adc    x16, x16, xzr *)
  0xf90023f0; (* str    x16, [sp, #64] *)
  0xa9401430; (* ldp    x16, x5, [x1] *)
  0xeb1000e7; (* subs   x7, x7, x16 *)
  0xfa050063; (* sbcs   x3, x3, x5 *)
  0xa9411430; (* ldp    x16, x5, [x1, #16] *)
  0xfa100339; (* sbcs   x25, x25, x16 *)
  0xfa05014a; (* sbcs   x10, x10, x5 *)
  0xda9f23f0; (* csetm  x16, cc  // cc = lo, ul, last *)
  0xa9405445; (* ldp    x5, x21, [x2] *)
  0xeb1800b8; (* subs   x24, x5, x24 *)
  0xfa0c02ac; (* sbcs   x12, x21, x12 *)
  0xa9414c45; (* ldp    x5, x19, [x2, #16] *)
  0xfa0600a6; (* sbcs   x6, x5, x6 *)
  0xfa170277; (* sbcs   x23, x19, x23 *)
  0xda9f23e5; (* csetm  x5, cc  // cc = lo, ul, last *)
  0xca1000e7; (* eor    x7, x7, x16 *)
  0xeb1000e7; (* subs   x7, x7, x16 *)
  0xca100063; (* eor    x3, x3, x16 *)
  0xfa100063; (* sbcs   x3, x3, x16 *)
  0xca100339; (* eor    x25, x25, x16 *)
  0xfa100339; (* sbcs   x25, x25, x16 *)
  0xca10014a; (* eor    x10, x10, x16 *)
  0xda10014a; (* sbc    x10, x10, x16 *)
  0xca050318; (* eor    x24, x24, x5 *)
  0xeb050318; (* subs   x24, x24, x5 *)
  0xca05018c; (* eor    x12, x12, x5 *)
  0xfa05018c; (* sbcs   x12, x12, x5 *)
  0xca0500c6; (* eor    x6, x6, x5 *)
  0xfa0500c6; (* sbcs   x6, x6, x5 *)
  0xca0502f7; (* eor    x23, x23, x5 *)
  0xda0502f7; (* sbc    x23, x23, x5 *)
  0xca1000b0; (* eor    x16, x5, x16 *)
  0x9b187cf5; (* mul    x21, x7, x24 *)
  0x9b0c7c65; (* mul    x5, x3, x12 *)
  0x9b067f33; (* mul    x19, x25, x6 *)
  0x9b177d48; (* mul    x8, x10, x23 *)
  0x9bd87ceb; (* umulh  x11, x7, x24 *)
  0xab0b00a5; (* adds   x5, x5, x11 *)
  0x9bcc7c6b; (* umulh  x11, x3, x12 *)
  0xba0b0273; (* adcs   x19, x19, x11 *)
  0x9bc67f2b; (* umulh  x11, x25, x6 *)
  0xba0b0108; (* adcs   x8, x8, x11 *)
  0x9bd77d4b; (* umulh  x11, x10, x23 *)
  0x9a1f016b; (* adc    x11, x11, xzr *)
  0xab1500af; (* adds   x15, x5, x21 *)
  0xba050265; (* adcs   x5, x19, x5 *)
  0xba130113; (* adcs   x19, x8, x19 *)
  0xba080168; (* adcs   x8, x11, x8 *)
  0x9a0b03eb; (* adc    x11, xzr, x11 *)
  0xab1500b4; (* adds   x20, x5, x21 *)
  0xba0f0269; (* adcs   x9, x19, x15 *)
  0xba050105; (* adcs   x5, x8, x5 *)
  0xba130173; (* adcs   x19, x11, x19 *)
  0xba0803e8; (* adcs   x8, xzr, x8 *)
  0x9a0b03eb; (* adc    x11, xzr, x11 *)
  0xeb0a032d; (* subs   x13, x25, x10 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xeb0602f6; (* subs   x22, x23, x6 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul    x4, x13, x22 *)
  0x9bd67dad; (* umulh  x13, x13, x22 *)
  0xda9a235a; (* cinv   x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn    x26, #0x1 *)
  0xca1a0096; (* eor    x22, x4, x26 *)
  0xba160273; (* adcs   x19, x19, x22 *)
  0xca1a01ad; (* eor    x13, x13, x26 *)
  0xba0d0108; (* adcs   x8, x8, x13 *)
  0x9a1a016b; (* adc    x11, x11, x26 *)
  0xeb0300ed; (* subs   x13, x7, x3 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xeb180196; (* subs   x22, x12, x24 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul    x4, x13, x22 *)
  0x9bd67dad; (* umulh  x13, x13, x22 *)
  0xda9a235a; (* cinv   x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn    x26, #0x1 *)
  0xca1a0096; (* eor    x22, x4, x26 *)
  0xba1601ef; (* adcs   x15, x15, x22 *)
  0xca1a01ad; (* eor    x13, x13, x26 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba1a0129; (* adcs   x9, x9, x26 *)
  0xba1a00a5; (* adcs   x5, x5, x26 *)
  0xba1a0273; (* adcs   x19, x19, x26 *)
  0xba1a0108; (* adcs   x8, x8, x26 *)
  0x9a1a016b; (* adc    x11, x11, x26 *)
  0xeb0a006d; (* subs   x13, x3, x10 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xeb0c02f6; (* subs   x22, x23, x12 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul    x4, x13, x22 *)
  0x9bd67dad; (* umulh  x13, x13, x22 *)
  0xda9a235a; (* cinv   x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn    x26, #0x1 *)
  0xca1a0096; (* eor    x22, x4, x26 *)
  0xba1600a5; (* adcs   x5, x5, x22 *)
  0xca1a01ad; (* eor    x13, x13, x26 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0xba1a0108; (* adcs   x8, x8, x26 *)
  0x9a1a016b; (* adc    x11, x11, x26 *)
  0xeb1900ed; (* subs   x13, x7, x25 *)
  0xda8d25ad; (* cneg   x13, x13, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xeb1800d6; (* subs   x22, x6, x24 *)
  0xda9626d6; (* cneg   x22, x22, cc  // cc = lo, ul, last *)
  0x9b167da4; (* mul    x4, x13, x22 *)
  0x9bd67dad; (* umulh  x13, x13, x22 *)
  0xda9a235a; (* cinv   x26, x26, cc  // cc = lo, ul, last *)
  0xb100075f; (* cmn    x26, #0x1 *)
  0xca1a0096; (* eor    x22, x4, x26 *)
  0xba160294; (* adcs   x20, x20, x22 *)
  0xca1a01ad; (* eor    x13, x13, x26 *)
  0xba0d0129; (* adcs   x9, x9, x13 *)
  0xba1a00a5; (* adcs   x5, x5, x26 *)
  0xba1a0273; (* adcs   x19, x19, x26 *)
  0xba1a0108; (* adcs   x8, x8, x26 *)
  0x9a1a016b; (* adc    x11, x11, x26 *)
  0xeb0a00e7; (* subs   x7, x7, x10 *)
  0xda8724e7; (* cneg   x7, x7, cc  // cc = lo, ul, last *)
  0xda9f23ea; (* csetm  x10, cc  // cc = lo, ul, last *)
  0xeb1802f8; (* subs   x24, x23, x24 *)
  0xda982718; (* cneg   x24, x24, cc  // cc = lo, ul, last *)
  0x9b187cf7; (* mul    x23, x7, x24 *)
  0x9bd87ce7; (* umulh  x7, x7, x24 *)
  0xda8a214a; (* cinv   x10, x10, cc  // cc = lo, ul, last *)
  0xb100055f; (* cmn    x10, #0x1 *)
  0xca0a02f8; (* eor    x24, x23, x10 *)
  0xba180138; (* adcs   x24, x9, x24 *)
  0xca0a00e7; (* eor    x7, x7, x10 *)
  0xba0700a7; (* adcs   x7, x5, x7 *)
  0xba0a0277; (* adcs   x23, x19, x10 *)
  0xba0a0105; (* adcs   x5, x8, x10 *)
  0x9a0a016a; (* adc    x10, x11, x10 *)
  0xeb190063; (* subs   x3, x3, x25 *)
  0xda832463; (* cneg   x3, x3, cc  // cc = lo, ul, last *)
  0xda9f23f9; (* csetm  x25, cc  // cc = lo, ul, last *)
  0xeb0c00cc; (* subs   x12, x6, x12 *)
  0xda8c258c; (* cneg   x12, x12, cc  // cc = lo, ul, last *)
  0x9b0c7c66; (* mul    x6, x3, x12 *)
  0x9bcc7c63; (* umulh  x3, x3, x12 *)
  0xda992339; (* cinv   x25, x25, cc  // cc = lo, ul, last *)
  0xb100073f; (* cmn    x25, #0x1 *)
  0xca1900cc; (* eor    x12, x6, x25 *)
  0xba0c0318; (* adcs   x24, x24, x12 *)
  0xca190063; (* eor    x3, x3, x25 *)
  0xba0300e7; (* adcs   x7, x7, x3 *)
  0xba1902e3; (* adcs   x3, x23, x25 *)
  0xba1900ac; (* adcs   x12, x5, x25 *)
  0x9a190159; (* adc    x25, x10, x25 *)
  0xa9401bea; (* ldp    x10, x6, [sp] *)
  0xa94117f7; (* ldp    x23, x5, [sp, #16] *)
  0xca1002b5; (* eor    x21, x21, x16 *)
  0xab0a02b5; (* adds   x21, x21, x10 *)
  0xca1001f3; (* eor    x19, x15, x16 *)
  0xba060273; (* adcs   x19, x19, x6 *)
  0xca100288; (* eor    x8, x20, x16 *)
  0xba170108; (* adcs   x8, x8, x23 *)
  0xca100318; (* eor    x24, x24, x16 *)
  0xba050318; (* adcs   x24, x24, x5 *)
  0xca1000e7; (* eor    x7, x7, x16 *)
  0xa9423feb; (* ldp    x11, x15, [sp, #32] *)
  0xa94327f4; (* ldp    x20, x9, [sp, #48] *)
  0xf94023ed; (* ldr    x13, [sp, #64] *)
  0xba0b00e7; (* adcs   x7, x7, x11 *)
  0xca100063; (* eor    x3, x3, x16 *)
  0xba0f0063; (* adcs   x3, x3, x15 *)
  0xca10018c; (* eor    x12, x12, x16 *)
  0xba14018c; (* adcs   x12, x12, x20 *)
  0xca100339; (* eor    x25, x25, x16 *)
  0xba090339; (* adcs   x25, x25, x9 *)
  0x9a1f01ba; (* adc    x26, x13, xzr *)
  0xab0a00e7; (* adds   x7, x7, x10 *)
  0xba060063; (* adcs   x3, x3, x6 *)
  0xba17018a; (* adcs   x10, x12, x23 *)
  0xba050339; (* adcs   x25, x25, x5 *)
  0x9240220c; (* and    x12, x16, #0x1ff *)
  0xd377daa6; (* lsl    x6, x21, #9 *)
  0xaa0c00cc; (* orr    x12, x6, x12 *)
  0xba0c016c; (* adcs   x12, x11, x12 *)
  0x93d5de66; (* extr   x6, x19, x21, #55 *)
  0xba0601e6; (* adcs   x6, x15, x6 *)
  0x93d3dd17; (* extr   x23, x8, x19, #55 *)
  0xba170297; (* adcs   x23, x20, x23 *)
  0x93c8df10; (* extr   x16, x24, x8, #55 *)
  0xba100130; (* adcs   x16, x9, x16 *)
  0xd377ff18; (* lsr    x24, x24, #55 *)
  0x9a0d0318; (* adc    x24, x24, x13 *)
  0xf9402045; (* ldr    x5, [x2, #64] *)
  0xa9404c35; (* ldp    x21, x19, [x1] *)
  0x9240cea8; (* and    x8, x21, #0xfffffffffffff *)
  0x9b087ca8; (* mul    x8, x5, x8 *)
  0xf940202b; (* ldr    x11, [x1, #64] *)
  0xa940504f; (* ldp    x15, x20, [x2] *)
  0x9240cde9; (* and    x9, x15, #0xfffffffffffff *)
  0x9b097d69; (* mul    x9, x11, x9 *)
  0x8b090108; (* add    x8, x8, x9 *)
  0x93d5d275; (* extr   x21, x19, x21, #52 *)
  0x9240ceb5; (* and    x21, x21, #0xfffffffffffff *)
  0x9b157cb5; (* mul    x21, x5, x21 *)
  0x93cfd28f; (* extr   x15, x20, x15, #52 *)
  0x9240cdef; (* and    x15, x15, #0xfffffffffffff *)
  0x9b0f7d6f; (* mul    x15, x11, x15 *)
  0x8b0f02b5; (* add    x21, x21, x15 *)
  0xd374fd0f; (* lsr    x15, x8, #52 *)
  0x8b0f02b5; (* add    x21, x21, x15 *)
  0xd374cd08; (* lsl    x8, x8, #12 *)
  0x93c832a8; (* extr   x8, x21, x8, #12 *)
  0xab0800e7; (* adds   x7, x7, x8 *)
  0xa9413c28; (* ldp    x8, x15, [x1, #16] *)
  0xa9413449; (* ldp    x9, x13, [x2, #16] *)
  0x93d3a113; (* extr   x19, x8, x19, #40 *)
  0x9240ce73; (* and    x19, x19, #0xfffffffffffff *)
  0x9b137cb3; (* mul    x19, x5, x19 *)
  0x93d4a134; (* extr   x20, x9, x20, #40 *)
  0x9240ce94; (* and    x20, x20, #0xfffffffffffff *)
  0x9b147d74; (* mul    x20, x11, x20 *)
  0x8b140273; (* add    x19, x19, x20 *)
  0xd374feb4; (* lsr    x20, x21, #52 *)
  0x8b140273; (* add    x19, x19, x20 *)
  0xd374ceb5; (* lsl    x21, x21, #12 *)
  0x93d56275; (* extr   x21, x19, x21, #24 *)
  0xba150063; (* adcs   x3, x3, x21 *)
  0x93c871f5; (* extr   x21, x15, x8, #28 *)
  0x9240ceb5; (* and    x21, x21, #0xfffffffffffff *)
  0x9b157cb5; (* mul    x21, x5, x21 *)
  0x93c971a8; (* extr   x8, x13, x9, #28 *)
  0x9240cd08; (* and    x8, x8, #0xfffffffffffff *)
  0x9b087d68; (* mul    x8, x11, x8 *)
  0x8b0802b5; (* add    x21, x21, x8 *)
  0xd374fe68; (* lsr    x8, x19, #52 *)
  0x8b0802b5; (* add    x21, x21, x8 *)
  0xd374ce73; (* lsl    x19, x19, #12 *)
  0x93d392b3; (* extr   x19, x21, x19, #36 *)
  0xba13014a; (* adcs   x10, x10, x19 *)
  0x8a0a0073; (* and    x19, x3, x10 *)
  0xa9425028; (* ldp    x8, x20, [x1, #32] *)
  0xa9425849; (* ldp    x9, x22, [x2, #32] *)
  0x93cf410f; (* extr   x15, x8, x15, #16 *)
  0x9240cdef; (* and    x15, x15, #0xfffffffffffff *)
  0x9b0f7ca4; (* mul    x4, x5, x15 *)
  0x93cd412f; (* extr   x15, x9, x13, #16 *)
  0x9240cdef; (* and    x15, x15, #0xfffffffffffff *)
  0x9b0f7d6f; (* mul    x15, x11, x15 *)
  0x8b0f008f; (* add    x15, x4, x15 *)
  0xd3503f4d; (* lsl    x13, x26, #48 *)
  0x8b0d01ef; (* add    x15, x15, x13 *)
  0xd374fead; (* lsr    x13, x21, #52 *)
  0x8b0d01ef; (* add    x15, x15, x13 *)
  0xd374ceb5; (* lsl    x21, x21, #12 *)
  0x93d5c1f5; (* extr   x21, x15, x21, #48 *)
  0xba150339; (* adcs   x25, x25, x21 *)
  0x8a190275; (* and    x21, x19, x25 *)
  0xd344fd13; (* lsr    x19, x8, #4 *)
  0x9240ce73; (* and    x19, x19, #0xfffffffffffff *)
  0x9b137cb3; (* mul    x19, x5, x19 *)
  0xd344fd3a; (* lsr    x26, x9, #4 *)
  0x9240cf4d; (* and    x13, x26, #0xfffffffffffff *)
  0x9b0d7d7a; (* mul    x26, x11, x13 *)
  0x8b1a0273; (* add    x19, x19, x26 *)
  0xd374fded; (* lsr    x13, x15, #52 *)
  0x8b0d0273; (* add    x19, x19, x13 *)
  0xd374cdef; (* lsl    x15, x15, #12 *)
  0x93cff26f; (* extr   x15, x19, x15, #60 *)
  0x93c8e288; (* extr   x8, x20, x8, #56 *)
  0x9240cd08; (* and    x8, x8, #0xfffffffffffff *)
  0x9b087ca8; (* mul    x8, x5, x8 *)
  0x93c9e2c9; (* extr   x9, x22, x9, #56 *)
  0x9240cd29; (* and    x9, x9, #0xfffffffffffff *)
  0x9b097d69; (* mul    x9, x11, x9 *)
  0x8b090108; (* add    x8, x8, x9 *)
  0xd374fe73; (* lsr    x19, x19, #52 *)
  0x8b130113; (* add    x19, x8, x19 *)
  0xd378dde8; (* lsl    x8, x15, #8 *)
  0x93c82268; (* extr   x8, x19, x8, #8 *)
  0xba08018c; (* adcs   x12, x12, x8 *)
  0x8a0c02b5; (* and    x21, x21, x12 *)
  0xa9432021; (* ldp    x1, x8, [x1, #48] *)
  0xa9433c42; (* ldp    x2, x15, [x2, #48] *)
  0x93d4b034; (* extr   x20, x1, x20, #44 *)
  0x9240ce94; (* and    x20, x20, #0xfffffffffffff *)
  0x9b147cb4; (* mul    x20, x5, x20 *)
  0x93d6b049; (* extr   x9, x2, x22, #44 *)
  0x9240cd29; (* and    x9, x9, #0xfffffffffffff *)
  0x9b097d69; (* mul    x9, x11, x9 *)
  0x8b090294; (* add    x20, x20, x9 *)
  0xd374fe69; (* lsr    x9, x19, #52 *)
  0x8b090296; (* add    x22, x20, x9 *)
  0xd374ce73; (* lsl    x19, x19, #12 *)
  0x93d352d3; (* extr   x19, x22, x19, #20 *)
  0xba1300c6; (* adcs   x6, x6, x19 *)
  0x8a0602b5; (* and    x21, x21, x6 *)
  0x93c18101; (* extr   x1, x8, x1, #32 *)
  0x9240cc21; (* and    x1, x1, #0xfffffffffffff *)
  0x9b017ca1; (* mul    x1, x5, x1 *)
  0x93c281e2; (* extr   x2, x15, x2, #32 *)
  0x9240cc42; (* and    x2, x2, #0xfffffffffffff *)
  0x9b027d62; (* mul    x2, x11, x2 *)
  0x8b020022; (* add    x2, x1, x2 *)
  0xd374fec1; (* lsr    x1, x22, #52 *)
  0x8b010042; (* add    x2, x2, x1 *)
  0xd374cec1; (* lsl    x1, x22, #12 *)
  0x93c18041; (* extr   x1, x2, x1, #32 *)
  0xba0102f7; (* adcs   x23, x23, x1 *)
  0x8a1702b5; (* and    x21, x21, x23 *)
  0xd354fd01; (* lsr    x1, x8, #20 *)
  0x9b017ca1; (* mul    x1, x5, x1 *)
  0xd354fdf3; (* lsr    x19, x15, #20 *)
  0x9b137d73; (* mul    x19, x11, x19 *)
  0x8b130021; (* add    x1, x1, x19 *)
  0xd374fc53; (* lsr    x19, x2, #52 *)
  0x8b130033; (* add    x19, x1, x19 *)
  0xd374cc42; (* lsl    x2, x2, #12 *)
  0x93c2b262; (* extr   x2, x19, x2, #44 *)
  0xba020210; (* adcs   x16, x16, x2 *)
  0x8a1002a2; (* and    x2, x21, x16 *)
  0x9b0b7ca5; (* mul    x5, x5, x11 *)
  0xd36cfe61; (* lsr    x1, x19, #44 *)
  0x8b0100a5; (* add    x5, x5, x1 *)
  0x9a050318; (* adc    x24, x24, x5 *)
  0xd349ff05; (* lsr    x5, x24, #9 *)
  0xb277db18; (* orr    x24, x24, #0xfffffffffffffe00 *)
  0xeb1f03ff; (* cmp    xzr, xzr *)
  0xba0500ff; (* adcs   xzr, x7, x5 *)
  0xba1f005f; (* adcs   xzr, x2, xzr *)
  0xba1f031f; (* adcs   xzr, x24, xzr *)
  0xba0500e7; (* adcs   x7, x7, x5 *)
  0xba1f0062; (* adcs   x2, x3, xzr *)
  0xba1f014a; (* adcs   x10, x10, xzr *)
  0xba1f0339; (* adcs   x25, x25, xzr *)
  0xba1f018c; (* adcs   x12, x12, xzr *)
  0xba1f00c6; (* adcs   x6, x6, xzr *)
  0xba1f02f7; (* adcs   x23, x23, xzr *)
  0xba1f0210; (* adcs   x16, x16, xzr *)
  0x9a1f0303; (* adc    x3, x24, xzr *)
  0xa9002802; (* stp    x2, x10, [x0] *)
  0xa9013019; (* stp    x25, x12, [x0, #16] *)
  0xa9025c06; (* stp    x6, x23, [x0, #32] *)
  0xd377d8f9; (* lsl    x25, x7, #9 *)
  0x92402063; (* and    x3, x3, #0x1ff *)
  0xaa190063; (* orr    x3, x3, x25 *)
  0xa9030c10; (* stp    x16, x3, [x0, #48] *)
  0xd377fcee; (* lsr    x14, x7, #55 *)
  0xf900200e; (* str    x14, [x0, #64] *)
];;

let bignum_montmul_p521_interm1_core_mc =
  define_mc_from_intlist "bignum_montmul_p521_interm1_core_mc" bignum_montmul_p521_interm1_ops;;

let BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC =
  ARM_MK_EXEC_RULE bignum_montmul_p521_interm1_core_mc;;

let montmul_p521_eqin = new_definition
  `!s1 s1' x y z stackpointer.
    (montmul_p521_eqin:(armstate#armstate)->int64->int64->int64->int64->bool)
        (s1,s1') x y z stackpointer <=>
    (C_ARGUMENTS [z; x; y] s1 /\
     C_ARGUMENTS [z; x; y] s1' /\
     read SP s1 = stackpointer /\
     read SP s1' = stackpointer /\
     ?a. bignum_from_memory (x,9) s1 = a /\
         bignum_from_memory (x,9) s1' = a /\
     (?b. bignum_from_memory (y,9) s1 = b /\
          bignum_from_memory (y,9) s1' = b))`;;

let montmul_p521_eqout = new_definition
  `!s1 s1' z stackpointer.
    (montmul_p521_eqout:(armstate#armstate)->int64->int64->bool)
        (s1,s1') z stackpointer <=>
    (?a.
      read SP s1 = stackpointer /\
      read SP s1' = stackpointer /\
      bignum_from_memory (z,9) s1 = a /\
      bignum_from_memory (z,9) s1' = a)`;;

(* This diff is generated by tools/gen-actions.py.
   To get this diff you will need an 'original register name'
   version of the bignum_montmul_p521_interm1_mc. *)
let actions = [
  ("equal", 0, 3, 0, 3);
  ("insert", 3, 3, 3, 5);
  ("equal", 3, 4, 5, 6);
  ("replace", 4, 6, 6, 26);
  ("equal", 6, 8, 26, 28);
  ("replace", 8, 9, 28, 29);
  ("equal", 9, 10, 29, 30);
  ("replace", 10, 11, 30, 31);
  ("equal", 11, 134, 31, 154);
  ("insert", 134, 134, 154, 155);
  ("equal", 134, 136, 155, 157);
  ("insert", 136, 136, 157, 158);
  ("equal", 136, 137, 158, 159);
  ("replace", 137, 141, 159, 190);
  ("equal", 141, 145, 190, 194);
  ("replace", 145, 146, 194, 195);
  ("equal", 146, 147, 195, 196);
  ("replace", 147, 148, 196, 197);
  ("equal", 148, 619, 197, 668);
];;

let actions = break_equal_loads actions
    (snd BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC) 0x0;;

let equiv_goal1 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montmul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_interm1_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_montmul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_interm1_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    montmul_p521_eqin
    montmul_p521_eqout
    bignum_montmul_p521_unopt_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_montmul_p521_interm1_core_mc
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

let BIGNUM_MONTMUL_P521_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC;
    fst BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p521_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
    BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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

let bignum_montmul_p521_mc =
  define_from_elf "bignum_montmul_p521_mc"
    "arm/p521/bignum_montmul_p521.o";;

let BIGNUM_MONTMUL_P521_EXEC =
    ARM_MK_EXEC_RULE bignum_montmul_p521_mc;;

let bignum_montmul_p521_core_mc_def,
    bignum_montmul_p521_core_mc,
    BIGNUM_MONTMUL_P521_CORE_EXEC =
  mk_sublist_of_mc "bignum_montmul_p521_core_mc"
    bignum_montmul_p521_mc
    (`20`,`LENGTH bignum_montmul_p521_mc - 44`)
    (fst BIGNUM_MONTMUL_P521_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `aligned 16 stackpointer /\
     ALL (nonoverlapping (z:int64,8 * 9))
       [(word pc,LENGTH bignum_montmul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_montmul_p521_interm1_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    montmul_p521_eqin
    montmul_p521_eqout
    bignum_montmul_p521_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_montmul_p521_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;


(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws. *)

let inst_map = [5;4;161;2;7;6;8;9;1;11;10;48;13;175;49;12;160;50;28;15;14;51;174;55;52;172;17;53;16;179;22;18;54;57;19;182;62;21;173;63;185;20;23;178;35;177;181;24;27;59;158;176;3;64;26;155;187;25;33;31;29;180;163;30;162;171;32;164;165;34;36;37;183;186;38;39;184;40;166;41;42;43;167;44;188;45;168;46;47;65;66;67;68;69;56;58;71;60;61;80;81;82;83;87;84;70;86;73;72;74;75;76;77;85;78;79;95;97;96;98;102;99;89;112;100;114;113;115;116;119;101;91;128;129;104;130;88;106;90;118;144;92;93;94;131;132;135;103;117;145;105;107;123;108;121;195;109;146;133;110;151;156;111;120;189;134;122;137;124;154;125;157;139;126;127;210;212;211;136;191;138;140;147;141;159;193;142;143;224;149;170;226;150;225;213;190;214;197;217;192;215;152;148;194;169;153;196;198;216;219;227;231;228;221;199;200;229;201;202;230;203;204;233;205;206;207;208;209;235;218;220;222;223;242;244;243;245;246;249;232;234;247;236;237;248;251;238;239;240;241;257;258;259;260;264;261;250;253;252;262;254;255;256;274;263;275;276;277;278;281;279;266;265;268;267;283;269;328;280;270;271;272;273;282;284;285;286;325;287;288;289;290;291;292;326;327;332;329;330;331;293;294;297;333;334;343;335;345;296;339;341;336;337;295;338;340;347;342;353;344;301;349;346;348;299;350;351;352;362;354;298;300;302;306;303;356;304;305;307;366;308;310;309;355;357;311;314;358;312;313;318;364;315;322;316;317;319;360;320;323;321;379;381;380;324;359;393;394;395;382;383;386;361;363;385;365;367;396;400;384;390;397;368;388;399;369;370;371;372;373;398;374;477;375;376;377;378;387;389;391;404;392;402;411;412;413;414;415;418;401;403;416;405;417;406;420;407;408;409;410;426;427;428;429;430;433;443;431;422;444;432;445;446;447;435;450;419;479;421;423;424;437;425;459;460;461;434;436;448;438;481;439;440;449;441;514;442;462;463;454;452;464;466;451;453;522;465;523;455;468;456;515;470;457;458;467;469;501;475;471;472;476;490;473;474;478;502;492;486;503;483;480;482;485;487;494;484;513;489;488;491;493;495;496;497;516;498;505;499;534;509;500;504;524;518;506;548;536;507;549;508;517;525;519;550;510;526;535;520;539;540;521;511;527;551;537;538;529;531;528;512;562;530;552;532;570;541;542;543;566;567;553;544;555;545;546;533;561;547;592;568;554;556;578;557;558;579;563;580;593;559;564;565;581;582;589;574;590;583;572;603;569;571;560;594;573;584;575;602;607;585;591;632;595;617;618;620;633;586;630;621;608;604;609;576;605;587;577;606;596;597;588;613;598;619;599;611;610;600;601;612;622;614;624;631;626;623;615;625;635;641;616;634;637;636;627;642;638;643;628;639;629;644;647;646;645;648;640;649;650;651;663;667;668;652;653;660;654;655;661;656;657;658;662;659;664;665;666];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTMUL_P521_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;SOME_FLAGS;
    MODIFIABLE_SIMD_REGS;ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTMUL_P521_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montmul_p521_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MONTMUL_P521_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montmul_p521_eqout;mk_equiv_regs;mk_equiv_bool_regs;
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
       [(word pc,LENGTH bignum_montmul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_core_mc)] /\
     ALL (nonoverlapping (stackpointer, 80))
       [(word pc,LENGTH bignum_montmul_p521_unopt_core_mc);
        (word pc2,LENGTH bignum_montmul_p521_core_mc);
        (z,8 * 9); (x:int64,8 * 9); (y:int64,8 * 9)]`
    montmul_p521_eqin
    montmul_p521_eqout
    bignum_montmul_p521_unopt_core_mc
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`
    bignum_montmul_p521_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                X10; X11; X12; X13; X14; X15; X16; X17; X19;
                X20; X21; X22; X23; X24; X25; X26] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bignum(z,9);
                memory :> bytes(stackpointer,80)]`;;

let montmul_p521_eqout_TRANS = prove(
  `!s s2 s' z stackpointer.
    montmul_p521_eqout (s,s') z stackpointer/\
    montmul_p521_eqout (s',s2) z stackpointer
    ==> montmul_p521_eqout (s,s2) z stackpointer`,
  MESON_TAC[montmul_p521_eqout]);;

let BIGNUM_MONTMUL_P521_CORE_EQUIV = time prove(equiv_goal,
  REPEAT STRIP_TAC THEN
  (* To prove the goal, show that there exists an empty slot in the memory
     which can locate bignum_montmul_p521_interm1_core_mc. *)
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc:int64,LENGTH bignum_montmul_p521_unopt_core_mc);
        (word pc3:int64,LENGTH bignum_montmul_p521_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 9))
        [(word pc3:int64,LENGTH bignum_montmul_p521_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montmul_p521_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montmul_p521_interm1_core_mc))
        [x,8 * 9; y,8 * 9; stackpointer,80] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    REPEAT (FIRST_X_ASSUM MP_TAC) THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTMUL_P521_CORE_EXEC;
       fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC;GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTMUL_P521_CORE_EQUIV1,BIGNUM_MONTMUL_P521_CORE_EQUIV2)
    (montmul_p521_eqin,montmul_p521_eqin,montmul_p521_eqin)
    montmul_p521_eqout_TRANS
    (BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P521_INTERM1_CORE_EXEC,
     BIGNUM_MONTMUL_P521_CORE_EXEC));;



(******************************************************************************
          Inducing BIGNUM_MONTMUL_P521_SUBROUTINE_CORRECT
          from BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `ALL (nonoverlapping
      (word pc:int64, LENGTH
        (APPEND bignum_montmul_p521_unopt_core_mc barrier_inst_bytes)))
      [(z:int64,8 * 9); (stackpointer:int64,80)] /\
     aligned 16 stackpointer`
    [`z:int64`;`x:int64`;`y:int64`] bignum_montmul_p521_unopt_core_mc
    `\s0. C_ARGUMENTS [z;x;y] s0 /\ read SP s0 = stackpointer`;;

let BIGNUM_MONTMUL_P521_EVENTUALLY_N_AT_PC = time prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC;
              BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montmul_p521_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                              fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC]
    THEN CONV_TAC NUM_DIVIDES_CONV
    THEN NO_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC);;


let BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTMUL_P521_UNOPT_EXEC
    BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC
    BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT
    BIGNUM_MONTMUL_P521_EVENTUALLY_N_AT_PC;;


(* This theorem is a copy of BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montmul_p521_unopt_core_mc replaced with
    bignum_montmul_p521_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)
let BIGNUM_MONTMUL_P521_CORE_CORRECT = prove
 (`!z x y a b pc2 stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc2,LENGTH bignum_montmul_p521_core_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc2,LENGTH bignum_montmul_p521_core_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montmul_p521_core_mc /\
                  read PC s = word(pc2) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc2 + LENGTH bignum_montmul_p521_core_mc) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
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
        LENGTH (APPEND bignum_montmul_p521_unopt_core_mc barrier_inst_bytes)))
      [(stackpointer:int64,80);(z:int64,8*9);(x:int64,8 * 9);(y:int64,8 * 9)] /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    time FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTMUL_P521_CORE_EQUIV BIGNUM_MONTMUL_P521_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTMUL_P521_UNOPT_CORE_EXEC,BIGNUM_MONTMUL_P521_CORE_EXEC)
    (montmul_p521_eqin,montmul_p521_eqout));;


let BIGNUM_MONTMUL_P521_CORRECT = prove
 (`!z x y a b pc stackpointer.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (stackpointer,80))
            [(word pc,LENGTH bignum_montmul_p521_mc); (z,8 * 9);
             (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_montmul_p521_mc)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_mc /\
                  read PC s = word(pc+20) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = word (pc + (20 + LENGTH bignum_montmul_p521_core_mc)) /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22; X23; X24; X25; X26] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9);
                          memory :> bytes(stackpointer,80)])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTMUL_P521_CORE_CORRECT
      bignum_montmul_p521_core_mc_def
      [fst BIGNUM_MONTMUL_P521_EXEC;
       fst BIGNUM_MONTMUL_P521_CORE_EXEC]);;


let BIGNUM_MONTMUL_P521_SUBROUTINE_CORRECT = prove
 (`!z x y a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 9) (word pc,LENGTH bignum_montmul_p521_mc) /\
        ALL (nonoverlapping (word_sub stackpointer (word 144),144))
            [(word pc,LENGTH bignum_montmul_p521_mc); (x,8 * 9); (y,8 * 9);
             (z,8 * 9)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p521_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = a /\
                  bignum_from_memory (y,9) s = b)
             (\s. read PC s = returnaddress /\
                  (a < p_521 /\ b < p_521
                   ==> bignum_from_memory (z,9) s =
                        (inverse_mod p_521 (2 EXP 576) * a * b) MOD p_521))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 144),144)])`,
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV)
    (REWRITE_RULE [fst BIGNUM_MONTMUL_P521_CORE_EXEC;
                   fst BIGNUM_MONTMUL_P521_EXEC]
     BIGNUM_MONTMUL_P521_CORRECT) in
  REWRITE_TAC[fst BIGNUM_MONTMUL_P521_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P521_EXEC th
   `[X19;X20;X21;X22;X23;X24;X25;X26]` 144);;
