(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Double (fresh and basepoint) scalar multiplication for edwards25519.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bignum_inv_p25519.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/edwards25519.ml";;
needs "EC/exprojective.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The code; however, the text segment here contains data at the end         *)
(* so we manually split that off to avoid confusing the decoder.             *)
(* ------------------------------------------------------------------------- *)

(**** print_coda_from_elf (-1) "arm/curve25519/edwards25519_scalarmuldouble_alt.o";;
 ****)

let edwards25519_scalarmuldouble_alt_mc,edwards25519_scalarmuldouble_alt_data =
  define_coda_literal_from_elf
  "edwards25519_scalarmuldouble_alt_mc" "edwards25519_scalarmuldouble_alt_data"
  "arm/curve25519/edwards25519_scalarmuldouble_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf9;       (* arm_STP X25 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd11683ff;       (* arm_SUB SP SP (rvalue (word 1440)) *)
  0xaa0003f9;       (* arm_MOV X25 X0 *)
  0xd29d2404;       (* arm_MOV X4 (rvalue (word 59680)) *)
  0xf2b41b24;       (* arm_MOVK X4 (word 41177) 16 *)
  0xf2cdf6a4;       (* arm_MOVK X4 (word 28597) 32 *)
  0xf2f8fea4;       (* arm_MOVK X4 (word 51189) 48 *)
  0xd2943aa5;       (* arm_MOV X5 (rvalue (word 41429)) *)
  0xf2ae1965;       (* arm_MOVK X5 (word 28875) 16 *)
  0xf2d73265;       (* arm_MOVK X5 (word 47507) 32 *)
  0xf2fc3205;       (* arm_MOVK X5 (word 57744) 48 *)
  0xb201e3e7;       (* arm_MOV X7 (rvalue (word 9838263505978427528)) *)
  0xd10004e6;       (* arm_SUB X6 X7 (rvalue (word 1)) *)
  0x9240ece8;       (* arm_AND X8 X7 (rvalue (word 1152921504606846975)) *)
  0xa9402c6a;       (* arm_LDP X10 X11 X3 (Immediate_Offset (iword (&0))) *)
  0xa941346c;       (* arm_LDP X12 X13 X3 (Immediate_Offset (iword (&16))) *)
  0xd2f00003;       (* arm_MOVZ X3 (word 32768) 48 *)
  0xeb0d007f;       (* arm_CMP X3 X13 *)
  0x9a8420ee;       (* arm_CSEL X14 X7 X4 Condition_CS *)
  0x9a8520ef;       (* arm_CSEL X15 X7 X5 Condition_CS *)
  0x9a8620f0;       (* arm_CSEL X16 X7 X6 Condition_CS *)
  0x9a872111;       (* arm_CSEL X17 X8 X7 Condition_CS *)
  0xab0e014a;       (* arm_ADDS X10 X10 X14 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9a1101ad;       (* arm_ADC X13 X13 X17 *)
  0xa9022fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&32))) *)
  0xa90337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&48))) *)
  0xa9402c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&0))) *)
  0xa941342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&16))) *)
  0xd2f00003;       (* arm_MOVZ X3 (word 32768) 48 *)
  0xeb0d007f;       (* arm_CMP X3 X13 *)
  0x9a8420ee;       (* arm_CSEL X14 X7 X4 Condition_CS *)
  0x9a8520ef;       (* arm_CSEL X15 X7 X5 Condition_CS *)
  0x9a8620f0;       (* arm_CSEL X16 X7 X6 Condition_CS *)
  0x9a872111;       (* arm_CSEL X17 X8 X7 Condition_CS *)
  0xab0e014a;       (* arm_ADDS X10 X10 X14 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9a1101ad;       (* arm_ADC X13 X13 X17 *)
  0xa9002fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0xa90137ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  0xa9402c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&0))) *)
  0xa941344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&16))) *)
  0xb100994e;       (* arm_ADDS X14 X10 (rvalue (word 38)) *)
  0xba1f016f;       (* arm_ADCS X15 X11 XZR *)
  0xba1f0190;       (* arm_ADCS X16 X12 XZR *)
  0xba1f01b1;       (* arm_ADCS X17 X13 XZR *)
  0x9a8a21ca;       (* arm_CSEL X10 X14 X10 Condition_CS *)
  0x9a8b21eb;       (* arm_CSEL X11 X15 X11 Condition_CS *)
  0x9a8c220c;       (* arm_CSEL X12 X16 X12 Condition_CS *)
  0x9a8d222d;       (* arm_CSEL X13 X17 X13 Condition_CS *)
  0xa91a2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&416))) *)
  0xa91b37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&432))) *)
  0xa9422c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&32))) *)
  0xa943344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&48))) *)
  0xb100994e;       (* arm_ADDS X14 X10 (rvalue (word 38)) *)
  0xba1f016f;       (* arm_ADCS X15 X11 XZR *)
  0xba1f0190;       (* arm_ADCS X16 X12 XZR *)
  0xba1f01b1;       (* arm_ADCS X17 X13 XZR *)
  0x9a8a21ca;       (* arm_CSEL X10 X14 X10 Condition_CS *)
  0x9a8b21eb;       (* arm_CSEL X11 X15 X11 Condition_CS *)
  0x9a8c220c;       (* arm_CSEL X12 X16 X12 Condition_CS *)
  0x9a8d222d;       (* arm_CSEL X13 X17 X13 Condition_CS *)
  0xa91c2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&448))) *)
  0xa91d37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&464))) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0xa91e7fe1;       (* arm_STP X1 XZR SP (Immediate_Offset (iword (&480))) *)
  0xa91f7fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&496))) *)
  0x910803f6;       (* arm_ADD X22 SP (rvalue (word 512)) *)
  0x910683f7;       (* arm_ADD X23 SP (rvalue (word 416)) *)
  0x910703f8;       (* arm_ADD X24 SP (rvalue (word 448)) *)
  0xa94012e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&0))) *)
  0xa9402307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&16))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa9013ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&16))) *)
  0x910883f6;       (* arm_ADD X22 SP (rvalue (word 544)) *)
  0x910683f7;       (* arm_ADD X23 SP (rvalue (word 416)) *)
  0x94000875;       (* arm_BL (word 8660) *)
  0x910a83f6;       (* arm_ADD X22 SP (rvalue (word 672)) *)
  0x910683f7;       (* arm_ADD X23 SP (rvalue (word 416)) *)
  0x910883f8;       (* arm_ADD X24 SP (rvalue (word 544)) *)
  0x94000e05;       (* arm_BL (word 14356) *)
  0x910c83f6;       (* arm_ADD X22 SP (rvalue (word 800)) *)
  0x910883f7;       (* arm_ADD X23 SP (rvalue (word 544)) *)
  0x9400086e;       (* arm_BL (word 8632) *)
  0x910e83f6;       (* arm_ADD X22 SP (rvalue (word 928)) *)
  0x910683f7;       (* arm_ADD X23 SP (rvalue (word 416)) *)
  0x910c83f8;       (* arm_ADD X24 SP (rvalue (word 800)) *)
  0x94000dfe;       (* arm_BL (word 14328) *)
  0x911083f6;       (* arm_ADD X22 SP (rvalue (word 1056)) *)
  0x910a83f7;       (* arm_ADD X23 SP (rvalue (word 672)) *)
  0x94000867;       (* arm_BL (word 8604) *)
  0x911283f6;       (* arm_ADD X22 SP (rvalue (word 1184)) *)
  0x910683f7;       (* arm_ADD X23 SP (rvalue (word 416)) *)
  0x911083f8;       (* arm_ADD X24 SP (rvalue (word 1056)) *)
  0x94000df7;       (* arm_BL (word 14300) *)
  0x911483f6;       (* arm_ADD X22 SP (rvalue (word 1312)) *)
  0x910c83f7;       (* arm_ADD X23 SP (rvalue (word 800)) *)
  0x94000860;       (* arm_BL (word 8576) *)
  0xd2801f93;       (* arm_MOV X19 (rvalue (word 252)) *)
  0xf9401fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 56)) *)
  0xd37cfc14;       (* arm_LSR X20 X0 60 *)
  0x10029c8e;       (* arm_ADR X14 (word 21392) *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0xaa1f03e1;       (* arm_MOV X1 XZR *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xd2800024;       (* arm_MOV X4 (rvalue (word 1)) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xaa1f03eb;       (* arm_MOV X11 XZR *)
  0xf100069f;       (* arm_CMP X20 (rvalue (word 1)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1000a9f;       (* arm_CMP X20 (rvalue (word 2)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1000e9f;       (* arm_CMP X20 (rvalue (word 3)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf100129f;       (* arm_CMP X20 (rvalue (word 4)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf100169f;       (* arm_CMP X20 (rvalue (word 5)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1001a9f;       (* arm_CMP X20 (rvalue (word 6)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1001e9f;       (* arm_CMP X20 (rvalue (word 7)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf100229f;       (* arm_CMP X20 (rvalue (word 8)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0xa90407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9050fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&80))) *)
  0xa90617e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&96))) *)
  0xa9071fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&112))) *)
  0xa90827e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&128))) *)
  0xa9092fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&144))) *)
  0xf9400fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 24)) *)
  0xd37cfc14;       (* arm_LSR X20 X0 60 *)
  0x910683f6;       (* arm_ADD X22 SP (rvalue (word 416)) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xaa1f03e1;       (* arm_MOV X1 XZR *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xd2800024;       (* arm_MOV X4 (rvalue (word 1)) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xaa1f03eb;       (* arm_MOV X11 XZR *)
  0xaa1f03ec;       (* arm_MOV X12 XZR *)
  0xaa1f03ed;       (* arm_MOV X13 XZR *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xaa1f03ef;       (* arm_MOV X15 XZR *)
  0xf100069f;       (* arm_CMP X20 (rvalue (word 1)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1000a9f;       (* arm_CMP X20 (rvalue (word 2)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1000e9f;       (* arm_CMP X20 (rvalue (word 3)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf100129f;       (* arm_CMP X20 (rvalue (word 4)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf100169f;       (* arm_CMP X20 (rvalue (word 5)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1001a9f;       (* arm_CMP X20 (rvalue (word 6)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1001e9f;       (* arm_CMP X20 (rvalue (word 7)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf100229f;       (* arm_CMP X20 (rvalue (word 8)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa9130fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&304))) *)
  0xa91417e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&320))) *)
  0xa9151fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&336))) *)
  0xa91627e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&352))) *)
  0xa9172fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&368))) *)
  0xa91837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&384))) *)
  0xa9193fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&400))) *)
  0x910283f6;       (* arm_ADD X22 SP (rvalue (word 160)) *)
  0x910483f7;       (* arm_ADD X23 SP (rvalue (word 288)) *)
  0x910103f8;       (* arm_ADD X24 SP (rvalue (word 64)) *)
  0x94001042;       (* arm_BL (word 16648) *)
  0xd1001273;       (* arm_SUB X19 X19 (rvalue (word 4)) *)
  0x910283f6;       (* arm_ADD X22 SP (rvalue (word 160)) *)
  0x910283f7;       (* arm_ADD X23 SP (rvalue (word 160)) *)
  0x940009b2;       (* arm_BL (word 9928) *)
  0xd346fe60;       (* arm_LSR X0 X19 6 *)
  0x910083e1;       (* arm_ADD X1 SP (rvalue (word 32)) *)
  0xf8607822;       (* arm_LDR X2 X1 (Shiftreg_Offset X0 3) *)
  0x9ad32443;       (* arm_LSRV X3 X2 X19 *)
  0x92400c60;       (* arm_AND X0 X3 (rvalue (word 15)) *)
  0xf1002014;       (* arm_SUBS X20 X0 (rvalue (word 8)) *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0x1002670e;       (* arm_ADR X14 (word 19680) *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0xaa1f03e1;       (* arm_MOV X1 XZR *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xd2800024;       (* arm_MOV X4 (rvalue (word 1)) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xaa1f03eb;       (* arm_MOV X11 XZR *)
  0xf100069f;       (* arm_CMP X20 (rvalue (word 1)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1000a9f;       (* arm_CMP X20 (rvalue (word 2)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1000e9f;       (* arm_CMP X20 (rvalue (word 3)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf100129f;       (* arm_CMP X20 (rvalue (word 4)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf100169f;       (* arm_CMP X20 (rvalue (word 5)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1001a9f;       (* arm_CMP X20 (rvalue (word 6)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf1001e9f;       (* arm_CMP X20 (rvalue (word 7)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0x910181ce;       (* arm_ADD X14 X14 (rvalue (word 96)) *)
  0xf100229f;       (* arm_CMP X20 (rvalue (word 8)) *)
  0xa94035cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&0))) *)
  0x9a8c1000;       (* arm_CSEL X0 X0 X12 Condition_NE *)
  0x9a8d1021;       (* arm_CSEL X1 X1 X13 Condition_NE *)
  0xa94135cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&16))) *)
  0x9a8c1042;       (* arm_CSEL X2 X2 X12 Condition_NE *)
  0x9a8d1063;       (* arm_CSEL X3 X3 X13 Condition_NE *)
  0xa94235cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&32))) *)
  0x9a8c1084;       (* arm_CSEL X4 X4 X12 Condition_NE *)
  0x9a8d10a5;       (* arm_CSEL X5 X5 X13 Condition_NE *)
  0xa94335cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&48))) *)
  0x9a8c10c6;       (* arm_CSEL X6 X6 X12 Condition_NE *)
  0x9a8d10e7;       (* arm_CSEL X7 X7 X13 Condition_NE *)
  0xa94435cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&64))) *)
  0x9a8c1108;       (* arm_CSEL X8 X8 X12 Condition_NE *)
  0x9a8d1129;       (* arm_CSEL X9 X9 X13 Condition_NE *)
  0xa94535cc;       (* arm_LDP X12 X13 X14 (Immediate_Offset (iword (&80))) *)
  0x9a8c114a;       (* arm_CSEL X10 X10 X12 Condition_NE *)
  0x9a8d116b;       (* arm_CSEL X11 X11 X13 Condition_NE *)
  0xeb1f02bf;       (* arm_CMP X21 XZR *)
  0x9a84000c;       (* arm_CSEL X12 X0 X4 Condition_EQ *)
  0x9a841004;       (* arm_CSEL X4 X0 X4 Condition_NE *)
  0x9a85002d;       (* arm_CSEL X13 X1 X5 Condition_EQ *)
  0x9a851025;       (* arm_CSEL X5 X1 X5 Condition_NE *)
  0x9a86004e;       (* arm_CSEL X14 X2 X6 Condition_EQ *)
  0x9a861046;       (* arm_CSEL X6 X2 X6 Condition_NE *)
  0x9a87006f;       (* arm_CSEL X15 X3 X7 Condition_EQ *)
  0x9a871067;       (* arm_CSEL X7 X3 X7 Condition_NE *)
  0xca150108;       (* arm_EOR X8 X8 X21 *)
  0xca150129;       (* arm_EOR X9 X9 X21 *)
  0xca15014a;       (* arm_EOR X10 X10 X21 *)
  0xca15016b;       (* arm_EOR X11 X11 X21 *)
  0xd28004a0;       (* arm_MOV X0 (rvalue (word 37)) *)
  0x8a150000;       (* arm_AND X0 X0 X21 *)
  0xeb000108;       (* arm_SUBS X8 X8 X0 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xa90437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&64))) *)
  0xa9053fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&80))) *)
  0xa90617e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&96))) *)
  0xa9071fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&112))) *)
  0xa90827e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&128))) *)
  0xa9092fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&144))) *)
  0xd346fe60;       (* arm_LSR X0 X19 6 *)
  0xf8607be1;       (* arm_LDR X1 SP (Shiftreg_Offset X0 3) *)
  0x9ad32422;       (* arm_LSRV X2 X1 X19 *)
  0x92400c40;       (* arm_AND X0 X2 (rvalue (word 15)) *)
  0xf1002014;       (* arm_SUBS X20 X0 (rvalue (word 8)) *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0xda9f23f5;       (* arm_CSETM X21 Condition_CC *)
  0x910683f6;       (* arm_ADD X22 SP (rvalue (word 416)) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xaa1f03e1;       (* arm_MOV X1 XZR *)
  0xaa1f03e2;       (* arm_MOV X2 XZR *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xd2800024;       (* arm_MOV X4 (rvalue (word 1)) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xaa1f03eb;       (* arm_MOV X11 XZR *)
  0xaa1f03ec;       (* arm_MOV X12 XZR *)
  0xaa1f03ed;       (* arm_MOV X13 XZR *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xaa1f03ef;       (* arm_MOV X15 XZR *)
  0xf100069f;       (* arm_CMP X20 (rvalue (word 1)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1000a9f;       (* arm_CMP X20 (rvalue (word 2)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1000e9f;       (* arm_CMP X20 (rvalue (word 3)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf100129f;       (* arm_CMP X20 (rvalue (word 4)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf100169f;       (* arm_CMP X20 (rvalue (word 5)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1001a9f;       (* arm_CMP X20 (rvalue (word 6)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf1001e9f;       (* arm_CMP X20 (rvalue (word 7)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0x910202d6;       (* arm_ADD X22 X22 (rvalue (word 128)) *)
  0xf100229f;       (* arm_CMP X20 (rvalue (word 8)) *)
  0xa94046d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&0))) *)
  0x9a901000;       (* arm_CSEL X0 X0 X16 Condition_NE *)
  0x9a911021;       (* arm_CSEL X1 X1 X17 Condition_NE *)
  0xa94146d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&16))) *)
  0x9a901042;       (* arm_CSEL X2 X2 X16 Condition_NE *)
  0x9a911063;       (* arm_CSEL X3 X3 X17 Condition_NE *)
  0xa94246d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&32))) *)
  0x9a901084;       (* arm_CSEL X4 X4 X16 Condition_NE *)
  0x9a9110a5;       (* arm_CSEL X5 X5 X17 Condition_NE *)
  0xa94346d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&48))) *)
  0x9a9010c6;       (* arm_CSEL X6 X6 X16 Condition_NE *)
  0x9a9110e7;       (* arm_CSEL X7 X7 X17 Condition_NE *)
  0xa94446d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&64))) *)
  0x9a901108;       (* arm_CSEL X8 X8 X16 Condition_NE *)
  0x9a911129;       (* arm_CSEL X9 X9 X17 Condition_NE *)
  0xa94546d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&80))) *)
  0x9a90114a;       (* arm_CSEL X10 X10 X16 Condition_NE *)
  0x9a91116b;       (* arm_CSEL X11 X11 X17 Condition_NE *)
  0xa94646d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&96))) *)
  0x9a90118c;       (* arm_CSEL X12 X12 X16 Condition_NE *)
  0x9a9111ad;       (* arm_CSEL X13 X13 X17 Condition_NE *)
  0xa94746d0;       (* arm_LDP X16 X17 X22 (Immediate_Offset (iword (&112))) *)
  0x9a9011ce;       (* arm_CSEL X14 X14 X16 Condition_NE *)
  0x9a9111ef;       (* arm_CSEL X15 X15 X17 Condition_NE *)
  0xca150000;       (* arm_EOR X0 X0 X21 *)
  0xca150021;       (* arm_EOR X1 X1 X21 *)
  0xca150042;       (* arm_EOR X2 X2 X21 *)
  0xca150063;       (* arm_EOR X3 X3 X21 *)
  0xd28004b0;       (* arm_MOV X16 (rvalue (word 37)) *)
  0x8a150210;       (* arm_AND X16 X16 X21 *)
  0xeb100000;       (* arm_SUBS X0 X0 X16 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0063;       (* arm_SBC X3 X3 XZR *)
  0xca15018c;       (* arm_EOR X12 X12 X21 *)
  0xca1501ad;       (* arm_EOR X13 X13 X21 *)
  0xca1501ce;       (* arm_EOR X14 X14 X21 *)
  0xca1501ef;       (* arm_EOR X15 X15 X21 *)
  0xeb10018c;       (* arm_SUBS X12 X12 X16 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa9130fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&304))) *)
  0xa91417e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&320))) *)
  0xa9151fe6;       (* arm_STP X6 X7 SP (Immediate_Offset (iword (&336))) *)
  0xa91627e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&352))) *)
  0xa9172fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&368))) *)
  0xa91837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&384))) *)
  0xa9193fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&400))) *)
  0x910283f6;       (* arm_ADD X22 SP (rvalue (word 160)) *)
  0x910283f7;       (* arm_ADD X23 SP (rvalue (word 160)) *)
  0x940007e1;       (* arm_BL (word 8068) *)
  0x910483f6;       (* arm_ADD X22 SP (rvalue (word 288)) *)
  0x910483f7;       (* arm_ADD X23 SP (rvalue (word 288)) *)
  0x910103f8;       (* arm_ADD X24 SP (rvalue (word 64)) *)
  0x94000e69;       (* arm_BL (word 14756) *)
  0x910283f6;       (* arm_ADD X22 SP (rvalue (word 160)) *)
  0x910283f7;       (* arm_ADD X23 SP (rvalue (word 160)) *)
  0x940007da;       (* arm_BL (word 8040) *)
  0x910283f6;       (* arm_ADD X22 SP (rvalue (word 160)) *)
  0x910283f7;       (* arm_ADD X23 SP (rvalue (word 160)) *)
  0x940004de;       (* arm_BL (word 4984) *)
  0x910283f6;       (* arm_ADD X22 SP (rvalue (word 160)) *)
  0x910283f7;       (* arm_ADD X23 SP (rvalue (word 160)) *)
  0x910483f8;       (* arm_ADD X24 SP (rvalue (word 288)) *)
  0x94000a6e;       (* arm_BL (word 10680) *)
  0xb5ffc3b3;       (* arm_CBNZ X19 (word 2095220) *)
  0x910483e0;       (* arm_ADD X0 SP (rvalue (word 288)) *)
  0x910383e1;       (* arm_ADD X1 SP (rvalue (word 224)) *)
  0xaa0003f4;       (* arm_MOV X20 X0 *)
  0x9280024a;       (* arm_MOVN X10 (word 18) 0 *)
  0x9280000b;       (* arm_MOVN X11 (word 0) 0 *)
  0xa9002fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0x92f0000c;       (* arm_MOVN X12 (word 32768) 48 *)
  0xa90133eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0xd37ffca6;       (* arm_LSR X6 X5 63 *)
  0x9b061ce6;       (* arm_MADD X6 X7 X6 X7 *)
  0xab060042;       (* arm_ADDS X2 X2 X6 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xb24100a5;       (* arm_ORR X5 X5 (rvalue (word 9223372036854775808)) *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a9f30e6;       (* arm_CSEL X6 X7 XZR Condition_CC *)
  0xeb060042;       (* arm_SUBS X2 X2 X6 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xa9020fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  0xa90317e4;       (* arm_STP X4 X5 SP (Immediate_Offset (iword (&48))) *)
  0xa9047fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&64))) *)
  0xa9057fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&80))) *)
  0xd284132a;       (* arm_MOV X10 (rvalue (word 8345)) *)
  0xf2aea04a;       (* arm_MOVK X10 (word 29954) 16 *)
  0xf2d3c46a;       (* arm_MOVK X10 (word 40483) 32 *)
  0xf2f41f2a;       (* arm_MOVK X10 (word 41209) 48 *)
  0xd284b2ab;       (* arm_MOV X11 (rvalue (word 9621)) *)
  0xf2a3a26b;       (* arm_MOVK X11 (word 7443) 16 *)
  0xf2d1e7eb;       (* arm_MOVK X11 (word 36671) 32 *)
  0xf2f518cb;       (* arm_MOVK X11 (word 43206) 48 *)
  0xd28a484c;       (* arm_MOV X12 (rvalue (word 21058)) *)
  0xf2a0b58c;       (* arm_MOVK X12 (word 1452) 16 *)
  0xf2d1270c;       (* arm_MOVK X12 (word 35128) 32 *)
  0xf2ed8d8c;       (* arm_MOVK X12 (word 27756) 48 *)
  0xd280c2ad;       (* arm_MOV X13 (rvalue (word 1557)) *)
  0xf2a82eed;       (* arm_MOVK X13 (word 16759) 16 *)
  0xf2c1164d;       (* arm_MOVK X13 (word 2226) 32 *)
  0xf2e4ecad;       (* arm_MOVK X13 (word 10085) 48 *)
  0xa9062fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&96))) *)
  0xa90737ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&112))) *)
  0xd2800155;       (* arm_MOV X21 (rvalue (word 10)) *)
  0xd2800036;       (* arm_MOV X22 (rvalue (word 1)) *)
  0x1400010b;       (* arm_B (word 1068) *)
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
  0xf94013e8;       (* arm_LDR X8 SP (Immediate_Offset (word 32)) *)
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
  0xf94017e8;       (* arm_LDR X8 SP (Immediate_Offset (word 40)) *)
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
  0xf90013e5;       (* arm_STR X5 SP (Immediate_Offset (word 32)) *)
  0xf9400be7;       (* arm_LDR X7 SP (Immediate_Offset (word 16)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9401be8;       (* arm_LDR X8 SP (Immediate_Offset (word 48)) *)
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
  0xf90017e3;       (* arm_STR X3 SP (Immediate_Offset (word 40)) *)
  0xf9400fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 24)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x937ffc23;       (* arm_ASR X3 X1 63 *)
  0x8a0a0063;       (* arm_AND X3 X3 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9401fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 56)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x937ffc20;       (* arm_ASR X0 X1 63 *)
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
  0xf9001be4;       (* arm_STR X4 SP (Immediate_Offset (word 48)) *)
  0x93c2eca2;       (* arm_EXTR X2 X5 X2 59 *)
  0xf9001fe2;       (* arm_STR X2 SP (Immediate_Offset (word 56)) *)
  0xf94023e7;       (* arm_LDR X7 SP (Immediate_Offset (word 64)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94033e8;       (* arm_LDR X8 SP (Immediate_Offset (word 96)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90023e4;       (* arm_STR X4 SP (Immediate_Offset (word 64)) *)
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
  0xf90033e5;       (* arm_STR X5 SP (Immediate_Offset (word 96)) *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf94027e7;       (* arm_LDR X7 SP (Immediate_Offset (word 72)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94037e8;       (* arm_LDR X8 SP (Immediate_Offset (word 104)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90027e2;       (* arm_STR X2 SP (Immediate_Offset (word 72)) *)
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
  0xf90037e3;       (* arm_STR X3 SP (Immediate_Offset (word 104)) *)
  0x9a010084;       (* arm_ADC X4 X4 X1 *)
  0xf9402be7;       (* arm_LDR X7 SP (Immediate_Offset (word 80)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9403be8;       (* arm_LDR X8 SP (Immediate_Offset (word 112)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf9002be6;       (* arm_STR X6 SP (Immediate_Offset (word 80)) *)
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
  0xf9003be4;       (* arm_STR X4 SP (Immediate_Offset (word 112)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf9402fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 88)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c3;       (* arm_AND X3 X14 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9403fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 120)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c5fc66;       (* arm_EXTR X6 X3 X5 63 *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0x8b83fcc6;       (* arm_ADD X6 X6 (Shiftedreg X3 ASR 63) *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b037cc4;       (* arm_MUL X4 X6 X3 *)
  0x8b06fca5;       (* arm_ADD X5 X5 (Shiftedreg X6 LSL 63) *)
  0x9b437cc3;       (* arm_SMULH X3 X6 X3 *)
  0xf9402be6;       (* arm_LDR X6 SP (Immediate_Offset (word 80)) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0x937ffc63;       (* arm_ASR X3 X3 63 *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0x9a0300a5;       (* arm_ADC X5 X5 X3 *)
  0xa90407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa90517e6;       (* arm_STP X6 X5 SP (Immediate_Offset (iword (&80))) *)
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
  0x93c2fca6;       (* arm_EXTR X6 X5 X2 63 *)
  0xa94607e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0x8b85fcc6;       (* arm_ADD X6 X6 (Shiftedreg X5 ASR 63) *)
  0xd2800265;       (* arm_MOV X5 (rvalue (word 19)) *)
  0x9b057cc4;       (* arm_MUL X4 X6 X5 *)
  0x8b06fc42;       (* arm_ADD X2 X2 (Shiftedreg X6 LSL 63) *)
  0x9b457cc5;       (* arm_SMULH X5 X6 X5 *)
  0xf9403be3;       (* arm_LDR X3 SP (Immediate_Offset (word 112)) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba050021;       (* arm_ADCS X1 X1 X5 *)
  0x937ffca5;       (* arm_ASR X5 X5 63 *)
  0xba050063;       (* arm_ADCS X3 X3 X5 *)
  0x9a050042;       (* arm_ADC X2 X2 X5 *)
  0xa90607e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  0xa9070be3;       (* arm_STP X3 X2 SP (Immediate_Offset (iword (&112))) *)
  0xaa1603e1;       (* arm_MOV X1 X22 *)
  0xf94003e2;       (* arm_LDR X2 SP (Immediate_Offset (word 0)) *)
  0xf94013e3;       (* arm_LDR X3 SP (Immediate_Offset (word 32)) *)
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
  0x54ff9281;       (* arm_BNE (word 2093648) *)
  0xf94003e0;       (* arm_LDR X0 SP (Immediate_Offset (word 0)) *)
  0xf94013e1;       (* arm_LDR X1 SP (Immediate_Offset (word 32)) *)
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
  0xf94023e7;       (* arm_LDR X7 SP (Immediate_Offset (word 64)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000124;       (* arm_ADDS X4 X9 X0 *)
  0x9a0103e2;       (* arm_ADC X2 XZR X1 *)
  0xf94033e8;       (* arm_LDR X8 SP (Immediate_Offset (word 96)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0xf90023e4;       (* arm_STR X4 SP (Immediate_Offset (word 64)) *)
  0x9a010042;       (* arm_ADC X2 X2 X1 *)
  0xf94027e7;       (* arm_LDR X7 SP (Immediate_Offset (word 72)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0x9a0103e6;       (* arm_ADC X6 XZR X1 *)
  0xf94037e8;       (* arm_LDR X8 SP (Immediate_Offset (word 104)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab000042;       (* arm_ADDS X2 X2 X0 *)
  0xf90027e2;       (* arm_STR X2 SP (Immediate_Offset (word 72)) *)
  0x9a0100c6;       (* arm_ADC X6 X6 X1 *)
  0xf9402be7;       (* arm_LDR X7 SP (Immediate_Offset (word 80)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0x9a0103e5;       (* arm_ADC X5 XZR X1 *)
  0xf9403be8;       (* arm_LDR X8 SP (Immediate_Offset (word 112)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000c6;       (* arm_ADDS X6 X6 X0 *)
  0xf9002be6;       (* arm_STR X6 SP (Immediate_Offset (word 80)) *)
  0x9a0100a5;       (* arm_ADC X5 X5 X1 *)
  0xf9402fe7;       (* arm_LDR X7 SP (Immediate_Offset (word 88)) *)
  0xca0e00e1;       (* arm_EOR X1 X7 X14 *)
  0x8a0a01c3;       (* arm_AND X3 X14 X10 *)
  0xcb0303e3;       (* arm_NEG X3 X3 *)
  0x9b0a7c20;       (* arm_MUL X0 X1 X10 *)
  0x9bca7c21;       (* arm_UMULH X1 X1 X10 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0xf9403fe8;       (* arm_LDR X8 SP (Immediate_Offset (word 120)) *)
  0xca0f0101;       (* arm_EOR X1 X8 X15 *)
  0x8a0b01e0;       (* arm_AND X0 X15 X11 *)
  0xcb000063;       (* arm_SUB X3 X3 X0 *)
  0x9b0b7c20;       (* arm_MUL X0 X1 X11 *)
  0x9bcb7c21;       (* arm_UMULH X1 X1 X11 *)
  0xab0000a5;       (* arm_ADDS X5 X5 X0 *)
  0x9a010063;       (* arm_ADC X3 X3 X1 *)
  0x93c5fc66;       (* arm_EXTR X6 X3 X5 63 *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xea03007f;       (* arm_TST X3 X3 *)
  0x9a8644c6;       (* arm_CINC X6 X6 Condition_PL *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b037cc4;       (* arm_MUL X4 X6 X3 *)
  0x8b06fca5;       (* arm_ADD X5 X5 (Shiftedreg X6 LSL 63) *)
  0x9b437cc6;       (* arm_SMULH X6 X6 X3 *)
  0xf9402be2;       (* arm_LDR X2 SP (Immediate_Offset (word 80)) *)
  0xab040000;       (* arm_ADDS X0 X0 X4 *)
  0xba060021;       (* arm_ADCS X1 X1 X6 *)
  0x937ffcc6;       (* arm_ASR X6 X6 63 *)
  0xba060042;       (* arm_ADCS X2 X2 X6 *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0x9a9f4063;       (* arm_CSEL X3 X3 XZR Condition_MI *)
  0xeb030000;       (* arm_SUBS X0 X0 X3 *)
  0xfa1f0021;       (* arm_SBCS X1 X1 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xaa1403e4;       (* arm_MOV X4 X20 *)
  0xa9000480;       (* arm_STP X0 X1 X4 (Immediate_Offset (iword (&0))) *)
  0xa9011482;       (* arm_STP X2 X5 X4 (Immediate_Offset (iword (&16))) *)
  0xaa1903f6;       (* arm_MOV X22 X25 *)
  0x910283f7;       (* arm_ADD X23 SP (rvalue (word 160)) *)
  0x910483f8;       (* arm_ADD X24 SP (rvalue (word 288)) *)
  0xa94012e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&0))) *)
  0xa9402307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&16))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0xb24101ef;       (* arm_ORR X15 X15 (rvalue (word 9223372036854775808)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b081ceb;       (* arm_MADD X11 X7 X8 X7 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9a9f30e7;       (* arm_CSEL X7 X7 XZR Condition_CC *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa9013ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&16))) *)
  0x91008336;       (* arm_ADD X22 X25 (rvalue (word 32)) *)
  0x910303f7;       (* arm_ADD X23 SP (rvalue (word 192)) *)
  0x910483f8;       (* arm_ADD X24 SP (rvalue (word 288)) *)
  0xa94012e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&0))) *)
  0xa9402307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&16))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0xb24101ef;       (* arm_ORR X15 X15 (rvalue (word 9223372036854775808)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b081ceb;       (* arm_MADD X11 X7 X8 X7 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9a9f30e7;       (* arm_CSEL X7 X7 XZR Condition_CC *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa9013ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&16))) *)
  0x911683ff;       (* arm_ADD SP SP (rvalue (word 1440)) *)
  0xa8c17bf9;       (* arm_LDP X25 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd10283ff;       (* arm_SUB SP SP (rvalue (word 160)) *)
  0xa94012e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&0))) *)
  0xa94222e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&32))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9411ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&16))) *)
  0xa94322e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&48))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90013e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9011be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa9440ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&64))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94516e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&80))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&32))) *)
  0xa9032fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&48))) *)
  0xa9400ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94116e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&16))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90427e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&64))) *)
  0xa9052fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&80))) *)
  0xa9420ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&32))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94316e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&48))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90627e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&96))) *)
  0xa9072fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&112))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xab030063;       (* arm_ADDS X3 X3 X3 *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0600c6;       (* arm_ADCS X6 X6 X6 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90213e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa9031be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xa9400fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&16))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
  0xa94723e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90813e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa9091be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9460fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&96))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9470fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&112))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90613e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9071be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9021be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa90323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90236cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&32))) *)
  0xa9033ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&48))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90436cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&64))) *)
  0xa9053ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&80))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90636cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&96))) *)
  0xa9073ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&112))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9472be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa9013ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&16))) *)
  0x910283ff;       (* arm_ADD SP SP (rvalue (word 160)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd10283ff;       (* arm_SUB SP SP (rvalue (word 160)) *)
  0xa94012e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&0))) *)
  0xa94222e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&32))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9411ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&16))) *)
  0xa94322e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&48))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90013e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9011be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa9440ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&64))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94516e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&80))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&32))) *)
  0xa9032fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&48))) *)
  0xa9400ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94116e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&16))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90427e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&64))) *)
  0xa9052fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&80))) *)
  0xa9420ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&32))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94316e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&48))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90627e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&96))) *)
  0xa9072fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&112))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xab030063;       (* arm_ADDS X3 X3 X3 *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0600c6;       (* arm_ADCS X6 X6 X6 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90213e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa9031be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xa9400fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&16))) *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b047c47;       (* arm_MUL X7 X2 X4 *)
  0x9bc47c46;       (* arm_UMULH X6 X2 X4 *)
  0xab07014a;       (* arm_ADDS X10 X10 X7 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9b047c67;       (* arm_MUL X7 X3 X4 *)
  0x9bc47c66;       (* arm_UMULH X6 X3 X4 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07016b;       (* arm_ADDS X11 X11 X7 *)
  0x9b057c8d;       (* arm_MUL X13 X4 X5 *)
  0x9bc57c8e;       (* arm_UMULH X14 X4 X5 *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0x9b057c67;       (* arm_MUL X7 X3 X5 *)
  0x9bc57c66;       (* arm_UMULH X6 X3 X5 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x9bc27c47;       (* arm_UMULH X7 X2 X2 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9b037c67;       (* arm_MUL X7 X3 X3 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9bc37c67;       (* arm_UMULH X7 X3 X3 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9b047c87;       (* arm_MUL X7 X4 X4 *)
  0xba07018c;       (* arm_ADCS X12 X12 X7 *)
  0x9bc47c87;       (* arm_UMULH X7 X4 X4 *)
  0xba0701ad;       (* arm_ADCS X13 X13 X7 *)
  0x9b057ca7;       (* arm_MUL X7 X5 X5 *)
  0xba0701ce;       (* arm_ADCS X14 X14 X7 *)
  0x9bc57ca7;       (* arm_UMULH X7 X5 X5 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9b0c7c67;       (* arm_MUL X7 X3 X12 *)
  0x9bcc7c64;       (* arm_UMULH X4 X3 X12 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0x9b0d7c67;       (* arm_MUL X7 X3 X13 *)
  0x9bcd7c6d;       (* arm_UMULH X13 X3 X13 *)
  0xba070129;       (* arm_ADCS X9 X9 X7 *)
  0x9b0e7c67;       (* arm_MUL X7 X3 X14 *)
  0x9bce7c6e;       (* arm_UMULH X14 X3 X14 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9b067c67;       (* arm_MUL X7 X3 X6 *)
  0x9bc67c66;       (* arm_UMULH X6 X3 X6 *)
  0xba07016b;       (* arm_ADCS X11 X11 X7 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0e016b;       (* arm_ADDS X11 X11 X14 *)
  0x9a06018c;       (* arm_ADC X12 X12 X6 *)
  0xab0b017f;       (* arm_CMN X11 X11 *)
  0x9240f96b;       (* arm_AND X11 X11 (rvalue (word 9223372036854775807)) *)
  0x9a0c0182;       (* arm_ADC X2 X12 X12 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0x9b027c67;       (* arm_MUL X7 X3 X2 *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba040129;       (* arm_ADCS X9 X9 X4 *)
  0xba0d014a;       (* arm_ADCS X10 X10 X13 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xa90027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&0))) *)
  0xa9012fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&16))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
  0xa94723e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90813e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa9091be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9460fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&96))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9470fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&112))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90613e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9071be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa9400fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9410fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9021be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa90323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90236cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&32))) *)
  0xa9033ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&48))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90436cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&64))) *)
  0xa9053ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&80))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9472be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa9013ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&16))) *)
  0x910283ff;       (* arm_ADD SP SP (rvalue (word 160)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd10303ff;       (* arm_SUB SP SP (rvalue (word 192)) *)
  0xa94612e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&96))) *)
  0xa9462307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&96))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9472b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&112))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9471ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&112))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90037ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&0))) *)
  0xa9013fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&16))) *)
  0xa9421ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&32))) *)
  0xa9400ee4;       (* arm_LDP X4 X3 X23 (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94322e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&48))) *)
  0xa9410ee4;       (* arm_LDP X4 X3 X23 (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9021be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa90323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa9421b05;       (* arm_LDP X5 X6 X24 (Immediate_Offset (iword (&32))) *)
  0xa9400f04;       (* arm_LDP X4 X3 X24 (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa9432307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&48))) *)
  0xa9410f04;       (* arm_LDP X4 X3 X24 (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9041be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa90523e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa94212e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&32))) *)
  0xa94022e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&0))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9431ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&48))) *)
  0xa94122e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&16))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90613e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9071be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa9421303;       (* arm_LDP X3 X4 X24 (Immediate_Offset (iword (&32))) *)
  0xa9402307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&0))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9431b05;       (* arm_LDP X5 X6 X24 (Immediate_Offset (iword (&48))) *)
  0xa9412307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&16))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90813e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa9091be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa9441303;       (* arm_LDP X3 X4 X24 (Immediate_Offset (iword (&64))) *)
  0xab030063;       (* arm_ADDS X3 X3 X3 *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xa9451b05;       (* arm_LDP X5 X6 X24 (Immediate_Offset (iword (&80))) *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0600c6;       (* arm_ADCS X6 X6 X6 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&32))) *)
  0xa9033fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&48))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90637ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&96))) *)
  0xa9073fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&112))) *)
  0xd29e2b20;       (* arm_MOV X0 (rvalue (word 61785)) *)
  0xd2962ac1;       (* arm_MOV X1 (rvalue (word 45398)) *)
  0xd29a2602;       (* arm_MOV X2 (rvalue (word 53552)) *)
  0xd29f9ce3;       (* arm_MOV X3 (rvalue (word 64743)) *)
  0xf2a4d640;       (* arm_MOVK X0 (word 9906) 16 *)
  0xf2b05061;       (* arm_MOVK X1 (word 33411) 16 *)
  0xf2bdde62;       (* arm_MOVK X2 (word 61171) 16 *)
  0xf2aadbe3;       (* arm_MOVK X3 (word 22239) 16 *)
  0xf2d37280;       (* arm_MOVK X0 (word 39828) 32 *)
  0xf2c29341;       (* arm_MOVK X1 (word 5274) 32 *)
  0xf2d01e42;       (* arm_MOVK X2 (word 33010) 32 *)
  0xf2db3b83;       (* arm_MOVK X3 (word 55772) 32 *)
  0xf2fd7ac0;       (* arm_MOVK X0 (word 60374) 48 *)
  0xf2e01c01;       (* arm_MOVK X1 (word 224) 48 *)
  0xf2e331c2;       (* arm_MOVK X2 (word 6542) 48 *)
  0xf2e480c3;       (* arm_MOVK X3 (word 9222) 48 *)
  0xa90407e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9050fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&80))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa94023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&64))) *)
  0xa9053fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&80))) *)
  0xa94412e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&64))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94b2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9451ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&80))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90837ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  0xa9093fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&144))) *)
  0xa9461be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&96))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94723e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9001be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa90123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa94323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa9481be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa9440fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&64))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94923e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa9450fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&80))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9021be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa90323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa94813e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90613e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa9071be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&112))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94b2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90636cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&96))) *)
  0xa9073ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&112))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9432be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa9013ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&16))) *)
  0xa94613e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&96))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa94b2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9471be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&112))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90236cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&32))) *)
  0xa9033ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&48))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9472be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90436cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&64))) *)
  0xa9053ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&80))) *)
  0x910303ff;       (* arm_ADD SP SP (rvalue (word 192)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd10303ff;       (* arm_SUB SP SP (rvalue (word 192)) *)
  0xa94412e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&64))) *)
  0xab030063;       (* arm_ADDS X3 X3 X3 *)
  0xba040084;       (* arm_ADCS X4 X4 X4 *)
  0xa9451ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&80))) *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0600c6;       (* arm_ADCS X6 X6 X6 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90013e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9011be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa9421ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&32))) *)
  0xa9400ee4;       (* arm_LDP X4 X3 X23 (Immediate_Offset (iword (&0))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94322e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&48))) *)
  0xa9410ee4;       (* arm_LDP X4 X3 X23 (Immediate_Offset (iword (&16))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9021be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&32))) *)
  0xa90323e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xa94212e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&32))) *)
  0xa94022e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&0))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9431ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&48))) *)
  0xa94122e7;       (* arm_LDP X7 X8 X23 (Immediate_Offset (iword (&16))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90413e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa9051be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&80))) *)
  0xa94612e3;       (* arm_LDP X3 X4 X23 (Immediate_Offset (iword (&96))) *)
  0xa9442307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&64))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9452b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&80))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9471ae5;       (* arm_LDP X5 X6 X23 (Immediate_Offset (iword (&112))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90637ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&96))) *)
  0xa9073fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&112))) *)
  0xa94213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa9402307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9431be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&48))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&32))) *)
  0xa9033fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&48))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa9422307;       (* arm_LDP X7 X8 X24 (Immediate_Offset (iword (&32))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9432b09;       (* arm_LDP X9 X10 X24 (Immediate_Offset (iword (&48))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90437ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&64))) *)
  0xa9053fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&80))) *)
  0xa9401be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&0))) *)
  0xa9460fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&96))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&16))) *)
  0xa9470fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&112))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9081be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  0xa90923e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa94623e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa94723e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&112))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90013e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa9011be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&16))) *)
  0xa9441be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&64))) *)
  0xa9420fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&32))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xa9430fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&48))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa90a1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0xa90b23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9451be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&80))) *)
  0xa94323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&48))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90213e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&32))) *)
  0xa9031be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&48))) *)
  0xa94813e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa94023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&0))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&16))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9491be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90436cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&64))) *)
  0xa9053ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&80))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa94823e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9492be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&144))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90036cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&0))) *)
  0xa9013ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&16))) *)
  0xa94013e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&0))) *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9432be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9411be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&16))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90236cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&32))) *)
  0xa9033ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&48))) *)
  0xa94a13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa94223e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9432be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
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
  0x9bc77ccb;       (* arm_UMULH X11 X6 X7 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc87ccb;       (* arm_UMULH X11 X6 X8 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9bc97ccb;       (* arm_UMULH X11 X6 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xd28004c7;       (* arm_MOV X7 (rvalue (word 38)) *)
  0x9b107ceb;       (* arm_MUL X11 X7 X16 *)
  0x9bd07ce9;       (* arm_UMULH X9 X7 X16 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0x9b037ceb;       (* arm_MUL X11 X7 X3 *)
  0x9bc37ce3;       (* arm_UMULH X3 X7 X3 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0x9b047ceb;       (* arm_MUL X11 X7 X4 *)
  0x9bc47ce4;       (* arm_UMULH X4 X7 X4 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b057ceb;       (* arm_MUL X11 X7 X5 *)
  0x9bc57ce5;       (* arm_UMULH X5 X7 X5 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a9f37f0;       (* arm_CSET X16 Condition_CS *)
  0xab0401ef;       (* arm_ADDS X15 X15 X4 *)
  0x9a050210;       (* arm_ADC X16 X16 X5 *)
  0xab0f01ff;       (* arm_CMN X15 X15 *)
  0x9240f9ef;       (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  0x9a100208;       (* arm_ADC X8 X16 X16 *)
  0xd2800267;       (* arm_MOV X7 (rvalue (word 19)) *)
  0x9b087ceb;       (* arm_MUL X11 X7 X8 *)
  0xab0b018c;       (* arm_ADDS X12 X12 X11 *)
  0xba0901ad;       (* arm_ADCS X13 X13 X9 *)
  0xba0301ce;       (* arm_ADCS X14 X14 X3 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa90636cc;       (* arm_STP X12 X13 X22 (Immediate_Offset (iword (&96))) *)
  0xa9073ece;       (* arm_STP X14 X15 X22 (Immediate_Offset (iword (&112))) *)
  0x910303ff;       (* arm_ADD SP SP (rvalue (word 192)) *)
  0xd65f03c0        (* arm_RET X30 *)
]
[62; 145; 64; 215; 5; 57; 16; 157; 179; 190; 64; 209; 5; 159; 57; 253; 9;
 138; 143; 104; 52; 132; 193; 165; 103; 18; 248; 152; 146; 47; 253; 68; 133;
 59; 140; 245; 198; 147; 188; 47; 25; 14; 140; 251; 198; 45; 147; 207; 194;
 66; 61; 100; 152; 72; 11; 39; 101; 186; 212; 51; 58; 157; 207; 7; 104; 170;
 122; 135; 5; 18; 201; 171; 158; 196; 170; 204; 35; 232; 217; 38; 140; 89;
 67; 221; 203; 125; 27; 90; 168; 101; 12; 159; 104; 123; 17; 111; 168; 213;
 180; 66; 96; 165; 153; 138; 246; 172; 96; 78; 12; 129; 43; 143; 170; 55;
 110; 177; 107; 35; 158; 224; 85; 37; 201; 105; 166; 149; 181; 107; 215; 113;
 60; 147; 252; 231; 36; 146; 181; 245; 15; 122; 150; 157; 70; 159; 2; 7; 214;
 225; 101; 154; 166; 90; 46; 46; 125; 168; 63; 6; 12; 89; 95; 122; 155; 165;
 179; 168; 250; 67; 120; 207; 154; 93; 221; 107; 193; 54; 49; 106; 61; 11;
 132; 160; 15; 80; 115; 11; 165; 62; 177; 245; 26; 112; 101; 210; 252; 164;
 232; 31; 97; 86; 125; 186; 193; 229; 253; 83; 211; 59; 189; 214; 75; 33; 26;
 243; 49; 129; 98; 218; 91; 85; 135; 21; 185; 42; 48; 151; 238; 76; 168; 176;
 37; 175; 138; 75; 134; 232; 48; 132; 90; 2; 50; 103; 1; 159; 2; 80; 27; 193;
 244; 248; 128; 154; 27; 78; 22; 122; 137; 216; 208; 13; 63; 147; 174; 20;
 98; 218; 53; 28; 34; 35; 148; 88; 76; 219; 242; 140; 69; 229; 112; 209; 198;
 180; 185; 18; 175; 38; 40; 90; 191; 24; 104; 5; 10; 5; 254; 149; 169; 250;
 96; 86; 113; 137; 126; 50; 115; 80; 160; 6; 205; 227; 232; 195; 154; 164;
 69; 116; 76; 63; 147; 39; 159; 9; 252; 142; 185; 81; 115; 40; 56; 37; 253;
 125; 244; 198; 101; 103; 101; 146; 10; 251; 61; 141; 52; 202; 39; 135; 229;
 33; 3; 145; 14; 104; 9; 255; 118; 196; 233; 251; 19; 90; 114; 193; 92; 123;
 69; 57; 158; 110; 148; 68; 43; 16; 249; 220; 219; 93; 43; 62; 85; 99; 191;
 12; 157; 127; 186; 214; 71; 164; 195; 130; 145; 127; 183; 41; 39; 75; 209;
 20; 0; 213; 135; 160; 100; 184; 28; 241; 60; 227; 243; 85; 27; 235; 115;
 126; 74; 21; 51; 187; 165; 8; 68; 188; 18; 162; 2; 237; 94; 199; 195; 72;
 80; 141; 68; 236; 191; 90; 12; 235; 27; 221; 235; 6; 226; 70; 241; 204; 69;
 41; 133; 130; 42; 129; 241; 219; 187; 188; 252; 209; 189; 208; 7; 8; 14; 39;
 45; 167; 189; 27; 11; 103; 27; 180; 154; 182; 59; 107; 105; 190; 170; 67;
 164; 140; 125; 123; 182; 6; 152; 73; 57; 39; 210; 39; 132; 226; 91; 87; 185;
 83; 69; 32; 231; 92; 8; 187; 132; 120; 65; 174; 65; 76; 182; 56; 49; 113;
 21; 119; 235; 238; 12; 58; 136; 175; 200; 0; 137; 21; 39; 155; 54; 167; 89;
 218; 104; 182; 101; 128; 189; 56; 204; 162; 182; 123; 229; 81; 113; 75; 234;
 2; 103; 50; 172; 133; 1; 187; 161; 65; 3; 224; 112; 190; 68; 193; 59; 8; 75;
 162; 228; 83; 227; 97; 13; 159; 26; 233; 184; 16; 177; 33; 50; 170; 154; 44;
 111; 186; 167; 35; 186; 59; 83; 33; 160; 108; 58; 44; 25; 146; 79; 118; 234;
 157; 224; 23; 83; 46; 93; 221; 110; 29; 191; 163; 78; 148; 208; 92; 26; 107;
 210; 192; 157; 179; 58; 53; 112; 116; 73; 46; 84; 40; 130; 82; 178; 113;
 126; 146; 60; 40; 105; 234; 27; 70; 162; 179; 184; 1; 200; 109; 131; 241;
 154; 164; 62; 5; 71; 95; 3; 179; 243; 173; 119; 88; 186; 65; 156; 82; 167;
 144; 15; 106; 28; 187; 159; 122; 217; 52; 146; 243; 237; 93; 167; 226; 249;
 88; 181; 225; 128; 118; 61; 150; 251; 35; 60; 110; 172; 65; 39; 44; 195; 1;
 14; 50; 161; 36; 144; 58; 143; 62; 221; 4; 102; 89; 183; 89; 44; 112; 136;
 226; 119; 3; 179; 108; 35; 195; 217; 94; 102; 156; 51; 177; 47; 229; 188;
 97; 96; 231; 21; 9; 26; 145; 162; 201; 217; 245; 193; 231; 215; 167; 204;
 139; 120; 113; 163; 184; 50; 42; 182; 14; 25; 18; 100; 99; 149; 78; 204; 46;
 92; 124; 144; 38];;

let EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC =
  ARM_MK_EXEC_RULE edwards25519_scalarmuldouble_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Actually proving that the tables are correct.                             *)
(* ------------------------------------------------------------------------- *)

let edwards25519_projective = define
 `edwards25519_projective P (X,Y,Z) <=>
        projective (integer_mod_ring p_25519) P (&X,&Y,&Z)`;;

let edwards25519_projective2 = define
 `edwards25519_projective2 P (X,Y,Z) <=>
        X < 2 * p_25519 /\ Y < 2 * p_25519 /\ Z < 2 * p_25519 /\
        edwards25519_projective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519)`;;

let EDWARDS25519_PROJECTIVE_IMP_PROJECTIVE2 = prove
 (`!P X Y Z.
        edwards25519_projective P (X,Y,Z)
        ==> edwards25519_projective2 P (X,Y,Z)`,
  REWRITE_TAC[edwards25519_projective; edwards25519_projective2] THEN
  SIMP_TAC[PROJECTIVE_ALT; FORALL_PAIR_THM;
           FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_25519] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[INT_REM_LT; INT_POS] THEN INT_ARITH_TAC);;

let EDWARDS25519_PROJECTIVE_BOUND = prove
 (`!x y X Y Z.
        edwards25519_projective (x,y) (X,Y,Z)
        ==> x < &p_25519 /\ y < &p_25519 /\
            X < p_25519 /\ Y < p_25519 /\ Z < p_25519`,
  REWRITE_TAC[edwards25519_projective; projective] THEN
  REWRITE_TAC[p_25519; IN_INTEGER_MOD_RING_CARRIER; INT_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let edwards25519_exprojective = define
 `edwards25519_exprojective P (X,Y,Z,W) <=>
        exprojective (integer_mod_ring p_25519) P (&X,&Y,&Z,&W)`;;

let edwards25519_exprojective2 = define
 `edwards25519_exprojective2 P (X,Y,Z,W) <=>
        X < 2 * p_25519 /\ Y < 2 * p_25519 /\
        Z < 2 * p_25519 /\ W < 2 * p_25519 /\
        edwards25519_exprojective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519, W MOD p_25519)`;;

let edwards25519_epprojective = define
 `edwards25519_epprojective (x,y) (YMX,XPY,KXY) <=>
        x < &p_25519 /\ y < &p_25519 /\
        &YMX = (y - x) rem &p_25519 /\
        &XPY = (x + y) rem &p_25519 /\
        &KXY = (&2 * &d_25519 * x * y) rem &p_25519`;;

let edwards25519_epprojectivew = define
 `edwards25519_epprojectivew (x,y) (YMX,XPY,KXY) <=>
        edwards25519_epprojective (x,y)
          (YMX MOD p_25519,XPY MOD p_25519,KXY MOD p_25519)`;;

let edwards25519_exprojective2w = define
 `edwards25519_exprojective2w P (X,Y,Z,W) <=>
        X <= 2 * p_25519 /\ Y < 2 * p_25519 /\ Z < 2 * p_25519 /\
        edwards25519_exprojective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519, W MOD p_25519)`;;

let EDWARDS25519_EXPROJECTIVE_IMP_EXPROJECTIVE2 = prove
 (`!P X Y Z W.
        edwards25519_exprojective P (X,Y,Z,W)
        ==> edwards25519_exprojective2 P (X,Y,Z,W)`,
  REWRITE_TAC[edwards25519_exprojective; edwards25519_exprojective2] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FORALL_PAIR_THM;
           FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_25519] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[INT_REM_LT; INT_POS] THEN INT_ARITH_TAC);;

let EDWARDS25519_EXPROJECTIVE2_IMP_EXPROJECTIVE2W = prove
 (`!P X Y Z W.
        edwards25519_exprojective2 P (X,Y,Z,W)
        ==> edwards25519_exprojective2w P (X,Y,Z,W)`,
  REWRITE_TAC[edwards25519_exprojective2; edwards25519_exprojective2w] THEN
  SIMP_TAC[LT_IMP_LE]);;

let EDWARDS25519_EPPROJECTIVE_BOUND = prove
 (`!P X Y Z.
        edwards25519_epprojective P (X,Y,Z)
        ==> X < p_25519 /\ Y < p_25519 /\ Z < p_25519`,
  REWRITE_TAC[FORALL_PAIR_THM; edwards25519_epprojective] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC INT_LT_REM THEN REWRITE_TAC[p_25519] THEN INT_ARITH_TAC);;

let EDWARDS25519_EPPROJECTIVE_IMP_EPPROJECTIVEW = prove
 (`!P X Y Z.
        edwards25519_epprojective P (X,Y,Z)
        ==> edwards25519_epprojectivew P (X,Y,Z)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[edwards25519_epprojective; edwards25519_epprojectivew] THEN
  SIMP_TAC[GSYM INT_OF_NUM_REM; INT_REM_REM]);;

let EDWARDS25519_EXPROJECTIVE2W_NEG = prove
 (`!P X Y Z W X' W'.
        edwards25519_exprojective2 P (X,Y,Z,W) /\
        X' < 2 EXP 256 /\ W' < 2 EXP 256 /\
        (X + X' == 2 * p_25519) (mod (2 EXP 256)) /\
        (W + W' == 2 * p_25519) (mod (2 EXP 256))
        ==> edwards25519_exprojective2w
             (group_inv edwards25519_group P) (X',Y,Z,W')`,
  REWRITE_TAC[edwards25519_exprojective2w; FORALL_PAIR_THM;
              edwards25519_exprojective2; edwards25519_exprojective;
              EDWARDS25519_GROUP; edwards_neg; INTEGER_MOD_RING_CLAUSES] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CARRIER_REM; GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    INT_CONG_IMP_EQ))) THEN
  REPEAT(ANTS_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `(&0:int <= y /\ y < p) /\ (&0 <= q - x /\ q - x < p)
      ==> abs((x + y) - q) < p`) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[p_25519] THEN INT_ARITH_TAC;
    DISCH_TAC]) THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (INT_ARITH
   `x + y:int = p ==> y = p - x`))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_REM_EQ])) THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  CONV_TAC INTEGER_RULE);;

let EDWARDS25519_EPPROJECTIVEW_NEG = prove
 (`!P X Y Z Z'.
        edwards25519_epprojectivew P (X,Y,Z) /\ p_25519 divides (Z + Z')
        ==> edwards25519_epprojectivew (group_inv edwards25519_group P)
                                       (Y,X,Z')`,
  REWRITE_TAC[edwards25519_epprojectivew; FORALL_PAIR_THM;
              edwards25519_epprojective; EDWARDS25519_GROUP;
              edwards_neg; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INTEGER_RULE `p divides (a + b:int) <=> (b == --a) (mod p)`] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; GSYM INT_OF_NUM_REM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC INT_LT_REM THEN
      REWRITE_TAC[p_25519] THEN INT_ARITH_TAC) THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[INTEGER_RULE
   `(--x:int == y) (mod p) <=> (x == --y) (mod p)`] THEN
  ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let EDWARDS25519_EXPROJECTIVE_BOUND = prove
 (`!x y X Y Z W.
        edwards25519_exprojective (x,y) (X,Y,Z,W)
        ==> x < &p_25519 /\ y < &p_25519 /\
            X < p_25519 /\ Y < p_25519 /\ Z < p_25519 /\ W < p_25519`,
  REWRITE_TAC[edwards25519_exprojective; exprojective] THEN
  REWRITE_TAC[p_25519; IN_INTEGER_MOD_RING_CARRIER; INT_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 = prove
 (`!P X Y Z W.
        edwards25519_exprojective2 P (X,Y,Z,W)
        ==> edwards25519_projective2 P (X,Y,Z)`,
  SIMP_TAC[edwards25519_exprojective2; edwards25519_projective2] THEN
  SIMP_TAC[FORALL_PAIR_THM; EXPROJECTIVE_PROJECTIVE; edwards25519_exprojective;
           edwards25519_projective; FIELD_INTEGER_MOD_RING; PRIME_P25519]);;

let GE25519_POW_1 = prove
 (`group_pow edwards25519_group E_25519 1 =
    (&15112221349535400772501151409588531511454012693041857206046113283949847762202,
     &46316835694926478169428394003475163141307993866256225615783033603165251855960)`,
  REWRITE_TAC[E_25519] THEN
  MATCH_MP_TAC GROUP_POW_1 THEN
  REWRITE_TAC[GSYM E_25519; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]);;

let GE25519_GROUPER =
  let pth = prove
   (`group_pow edwards25519_group E_25519 m = x /\
     group_pow edwards25519_group E_25519 n = y
     ==> group_pow edwards25519_group E_25519 (m + n) =
         group_mul edwards25519_group x y`,
    MESON_TAC[GROUP_POW_ADD; GROUP_POW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]) in
  fun th1 th2 ->
    CONV_RULE
     (BINOP2_CONV (RAND_CONV NUM_ADD_CONV) ECGROUP_MUL_CONV)
     (MATCH_MP pth (CONJ th1 th2));;

let BYTES_LOADED_DATA = prove
 (`bytes_loaded s (word (pc + 0x56a0)) edwards25519_scalarmuldouble_alt_data <=>
   read (memory :> bytes(word (pc + 0x56a0),768)) s =
   num_of_bytelist edwards25519_scalarmuldouble_alt_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` edwards25519_scalarmuldouble_alt_data)]);;

let EDWARDS25519DOUBLEBASE_TABLE_LEMMA = prove
 (`read (memory :> bytes(word (pc + 0x56a0),768)) s =
   num_of_bytelist edwards25519_scalarmuldouble_alt_data
   ==> !i. i < 8
           ==> edwards25519_epprojective
                (group_pow edwards25519_group E_25519 (i + 1))
         (bignum_from_memory(word(pc + 0x56a0 + 96 * i),4) s,
          bignum_from_memory(word(pc + 0x56a0 + 96 * i + 32),4) s,
          bignum_from_memory(word(pc + 0x56a0 + 96 * i + 64),4) s) /\
         ~(bignum_from_memory(word(pc + 0x56a0 + 96 * i + 64),4) s =
           0)`,
  let GE25519_POWERS =
    end_itlist CONJ
    (funpow 7 (fun l -> GE25519_GROUPER GE25519_POW_1 (hd l)::l)
                          [GE25519_POW_1]) in
  REWRITE_TAC[GSYM BYTES_LOADED_DATA;
              edwards25519_scalarmuldouble_alt_data] THEN
  CONV_TAC(LAND_CONV DATA64_CONV) THEN STRIP_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bignum_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[GE25519_POWERS] THEN
  REWRITE_TAC[p_25519; edwards25519_exprojective; edwards25519_epprojective;
              exprojective; d_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Common lemmas and tactics for the component proofs.                       *)
(* ------------------------------------------------------------------------- *)

let DESUM_RULE' = cache DESUM_RULE and DECARRY_RULE' = cache DECARRY_RULE;;

let lvs =
 [
  (*** These are for the toplevel function, and not used often ***)

  "resx",[`X25`;`0`];
  "resy",[`X25`;`32`];
  "scalar",[`SP`;`0`];
  "bscalar",[`SP`;`32`];
  "btabent",[`SP`;`64`];
  "acc",[`SP`;`160`];
  "acc_x",[`SP`;`160`];
  "acc_y",[`SP`;`196`];
  "acc_z",[`SP`;`228`];
  "acc_w",[`SP`;`260`];
  "tabent",[`SP`;`288`];
  "tab",[`SP`;`416`];

  (*** These are local for the subroutines ***)

  "x_0",[`X22`;`0`];
  "y_0",[`X22`;`32`];
  "z_0",[`X22`;`64`];
  "w_0",[`X22`;`96`];
  "x_1",[`X23`;`0`];
  "y_1",[`X23`;`32`];
  "z_1",[`X23`;`64`];
  "w_1",[`X23`;`96`];
  "x_2",[`X24`;`0`];
  "y_2",[`X24`;`32`];
  "z_2",[`X24`;`64`];
  "w_2",[`X24`;`96`];
  "t0",[`SP`;`0`];
  "t1",[`SP`;`32`];
  "t2",[`SP`;`64`];
  "t3",[`SP`;`96`];
  "t4",[`SP`;`128`];
  "t5",[`SP`;`160`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_mc 100 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x59a0) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X22 s = read X22 t /\
                read X23 s = read X23 t /\
                read X24 s = read X24 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                    X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   [3;5;7;9;11;12;14;15;17;18;19;20;21;22;23;24;26;28;30;32;33;34;35;36;37;
    38;39;40;41;43;45;47;49;50;51;52;53;54;55;56;57;58;60;62;64;66;67]
   (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   [69;71;72;74;75;77;78;80;82;83;84;86;88;89;90;91;92] (68--92) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s86:int64) + 1) <= 80 /\
    (val(sum_s86:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s86:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64)) +
        2 EXP 64 * val(mulhi_s69:int64) +
        2 EXP 128 * val(mulhi_s72:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  SUBGOAL_THEN
   `&(val(word(19 + 19 * val(sum_s86:int64)):int64)):real =
    &19 * (&(val(sum_s86:int64)) + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `19 * (x + 1) = 19 + 19 * x`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s86:int64) + 1 <= 80` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_or sum_s82 (word 9223372036854775808:int64))):real =
    &2 pow 63 + &(val(sum_s84:int64)) / &2`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or m (word_and x (word_not m))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and m (word_and x (word_not m)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s86:int64) + val(sum_s84:int64) =
      2 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 pow 256 * (&(bitval carry_s92) - &1:real) +
    &(bignum_of_wordlist[sum_s89; sum_s90; sum_s91; sum_s92]):real =
    &(38 * h + l) - &((val(sum_s86:int64) + 1) * p_25519)`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   (94--97) (93--100) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s86:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l < (val(sum_s86:int64) + 1) * p_25519 <=> ~carry_s92`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[REAL_BITVAL_NOT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x - y = &2 pow 256 * c + s`)) THEN
    BOUNDER_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x = &2 pow 256 * c + s + y`)) THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s92:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_mc 94 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x59a0) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X22 s = read X22 t /\
                read X23 s = read X23 t /\
                read X24 s = read X24 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 m * n) (mod p_25519))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                    X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   [3;5;7;9;11;12;14;15;17;18;19;20;21;22;23;24;26;28;30;32;33;34;35;36;37;
    38;39;40;41;43;45;47;49;50;51;52;53;54;55;56;57;58;60;62;64;66;67]
   (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   [69;71;72;74;75;77;78;80;82;83;84;86;88;89;90;91;92] (68--94) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s86:int64) + 1) <= 80 /\
    (val(sum_s86:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s86:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64)) +
        2 EXP 64 * val(mulhi_s69:int64) +
        2 EXP 128 * val(mulhi_s72:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  UNDISCH_TAC
   `&2 pow 64 * &(val(mulhi_s88:int64)) + &(val(mullo_s88:int64)) =
    &19 * &(val(sum_s86:int64))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= 80 ==> a < 80`)) THEN
  DISCH_THEN(fun bth -> DISCH_THEN(fun th ->
        MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE [bth] [th])))) THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT2) THEN

  SUBGOAL_THEN
   `&(val(word_and sum_s82 (word 9223372036854775807:int64))):real =
    &(val(sum_s84:int64)) / &2`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s86:int64) + val(sum_s84:int64) =
      2 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN

  REWRITE_TAC[GSYM CONG; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\
        (&0 <= ca - q * p /\ ca - q * p < p2) /\
        (&0 <= ca - q * p /\ ca - q * p < p2 ==> x = ca - q * p)
        ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s86:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519`;
      `38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    STRIP_TAC] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
              int_mul_th; int_pow_th] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_mc 72 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n.
      read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x59a0) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X22 s = read X22 t /\
                read X23 s = read X23 t /\
                read X24 s = read X24 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 n EXP 2)
                (mod p_25519))
        (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                    X10; X11; X12; X13; X14] ,,
         MAYCHANGE
          [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8_alt ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--45) (1--45) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s31; sum_s33; sum_s35; sum_s37]`;
    `h = bignum_of_wordlist[sum_s39; sum_s41; sum_s43; sum_s45]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (46--70) (46--72) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s64:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s64:int64) + 1) <= 80 /\
    (val(sum_s64:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s64:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s64:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s61:int64) + val(sum_s60:int64)) +
        2 EXP 64 * val(mulhi_s47:int64) +
        2 EXP 128 * val(mulhi_s50:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  UNDISCH_TAC
   `&2 pow 64 * &(val(mulhi_s66:int64)) + &(val(mullo_s66:int64)) =
    &19 * &(val(sum_s64:int64))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= 80 ==> a < 80`)) THEN
  DISCH_THEN(fun bth -> DISCH_THEN(fun th ->
        MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE [bth] [th])))) THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT2) THEN

  SUBGOAL_THEN
   `&(val(word_and sum_s60 (word 9223372036854775807:int64))):real =
    &(val(sum_s62:int64)) / &2`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s64:int64) + val(sum_s62:int64) =
      2 * (2 EXP 64 * val(sum_s61:int64) + val(sum_s60:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN

  REWRITE_TAC[GSYM CONG; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\
        (&0 <= ca - q * p /\ ca - q * p < p2) /\
        (&0 <= ca - q * p /\ ca - q * p < p2 ==> x = ca - q * p)
        ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s64:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(val(sum_s64:int64) + 1) * p_25519 <= (38 * h + l) + p_25519`;
      `38 * h + l < (val(sum_s64:int64) + 1) * p_25519 + p_25519`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    STRIP_TAC] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
              int_mul_th; int_pow_th] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add_twice4 (slightly sharper disjunctive hypothesis).        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x59a0) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X22 s = read X22 t /\
                read X23 s = read X23 t /\
                read X24 s = read X24 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < 2 * p_25519 \/ n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                      m + n) (mod p_25519)))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (11--14) (9--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= m + n then (&m + &n) - &2 * &p_25519:int else &m + &n` THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `2 EXP 256` o MATCH_MP (ARITH_RULE
     `m < p \/ n < p
      ==> !e:num. p < e /\ m < e /\ n < e ==> m + n < e + p`)) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= m + n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of double_twice4.                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DOUBLE_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_mc 14 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x59a0) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X22 s = read X22 t /\
                read X23 s = read X23 t /\
                read X24 s = read X24 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                      2 * n) (mod p_25519)))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--6) (1--6) THEN
  SUBGOAL_THEN `carry_s6 <=> 2 EXP 256 <= 2 * n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (9--12) (7--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= 2 * n then (&2 * &n) - &2 * &p_25519:int else &2 * &n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LE; SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= 2 * n` THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4 (slightly sharper hypothesis distinctions).       *)
(* This version also has <= not < for n, to allow imprecise negations of 0.  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC edwards25519_scalarmuldouble_alt_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x59a0) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) edwards25519_scalarmuldouble_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X22 s = read X22 t /\
                read X23 s = read X23 t /\
                read X24 s = read X24 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < 2 * p_25519 /\ n <= 2 * p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519) /\
                (n <= 2 * p_25519
                 ==> (&(read(memory :> bytes
                         (word_add (read p3 t) (word n3),8 * 4)) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE') THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (11--14) (9--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT; INT_OF_NUM_LE]
   `!x':int. (x' == &m - &n) (mod p) /\
             (m < p2 /\ n <= p2 ==> x' < &p2) /\
             (n <= p2 ==> &x = x')
             ==> (m < p2 /\ n <= p2 ==> x < p2) /\
                 (n:num <= p2 ==> (&x:int == &m - &n) (mod p))`) THEN
  EXISTS_TAC `if m < n then &m - &n + &2 * &p_25519:int else &m - &n` THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      SUBGOAL_THEN `m < 2 EXP 256` MP_TAC THENL
       [EXPAND_TAC "m" THEN BOUNDER_TAC[];
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN REAL_ARITH_TAC]];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE') THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of modular inverse inlining                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MODINV_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_mc,
    EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,0x1128,
    (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_mc] THENC TRIM_LIST_CONV)
    `TRIM_LIST (12,16) bignum_inv_p25519_mc`,
    CORE_INV_P25519_CORRECT)
   [`read X0 s`; `read X1 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `pc + 0x1128`; `word_add stackpointer (word 192):int64`];;

(* ------------------------------------------------------------------------- *)
(* Embedded subroutine correctness.                                          *)
(* ------------------------------------------------------------------------- *)

let LOCAL_EPDOUBLE_CORRECT = time prove
 (`!p3 p1 T1 pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,160))
        [(word pc,0x59a0); (p3,128); (p1,96)] /\
    nonoverlapping (p3,128) (word pc,0x59a0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_mc /\
              read PC s = word(pc + 0x2484) /\
              read SP s = stackpointer /\
              read X22 s = p3 /\
              read X23 s = p1 /\
              bignum_triple_from_memory(p1,4) s = T1)
         (\s. read PC s = word (pc + 0x305c) /\
              !P1. P1 IN group_carrier edwards25519_group /\
                   edwards25519_projective2 P1 T1
                      ==> edwards25519_exprojective2
                           (edwards_add edwards25519 P1 P1)
                           (bignum_quadruple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,128);
                      memory :> bytes(stackpointer,160)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ;
              bignum_quadruple_from_memory; bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t0"; "x_1"; "y_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t1"; "z_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t2"; "x_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t3"; "y_1"] THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t1"; "t1"] THEN
  LOCAL_SQR_4_TAC 0 ["t0"; "t0"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t4"; "t2"; "t3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "t2"; "t3"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "t1"; "t2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "t4"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t2"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t3"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["w_0"; "t1"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t1"; "t3"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_projective2; edwards25519_exprojective2] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`] THEN STRIP_TAC THEN
  DISCARD_STATE_TAC "s14" THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`aligned a b`; `nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`; `&Z_1 rem &p_25519`]
   EDWARDS_PREXPROJDOUBLEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM edwards25519_projective; INT_OF_NUM_REM] THEN
    REWRITE_TAC[EDWARDS_NONSINGULAR_25519] THEN
    SIMP_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM edwards25519; edwards25519_exprojective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[edwards_prexprojdoublen; edwards_prexprojdouble;
              edwards25519] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_EPDOUBLE_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_quadruple_from_memory]
         LOCAL_EPDOUBLE_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_mc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_mc,th)
  [`read X22 s`; `read X23 s`;
   `read(memory :> bytes(read X23 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 64),8 * 4)) s`;
   `pc:num`; `read SP s`];;

let LOCAL_PDOUBLE_CORRECT = time prove
 (`!p3 p1 T1 pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,160))
        [(word pc,0x59a0); (p3,96); (p1,96)] /\
    nonoverlapping (p3,96) (word pc,0x59a0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_mc /\
              read PC s = word(pc + 0x3068) /\
              read SP s = stackpointer /\
              read X22 s = p3 /\
              read X23 s = p1 /\
              bignum_triple_from_memory(p1,4) s = T1)
         (\s. read PC s = word (pc + 0x3ac8) /\
              !P1. P1 IN group_carrier edwards25519_group /\
                   edwards25519_projective2 P1 T1
                      ==> edwards25519_projective2
                           (edwards_add edwards25519 P1 P1)
                           (bignum_triple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,96);
                      memory :> bytes(stackpointer,160)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; PAIR_EQ;
              bignum_triple_from_memory] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t0"; "x_1"; "y_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t1"; "z_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t2"; "x_1"] THEN
  LOCAL_SQR_4_TAC 0 ["t3"; "y_1"] THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t1"; "t1"] THEN
  LOCAL_SQR_4_TAC 0 ["t0"; "t0"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t4"; "t2"; "t3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "t2"; "t3"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "t1"; "t2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "t4"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t2"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t3"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t1"; "t3"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_projective2] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`] THEN STRIP_TAC THEN
  DISCARD_STATE_TAC "s13" THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`aligned a b`; `nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_imp o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`; `&Z_1 rem &p_25519`]
   EDWARDS_PREXPROJDOUBLEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM edwards25519_projective; INT_OF_NUM_REM] THEN
    REWRITE_TAC[EDWARDS_NONSINGULAR_25519] THEN
    SIMP_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    SIMP_TAC[REWRITE_RULE[GSYM FORALL_PAIR_THM] EXPROJECTIVE_PROJECTIVE;
             FIELD_INTEGER_MOD_RING; PRIME_P25519;
             edwards_prexprojdoublen; LET_DEF; LET_END_DEF;
             edwards_prexprojdouble] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[edwards25519; edwards25519_projective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[edwards_prexprojdoublen; edwards_prexprojdouble;
              edwards25519] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_PDOUBLE_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory]
         LOCAL_PDOUBLE_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_mc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_mc,th)
  [`read X22 s`; `read X23 s`;
   `read(memory :> bytes(read X23 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 64),8 * 4)) s`;
   `pc:num`; `read SP s`];;

let LOCAL_EPADD_CORRECT = time prove
 (`!p3 p1 Q1 p2 Q2 pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,192))
        [(word pc,0x59a0); (p3,128); (p1,128); (p2,128)] /\
    nonoverlapping (p3,128) (word pc,0x59a0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_mc /\
              read PC s = word(pc + 0x3ad4) /\
              read SP s = stackpointer /\
              read X22 s = p3 /\
              read X23 s = p1 /\
              read X24 s = p2 /\
              bignum_quadruple_from_memory(p1,4) s = Q1 /\
              bignum_quadruple_from_memory(p2,4) s = Q2)
         (\s. read PC s = word (pc + 0x4a8c) /\
              !P1 P2. P1 IN group_carrier edwards25519_group /\
                      P2 IN group_carrier edwards25519_group /\
                      edwards25519_exprojective2 P1 Q1 /\
                      edwards25519_exprojective2 P2 Q2
                      ==> edwards25519_exprojective2
                           (edwards_add edwards25519 P1 P2)
                           (bignum_quadruple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,128);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`; `W_1:num`;
    `p2:int64`; `X_2:num`; `Y_2:num`; `Z_2:num`; `W_2:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; bignum_quadruple_from_memory;
              bignum_pair_from_memory; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_MUL_4_TAC 0 ["t0"; "w_1"; "w_2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "y_1"; "x_1"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "y_2"; "x_2"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "y_1"; "x_1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t4"; "y_2"; "x_2"] THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t5"; "z_2"] THEN
  LOCAL_MUL_4_TAC 0 ["t1"; "t1"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["t3"; "t3"; "t4"] THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (12--29) THEN
  SUBGOAL_THEN
   `read (memory :> bytes (word_add stackpointer (word 64),8 * 4)) s29 =
    16295367250680780974490674513165176452449235426866156013048779062215315747161`
  ASSUME_TAC THENL
   [CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  LOCAL_MUL_4_TAC 0 ["t2"; "t2"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["t4"; "z_1"; "t5"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t0"; "t3"; "t1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t5"; "t3"; "t1"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "t4"; "t2"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t3"; "t4"; "t2"] THEN
  LOCAL_MUL_4_TAC 0 ["w_0"; "t0"; "t5"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t0"; "t1"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t3"; "t5"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t1"; "t3"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_exprojective2] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`; `x2:int`; `y2:int`] THEN
  STRIP_TAC THEN  DISCARD_STATE_TAC "s39" THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`aligned a b`; `nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`; `&Z_1 rem &p_25519`; `&W_1 rem &p_25519`;
    `x2:int`; `y2:int`;
    `&X_2 rem &p_25519`; `&Y_2 rem &p_25519`; `&Z_2 rem &p_25519`; `&W_2 rem &p_25519`]
   EDWARDS_EXPROJADD4) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EDWARDS_NONSINGULAR_25519; INT_OF_NUM_REM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN
    REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [edwards25519_exprojective])) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[exprojective] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CHAR; IN_INTEGER_MOD_RING_CARRIER;
                INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_25519] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC(MESON[RING_DIV_1]
     `x IN ring_carrier f /\ y = ring_1 f ==> ring_div f x y = x`) THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM edwards25519; edwards25519_exprojective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [edwards25519_exprojective]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[edwards_exprojadd4; edwards_exprojadd; edwards25519;
              INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM p_25519; GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES; GSYM
   (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[p_25519]
     (AP_TERM `\x. (2 * x) MOD p_25519` d_25519)))] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_EPADD_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_quadruple_from_memory]
         LOCAL_EPADD_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_mc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_mc,th)
  [`read X22 s`; `read X23 s`;
   `read(memory :> bytes(read X23 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 64),8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 96),8 * 4)) s`;
   `read X24 s`;
   `read(memory :> bytes(read X24 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X24 s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read X24 s) (word 64),8 * 4)) s,
    read(memory :> bytes(word_add (read X24 s) (word 96),8 * 4)) s`;
   `pc:num`; `read SP s`];;

let LOCAL_PEPADD_CORRECT = time prove
 (`!p3 p1 Q1 p2 T2 pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,192))
        [(word pc,0x59a0); (p3,128); (p1,128); (p2,96)] /\
    nonoverlapping (p3,128) (word pc,0x59a0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                 edwards25519_scalarmuldouble_alt_mc /\
              read PC s = word(pc + 0x4a98) /\
              read SP s = stackpointer /\
              read X22 s = p3 /\
              read X23 s = p1 /\
              read X24 s = p2 /\
              bignum_quadruple_from_memory(p1,4) s = Q1 /\
              bignum_triple_from_memory(p2,4) s = T2)
         (\s. read PC s = word (pc + 0x5698) /\
              !P1 P2. P1 IN group_carrier edwards25519_group /\
                      P2 IN group_carrier edwards25519_group /\
                      edwards25519_exprojective2w P1 Q1 /\
                      edwards25519_epprojectivew P2 T2
                      ==> edwards25519_exprojective2
                           (edwards_add edwards25519 P1 P2)
                           (bignum_quadruple_from_memory(p3,4) s))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(p3,128);
                      memory :> bytes(stackpointer,192)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p3:int64`; `p1:int64`; `X_1:num`; `Y_1:num`; `Z_1:num`; `W_1:num`;
    `p2:int64`; `YMX_2:num`; `XPY_2:num`; `KXY_2:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS;
              bignum_quadruple_from_memory; bignum_triple_from_memory;
              bignum_pair_from_memory; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_DOUBLE_TWICE4_TAC 0 ["t0"; "z_1"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t1"; "y_1"; "x_1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t2"; "y_1"; "x_1"] THEN
  LOCAL_MUL_4_TAC 0 ["t3"; "w_1"; "z_2"] THEN
  LOCAL_MUL_4_TAC 0 ["t1"; "t1"; "x_2"] THEN
  LOCAL_MUL_4_TAC 0 ["t2"; "t2"; "y_2"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t4"; "t0"; "t3"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t0"; "t0"; "t3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t5"; "t2"; "t1"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["t1"; "t2"; "t1"] THEN
  LOCAL_MUL_4_TAC 0 ["z_0"; "t4"; "t0"] THEN
  LOCAL_MUL_4_TAC 0 ["x_0"; "t5"; "t4"] THEN
  LOCAL_MUL_4_TAC 0 ["y_0"; "t0"; "t1"] THEN
  LOCAL_MUL_4_TAC 0 ["w_0"; "t5"; "t1"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[edwards25519_exprojective2; edwards25519_exprojective2w;
              edwards25519_epprojectivew] THEN
  MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`; `x2:int`; `y2:int`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EDWARDS25519_EXPROJECTIVE_BOUND) THEN
  DISCARD_STATE_TAC "s14" THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`aligned a b`; `nonoverlapping_modulo a b c`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(
   (ANTS_TAC THENL[ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) ORELSE
   DISCH_THEN(K ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
    `x1:int`; `y1:int`;
    `&X_1 rem &p_25519`; `&Y_1 rem &p_25519`;
    `&Z_1 rem &p_25519`; `&W_1 rem &p_25519`;
    `x2:int`; `y2:int`;
    `x2:int`; `y2:int`; `&1:int`; `(x2 * y2) rem &p_25519`]
   EDWARDS_EXPROJADD4) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EDWARDS_NONSINGULAR_25519; INT_OF_NUM_REM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
    SIMP_TAC[EDWARDS25519_GROUP] THEN
    REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [edwards25519_exprojective]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[exprojective] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CHAR; IN_INTEGER_MOD_RING_CARRIER;
                INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_25519] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC(MESON[RING_DIV_1]
     `x IN ring_carrier f /\ y = ring_1 f ==> ring_div f x y = x`) THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM edwards25519; edwards25519_exprojective] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [edwards25519_epprojective]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[edwards_exprojadd4; edwards_exprojadd; edwards25519;
              INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
   [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let LOCAL_PEPADD_TAC =
  let th =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_quadruple_from_memory]
         LOCAL_PEPADD_CORRECT) in
  ARM_SUBROUTINE_SIM_TAC
   (edwards25519_scalarmuldouble_alt_mc,EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC,
    0x0,edwards25519_scalarmuldouble_alt_mc,th)
  [`read X22 s`; `read X23 s`;
   `read(memory :> bytes(read X23 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 64),8 * 4)) s,
    read(memory :> bytes(word_add (read X23 s) (word 96),8 * 4)) s`;
   `read X24 s`;
   `read(memory :> bytes(read X24 s,8 * 4)) s,
    read(memory :> bytes(word_add (read X24 s) (word 32),8 * 4)) s,
    read(memory :> bytes(word_add (read X24 s) (word 64),8 * 4)) s`;
   `pc:num`; `read SP s`];;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let EDWARDS25519_SCALARMULDOUBLE_ALT_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,1632))
        [(word pc,0x59a0); (res,64); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x59a0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
               (APPEND edwards25519_scalarmuldouble_alt_mc
                       edwards25519_scalarmuldouble_alt_data) /\
              read PC s = word(pc + 0x14) /\
              read SP s = word_add stackpointer (word 192)/\
              C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read PC s = word (pc + 0x2468) /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X30] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(res,64);
                      memory :> bytes(stackpointer,1632)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `point:int64`; `bscalar:int64`;
    `n_input:num`; `x:num`; `y:num`; `m_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[bignum_pair_from_memory; PAIR_EQ] THEN
  REWRITE_TAC[WORD_RULE `word(8 * 4) = word 32`; GSYM FORALL_PAIR_THM] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  (*** The recoded forms of the inputs, mathematically ***)

  BIGNUM_TERMRANGE_TAC `4` `n_input:num` THEN
  BIGNUM_TERMRANGE_TAC `4` `m_input:num` THEN
  ABBREV_TAC
   `recoder =
    0x0888888888888888888888888888888888888888888888888888888888888888` THEN
  ABBREV_TAC
   `n = if n_input DIV 2 EXP 192 > 2 EXP 63
        then (n_input + recoder) - 8 * n_25519
        else n_input + recoder` THEN
  SUBGOAL_THEN `n < 9 * 2 EXP 252` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n"; "recoder"] THEN REWRITE_TAC[n_25519] THEN
    UNDISCH_TAC `n_input < 2 EXP (64 * 4)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `m = if m_input DIV 2 EXP 192 > 2 EXP 63
        then (m_input + recoder) - 8 * n_25519
        else m_input + recoder` THEN
  SUBGOAL_THEN `m < 9 * 2 EXP 252` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "recoder"] THEN REWRITE_TAC[n_25519] THEN
    UNDISCH_TAC `m_input < 2 EXP (64 * 4)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier edwards25519_group
        ==> group_pow edwards25519_group P n_input =
            group_zpow edwards25519_group P (&n - &recoder) /\
            group_pow edwards25519_group P m_input =
            group_zpow edwards25519_group P (&m - &recoder)`
   (fun th -> SIMP_TAC[th; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519])
  THENL
   [SIMP_TAC[GROUP_ZPOW_EQ; GSYM GROUP_NPOW] THEN
    REPEAT STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["n"; "m"; "recoder"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    TRY(W(MP_TAC o PART_MATCH (rand o rand) INT_OF_NUM_SUB o
          lhand o lhand o snd) THEN
        ANTS_TAC THENL
        [REWRITE_TAC[n_25519] THEN ASM_ARITH_TAC;
         DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INT_ARITH `(x + y) - y:int = x`; INT_CONG_REFL]THEN
    REWRITE_TAC[INTEGER_RULE
     `(n:int == (n + x) - m - x) (mod p) <=> p divides m`] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[HAS_SIZE] SIZE_EDWARDS25519_GROUP)] THEN
    MATCH_MP_TAC GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER THEN
    ASM_REWRITE_TAC[FINITE_GROUP_CARRIER_EDWARDS25519];
    ALL_TAC] THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_DOWN_TAC `63` `pc + 0x990` `pc + 0x111c`
   `\i s.
      read (memory :> bytes(word(pc + 0x56a0),768)) s =
      num_of_bytelist edwards25519_scalarmuldouble_alt_data /\
      read SP s = word_add stackpointer (word 192) /\
      read X25 s = res /\
      read X19 s = word (4 * i) /\
      bignum_from_memory(word_add stackpointer (word 192),4) s = n /\
      bignum_from_memory(word_add stackpointer (word 224),4) s = m /\
      !P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> (!j. j < 8
                   ==> edwards25519_exprojective2
                        (group_pow edwards25519_group P (j + 1))
                      (bignum_quadruple_from_memory
                        (word_add stackpointer (word (608 + 128 * j)),4) s)) /\
              edwards25519_exprojective2
               (group_mul edwards25519_group
                  (group_zpow edwards25519_group P
                    (&(n DIV 2 EXP (4 * i)) - &(recoder DIV 2 EXP (4 * i))))
                  (group_zpow edwards25519_group E_25519
                    (&(m DIV 2 EXP (4 * i)) - &(recoder DIV 2 EXP (4 * i)))))
               (bignum_quadruple_from_memory
                 (word_add stackpointer (word 352),4) s)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Recoding of m ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (bscalar,8 * 4)) s0` THEN
    ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (21--24) (1--26) THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word 224),8 * 4)) s26 = m`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 4)` THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
      ASM_SIMP_TAC[ARITH_RULE `n < 9 * 2 EXP 252 ==> n < 2 EXP (64 * 4)`] THEN
      EXPAND_TAC "m" THEN
      REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `m_input DIV 2 EXP 192 > 2 EXP 63 ==> 8 * n_25519 <= m_input + recoder`
      MP_TAC THENL
       [EXPAND_TAC "recoder" THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN DISCH_THEN(K ALL_TAC)] THEN
      EXPAND_TAC "m_input" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      EXPAND_TAC "recoder" THEN REWRITE_TAC[real_gt; n_25519] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_NOT_LE; COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "recoder" THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Recoding of n ***)

    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (scalar,8 * 4)) s26` THEN
    ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
     (35--38) (27--40) THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word 192),8 * 4)) s40 = n`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 4)` THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
      ASM_SIMP_TAC[ARITH_RULE `n < 9 * 2 EXP 252 ==> n < 2 EXP (64 * 4)`] THEN
      EXPAND_TAC "n" THEN
      REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      SUBGOAL_THEN
       `n_input DIV 2 EXP 192 > 2 EXP 63 ==> 8 * n_25519 <= n_input + recoder`
      MP_TAC THENL
       [EXPAND_TAC "recoder" THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN DISCH_THEN(K ALL_TAC)] THEN
      EXPAND_TAC "n_input" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      EXPAND_TAC "recoder" THEN REWRITE_TAC[real_gt; n_25519] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_NOT_LE; COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "recoder" THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    (*** Modular reduction of x ***)

    BIGNUM_LDIGITIZE_TAC "x_" `read(memory :> bytes(point,8 * 4)) s40` THEN
    ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
      (43--46) (41--52) THEN
    ABBREV_TAC
     `X =
      read(memory :> bytes(word_add stackpointer (word 608),8 * 4)) s52` THEN
    SUBGOAL_THEN `x MOD (2 * p_25519) = X` MP_TAC THENL
     [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
       [`256`;
       `(if x < 2 * p_25519 then &x else &x - &2 * &p_25519):real`] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "X" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[ARITH_RULE `256 = 64 * 4`; BIGNUM_FROM_MEMORY_BOUND];
        ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM NOT_LE; COND_SWAP];
        SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
        ONCE_REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC MOD_CASES THEN
        EXPAND_TAC "x" THEN REWRITE_TAC[p_25519] THEN
        CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]] THEN
      SUBGOAL_THEN `carry_s46 <=> 2 * p_25519 <= x` (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "x" THEN REWRITE_TAC[p_25519] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_POP_ASSUM_LIST
         (MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["X"; "x"] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_25519] THEN
        ASM_REWRITE_TAC[] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [MOD_UNIQUE] THEN
      REWRITE_TAC[MULT_EQ_0; ARITH_EQ; p_25519] THEN
      REWRITE_TAC[GSYM p_25519] THEN STRIP_TAC] THEN

    (*** Modular reduction of y ***)

    BIGNUM_LDIGITIZE_TAC
      "y_" `read(memory :> bytes(word_add point (word 32),8 * 4)) s52` THEN
    ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
     (55--58) (53--64) THEN
    ABBREV_TAC
     `Y =
      read(memory :> bytes(word_add stackpointer (word 640),8 * 4)) s64` THEN
    SUBGOAL_THEN `y MOD (2 * p_25519) = Y` MP_TAC THENL
     [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN MAP_EVERY EXISTS_TAC
       [`256`;
       `(if y < 2 * p_25519 then &y else &y - &2 * &p_25519):real`] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Y" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[ARITH_RULE `256 = 64 * 4`; BIGNUM_FROM_MEMORY_BOUND];
        ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM NOT_LE; COND_SWAP];
        SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
        ONCE_REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC MOD_CASES THEN
        EXPAND_TAC "y" THEN REWRITE_TAC[p_25519] THEN
        CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]] THEN
      SUBGOAL_THEN `carry_s58 <=> 2 * p_25519 <= y` (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "y" THEN REWRITE_TAC[p_25519] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["Y"; "y"] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_25519] THEN
        ASM_REWRITE_TAC[] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [MOD_UNIQUE] THEN
      REWRITE_TAC[MULT_EQ_0; ARITH_EQ; p_25519] THEN
      REWRITE_TAC[GSYM p_25519] THEN STRIP_TAC] THEN

    (*** Creation of point multiple 1 ****)

    LOCAL_MUL_4_TAC 6 ["x_0"; "x_1"; "x_2"] THEN
    REABBREV_TAC
     `W =
      read(memory :> bytes(word_add stackpointer (word 704),8 * 4)) s71` THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    ABBREV_TAC
     `Z =
      read(memory :> bytes(word_add stackpointer (word 672),8 * 4)) s71` THEN
    SUBGOAL_THEN `Z < 2 * p_25519 /\ (Z == 1) (mod (2 * p_25519))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Z" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
      ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1; p_25519; CONG] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 1) (X,Y,Z,W)`
    ASSUME_TAC THENL
     [X_GEN_TAC `P:int#int` THEN SIMP_TAC[GROUP_POW_1] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
      ASM_REWRITE_TAC[paired; modular_decode; edwards25519_exprojective2] THEN
      SIMP_TAC[edwards25519_exprojective; EXPROJECTIVE_ALT;
                FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
      REWRITE_TAC[INTEGER_MOD_RING_CARRIER_REM; INTEGER_MOD_RING_CLAUSES;
                  GSYM INT_OF_NUM_REM] THEN
      REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD p_25519` o
             GEN_REWRITE_RULE I [CONG])) THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] MOD_MOD; MOD_MOD_REFL] THEN
      REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[MULT_CLAUSES] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [CONG]))] THEN

    (*** Creation of point multiple 2 ****)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (72--75) THEN
    LOCAL_EPDOUBLE_TAC 76 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_2 = read(memory :> bytes(word_add stackpointer (word 736),8 * 4)) s76`;
      `Y_2 = read(memory :> bytes(word_add stackpointer (word 768),8 * 4)) s76`;
      `Z_2 = read(memory :> bytes(word_add stackpointer (word 800),8 * 4)) s76`;
      `W_2 = read(memory :> bytes(word_add stackpointer (word 832),8 * 4)) s76`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 2) (X_2,Y_2,Z_2,W_2)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 1`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W:num` THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 3 ****)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (77--83) THEN
    LOCAL_EPADD_TAC 84 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_3 = read(memory :> bytes(word_add stackpointer (word 864),8 * 4)) s84`;
      `Y_3 = read(memory :> bytes(word_add stackpointer (word 896),8 * 4)) s84`;
      `Z_3 = read(memory :> bytes(word_add stackpointer (word 928),8 * 4)) s84`;
      `W_3 = read(memory :> bytes(word_add stackpointer (word 960),8 * 4)) s84`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 3) (X_3,Y_3,Z_3,W_3)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`group_pow edwards25519_group P 1`;
        `group_pow edwards25519_group P 2`]) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 4 ****)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (85--90) THEN
    LOCAL_EPDOUBLE_TAC 91 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_4 = read(memory :> bytes(word_add stackpointer (word 992),8 * 4)) s91`;
      `Y_4 = read(memory :> bytes(word_add stackpointer (word 1024),8 * 4)) s91`;
      `Z_4 = read(memory :> bytes(word_add stackpointer (word 1056),8 * 4)) s91`;
      `W_4 = read(memory :> bytes(word_add stackpointer (word 1088),8 * 4)) s91`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 4) (X_4,Y_4,Z_4,W_4)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 2`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W_2:num` THEN
      RULE_ASSUM_TAC(SIMP_RULE[GROUP_POW_1]) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 5 ****)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (92--98) THEN
    LOCAL_EPADD_TAC 99 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_5 = read(memory :> bytes(word_add stackpointer (word 1120),8 * 4)) s99`;
      `Y_5 = read(memory :> bytes(word_add stackpointer (word 1152),8 * 4)) s99`;
      `Z_5 = read(memory :> bytes(word_add stackpointer (word 1184),8 * 4)) s99`;
      `W_5 = read(memory :> bytes(word_add stackpointer (word 1216),8 * 4)) s99`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 5) (X_5,Y_5,Z_5,W_5)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`group_pow edwards25519_group P 1`;
        `group_pow edwards25519_group P 4`]) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 6 ****)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (100--105) THEN
    LOCAL_EPDOUBLE_TAC 106 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_6 = read(memory :> bytes(word_add stackpointer (word 1248),8 * 4)) s106`;
      `Y_6 = read(memory :> bytes(word_add stackpointer (word 1280),8 * 4)) s106`;
      `Z_6 = read(memory :> bytes(word_add stackpointer (word 1312),8 * 4)) s106`;
      `W_6 = read(memory :> bytes(word_add stackpointer (word 1344),8 * 4)) s106`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 6) (X_6,Y_6,Z_6,W_6)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 3`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W_3:num` THEN
      RULE_ASSUM_TAC(SIMP_RULE[GROUP_POW_1]) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 7 ****)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (107--113) THEN
    LOCAL_EPADD_TAC 114 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_7 = read(memory :> bytes(word_add stackpointer (word 1376),8 * 4)) s114`;
      `Y_7 = read(memory :> bytes(word_add stackpointer (word 1408),8 * 4)) s114`;
      `Z_7 = read(memory :> bytes(word_add stackpointer (word 1440),8 * 4)) s114`;
      `W_7 = read(memory :> bytes(word_add stackpointer (word 1472),8 * 4)) s114`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 7) (X_7,Y_7,Z_7,W_7)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`group_pow edwards25519_group P 1`;
        `group_pow edwards25519_group P 6`]) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN

    (*** Creation of point multiple 8 ****)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (115--120) THEN
    LOCAL_EPDOUBLE_TAC 121 THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY ABBREV_TAC
     [`X_8 = read(memory :> bytes(word_add stackpointer (word 1504),8 * 4)) s121`;
      `Y_8 = read(memory :> bytes(word_add stackpointer (word 1536),8 * 4)) s121`;
      `Z_8 = read(memory :> bytes(word_add stackpointer (word 1568),8 * 4)) s121`;
      `W_8 = read(memory :> bytes(word_add stackpointer (word 1600),8 * 4)) s121`]
    THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P 8) (X_8,Y_8,Z_8,W_8)`
    MP_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `group_pow edwards25519_group P 4`) THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[GSYM edwards25519] EDWARDS25519_GROUP)] THEN
      ASM_SIMP_TAC[GSYM GROUP_POW_ADD; GROUP_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
      EXISTS_TAC `W_4:num` THEN
      RULE_ASSUM_TAC(SIMP_RULE[GROUP_POW_1]) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN DISCH_TAC] THEN
    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (122--123) THEN

    (*** Top nybble of bscalar ***)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (124--127) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m DIV 2 EXP 252` o MATCH_MP (MESON[]
     `read X20 s = x ==> !m. x = word m ==> read X20 s = word m`)) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[word_ushr];
      DISCH_TAC] THEN

    (*** Address the precomputed table separately ***)

    FIRST_ASSUM(MP_TAC o
      MATCH_MP EDWARDS25519DOUBLEBASE_TABLE_LEMMA) THEN
    REWRITE_TAC[ARITH_RULE `pc + 0x56a0 + x = (pc + 0x56a0) + x`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD] THEN
    ABBREV_TAC `wpc:int64 = word(pc + 0x56a0)` THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
    BIGNUM_LDIGITIZE_TAC "tab_" `read(memory :> bytes(wpc,8 * 96)) s127` THEN
    CLARIFY_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping_modulo (2 EXP 64) (val(stackpointer:int64),1632)
                                       (val(wpc:int64),768)`
    ASSUME_TAC THENL [EXPAND_TAC "wpc" THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

    (*** Constant-time indexing into the precomputed table ***)

    ABBREV_TAC `ix = m DIV 2 EXP 252` THEN
    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (128--304) THEN
    MAP_EVERY ABBREV_TAC
     [`XPY = read(memory :> bytes(word_add stackpointer (word 256),8 * 4)) s304`;
      `YMX = read(memory :> bytes(word_add stackpointer (word 288),8 * 4)) s304`;
      `KXY = read(memory :> bytes(word_add stackpointer (word 320),8 * 4)) s304`]
    THEN
    SUBGOAL_THEN
     `edwards25519_epprojective (group_pow edwards25519_group E_25519 ix)
                                (XPY,YMX,KXY)`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["XPY"; "YMX"; "KXY"] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 < 9` MP_TAC THENL
       [UNDISCH_TAC `m < 9 * 2 EXP 252` THEN ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      SPEC_TAC(`ix:num`,`ix:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
      REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_epprojective;
                  edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[d_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV;
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o
        check(free_in `word_add (wpc:int64)` o concl))) THEN
      UNDISCH_THEN `m DIV 2 EXP 252 = ix` (SUBST_ALL_TAC o SYM) THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read c s = if x then y else z`] THEN
      CLARIFY_TAC] THEN

    (*** Top nybble of scalar ***)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (305--307) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 2 EXP 252` o MATCH_MP (MESON[]
     `read X20 s = x ==> !m. x = word m ==> read X20 s = word m`)) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[word_ushr];
      DISCH_TAC] THEN

    (*** Constant-time indexing in the fresh-point table ***)

    ABBREV_TAC `iy = n DIV 2 EXP 252` THEN
    BIGNUM_LDIGITIZE_TAC "fab_"
     `read(memory :> bytes(word_add stackpointer (word 608),8 * 128)) s307` THEN
    CLARIFY_TAC THEN
    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (308--538) THEN
    MAP_EVERY ABBREV_TAC
     [`Xt = read(memory :> bytes(word_add stackpointer (word 480),8 * 4)) s538`;
      `Yt = read(memory :> bytes(word_add stackpointer (word 512),8 * 4)) s538`;
      `Zt = read(memory :> bytes(word_add stackpointer (word 544),8 * 4)) s538`;
      `Wt = read(memory :> bytes(word_add stackpointer (word 576),8 * 4)) s538`]
    THEN
    SUBGOAL_THEN
     `!P. P IN group_carrier edwards25519_group /\
          paired (modular_decode (256,p_25519)) (x,y) = P
          ==> edwards25519_exprojective2
               (group_pow edwards25519_group P iy) (Xt,Yt,Zt,Wt)`
    ASSUME_TAC THENL
     [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`)) THEN
      ASM_REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["Xt";"Yt";"Zt";"Wt"] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `n DIV 2 EXP 252 < 9` MP_TAC THENL
       [UNDISCH_TAC `n < 9 * 2 EXP 252` THEN ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      SPEC_TAC(`iy:num`,`iy:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
        REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_exprojective2;
         edwards25519_exprojective; edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
        SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
        REWRITE_TAC[bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES;
                    IN_INTEGER_MOD_RING_CARRIER;
                    GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[d_25519; p_25519] THEN
        CONV_TAC INT_REDUCE_CONV;
        FIRST_X_ASSUM(MP_TAC o check (is_conj o concl))] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[];
      UNDISCH_THEN `n DIV 2 EXP 252 = iy` (SUBST_ALL_TAC o SYM) THEN
      DISCARD_MATCHING_ASSUMPTIONS [`read c s = if x then y else z`]] THEN

    (*** The table entry addition ***)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (539--543) THEN
    LOCAL_PEPADD_TAC 544 THEN
    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (545--546) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    (*** Final proof of the invariant ***)

    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[] THEN X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`group_pow edwards25519_group P (n DIV 2 EXP 252)`;
      `group_pow edwards25519_group E_25519 (m DIV 2 EXP 252)`]) THEN
    ASM_SIMP_TAC[GENERATOR_IN_GROUP_CARRIER_EDWARDS25519; GROUP_POW] THEN
    ASM_SIMP_TAC[EDWARDS25519_EXPROJECTIVE2_IMP_EXPROJECTIVE2W;
                 EDWARDS25519_EPPROJECTIVE_IMP_EPPROJECTIVEW] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    EXPAND_TAC "recoder" THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INT_SUB_RZERO; GROUP_NPOW] THEN
    REWRITE_TAC[EDWARDS25519_GROUP; edwards25519] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `P:int#int`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`)) THEN
    ASM_REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[];

    (*** Defer the main invariant proof to below ***)

    ALL_TAC;

    (*** The trivial loop-back subgoal ***)

    REPEAT STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ARM_SIM_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC [1] THEN
    VAL_INT64_TAC `4 * i` THEN
    ASM_REWRITE_TAC[ARITH_RULE `4 * i = 0 <=> ~(0 < i)`];

    (*** The finale with the modular inverse ***)

    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    REWRITE_TAC[bignum_quadruple_from_memory] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN

    (*** Ghost up the still-relevant parts of the state ***)

    FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[]
     `(!x. P x ==> Q x /\ R x) ==> (!x. P x ==> R x)`)) THEN
    MAP_EVERY ABBREV_TAC
     [`X = read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s0`;
      `Y = read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s0`;
      `Z = read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s0`;
      `W = read(memory :> bytes(word_add stackpointer (word 448),8 * 4)) s0`]
    THEN DISCH_TAC THEN

    (*** Call the modular inverse ***)

    ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--3) THEN
    LOCAL_MODINV_TAC 4 THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP(MESON[PRIME_COPRIME_EQ; PRIME_P25519]
     `(bnx = if p_25519 divides n then 0 else inverse_mod p_25519 n)
      ==> coprime(p_25519,n) ==> bnx = inverse_mod p_25519 n`)) THEN
    ABBREV_TAC
     `Z' =
      read(memory :> bytes(word_add stackpointer (word 480),8 * 4)) s4` THEN

    (*** Final multiplications ***)

    LOCAL_MUL_P25519_TAC 3 ["x_0"; "x_1"; "x_2"] THEN
    LOCAL_MUL_P25519_TAC 3 ["x_0"; "x_1"; "x_2"] THEN

    (*** Finishing mathematics ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`) THEN
    ASM_REWRITE_TAC[edwards25519_exprojective2] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SPEC_TAC
     (`group_mul edwards25519_group
        (group_zpow edwards25519_group P (&n - &recoder))
        (group_zpow edwards25519_group E_25519 (&m - &recoder))`,
      `Q:int#int`) THEN
    REWRITE_TAC[edwards25519_exprojective; edwards25519_exprojective] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
    SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REWRITE_TAC[paired; modular_encode; PAIR_EQ; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC[p_25519; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS_EQ; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM p_25519; GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ_0; INT_REM_EQ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `Z' < p_25519 /\ (Z * Z' == 1) (mod p_25519)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN MATCH_MP_TAC(TAUT
        `p /\ (q ==> r) /\ (p /\ q ==> s) ==> (p ==> q) ==> r /\ s`) THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519; num_divides];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INVERSE_MOD_BOUND] THEN
        REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
        MESON_TAC[INVERSE_MOD_RMUL]];
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; num_congruent]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(x * z:int == X) (mod p) /\ (y * z == Y) (mod p)
      ==> (z * z' == &1) (mod p)
          ==> (X * z' == x) (mod p) /\ (Y * z' == y) (mod p)`) THEN
    ASM_REWRITE_TAC[]] THEN

  (*** The preservation of the loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [MESON[] `(!x. P x ==> Q x /\ R x) <=>
             (!x. P x ==> Q x) /\ (!x. P x ==> R x)`] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [bignum_quadruple_from_memory] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  GHOST_INTRO_TAC `Xa:num`
   `bignum_from_memory (word_add stackpointer (word 352),4)` THEN
  GHOST_INTRO_TAC `Ya:num`
   `bignum_from_memory (word_add stackpointer (word 384),4)` THEN
  GHOST_INTRO_TAC `Za:num`
   `bignum_from_memory (word_add stackpointer (word 416),4)` THEN
  GHOST_INTRO_TAC `Wa:num`
   `bignum_from_memory(word_add stackpointer (word 448),4)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  (*** Doubling to acc' = 2 * acc ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (4 * (i + 1))) (word 4) = word(4 * i)`]) THEN
  LOCAL_PDOUBLE_TAC 6 THEN MAP_EVERY ABBREV_TAC
   [`X2a = read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s6`;
    `Y2a = read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s6`;
    `Z2a = read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s6`
   ] THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (7--8) THEN

  (*** Selection of btable nybble ***)

  SUBGOAL_THEN
   `read(memory :> bytes64 (word_add stackpointer
         (word(224 + 8 * val(word_ushr (word (4 * i)) 6:int64))))) s8 =
    word(m DIV 2 EXP (64 * (4 * i) DIV 64) MOD 2 EXP (64 * 1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `i < 63 ==> MIN (4 - (4 * i) DIV 64) 1 = 1`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_THM_TAC THEN REPLICATE_TAC 7 AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Recoding offset to get indexing and negation flag ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (9--17) THEN
  ABBREV_TAC `bf = (m DIV (2 EXP (4 * i))) MOD 16` THEN
  SUBGOAL_THEN
   `word_and
     (word_jushr
      (word ((m DIV 2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP 64))
     (word (4 * i)))
    (word 15):int64 = word bf` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD;
                ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
    REWRITE_TAC[word_jushr; VAL_WORD_USHR; DIMINDEX_64; MOD_64_CLAUSES] THEN
    EXPAND_TAC "bf" THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `16 = 2 EXP 4`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
    REWRITE_TAC[DIV_MOD; MOD_MOD_EXP_MIN; GSYM EXP_ADD; DIV_DIV] THEN
    REWRITE_TAC[ADD_ASSOC; ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
    AP_THM_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    REWRITE_TAC[ARITH_RULE
     `x <= 64 * y DIV 64 + z <=> x + y MOD 64 <= y + z`] THEN
    REWRITE_TAC[ARITH_RULE `64 = 4 * 16`; MOD_MULT2] THEN
    UNDISCH_TAC `i < 63` THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  SUBGOAL_THEN `val(word bf:int64) = bf` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "bf" THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ix = if bf < 8 then 8 - bf else bf - 8` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word ix:int64` o MATCH_MP (MESON[]
   `read X20 s = x ==> !x'. x = x' ==> read X20 s = x'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "ix" THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
    REWRITE_TAC[WORD_NEG_SUB] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN

  (*** Address the precomputed table separately ***)

  FIRST_ASSUM(MP_TAC o
    MATCH_MP EDWARDS25519DOUBLEBASE_TABLE_LEMMA) THEN
  REWRITE_TAC[ARITH_RULE `pc + 0x56a0 + x = (pc + 0x56a0) + x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD] THEN
  ABBREV_TAC `wpc:int64 = word(pc + 0x56a0)` THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
  BIGNUM_LDIGITIZE_TAC "tab_" `read(memory :> bytes(wpc,8 * 96)) s17` THEN
  CLARIFY_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val(stackpointer:int64),1632)
                                     (val(wpc:int64),768)`
  ASSUME_TAC THENL [EXPAND_TAC "wpc" THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  (*** Constant-time indexing into the precomputed table ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (18--188) THEN
  MAP_EVERY REABBREV_TAC
   [`tab0 = read X0 s188`;
    `tab1 = read X1 s188`;
    `tab2 = read X2 s188`;
    `tab3 = read X3 s188`;
    `tab4 = read X4 s188`;
    `tab5 = read X5 s188`;
    `tab6 = read X6 s188`;
    `tab7 = read X7 s188`;
    `tab8 = read X8 s188`;
    `tab9 = read X9 s188`;
    `tab10 = read X10 s188`;
    `tab11 = read X11 s188`] THEN
  SUBGOAL_THEN
   `edwards25519_epprojective (group_pow edwards25519_group E_25519 ix)
     (bignum_of_wordlist[tab0; tab1; tab2; tab3],
      bignum_of_wordlist[tab4; tab5; tab6; tab7],
      bignum_of_wordlist[tab8; tab9; tab10; tab11])`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC
     (map (fun n -> "tab"^string_of_int n) (0--11)) THEN
    SUBGOAL_THEN `ix < 9` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ix"; "bf"] THEN ARITH_TAC;
      SPEC_TAC(`ix:num`,`ix:num`)] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
    REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_epprojective;
                edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM INT_OF_NUM_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[d_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o
        check(free_in `word_add (wpc:int64)` o concl))) THEN
    CLARIFY_TAC] THEN

  (*** Optional negation of the table entry ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (204--207) (189--213) THEN
  MAP_EVERY ABBREV_TAC
   [`XPY = read(memory :> bytes(word_add stackpointer (word 256),8 * 4)) s213`;
    `YMX = read(memory :> bytes(word_add stackpointer (word 288),8 * 4)) s213`;
    `KXY = read(memory :> bytes(word_add stackpointer (word 320),8 * 4)) s213`]
  THEN
  SUBGOAL_THEN
   `edwards25519_epprojectivew
     (group_zpow edwards25519_group E_25519 (&bf - &8)) (XPY,YMX,KXY)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["XPY"; "YMX"; "KXY"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&bf - &8:int = if bf < 8 then --(&ix) else &ix`
    SUBST1_TAC THENL
     [EXPAND_TAC "ix" THEN
      SUBGOAL_THEN `bf < 16` MP_TAC THENL
       [EXPAND_TAC "bf" THEN ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM NOT_LT] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GROUP_ZPOW_POW] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP
        EDWARDS25519_EPPROJECTIVE_IMP_EPPROJECTIVEW)
    THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
       EDWARDS25519_EPPROJECTIVEW_NEG);
      MATCH_MP_TAC EQ_IMP THEN REPLICATE_TAC 3 AP_TERM_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THENL
     [REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64];
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC] THEN
    DISCH_THEN(MAP_EVERY ASSUME_TAC o rev o CONJUNCTS) THEN
    REWRITE_TAC[num_divides; GSYM INT_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(INTEGER_RULE `y:int = &2 * p - x ==> p divides (x + y)`) THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `(&0:int <= x /\ x < p) /\ (&0 <= y /\ y < p) ==> abs(x - y) < p`) THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_25519] THEN INT_ARITH_TAC] THEN
      REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP EDWARDS25519_EPPROJECTIVE_BOUND) THEN
      ARITH_TAC;
      REWRITE_TAC[REAL_INT_CONGRUENCE; GSYM REAL_OF_INT_CLAUSES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `ix:num` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (free_in `edwards25519_epprojective` o concl))) THEN
    CLARIFY_TAC] THEN

  (*** Selection of fresh table nybble ***)

  SUBGOAL_THEN
   `read(memory :> bytes64 (word_add stackpointer
         (word(192 + 8 * val(word_ushr (word (4 * i)) 6:int64))))) s213 =
    word(n DIV 2 EXP (64 * (4 * i) DIV 64) MOD 2 EXP (64 * 1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `i < 63 ==> MIN (4 - (4 * i) DIV 64) 1 = 1`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_THM_TAC THEN REPLICATE_TAC 7 AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Recoding offset to get indexing and negation flag ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (214--221) THEN
  ABBREV_TAC `cf = (n DIV (2 EXP (4 * i))) MOD 16` THEN
  SUBGOAL_THEN
   `word_and
     (word_jushr
      (word ((n DIV 2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP 64))
     (word (4 * i)))
    (word 15):int64 = word cf` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD;
                ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
    REWRITE_TAC[word_jushr; VAL_WORD_USHR; DIMINDEX_64; MOD_64_CLAUSES] THEN
    EXPAND_TAC "cf" THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `16 = 2 EXP 4`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
    REWRITE_TAC[DIV_MOD; MOD_MOD_EXP_MIN; GSYM EXP_ADD; DIV_DIV] THEN
    REWRITE_TAC[ADD_ASSOC; ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
    AP_THM_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    REWRITE_TAC[ARITH_RULE
     `x <= 64 * y DIV 64 + z <=> x + y MOD 64 <= y + z`] THEN
    REWRITE_TAC[ARITH_RULE `64 = 4 * 16`; MOD_MULT2] THEN
    UNDISCH_TAC `i < 63` THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LE]) THEN
  SUBGOAL_THEN `val(word cf:int64) = cf` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "cf" THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `iy = if cf < 8 then 8 - cf else cf - 8` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word iy:int64` o MATCH_MP (MESON[]
   `read X20 s = x ==> !x'. x = x' ==> read X20 s = x'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "iy" THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
    REWRITE_TAC[WORD_NEG_SUB] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN

  (*** Constant-time indexing in the fresh-point table ***)

  BIGNUM_LDIGITIZE_TAC "fab_"
   `read(memory :> bytes(word_add stackpointer (word 608),8 * 128)) s221` THEN
  CLARIFY_TAC THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (222--444) THEN
  MAP_EVERY REABBREV_TAC
   [`fab0 = read X0 s444`;
    `fab1 = read X1 s444`;
    `fab2 = read X2 s444`;
    `fab3 = read X3 s444`;
    `fab4 = read X4 s444`;
    `fab5 = read X5 s444`;
    `fab6 = read X6 s444`;
    `fab7 = read X7 s444`;
    `fab8 = read X8 s444`;
    `fab9 = read X9 s444`;
    `fab10 = read X10 s444`;
    `fab11 = read X11 s444`;
    `fab12 = read X12 s444`;
    `fab13 = read X13 s444`;
    `fab14 = read X14 s444`;
    `fab15 = read X15 s444`] THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier edwards25519_group /\
        paired (modular_decode (256,p_25519)) (x,y) = P
        ==> edwards25519_exprojective2
             (group_pow edwards25519_group P iy)
             (bignum_of_wordlist[fab0; fab1; fab2; fab3],
              bignum_of_wordlist[fab4; fab5; fab6; fab7],
              bignum_of_wordlist[fab8; fab9; fab10; fab11],
              bignum_of_wordlist[fab12; fab13; fab14; fab15])`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC
     (map (fun n -> "fab"^string_of_int n) (0--15)) THEN
    SUBGOAL_THEN `iy < 9` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["iy"; "cf"] THEN ARITH_TAC;
      SPEC_TAC(`iy:num`,`iy:num`)] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[CONJUNCT1 group_pow] THEN
    REWRITE_TAC[EDWARDS25519_GROUP; edwards25519_exprojective2;
     edwards25519_exprojective; edwards_0; INTEGER_MOD_RING_CLAUSES] THEN
    SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REWRITE_TAC[bignum_of_wordlist; INTEGER_MOD_RING_CLAUSES;
                IN_INTEGER_MOD_RING_CARRIER;
                GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[d_25519; p_25519] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Optional negation of the table entry ***)

  ARM_ACCSTEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
    [451;452;453;454;459;460;461;462] (445--470) THEN
  MAP_EVERY ABBREV_TAC
   [`Xb = read(memory :> bytes(word_add stackpointer (word 480),8 * 4)) s470`;
    `Yb = read(memory :> bytes(word_add stackpointer (word 512),8 * 4)) s470`;
    `Zb = read(memory :> bytes(word_add stackpointer (word 544),8 * 4)) s470`;
    `Wb = read(memory :> bytes(word_add stackpointer (word 576),8 * 4)) s470`]
  THEN
  SUBGOAL_THEN
   `!P. P IN group_carrier edwards25519_group /\
        paired (modular_decode (256,p_25519)) (x,y) = P
        ==> edwards25519_exprojective2w
              (group_zpow edwards25519_group P (&cf - &8)) (Xb,Yb,Zb,Wb)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `P:int#int`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:int#int`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["Xb"; "Yb"; "Zb"; "Wb"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&cf - &8:int = if cf < 8 then --(&iy) else &iy`
    SUBST1_TAC THENL
     [EXPAND_TAC "iy" THEN
      SUBGOAL_THEN `cf < 16` MP_TAC THENL
       [EXPAND_TAC "cf" THEN ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM NOT_LT] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[GROUP_ZPOW_POW] THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (ONCE_REWRITE_RULE[IMP_CONJ] EDWARDS25519_EXPROJECTIVE2W_NEG)) THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
      REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN REAL_INTEGER_TAC;
      FIRST_ASSUM(MP_TAC o MATCH_MP
        EDWARDS25519_EXPROJECTIVE2_IMP_EXPROJECTIVE2W) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[PAIR_EQ] THEN
      REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
      REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `iy:num` o concl))) THEN
    CLARIFY_TAC] THEN

  (*** Doubling to acc' = 4 * acc ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (471--474) THEN
  LOCAL_PDOUBLE_TAC 475 THEN MAP_EVERY ABBREV_TAC
   [`X4a = read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s475`;
    `Y4a = read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s475`;
    `Z4a = read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s475`
   ] THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (476--477) THEN

  (*** Addition of precomputed and fresh table entries ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (478--482) THEN
  LOCAL_PEPADD_TAC 483 THEN MAP_EVERY ABBREV_TAC
   [`Xc = read(memory :> bytes(word_add stackpointer (word 480),8 * 4)) s483`;
    `Yc = read(memory :> bytes(word_add stackpointer (word 512),8 * 4)) s483`;
    `Zc = read(memory :> bytes(word_add stackpointer (word 544),8 * 4)) s483`;
    `Wc = read(memory :> bytes(word_add stackpointer (word 576),8 * 4)) s483`
   ] THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (484--485) THEN

  (*** Doubling to acc' = 8 * acc ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (486--489) THEN
  LOCAL_PDOUBLE_TAC 490 THEN MAP_EVERY ABBREV_TAC
   [`X8a = read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s490`;
    `Y8a = read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s490`;
    `Z8a = read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s490`
   ] THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (491--492) THEN

  (*** Doubling to acc' = 16 * acc ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (493--496) THEN
  LOCAL_EPDOUBLE_TAC 497 THEN MAP_EVERY ABBREV_TAC
   [`Xha = read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s497`;
    `Yha = read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s497`;
    `Zha = read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s497`;
    `Wha = read(memory :> bytes(word_add stackpointer (word 448),8 * 4)) s497`
   ] THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (498--499) THEN

  (*** The final addition acc' = 16 * acc + tables ***)

  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (500--504) THEN
  LOCAL_EPADD_TAC 505 THEN MAP_EVERY ABBREV_TAC
   [`Xf = read(memory :> bytes(word_add stackpointer (word 352),8 * 4)) s505`;
    `Yf = read(memory :> bytes(word_add stackpointer (word 384),8 * 4)) s505`;
    `Zf = read(memory :> bytes(word_add stackpointer (word 416),8 * 4)) s505`;
    `Wf = read(memory :> bytes(word_add stackpointer (word 448),8 * 4)) s505`
   ] THEN
  ARM_STEPS_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC (506--507) THEN

  (*** The final mathematics of adding the points up ***)

  FIRST_X_ASSUM(MP_TAC o
    check (can (term_match [] `(MAYCHANGE a ,, b) s s'` o concl))) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN MP_TAC th) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bignum_quadruple_from_memory] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ASM_SIMP_TAC[] THEN
  DISCARD_STATE_TAC "s507" THEN
  X_GEN_TAC `P:int#int` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_forall o concl))) THEN
  REWRITE_TAC[REWRITE_RULE[GSYM edwards25519]
   (GSYM(CONJUNCT2 EDWARDS25519_GROUP))] THEN
  SIMP_TAC[GSYM GROUP_POW_2] THEN
  DISCH_THEN(MP_TAC o SPEC `P:int#int`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Q = group_mul edwards25519_group
          (group_zpow edwards25519_group P
            (&(n DIV 2 EXP (4 * (i + 1))) -
             &(recoder DIV 2 EXP (4 * (i + 1)))))
          (group_zpow edwards25519_group E_25519
             (&(m DIV 2 EXP (4 * (i + 1))) -
              &(recoder DIV 2 EXP (4 * (i + 1)))))` THEN
  SUBGOAL_THEN `Q IN group_carrier edwards25519_group` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC GROUP_MUL THEN
    ASM_SIMP_TAC[GROUP_ZPOW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519];
    DISCH_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Q:int#int`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE2_IMP_PROJECTIVE2 THEN
    EXISTS_TAC `Wa:num` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `P:int#int`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `group_pow edwards25519_group (Q:int#int) 2`) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPECL
   [`group_zpow edwards25519_group P (&cf - &8)`;
    `group_zpow edwards25519_group E_25519 (&bf - &8)`]) THEN
  ASM_SIMP_TAC[GROUP_ZPOW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `group_pow edwards25519_group (Q:int#int) 4`) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `group_pow edwards25519_group (Q:int#int) 8`) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPECL
   [`group_pow edwards25519_group Q 16`;
    `group_mul edwards25519_group
       (group_zpow edwards25519_group P (&cf - &8))
       (group_zpow edwards25519_group E_25519 (&bf - &8))`]) THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_ZPOW; GROUP_MUL;
               GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!n. n DIV 2 EXP (4 * i) =
        16 * (n DIV 2 EXP (4 * (i + 1))) + (n DIV 2 EXP (4 * i)) MOD 16`
  MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`; EXP_ADD] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN ARITH_TAC;
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(recoder DIV 2 EXP (4 * i)) MOD 16 = 8` SUBST1_TAC THENL
   [UNDISCH_TAC `i < 63` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    EXPAND_TAC "recoder" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_ARITH
   `(&16 * x + y) - (&16 * z + &8):int =
    (x - z) * &16 + (y - &8)`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM GROUP_NPOW] THEN
  ASM_SIMP_TAC[ABELIAN_GROUP_MUL_ZPOW; ABELIAN_EDWARDS25519_GROUP;
               GENERATOR_IN_GROUP_CARRIER_EDWARDS25519; GROUP_ZPOW;
               GSYM GROUP_ZPOW_MUL; GROUP_ZPOW_ADD] THEN
  ASM_SIMP_TAC[GEN_REWRITE_RULE I [ABELIAN_GROUP_MUL_AC]
        ABELIAN_EDWARDS25519_GROUP; GROUP_MUL; GROUP_ZPOW;
        GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]);;

let EDWARDS25519_SCALARMULDOUBLE_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar point bscalar n xy m pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 1696),1696))
        [(word pc,0x59a0); (res,64); (scalar,32); (point,64); (bscalar,32)] /\
    nonoverlapping (res,64) (word pc,0x59a0)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
               (APPEND edwards25519_scalarmuldouble_alt_mc
                       edwards25519_scalarmuldouble_alt_data) /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [res; scalar; point; bscalar] s /\
              bignum_from_memory (scalar,4) s = n /\
              bignum_pair_from_memory (point,4) s = xy /\
              bignum_from_memory (bscalar,4) s = m)
         (\s. read PC s = returnaddress /\
              !P. P IN group_carrier edwards25519_group /\
                  paired (modular_decode (256,p_25519)) xy = P
                  ==> bignum_pair_from_memory(res,4) s =
                      paired (modular_encode (256,p_25519))
                             (group_mul edwards25519_group
                                 (group_pow edwards25519_group P n)
                                 (group_pow edwards25519_group E_25519 m)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,64);
                    memory :> bytes(word_sub stackpointer (word 1696),1696)])`,
  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
              fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC
   (REWRITE_RULE[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                fst EDWARDS25519_SCALARMULDOUBLE_ALT_EXEC]
    EDWARDS25519_SCALARMULDOUBLE_ALT_CORRECT)
   `[X19; X20; X21; X22; X23; X24; X25; X30]` 1696);;
