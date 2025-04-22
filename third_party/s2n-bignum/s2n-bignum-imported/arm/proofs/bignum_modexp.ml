(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular exponentiation for bignums (with odd modulus).                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_modexp.o";;
 ****)

let bignum_modexp_mc =
  define_assert_from_elf "bignum_modexp_mc" "arm/generic/bignum_modexp.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf9;       (* arm_STP X25 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xb4000740;       (* arm_CBZ X0 (word 232) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0xaa0103f4;       (* arm_MOV X20 X1 *)
  0xaa0203f5;       (* arm_MOV X21 X2 *)
  0xaa0303f6;       (* arm_MOV X22 X3 *)
  0xaa0403f7;       (* arm_MOV X23 X4 *)
  0xaa0503f8;       (* arm_MOV X24 X5 *)
  0xaa1303e0;       (* arm_MOV X0 X19 *)
  0x8b131301;       (* arm_ADD X1 X24 (Shiftedreg X19 LSL 4) *)
  0xaa1703e2;       (* arm_MOV X2 X23 *)
  0x8b130f03;       (* arm_ADD X3 X24 (Shiftedreg X19 LSL 3) *)
  0x94000034;       (* arm_BL (word 208) *)
  0xaa1303e0;       (* arm_MOV X0 X19 *)
  0xaa1803e1;       (* arm_MOV X1 X24 *)
  0x8b131302;       (* arm_ADD X2 X24 (Shiftedreg X19 LSL 4) *)
  0xaa1503e3;       (* arm_MOV X3 X21 *)
  0xaa1703e4;       (* arm_MOV X4 X23 *)
  0x940000f5;       (* arm_BL (word 980) *)
  0xaa1303e0;       (* arm_MOV X0 X19 *)
  0x8b131301;       (* arm_ADD X1 X24 (Shiftedreg X19 LSL 4) *)
  0x8b131302;       (* arm_ADD X2 X24 (Shiftedreg X19 LSL 4) *)
  0xaa1703e3;       (* arm_MOV X3 X23 *)
  0x9400013c;       (* arm_BL (word 1264) *)
  0xd37ae679;       (* arm_LSL X25 X19 6 *)
  0xd1000739;       (* arm_SUB X25 X25 (rvalue (word 1)) *)
  0xaa1303e0;       (* arm_MOV X0 X19 *)
  0x8b130f01;       (* arm_ADD X1 X24 (Shiftedreg X19 LSL 3) *)
  0x8b131302;       (* arm_ADD X2 X24 (Shiftedreg X19 LSL 4) *)
  0x8b131303;       (* arm_ADD X3 X24 (Shiftedreg X19 LSL 4) *)
  0xaa1703e4;       (* arm_MOV X4 X23 *)
  0x940000e8;       (* arm_BL (word 928) *)
  0xaa1303e0;       (* arm_MOV X0 X19 *)
  0x8b131301;       (* arm_ADD X1 X24 (Shiftedreg X19 LSL 4) *)
  0xaa1803e2;       (* arm_MOV X2 X24 *)
  0x8b130f03;       (* arm_ADD X3 X24 (Shiftedreg X19 LSL 3) *)
  0xaa1703e4;       (* arm_MOV X4 X23 *)
  0x940000e2;       (* arm_BL (word 904) *)
  0xd346ff20;       (* arm_LSR X0 X25 6 *)
  0xf8607ac0;       (* arm_LDR X0 X22 (Shiftreg_Offset X0 3) *)
  0x9ad92400;       (* arm_LSRV X0 X0 X25 *)
  0x92400000;       (* arm_AND X0 X0 (rvalue (word 1)) *)
  0xaa1303e1;       (* arm_MOV X1 X19 *)
  0x8b131302;       (* arm_ADD X2 X24 (Shiftedreg X19 LSL 4) *)
  0x8b131303;       (* arm_ADD X3 X24 (Shiftedreg X19 LSL 4) *)
  0x8b130f04;       (* arm_ADD X4 X24 (Shiftedreg X19 LSL 3) *)
  0x94000167;       (* arm_BL (word 1436) *)
  0xb5fffd59;       (* arm_CBNZ X25 (word 2097064) *)
  0xaa1303e0;       (* arm_MOV X0 X19 *)
  0x8b131301;       (* arm_ADD X1 X24 (Shiftedreg X19 LSL 4) *)
  0x8b131302;       (* arm_ADD X2 X24 (Shiftedreg X19 LSL 4) *)
  0xaa1703e3;       (* arm_MOV X3 X23 *)
  0x9400011f;       (* arm_BL (word 1148) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xaa1303e1;       (* arm_MOV X1 X19 *)
  0xaa1403e2;       (* arm_MOV X2 X20 *)
  0x8b131303;       (* arm_ADD X3 X24 (Shiftedreg X19 LSL 4) *)
  0x8b131304;       (* arm_ADD X4 X24 (Shiftedreg X19 LSL 4) *)
  0x9400015b;       (* arm_BL (word 1388) *)
  0xa8c17bf9;       (* arm_LDP X25 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xb40018c0;       (* arm_CBZ X0 (word 792) *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xf8647849;       (* arm_LDR X9 X2 (Shiftreg_Offset X4 3) *)
  0xf8247869;       (* arm_STR X9 X3 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xf1000404;       (* arm_SUBS X4 X0 (rvalue (word 1)) *)
  0x540001a0;       (* arm_BEQ (word 52) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xeb1f013f;       (* arm_CMP X9 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa0703e9;       (* arm_MOV X9 X7 *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0x9a870129;       (* arm_CSEL X9 X9 X7 Condition_EQ *)
  0xf8257869;       (* arm_STR X9 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000ab;       (* arm_SUB X11 X5 X0 *)
  0xb5ffff4b;       (* arm_CBNZ X11 (word 2097128) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffea1;       (* arm_BNE (word 2097108) *)
  0xdac01129;       (* arm_CLZ X9 X9 *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xf240153f;       (* arm_TST X9 (rvalue (word 63)) *)
  0xda9f03e8;       (* arm_CSETM X8 Condition_NE *)
  0xcb0903eb;       (* arm_NEG X11 X9 *)
  0xf8647865;       (* arm_LDR X5 X3 (Shiftreg_Offset X4 3) *)
  0x9ac920a7;       (* arm_LSLV X7 X5 X9 *)
  0xaa0a00e7;       (* arm_ORR X7 X7 X10 *)
  0x9acb24aa;       (* arm_LSRV X10 X5 X11 *)
  0x8a08014a;       (* arm_AND X10 X10 X8 *)
  0xf8247867;       (* arm_STR X7 X3 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffff03;       (* arm_BCC (word 2097120) *)
  0xd1000406;       (* arm_SUB X6 X0 (rvalue (word 1)) *)
  0xf8667866;       (* arm_LDR X6 X3 (Shiftreg_Offset X6 3) *)
  0xd280002b;       (* arm_MOV X11 (rvalue (word 1)) *)
  0xcb0603ea;       (* arm_NEG X10 X6 *)
  0xd28007c4;       (* arm_MOV X4 (rvalue (word 62)) *)
  0x8b0b016b;       (* arm_ADD X11 X11 X11 *)
  0xaa0603e7;       (* arm_MOV X7 X6 *)
  0xcb0a00e7;       (* arm_SUB X7 X7 X10 *)
  0xeb07015f;       (* arm_CMP X10 X7 *)
  0xda9f33e7;       (* arm_CSETM X7 Condition_CS *)
  0xcb07016b;       (* arm_SUB X11 X11 X7 *)
  0x8b0a014a;       (* arm_ADD X10 X10 X10 *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xcb07014a;       (* arm_SUB X10 X10 X7 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffec1;       (* arm_BNE (word 2097112) *)
  0xeb06015f;       (* arm_CMP X10 X6 *)
  0x9a8b156b;       (* arm_CINC X11 X11 Condition_EQ *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xab1f03e4;       (* arm_ADDS X4 XZR XZR *)
  0xf8647867;       (* arm_LDR X7 X3 (Shiftreg_Offset X4 3) *)
  0x9b077d68;       (* arm_MUL X8 X11 X7 *)
  0xba090108;       (* arm_ADCS X8 X8 X9 *)
  0x9bc77d69;       (* arm_UMULH X9 X11 X7 *)
  0xf8247828;       (* arm_STR X8 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xcb000087;       (* arm_SUB X7 X4 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd2e80007;       (* arm_MOVZ X7 (word 16384) 48 *)
  0xeb070129;       (* arm_SUBS X9 X9 X7 *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0xeb1f03e4;       (* arm_NEGS X4 XZR *)
  0xf8647867;       (* arm_LDR X7 X3 (Shiftreg_Offset X4 3) *)
  0xf864782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X4 3) *)
  0x8a0b00e7;       (* arm_AND X7 X7 X11 *)
  0xfa0a00e7;       (* arm_SBCS X7 X7 X10 *)
  0xf8247827;       (* arm_STR X7 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xcb000087;       (* arm_SUB X7 X4 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0x93c9fce9;       (* arm_EXTR X9 X7 X9 63 *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0xfa0a0129;       (* arm_SBCS X9 X9 X10 *)
  0xf8257829;       (* arm_STR X9 X1 (Shiftreg_Offset X5 3) *)
  0xaa0703e9;       (* arm_MOV X9 X7 *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff07;       (* arm_CBNZ X7 (word 2097120) *)
  0xd37ffd29;       (* arm_LSR X9 X9 63 *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0x8a09014a;       (* arm_AND X10 X10 X9 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xf8257827;       (* arm_STR X7 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0x93c9fce9;       (* arm_EXTR X9 X7 X9 63 *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0xfa0a0129;       (* arm_SBCS X9 X9 X10 *)
  0xf8257829;       (* arm_STR X9 X1 (Shiftreg_Offset X5 3) *)
  0xaa0703e9;       (* arm_MOV X9 X7 *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff07;       (* arm_CBNZ X7 (word 2097120) *)
  0xd37ffd29;       (* arm_LSR X9 X9 63 *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0x8a09014a;       (* arm_AND X10 X10 X9 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xf8257827;       (* arm_STR X7 X1 (Shiftreg_Offset X5 3) *)
  0xf8257867;       (* arm_STR X7 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff07;       (* arm_CBNZ X7 (word 2097120) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa0003e4;       (* arm_MOV X4 X0 *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xab1f03e9;       (* arm_ADDS X9 XZR XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0x9b077cc8;       (* arm_MUL X8 X6 X7 *)
  0xba09014a;       (* arm_ADCS X10 X10 X9 *)
  0x9bc77cc9;       (* arm_UMULH X9 X6 X7 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab080148;       (* arm_ADDS X8 X10 X8 *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0xf8257868;       (* arm_STR X8 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5fffec7;       (* arm_CBNZ X7 (word 2097112) *)
  0xba090146;       (* arm_ADCS X6 X10 X9 *)
  0xda9f33e8;       (* arm_CSETM X8 Condition_CS *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0xf865782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X5 3) *)
  0x8a08014a;       (* arm_AND X10 X10 X8 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xf8257867;       (* arm_STR X7 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffca1;       (* arm_BNE (word 2097044) *)
  0xf9400047;       (* arm_LDR X7 X2 (Immediate_Offset (word 0)) *)
  0xd37ef4eb;       (* arm_LSL X11 X7 2 *)
  0xcb0b00eb;       (* arm_SUB X11 X7 X11 *)
  0xd27f016b;       (* arm_EOR X11 X11 (rvalue (word 2)) *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0x9b0b20e9;       (* arm_MADD X9 X7 X11 X8 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0x9b0b2d2b;       (* arm_MADD X11 X9 X11 X11 *)
  0x9b0a7d49;       (* arm_MUL X9 X10 X10 *)
  0x9b0b2d4b;       (* arm_MADD X11 X10 X11 X11 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0x9b0b2d2b;       (* arm_MADD X11 X9 X11 X11 *)
  0x9b0b2d4b;       (* arm_MADD X11 X10 X11 X11 *)
  0xf940006a;       (* arm_LDR X10 X3 (Immediate_Offset (word 0)) *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b077d68;       (* arm_MUL X8 X11 X7 *)
  0x9bc77d69;       (* arm_UMULH X9 X11 X7 *)
  0xd2800025;       (* arm_MOV X5 (rvalue (word 1)) *)
  0xd1000407;       (* arm_SUB X7 X0 (rvalue (word 1)) *)
  0xab08015f;       (* arm_CMN X10 X8 *)
  0xb40001a7;       (* arm_CBZ X7 (word 52) *)
  0xf8657847;       (* arm_LDR X7 X2 (Shiftreg_Offset X5 3) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0x9b077d68;       (* arm_MUL X8 X11 X7 *)
  0xba09014a;       (* arm_ADCS X10 X10 X9 *)
  0x9bc77d69;       (* arm_UMULH X9 X11 X7 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xd10004a7;       (* arm_SUB X7 X5 (rvalue (word 1)) *)
  0xf827786a;       (* arm_STR X10 X3 (Shiftreg_Offset X7 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5fffea7;       (* arm_CBNZ X7 (word 2097108) *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0xda9f33e8;       (* arm_CSETM X8 Condition_CS *)
  0xd1000407;       (* arm_SUB X7 X0 (rvalue (word 1)) *)
  0xf8277866;       (* arm_STR X6 X3 (Shiftreg_Offset X7 3) *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0xf865784a;       (* arm_LDR X10 X2 (Shiftreg_Offset X5 3) *)
  0x8a08014a;       (* arm_AND X10 X10 X8 *)
  0xfa0a00e7;       (* arm_SBCS X7 X7 X10 *)
  0xf8257827;       (* arm_STR X7 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xb4000960;       (* arm_CBZ X0 (word 300) *)
  0xf940008e;       (* arm_LDR X14 X4 (Immediate_Offset (word 0)) *)
  0xd37ef5c5;       (* arm_LSL X5 X14 2 *)
  0xcb0501c5;       (* arm_SUB X5 X14 X5 *)
  0xd27f00a5;       (* arm_EOR X5 X5 (rvalue (word 2)) *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0x9b0519c6;       (* arm_MADD X6 X14 X5 X6 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b0514c5;       (* arm_MADD X5 X6 X5 X5 *)
  0x9b077ce6;       (* arm_MUL X6 X7 X7 *)
  0x9b0514e5;       (* arm_MADD X5 X7 X5 X5 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b0514c5;       (* arm_MADD X5 X6 X5 X5 *)
  0x9b0514e5;       (* arm_MADD X5 X7 X5 X5 *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xf828783f;       (* arm_STR XZR X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xf8687849;       (* arm_LDR X9 X2 (Shiftreg_Offset X8 3) *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xab1f03eb;       (* arm_ADDS X11 XZR XZR *)
  0xf86a786e;       (* arm_LDR X14 X3 (Shiftreg_Offset X10 3) *)
  0xf86a782c;       (* arm_LDR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9b0e7d2d;       (* arm_MUL X13 X9 X14 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9bce7d2b;       (* arm_UMULH X11 X9 X14 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0d018c;       (* arm_ADDS X12 X12 X13 *)
  0xf82a782c;       (* arm_STR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014e;       (* arm_SUB X14 X10 X0 *)
  0xb5fffece;       (* arm_CBNZ X14 (word 2097112) *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0xf940002c;       (* arm_LDR X12 X1 (Immediate_Offset (word 0)) *)
  0x9b057d89;       (* arm_MUL X9 X12 X5 *)
  0xf940008e;       (* arm_LDR X14 X4 (Immediate_Offset (word 0)) *)
  0x9b0e7d2d;       (* arm_MUL X13 X9 X14 *)
  0x9bce7d2b;       (* arm_UMULH X11 X9 X14 *)
  0xab0d018c;       (* arm_ADDS X12 X12 X13 *)
  0xd280002a;       (* arm_MOV X10 (rvalue (word 1)) *)
  0xd100040e;       (* arm_SUB X14 X0 (rvalue (word 1)) *)
  0xb40001ae;       (* arm_CBZ X14 (word 52) *)
  0xf86a788e;       (* arm_LDR X14 X4 (Shiftreg_Offset X10 3) *)
  0xf86a782c;       (* arm_LDR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9b0e7d2d;       (* arm_MUL X13 X9 X14 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9bce7d2b;       (* arm_UMULH X11 X9 X14 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0d018c;       (* arm_ADDS X12 X12 X13 *)
  0xd100054d;       (* arm_SUB X13 X10 (rvalue (word 1)) *)
  0xf82d782c;       (* arm_STR X12 X1 (Shiftreg_Offset X13 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014e;       (* arm_SUB X14 X10 X0 *)
  0xb5fffeae;       (* arm_CBNZ X14 (word 2097108) *)
  0xba0b00cb;       (* arm_ADCS X11 X6 X11 *)
  0x9a1f00e6;       (* arm_ADC X6 X7 XZR *)
  0xd100054d;       (* arm_SUB X13 X10 (rvalue (word 1)) *)
  0xf82d782b;       (* arm_STR X11 X1 (Shiftreg_Offset X13 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54fffaa3;       (* arm_BCC (word 2096980) *)
  0xcb0603e6;       (* arm_NEG X6 X6 *)
  0xeb1f03ea;       (* arm_NEGS X10 XZR *)
  0xf86a782e;       (* arm_LDR X14 X1 (Shiftreg_Offset X10 3) *)
  0xf86a788c;       (* arm_LDR X12 X4 (Shiftreg_Offset X10 3) *)
  0x8a06018c;       (* arm_AND X12 X12 X6 *)
  0xfa0c01ce;       (* arm_SBCS X14 X14 X12 *)
  0xf82a782e;       (* arm_STR X14 X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014e;       (* arm_SUB X14 X10 X0 *)
  0xb5ffff2e;       (* arm_CBNZ X14 (word 2097124) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xb4000820;       (* arm_CBZ X0 (word 260) *)
  0xf940006b;       (* arm_LDR X11 X3 (Immediate_Offset (word 0)) *)
  0xd37ef564;       (* arm_LSL X4 X11 2 *)
  0xcb040164;       (* arm_SUB X4 X11 X4 *)
  0xd27f0084;       (* arm_EOR X4 X4 (rvalue (word 2)) *)
  0xd2800025;       (* arm_MOV X5 (rvalue (word 1)) *)
  0x9b041565;       (* arm_MADD X5 X11 X4 X5 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0x9b0410a4;       (* arm_MADD X4 X5 X4 X4 *)
  0x9b067cc5;       (* arm_MUL X5 X6 X6 *)
  0x9b0410c4;       (* arm_MADD X4 X6 X4 X4 *)
  0x9b057ca6;       (* arm_MUL X6 X5 X5 *)
  0x9b0410a4;       (* arm_MADD X4 X5 X4 X4 *)
  0x9b0410c4;       (* arm_MADD X4 X6 X4 X4 *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xf865784b;       (* arm_LDR X11 X2 (Shiftreg_Offset X5 3) *)
  0xf825782b;       (* arm_STR X11 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xeb0000bf;       (* arm_CMP X5 X0 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xf9400029;       (* arm_LDR X9 X1 (Immediate_Offset (word 0)) *)
  0x9b047d27;       (* arm_MUL X7 X9 X4 *)
  0xf940006b;       (* arm_LDR X11 X3 (Immediate_Offset (word 0)) *)
  0x9b0b7cea;       (* arm_MUL X10 X7 X11 *)
  0x9bcb7ce8;       (* arm_UMULH X8 X7 X11 *)
  0xab0a0129;       (* arm_ADDS X9 X9 X10 *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0xd100040b;       (* arm_SUB X11 X0 (rvalue (word 1)) *)
  0xb40001ab;       (* arm_CBZ X11 (word 52) *)
  0xf866786b;       (* arm_LDR X11 X3 (Shiftreg_Offset X6 3) *)
  0xf8667829;       (* arm_LDR X9 X1 (Shiftreg_Offset X6 3) *)
  0x9b0b7cea;       (* arm_MUL X10 X7 X11 *)
  0xba080129;       (* arm_ADCS X9 X9 X8 *)
  0x9bcb7ce8;       (* arm_UMULH X8 X7 X11 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab0a0129;       (* arm_ADDS X9 X9 X10 *)
  0xd10004ca;       (* arm_SUB X10 X6 (rvalue (word 1)) *)
  0xf82a7829;       (* arm_STR X9 X1 (Shiftreg_Offset X10 3) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xcb0000cb;       (* arm_SUB X11 X6 X0 *)
  0xb5fffeab;       (* arm_CBNZ X11 (word 2097108) *)
  0x9a0803e8;       (* arm_ADC X8 XZR X8 *)
  0xd10004ca;       (* arm_SUB X10 X6 (rvalue (word 1)) *)
  0xf82a7828;       (* arm_STR X8 X1 (Shiftreg_Offset X10 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xeb0000bf;       (* arm_CMP X5 X0 *)
  0x54fffcc3;       (* arm_BCC (word 2097048) *)
  0xeb1f03e6;       (* arm_NEGS X6 XZR *)
  0xf866782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X6 3) *)
  0xf8667869;       (* arm_LDR X9 X3 (Shiftreg_Offset X6 3) *)
  0xfa09017f;       (* arm_SBCS XZR X11 X9 *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xcb0000cb;       (* arm_SUB X11 X6 X0 *)
  0xb5ffff6b;       (* arm_CBNZ X11 (word 2097132) *)
  0xda9f33e8;       (* arm_CSETM X8 Condition_CS *)
  0xeb1f03e6;       (* arm_NEGS X6 XZR *)
  0xf866782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X6 3) *)
  0xf8667869;       (* arm_LDR X9 X3 (Shiftreg_Offset X6 3) *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xfa09016b;       (* arm_SBCS X11 X11 X9 *)
  0xf826782b;       (* arm_STR X11 X1 (Shiftreg_Offset X6 3) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xcb0000cb;       (* arm_SUB X11 X6 X0 *)
  0xb5ffff2b;       (* arm_CBNZ X11 (word 2097124) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xb4000101;       (* arm_CBZ X1 (word 32) *)
  0xf100001f;       (* arm_CMP X0 (rvalue (word 0)) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xf8617865;       (* arm_LDR X5 X3 (Shiftreg_Offset X1 3) *)
  0xf8617880;       (* arm_LDR X0 X4 (Shiftreg_Offset X1 3) *)
  0x9a8010a5;       (* arm_CSEL X5 X5 X0 Condition_NE *)
  0xf8217845;       (* arm_STR X5 X2 (Shiftreg_Offset X1 3) *)
  0xb5ffff61;       (* arm_CBNZ X1 (word 2097132) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MODEXP_EXEC = ARM_MK_EXEC_RULE bignum_modexp_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness for the subroutines                                           *)
(* ------------------------------------------------------------------------- *)

let ADJUST_LOCAL_POINTERS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [WORD_RULE `word_shl (word k) 3 = word(8 * k)`;
    WORD_RULE `word_shl (word k) 4 = word(16 * k)`]);;

let ARM_CASEWISE_SUBROUTINE_SIM_ABBREV_TAC (mc,ex,d,smc,cth) ins outs s n =
  let ths = CONJUNCTS
    (REWRITE_RULE[LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB; FORALL_AND_THM;
                  TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] cth) in
  MAP_FIRST (fun th g ->
     ARM_SUBROUTINE_SIM_ABBREV_TAC (mc,ex,d,smc,th) ins outs s n g) ths;;

needs "arm/proofs/bignum_amontifier.ml";;

let LOCAL_AMONTIFIER_TAC s n =
  ADJUST_LOCAL_POINTERS_TAC THEN
  ARM_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_mc,BIGNUM_MODEXP_EXEC,
     0x10c,bignum_amontifier_mc,BIGNUM_AMONTIFIER_SUBROUTINE_CORRECT)
    [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
     `read (memory :> bytes(read X2 s,8 * k)) s`;
     `pc + 0x10c`; `read X30 s`]
    `read (memory :> bytes(word_add t (word(16 * k)),8 * k)) s'` s n;;

needs "arm/proofs/bignum_amontmul.ml";;

let LOCAL_AMONTMUL_TAC s n =
  ADJUST_LOCAL_POINTERS_TAC THEN
  ARM_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_mc,BIGNUM_MODEXP_EXEC,
     0x428,bignum_amontmul_mc,BIGNUM_AMONTMUL_SUBROUTINE_CORRECT)
    [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
     `read (memory :> bytes(read X2 s,8 * k)) s`;
     `read (memory :> bytes(read X3 s,8 * k)) s`;
     `read (memory :> bytes(read X4 s,8 * k)) s`;
     `pc + 0x428`; `read X30 s`]
    `read (memory :> bytes(read X1 s,8 * k)) s'` s n;;

needs "arm/proofs/bignum_demont.ml";;

let LOCAL_DEMONT_TAC s n =
  ADJUST_LOCAL_POINTERS_TAC THEN
  ARM_CASEWISE_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_mc,BIGNUM_MODEXP_EXEC,
     0x558,bignum_demont_mc,BIGNUM_DEMONT_SUBROUTINE_CORRECT)
    [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
     `read (memory :> bytes(read X2 s,8 * k)) s`;
     `read (memory :> bytes(read X3 s,8 * k)) s`;
     `pc + 0x558`; `read X30 s`]
    `read (memory :> bytes(read X1 s,8 * k)) s'` s n;;

needs "arm/proofs/bignum_mux.ml";;

let LOCAL_MUX_TAC s n =
  ADJUST_LOCAL_POINTERS_TAC THEN
  ARM_CASEWISE_SUBROUTINE_SIM_ABBREV_TAC
    (bignum_modexp_mc,BIGNUM_MODEXP_EXEC,
     0x660,bignum_mux_mc,BIGNUM_MUX_SUBROUTINE_CORRECT)
    [`read X0 s`; `read X1 s`; `read X3 s`; `read X4 s`; `read X2 s`;
     `read (memory :> bytes(read X3 s,8 * k)) s`;
     `read (memory :> bytes(read X4 s,8 * k)) s`;
     `pc + 0x660`; `read X30 s`]
    `read (memory :> bytes(read X2 s,8 * k)) s'` s n;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODEXP_CORRECT = prove
 (`!k z a x p y m n t pc.
     val k < 2 EXP 58 /\
     ALL (nonoverlapping (word pc,0x684)) [(z,8 * val k); (t,24 * val k)] /\
     ALL (nonoverlapping (t,24 * val k))
         [(z,8 * val k); (a,8 * val k); (p,8 * val k); (m,8 * val k)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_modexp_mc /\
               read PC s = word(pc + 0x10) /\
               C_ARGUMENTS [k; z; a; p; m; t] s /\
               bignum_from_memory(a,val k) s = x /\
               bignum_from_memory(p,val k) s = y /\
               bignum_from_memory(m,val k) s = n)
          (\s. read PC s = word (pc + 0xf8) /\
               (ODD n ==> bignum_from_memory(z,val k) s = (x EXP y) MOD n))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X30] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(t,24 * val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `a:int64`; `x:num`; `p:int64`; `y:num`;
    `m:int64`; `n:num`; `t:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`x:num`; `y:num`; `n:num`] THEN

  (*** Deal with degenerate case k = 0 first ***)

  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [ARM_SIM_TAC BIGNUM_MODEXP_EXEC [1] THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; ODD];
    ALL_TAC] THEN

  (*** Setup of the main outer loop ***)

  ENSURES_WHILE_DOWN_TAC `64 * k` `pc + 0x70` `pc + 0xc8`
   `\i s. read X19 s = word k /\
          read X20 s = z /\
          read X21 s = a /\
          read X22 s = p /\
          read X23 s = m /\
          read X24 s = t /\
          read X25 s = word i /\
          bignum_from_memory(a,k) s = x /\
          bignum_from_memory(p,k) s = y /\
          bignum_from_memory(m,k) s = n /\
          (ODD n
           ==> (bignum_from_memory(word_add t (word(16 * k)),k) s ==
                2 EXP (64 * k) * x EXP (y DIV 2 EXP i)) (mod n) /\
               (bignum_from_memory(t,k) s ==
                2 EXP (64 * k) * x) (mod n))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ];

    (*** Initialization ***)

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (1--12) THEN
    LOCAL_AMONTIFIER_TAC "z2" 13 THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (14--19) THEN
    LOCAL_AMONTMUL_TAC "z1" 20 THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (21--25) THEN
    LOCAL_DEMONT_TAC "z0" 26 THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC [27] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DIV_LT; EXP] THEN
    REWRITE_TAC[ARITH_RULE `128 * k = 64 * k + 64 * k`; EXP_ADD] THEN
    MP_TAC(SPECL [`n:num`; `2 EXP (64 * k)`] INVERSE_MOD_LMUL) THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2; CONG_LMOD] THEN
    CONV_TAC NUMBER_RULE;

    (*** Main loop invariant ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `x1:num` `bignum_from_memory(t,k)` THEN
    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add t (word(16 * k)),k)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (1--7) THEN
    LOCAL_AMONTMUL_TAC "xn2" 8 THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (9--14) THEN
    LOCAL_AMONTMUL_TAC "xxn2" 15 THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_RULE `word_sub (word (i + 1)) (word 1) = word i`]) THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add p
       (word(8 * val(word_ushr (word i:int64) 6))))) s15 =
      word(y DIV (2 EXP (64 * i DIV 64)) MOD 2 EXP (64 * 1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 64 * k ==> MIN (k - i DIV 64) 1 = 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
      VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (16--19) THEN
    SUBGOAL_THEN
     `word_and
        (word_jushr (word((y DIV 2 EXP (64 * i DIV 64)) MOD 2 EXP 64))
                    (word i))
        (word 1:int64) =
      word(bitval(ODD(y DIV 2 EXP i)))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[WORD_AND_1_BITVAL; word_jushr; MOD_64_CLAUSES;
                  DIMINDEX_64; VAL_WORD; MOD_MOD_REFL] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[BIT_LSB; VAL_WORD_USHR] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
      REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + 64 = i + (64 - i MOD 64)`] THEN
      REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; ODD_MOD_POW2] THEN
      MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (20--24) THEN
    LOCAL_MUX_TAC "xmux" 25 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN  DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `yi = y DIV 2 EXP (i + 1)` THEN
    ABBREV_TAC `b = ODD(y DIV 2 EXP i)` THEN
    SUBGOAL_THEN `y DIV 2 EXP i = yi + yi + bitval b` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["b"; "yi"] THEN
      REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; BITVAL_ODD] THEN ARITH_TAC;
      SIMP_TAC[BITVAL_CLAUSES; ADD_CLAUSES; COND_ID]] THEN
    BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN
    MP_TAC(SPECL [`n:num`; `2 EXP (64 * k)`] INVERSE_MOD_LMUL) THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2; CONG_LMOD] THEN
    CONV_TAC NUMBER_RULE;

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_MODEXP_EXEC [1];

    (*** The finale ***)

    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add t (word(16 * k)),k)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (1--6) THEN
    LOCAL_DEMONT_TAC "z'" 7 THEN
    ARM_STEPS_TAC BIGNUM_MODEXP_EXEC (8--13) THEN
    LOCAL_MUX_TAC "res" 14 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN  DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[EXP; DIV_1] THEN SIMP_TAC[GSYM CONG] THEN
    MP_TAC(SPECL [`n:num`; `2 EXP (64 * k)`] INVERSE_MOD_LMUL) THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2] THEN CONV_TAC NUMBER_RULE]);;

let BIGNUM_MODEXP_SUBROUTINE_CORRECT = prove
 (`!k z a x p y m n t pc stackpointer returnaddress.
     val k < 2 EXP 58 /\
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),64))
          [(word pc,0x684); (z,8 * val k); (t,24 * val k);
          (a,8 * val k); (p,8 * val k); (m,8 * val k)] /\
     ALL (nonoverlapping (word pc,0x684)) [(z,8 * val k); (t,24 * val k)] /\
     ALL (nonoverlapping (t,24 * val k))
         [(z,8 * val k); (a,8 * val k); (p,8 * val k); (m,8 * val k)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_modexp_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [k; z; a; p; m; t] s /\
               bignum_from_memory(a,val k) s = x /\
               bignum_from_memory(p,val k) s = y /\
               bignum_from_memory(m,val k) s = n)
          (\s. read PC s = returnaddress /\
               (ODD n ==> bignum_from_memory(z,val k) s = (x EXP y) MOD n))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(t,24 * val k);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ARM_ADD_RETURN_STACK_TAC BIGNUM_MODEXP_EXEC BIGNUM_MODEXP_CORRECT
   `[X19;X20;X21;X22;X23;X24;X25;X30]` 64);;
