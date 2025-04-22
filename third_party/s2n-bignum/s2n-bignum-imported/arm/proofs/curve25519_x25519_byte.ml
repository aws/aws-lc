(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The x25519 function for curve25519 (byte array arguments)                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bignum_inv_p25519.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/curve25519.ml";;
needs "EC/formulary_xzprojective.ml";;
needs "EC/x25519.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/curve25519/curve25519_x25519_byte.o";;
 ****)

let curve25519_x25519_byte_mc = define_assert_from_elf
  "curve25519_x25519_byte_mc" "arm/curve25519/curve25519_x25519_byte.o"
[
  0xd10603ff;       (* arm_SUB SP SP (rvalue (word 384)) *)
  0x6d0e27e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&224))) *)
  0x6d0f2fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&240))) *)
  0x6d1037ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&256))) *)
  0x6d113fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&272))) *)
  0xa91253f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&288))) *)
  0xa9135bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&304))) *)
  0xa91463f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&320))) *)
  0xa9156bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&336))) *)
  0xa91673fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&352))) *)
  0xa9177bfd;       (* arm_STP X29 X30 SP (Immediate_Offset (iword (&368))) *)
  0xf90063e0;       (* arm_STR X0 SP (Immediate_Offset (word 192)) *)
  0x3940002a;       (* arm_LDRB W10 X1 (Immediate_Offset (word 0)) *)
  0x39400420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 1)) *)
  0xaa00214a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 8) *)
  0x39400820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 2)) *)
  0xaa00414a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 16) *)
  0x39400c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 3)) *)
  0xaa00614a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 24) *)
  0x39401020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 4)) *)
  0xaa00814a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 32) *)
  0x39401420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 5)) *)
  0xaa00a14a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 40) *)
  0x39401820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 6)) *)
  0xaa00c14a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 48) *)
  0x39401c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 7)) *)
  0xaa00e14a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 56) *)
  0x3940202b;       (* arm_LDRB W11 X1 (Immediate_Offset (word 8)) *)
  0x39402420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 9)) *)
  0xaa00216b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 8) *)
  0x39402820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 10)) *)
  0xaa00416b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 16) *)
  0x39402c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 11)) *)
  0xaa00616b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 24) *)
  0x39403020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 12)) *)
  0xaa00816b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 32) *)
  0x39403420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 13)) *)
  0xaa00a16b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 40) *)
  0x39403820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 14)) *)
  0xaa00c16b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 48) *)
  0x39403c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 15)) *)
  0xaa00e16b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 56) *)
  0x927df14a;       (* arm_AND X10 X10 (rvalue (word 18446744073709551608)) *)
  0xa9002fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  0x3940402c;       (* arm_LDRB W12 X1 (Immediate_Offset (word 16)) *)
  0x39404420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 17)) *)
  0xaa00218c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 8) *)
  0x39404820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 18)) *)
  0xaa00418c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 16) *)
  0x39404c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 19)) *)
  0xaa00618c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 24) *)
  0x39405020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 20)) *)
  0xaa00818c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 32) *)
  0x39405420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 21)) *)
  0xaa00a18c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 40) *)
  0x39405820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 22)) *)
  0xaa00c18c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 48) *)
  0x39405c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 23)) *)
  0xaa00e18c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 56) *)
  0x3940602d;       (* arm_LDRB W13 X1 (Immediate_Offset (word 24)) *)
  0x39406420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 25)) *)
  0xaa0021ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 8) *)
  0x39406820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 26)) *)
  0xaa0041ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 16) *)
  0x39406c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 27)) *)
  0xaa0061ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 24) *)
  0x39407020;       (* arm_LDRB W0 X1 (Immediate_Offset (word 28)) *)
  0xaa0081ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 32) *)
  0x39407420;       (* arm_LDRB W0 X1 (Immediate_Offset (word 29)) *)
  0xaa00a1ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 40) *)
  0x39407820;       (* arm_LDRB W0 X1 (Immediate_Offset (word 30)) *)
  0xaa00c1ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 48) *)
  0x39407c20;       (* arm_LDRB W0 X1 (Immediate_Offset (word 31)) *)
  0xaa00e1ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 56) *)
  0xb24201ad;       (* arm_ORR X13 X13 (rvalue (word 4611686018427387904)) *)
  0xa90137ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  0x39400044;       (* arm_LDRB W4 X2 (Immediate_Offset (word 0)) *)
  0x39400440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 1)) *)
  0xaa002084;       (* arm_ORR X4 X4 (Shiftedreg X0 LSL 8) *)
  0x39400840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 2)) *)
  0xaa004084;       (* arm_ORR X4 X4 (Shiftedreg X0 LSL 16) *)
  0x39400c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 3)) *)
  0xaa006084;       (* arm_ORR X4 X4 (Shiftedreg X0 LSL 24) *)
  0x39401040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 4)) *)
  0xaa008084;       (* arm_ORR X4 X4 (Shiftedreg X0 LSL 32) *)
  0x39401440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 5)) *)
  0xaa00a084;       (* arm_ORR X4 X4 (Shiftedreg X0 LSL 40) *)
  0x39401840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 6)) *)
  0xaa00c084;       (* arm_ORR X4 X4 (Shiftedreg X0 LSL 48) *)
  0x39401c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 7)) *)
  0xaa00e084;       (* arm_ORR X4 X4 (Shiftedreg X0 LSL 56) *)
  0x39402045;       (* arm_LDRB W5 X2 (Immediate_Offset (word 8)) *)
  0x39402440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 9)) *)
  0xaa0020a5;       (* arm_ORR X5 X5 (Shiftedreg X0 LSL 8) *)
  0x39402840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 10)) *)
  0xaa0040a5;       (* arm_ORR X5 X5 (Shiftedreg X0 LSL 16) *)
  0x39402c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 11)) *)
  0xaa0060a5;       (* arm_ORR X5 X5 (Shiftedreg X0 LSL 24) *)
  0x39403040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 12)) *)
  0xaa0080a5;       (* arm_ORR X5 X5 (Shiftedreg X0 LSL 32) *)
  0x39403440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 13)) *)
  0xaa00a0a5;       (* arm_ORR X5 X5 (Shiftedreg X0 LSL 40) *)
  0x39403840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 14)) *)
  0xaa00c0a5;       (* arm_ORR X5 X5 (Shiftedreg X0 LSL 48) *)
  0x39403c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 15)) *)
  0xaa00e0a5;       (* arm_ORR X5 X5 (Shiftedreg X0 LSL 56) *)
  0x39404046;       (* arm_LDRB W6 X2 (Immediate_Offset (word 16)) *)
  0x39404440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 17)) *)
  0xaa0020c6;       (* arm_ORR X6 X6 (Shiftedreg X0 LSL 8) *)
  0x39404840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 18)) *)
  0xaa0040c6;       (* arm_ORR X6 X6 (Shiftedreg X0 LSL 16) *)
  0x39404c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 19)) *)
  0xaa0060c6;       (* arm_ORR X6 X6 (Shiftedreg X0 LSL 24) *)
  0x39405040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 20)) *)
  0xaa0080c6;       (* arm_ORR X6 X6 (Shiftedreg X0 LSL 32) *)
  0x39405440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 21)) *)
  0xaa00a0c6;       (* arm_ORR X6 X6 (Shiftedreg X0 LSL 40) *)
  0x39405840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 22)) *)
  0xaa00c0c6;       (* arm_ORR X6 X6 (Shiftedreg X0 LSL 48) *)
  0x39405c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 23)) *)
  0xaa00e0c6;       (* arm_ORR X6 X6 (Shiftedreg X0 LSL 56) *)
  0x39406047;       (* arm_LDRB W7 X2 (Immediate_Offset (word 24)) *)
  0x39406440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 25)) *)
  0xaa0020e7;       (* arm_ORR X7 X7 (Shiftedreg X0 LSL 8) *)
  0x39406840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 26)) *)
  0xaa0040e7;       (* arm_ORR X7 X7 (Shiftedreg X0 LSL 16) *)
  0x39406c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 27)) *)
  0xaa0060e7;       (* arm_ORR X7 X7 (Shiftedreg X0 LSL 24) *)
  0x39407040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 28)) *)
  0xaa0080e7;       (* arm_ORR X7 X7 (Shiftedreg X0 LSL 32) *)
  0x39407440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 29)) *)
  0xaa00a0e7;       (* arm_ORR X7 X7 (Shiftedreg X0 LSL 40) *)
  0x39407840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 30)) *)
  0xaa00c0e7;       (* arm_ORR X7 X7 (Shiftedreg X0 LSL 48) *)
  0x39407c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 31)) *)
  0xaa00e0e7;       (* arm_ORR X7 X7 (Shiftedreg X0 LSL 56) *)
  0xd373fc8c;       (* arm_LSR X12 X4 51 *)
  0xd373fcd1;       (* arm_LSR X17 X6 51 *)
  0xaa05358c;       (* arm_ORR X12 X12 (Shiftedreg X5 LSL 13) *)
  0xaa073631;       (* arm_ORR X17 X17 (Shiftedreg X7 LSL 13) *)
  0xd34c94e8;       (* arm_UBFM X8 X7 12 37 *)
  0xd366f8e9;       (* arm_UBFM X9 X7 38 62 *)
  0xd35ac88b;       (* arm_UBFM X11 X4 26 50 *)
  0xd34d94ad;       (* arm_UBFM X13 X5 13 37 *)
  0xd366fcae;       (* arm_LSR X14 X5 38 *)
  0xd359c8d0;       (* arm_UBFM X16 X6 25 50 *)
  0x9240648a;       (* arm_AND X10 X4 (rvalue (word 67108863)) *)
  0x9240658c;       (* arm_AND X12 X12 (rvalue (word 67108863)) *)
  0x924060cf;       (* arm_AND X15 X6 (rvalue (word 33554431)) *)
  0x92406231;       (* arm_AND X17 X17 (rvalue (word 33554431)) *)
  0xaa0b814a;       (* arm_ORR X10 X10 (Shiftedreg X11 LSL 32) *)
  0xaa0d818b;       (* arm_ORR X11 X12 (Shiftedreg X13 LSL 32) *)
  0xaa0f81cc;       (* arm_ORR X12 X14 (Shiftedreg X15 LSL 32) *)
  0xaa11820d;       (* arm_ORR X13 X16 (Shiftedreg X17 LSL 32) *)
  0xaa09810e;       (* arm_ORR X14 X8 (Shiftedreg X9 LSL 32) *)
  0xa9022fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&32))) *)
  0xa90337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&48))) *)
  0xf90023ee;       (* arm_STR X14 SP (Immediate_Offset (word 64)) *)
  0xd2800021;       (* arm_MOV X1 (rvalue (word 1)) *)
  0x4e081c20;       (* arm_INS_GEN Q0 X1 0 64 *)
  0x4e081fe2;       (* arm_INS_GEN Q2 XZR 0 64 *)
  0x4e081fe4;       (* arm_INS_GEN Q4 XZR 0 64 *)
  0x4e081fe6;       (* arm_INS_GEN Q6 XZR 0 64 *)
  0x4e081fe8;       (* arm_INS_GEN Q8 XZR 0 64 *)
  0x4e081fe1;       (* arm_INS_GEN Q1 XZR 0 64 *)
  0x4e081fe3;       (* arm_INS_GEN Q3 XZR 0 64 *)
  0x4e081fe5;       (* arm_INS_GEN Q5 XZR 0 64 *)
  0x4e081fe7;       (* arm_INS_GEN Q7 XZR 0 64 *)
  0x4e081fe9;       (* arm_INS_GEN Q9 XZR 0 64 *)
  0x4e081d4a;       (* arm_INS_GEN Q10 X10 0 64 *)
  0x4e081d6c;       (* arm_INS_GEN Q12 X11 0 64 *)
  0x4e081d8e;       (* arm_INS_GEN Q14 X12 0 64 *)
  0x4e081db0;       (* arm_INS_GEN Q16 X13 0 64 *)
  0x4e081dd2;       (* arm_INS_GEN Q18 X14 0 64 *)
  0x4e081c2b;       (* arm_INS_GEN Q11 X1 0 64 *)
  0x4e081fed;       (* arm_INS_GEN Q13 XZR 0 64 *)
  0x4e081fef;       (* arm_INS_GEN Q15 XZR 0 64 *)
  0x4e081ff1;       (* arm_INS_GEN Q17 XZR 0 64 *)
  0x4e081ff3;       (* arm_INS_GEN Q19 XZR 0 64 *)
  0x52800260;       (* arm_MOV W0 (rvalue (word 19)) *)
  0x8b008000;       (* arm_ADD X0 X0 (Shiftedreg X0 LSL 32) *)
  0x4e081c1f;       (* arm_INS_GEN Q31 X0 0 64 *)
  0x4e181fff;       (* arm_INS_GEN Q31 XZR 64 64 *)
  0xb24067e0;       (* arm_MOV X0 (rvalue (word 67108863)) *)
  0x4e081c1e;       (* arm_INS_GEN Q30 X0 0 64 *)
  0x4e181c1e;       (* arm_INS_GEN Q30 X0 64 64 *)
  0xb21f67e0;       (* arm_MOV X0 (rvalue (word 576460743847706622)) *)
  0xd1012801;       (* arm_SUB X1 X0 (rvalue (word 74)) *)
  0xd1000800;       (* arm_SUB X0 X0 (rvalue (word 2)) *)
  0xa90487e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&72))) *)
  0x6d44f3fd;       (* arm_LDP D29 D28 SP (Immediate_Offset (iword (&72))) *)
  0xf9006bff;       (* arm_STR XZR SP (Immediate_Offset (word 208)) *)
  0xd2801fc0;       (* arm_MOV X0 (rvalue (word 254)) *)
  0xf90067e0;       (* arm_STR X0 SP (Immediate_Offset (word 200)) *)
  0xd346fc01;       (* arm_LSR X1 X0 6 *)
  0xf8617be2;       (* arm_LDR X2 SP (Shiftreg_Offset X1 3) *)
  0x9ac02442;       (* arm_LSRV X2 X2 X0 *)
  0x92400042;       (* arm_AND X2 X2 (rvalue (word 1)) *)
  0xf9406be0;       (* arm_LDR X0 SP (Immediate_Offset (word 208)) *)
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0xf9006be2;       (* arm_STR X2 SP (Immediate_Offset (word 208)) *)
  0x0ea38456;       (* arm_ADD_VEC Q22 Q2 Q3 32 64 *)
  0x2ea18795;       (* arm_SUB_VEC Q21 Q28 Q1 32 64 *)
  0x0ea18419;       (* arm_ADD_VEC Q25 Q0 Q1 32 64 *)
  0x2ea387b8;       (* arm_SUB_VEC Q24 Q29 Q3 32 64 *)
  0x0eb38643;       (* arm_ADD_VEC Q3 Q18 Q19 32 64 *)
  0x0eb58400;       (* arm_ADD_VEC Q0 Q0 Q21 32 64 *)
  0x2eaf87b4;       (* arm_SUB_VEC Q20 Q29 Q15 32 64 *)
  0x2ea587a1;       (* arm_SUB_VEC Q1 Q29 Q5 32 64 *)
  0x2eab879a;       (* arm_SUB_VEC Q26 Q28 Q11 32 64 *)
  0x2eb387b5;       (* arm_SUB_VEC Q21 Q29 Q19 32 64 *)
  0x0eab8553;       (* arm_ADD_VEC Q19 Q10 Q11 32 64 *)
  0x0eb485cb;       (* arm_ADD_VEC Q11 Q14 Q20 32 64 *)
  0x0eb58655;       (* arm_ADD_VEC Q21 Q18 Q21 32 64 *)
  0x2eb187b4;       (* arm_SUB_VEC Q20 Q29 Q17 32 64 *)
  0x0eb88452;       (* arm_ADD_VEC Q18 Q2 Q24 32 64 *)
  0x0eaf85ce;       (* arm_ADD_VEC Q14 Q14 Q15 32 64 *)
  0x0eb1860f;       (* arm_ADD_VEC Q15 Q16 Q17 32 64 *)
  0x0eb48602;       (* arm_ADD_VEC Q2 Q16 Q20 32 64 *)
  0x0ead8598;       (* arm_ADD_VEC Q24 Q12 Q13 32 64 *)
  0x0eba855a;       (* arm_ADD_VEC Q26 Q10 Q26 32 64 *)
  0x2ead87aa;       (* arm_SUB_VEC Q10 Q29 Q13 32 64 *)
  0x2ea787ad;       (* arm_SUB_VEC Q13 Q29 Q7 32 64 *)
  0x0ea784d7;       (* arm_ADD_VEC Q23 Q6 Q7 32 64 *)
  0x2ea987a7;       (* arm_SUB_VEC Q7 Q29 Q9 32 64 *)
  0x0eaa859b;       (* arm_ADD_VEC Q27 Q12 Q10 32 64 *)
  0x1e780ed4;       (* arm_FCSEL Q20 Q22 Q24 Condition_EQ 64 *)
  0x0ea5849c;       (* arm_ADD_VEC Q28 Q4 Q5 32 64 *)
  0x1e6f0eec;       (* arm_FCSEL Q12 Q23 Q15 Condition_EQ 64 *)
  0x0ea78507;       (* arm_ADD_VEC Q7 Q8 Q7 32 64 *)
  0x1e730f30;       (* arm_FCSEL Q16 Q25 Q19 Condition_EQ 64 *)
  0x4e083e80;       (* arm_UMOV X0 Q20 0 8 *)
  0x1e6e0f85;       (* arm_FCSEL Q5 Q28 Q14 Condition_EQ 64 *)
  0x4e083d95;       (* arm_UMOV X21 Q12 0 8 *)
  0x1e750cfd;       (* arm_FCSEL Q29 Q7 Q21 Condition_EQ 64 *)
  0x4e083e05;       (* arm_UMOV X5 Q16 0 8 *)
  0xd360fc1a;       (* arm_LSR X26 X0 32 *)
  0x8b1502bd;       (* arm_ADD X29 X21 X21 *)
  0x9bbd7caf;       (* arm_UMULL X15 W5 W29 *)
  0x0ead84cd;       (* arm_ADD_VEC Q13 Q6 Q13 32 64 *)
  0x8b1a034c;       (* arm_ADD X12 X26 X26 *)
  0x4e083cbe;       (* arm_UMOV X30 Q5 0 8 *)
  0x1e7b0e4a;       (* arm_FCSEL Q10 Q18 Q27 Condition_EQ 64 *)
  0xd360fcab;       (* arm_LSR X11 X5 32 *)
  0xd360ffca;       (* arm_LSR X10 X30 32 *)
  0x0e836ab4;       (* arm_TRN2 Q20 Q21 Q3 32 64 *)
  0x0ea98509;       (* arm_ADD_VEC Q9 Q8 Q9 32 64 *)
  0x8b0b016e;       (* arm_ADD X14 X11 X11 *)
  0x0e8f6846;       (* arm_TRN2 Q6 Q2 Q15 32 64 *)
  0x0e802b2c;       (* arm_TRN1 Q12 Q25 Q0 32 64 *)
  0x0ea18481;       (* arm_ADD_VEC Q1 Q4 Q1 32 64 *)
  0x0e8d2af0;       (* arm_TRN1 Q16 Q23 Q13 32 64 *)
  0x1e620da8;       (* arm_FCSEL Q8 Q13 Q2 Condition_EQ 64 *)
  0x0e986b71;       (* arm_TRN2 Q17 Q27 Q24 32 64 *)
  0xfd0053fd;       (* arm_STR D29 SP (Immediate_Offset (word 160)) *)
  0x8b0a0151;       (* arm_ADD X17 X10 X10 *)
  0x0e816b84;       (* arm_TRN2 Q4 Q28 Q1 32 64 *)
  0x0e812b85;       (* arm_TRN1 Q5 Q28 Q1 32 64 *)
  0x0e8f285c;       (* arm_TRN1 Q28 Q2 Q15 32 64 *)
  0x0e922ac2;       (* arm_TRN1 Q2 Q22 Q18 32 64 *)
  0x1e7a0c1d;       (* arm_FCSEL Q29 Q0 Q26 Condition_EQ 64 *)
  0x0e926acf;       (* arm_TRN2 Q15 Q22 Q18 32 64 *)
  0x2eb4c196;       (* arm_UMULL_VEC Q22 Q12 Q20 32 *)
  0x9bb17fd6;       (* arm_UMULL X22 W30 W17 *)
  0x6d082bfd;       (* arm_STP D29 D10 SP (Immediate_Offset (iword (&128))) *)
  0x0e8d6aea;       (* arm_TRN2 Q10 Q23 Q13 32 64 *)
  0x0e8e6977;       (* arm_TRN2 Q23 Q11 Q14 32 64 *)
  0x0e982b6d;       (* arm_TRN1 Q13 Q27 Q24 32 64 *)
  0x1e6b0c3b;       (* arm_FCSEL Q27 Q1 Q11 Condition_EQ 64 *)
  0x0e8e296e;       (* arm_TRN1 Q14 Q11 Q14 32 64 *)
  0x2ea68056;       (* arm_UMLAL_VEC Q22 Q2 Q6 32 *)
  0x9bbe7fd9;       (* arm_UMULL X25 W30 W30 *)
  0x2eb780b6;       (* arm_UMLAL_VEC Q22 Q5 Q23 32 *)
  0x8b1e03c3;       (* arm_ADD X3 X30 X30 *)
  0x2eb18216;       (* arm_UMLAL_VEC Q22 Q16 Q17 32 *)
  0x0b1506be;       (* arm_ADD W30 W21 (Shiftedreg W21 LSL 1) *)
  0x6d0923fb;       (* arm_STP D27 D8 SP (Immediate_Offset (iword (&144))) *)
  0x0b1513de;       (* arm_ADD W30 W30 (Shiftedreg W21 LSL 4) *)
  0x0e932b4b;       (* arm_TRN1 Q11 Q26 Q19 32 64 *)
  0x0e936b48;       (* arm_TRN2 Q8 Q26 Q19 32 64 *)
  0x0e806b33;       (* arm_TRN2 Q19 Q25 Q0 32 64 *)
  0x0ebf9e9d;       (* arm_MUL_VEC Q29 Q20 Q31 32 64 *)
  0xf9404ff4;       (* arm_LDR X20 SP (Immediate_Offset (word 152)) *)
  0x2ea6c279;       (* arm_UMULL_VEC Q25 Q19 Q6 32 *)
  0x8b000001;       (* arm_ADD X1 X0 X0 *)
  0x2eb7c27b;       (* arm_UMULL_VEC Q27 Q19 Q23 32 *)
  0x9ba17ca9;       (* arm_UMULL X9 W5 W1 *)
  0x2eb7c180;       (* arm_UMULL_VEC Q0 Q12 Q23 32 *)
  0xd360fe98;       (* arm_LSR X24 X20 32 *)
  0x0ebf9ef4;       (* arm_MUL_VEC Q20 Q23 Q31 32 64 *)
  0xd360feb0;       (* arm_LSR X16 X21 32 *)
  0x2eb781f9;       (* arm_UMLAL_VEC Q25 Q15 Q23 32 *)
  0x9bae256d;       (* arm_UMADDL X13 W11 W14 X9 *)
  0x2eb18099;       (* arm_UMLAL_VEC Q25 Q4 Q17 32 *)
  0x9bb13dc9;       (* arm_UMADDL X9 W14 W17 X15 *)
  0x2ea6c198;       (* arm_UMULL_VEC Q24 Q12 Q6 32 *)
  0x0b100602;       (* arm_ADD W2 W16 (Shiftedreg W16 LSL 1) *)
  0x1e630d3a;       (* arm_FCSEL Q26 Q9 Q3 Condition_EQ 64 *)
  0x0b101042;       (* arm_ADD W2 W2 (Shiftedreg W16 LSL 4) *)
  0x0e832ab2;       (* arm_TRN1 Q18 Q21 Q3 32 64 *)
  0x2ebdc263;       (* arm_UMULL_VEC Q3 Q19 Q29 32 *)
  0x9ba37cbc;       (* arm_UMULL X28 W5 W3 *)
  0x0ebf9cc1;       (* arm_MUL_VEC Q1 Q6 Q31 32 64 *)
  0x9ba57ca8;       (* arm_UMULL X8 W5 W5 *)
  0x2eb78058;       (* arm_UMLAL_VEC Q24 Q2 Q23 32 *)
  0x9bbe36ad;       (* arm_UMADDL X13 W21 W30 X13 *)
  0x0ebf9e37;       (* arm_MUL_VEC Q23 Q17 Q31 32 64 *)
  0x9bac71db;       (* arm_UMADDL X27 W14 W12 X28 *)
  0x0e876926;       (* arm_TRN2 Q6 Q9 Q7 32 64 *)
  0x4e083f46;       (* arm_UMOV X6 Q26 0 8 *)
  0x2ea181e3;       (* arm_UMLAL_VEC Q3 Q15 Q1 32 *)
  0x8b100210;       (* arm_ADD X16 X16 X16 *)
  0x2eb48083;       (* arm_UMLAL_VEC Q3 Q4 Q20 32 *)
  0xd360fcc4;       (* arm_LSR X4 X6 32 *)
  0x2eb78143;       (* arm_UMLAL_VEC Q3 Q10 Q23 32 *)
  0x8b0600c7;       (* arm_ADD X7 X6 X6 *)
  0x2ea8c27a;       (* arm_UMULL_VEC Q26 Q19 Q8 32 *)
  0x8b040097;       (* arm_ADD X23 X4 X4 *)
  0x9bb758bc;       (* arm_UMADDL X28 W5 W23 X22 *)
  0x0e872927;       (* arm_TRN1 Q7 Q9 Q7 32 64 *)
  0x2eb181fb;       (* arm_UMLAL_VEC Q27 Q15 Q17 32 *)
  0x0b04048f;       (* arm_ADD W15 W4 (Shiftedreg W4 LSL 1) *)
  0x2ea8809b;       (* arm_UMLAL_VEC Q27 Q4 Q8 32 *)
  0x0b0411ef;       (* arm_ADD W15 W15 (Shiftedreg W4 LSL 4) *)
  0x0b0a0556;       (* arm_ADD W22 W10 (Shiftedreg W10 LSL 1) *)
  0x2eb180b8;       (* arm_UMLAL_VEC Q24 Q5 Q17 32 *)
  0x0b0a12d6;       (* arm_ADD W22 W22 (Shiftedreg W10 LSL 4) *)
  0x9ba7716a;       (* arm_UMADDL X10 W11 W7 X28 *)
  0x2ea88159;       (* arm_UMLAL_VEC Q25 Q10 Q8 32 *)
  0x9bb07cb5;       (* arm_UMULL X21 W5 W16 *)
  0x2ebd80d9;       (* arm_UMLAL_VEC Q25 Q6 Q29 32 *)
  0x9bb765f7;       (* arm_UMADDL X23 W15 W23 X25 *)
  0x2ebd815b;       (* arm_UMLAL_VEC Q27 Q10 Q29 32 *)
  0x9bac7cb3;       (* arm_UMULL X19 W5 W12 *)
  0x2ea180db;       (* arm_UMLAL_VEC Q27 Q6 Q1 32 *)
  0x9bbd5579;       (* arm_UMADDL X25 W11 W29 X21 *)
  0x2eb18040;       (* arm_UMLAL_VEC Q0 Q2 Q17 32 *)
  0x9ba3241c;       (* arm_UMADDL X28 W0 W3 X9 *)
  0x4f415735;       (* arm_SHL_VEC Q21 Q25 1 64 128 *)
  0x9ba14d64;       (* arm_UMADDL X4 W11 W1 X19 *)
  0x9bbd1055;       (* arm_UMADDL X21 W2 W29 X4 *)
  0x0ebf9d19;       (* arm_MUL_VEC Q25 Q8 Q31 32 64 *)
  0x2ea88218;       (* arm_UMLAL_VEC Q24 Q16 Q8 32 *)
  0x9bb16413;       (* arm_UMADDL X19 W0 W17 X25 *)
  0x2ebd80f8;       (* arm_UMLAL_VEC Q24 Q7 Q29 32 *)
  0x9bb17cb9;       (* arm_UMULL X25 W5 W17 *)
  0x2ebc8278;       (* arm_UMLAL_VEC Q24 Q19 Q28 32 *)
  0x9bb02804;       (* arm_UMADDL X4 W0 W16 X10 *)
  0x2ea8c189;       (* arm_UMULL_VEC Q9 Q12 Q8 32 *)
  0x9ba75cb7;       (* arm_UMADDL X23 W5 W7 X23 *)
  0x2eb28195;       (* arm_UMLAL_VEC Q21 Q12 Q18 32 *)
  0x0b0604ca;       (* arm_ADD W10 W6 (Shiftedreg W6 LSL 1) *)
  0x4f41577b;       (* arm_SHL_VEC Q27 Q27 1 64 128 *)
  0x0b06114a;       (* arm_ADD W10 W10 (Shiftedreg W6 LSL 4) *)
  0x9bac735c;       (* arm_UMADDL X28 W26 W12 X28 *)
  0x2ebd81fa;       (* arm_UMLAL_VEC Q26 Q15 Q29 32 *)
  0x9bb05dc9;       (* arm_UMADDL X9 W14 W16 X23 *)
  0x2ebd8049;       (* arm_UMLAL_VEC Q9 Q2 Q29 32 *)
  0x9bb122d6;       (* arm_UMADDL X22 W22 W17 X8 *)
  0x2ebc8055;       (* arm_UMLAL_VEC Q21 Q2 Q28 32 *)
  0x9baa70dc;       (* arm_UMADDL X28 W6 W10 X28 *)
  0x9ba06c1b;       (* arm_UMADDL X27 W0 W0 X27 *)
  0x8b0e01c8;       (* arm_ADD X8 X14 X14 *)
  0x2ea880a0;       (* arm_UMLAL_VEC Q0 Q5 Q8 32 *)
  0x9bae7ca5;       (* arm_UMULL X5 W5 W14 *)
  0x2ea180a9;       (* arm_UMLAL_VEC Q9 Q5 Q1 32 *)
  0x9bbd240e;       (* arm_UMADDL X14 W0 W29 X9 *)
  0x2ea1809a;       (* arm_UMLAL_VEC Q26 Q4 Q1 32 *)
  0x9bb06c46;       (* arm_UMADDL X6 W2 W16 X27 *)
  0x2ea880f6;       (* arm_UMLAL_VEC Q22 Q7 Q8 32 *)
  0x9bb117c5;       (* arm_UMADDL X5 W30 W17 X5 *)
  0x9ba31445;       (* arm_UMADDL X5 W2 W3 X5 *)
  0x8b110237;       (* arm_ADD X23 X17 X17 *)
  0x2ebc819b;       (* arm_UMLAL_VEC Q27 Q12 Q28 32 *)
  0x9bb7344d;       (* arm_UMADDL X13 W2 W23 X13 *)
  0x2eb4815a;       (* arm_UMLAL_VEC Q26 Q10 Q20 32 *)
  0x8b0c0189;       (* arm_ADD X9 X12 X12 *)
  0x2eb48209;       (* arm_UMLAL_VEC Q9 Q16 Q20 32 *)
  0x9bbd195b;       (* arm_UMADDL X27 W10 W29 X6 *)
  0x2ebd8200;       (* arm_UMLAL_VEC Q0 Q16 Q29 32 *)
  0x9ba36566;       (* arm_UMADDL X6 W11 W3 X25 *)
  0x2eb28276;       (* arm_UMLAL_VEC Q22 Q19 Q18 32 *)
  0x9ba34f53;       (* arm_UMADDL X19 W26 W3 X19 *)
  0x0ebf9e52;       (* arm_MUL_VEC Q18 Q18 Q31 32 64 *)
  0x9bb76df7;       (* arm_UMADDL X23 W15 W23 X27 *)
  0x2eb980c3;       (* arm_UMLAL_VEC Q3 Q6 Q25 32 *)
  0x9bac1800;       (* arm_UMADDL X0 W0 W12 X6 *)
  0x2ea180e0;       (* arm_UMLAL_VEC Q0 Q7 Q1 32 *)
  0x8b10020b;       (* arm_ADD X11 X16 X16 *)
  0x2eb780e9;       (* arm_UMLAL_VEC Q9 Q7 Q23 32 *)
  0x9bb13986;       (* arm_UMADDL X6 W12 W17 X14 *)
  0x2eab8269;       (* arm_UMLAL_VEC Q9 Q19 Q11 32 *)
  0x9bbd1359;       (* arm_UMADDL X25 W26 W29 X4 *)
  0x2eb281e9;       (* arm_UMLAL_VEC Q9 Q15 Q18 32 *)
  0x9ba3354e;       (* arm_UMADDL X14 W10 W3 X13 *)
  0x2eb1c199;       (* arm_UMULL_VEC Q25 Q12 Q17 32 *)
  0x9bb0015b;       (* arm_UMADDL X27 W10 W16 X0 *)
  0x2eb780da;       (* arm_UMLAL_VEC Q26 Q6 Q23 32 *)
  0x8b466b20;       (* arm_ADD X0 X25 (Shiftedreg X6 LSR 26) *)
  0x0ebf9f97;       (* arm_MUL_VEC Q23 Q28 Q31 32 64 *)
  0x9bac154c;       (* arm_UMADDL X12 W10 W12 X5 *)
  0x4f415463;       (* arm_SHL_VEC Q3 Q3 1 64 128 *)
  0x8b4066d0;       (* arm_ADD X16 X22 (Shiftedreg X0 LSR 25) *)
  0x2eae80b5;       (* arm_UMLAL_VEC Q21 Q5 Q14 32 *)
  0x92679816;       (* arm_AND X22 X0 (rvalue (word 18446744073675997184)) *)
  0x2eab8183;       (* arm_UMLAL_VEC Q3 Q12 Q11 32 *)
  0x8b56621a;       (* arm_ADD X26 X16 (Shiftedreg X22 LSR 24) *)
  0x2eb28043;       (* arm_UMLAL_VEC Q3 Q2 Q18 32 *)
  0x9bb15550;       (* arm_UMADDL X16 W10 W17 X21 *)
  0x2eb780a3;       (* arm_UMLAL_VEC Q3 Q5 Q23 32 *)
  0x8b565756;       (* arm_ADD X22 X26 (Shiftedreg X22 LSR 21) *)
  0x2eb78089;       (* arm_UMLAL_VEC Q9 Q4 Q23 32 *)
  0x9bbd6de5;       (* arm_UMADDL X5 W15 W29 X27 *)
  0x2eb1c271;       (* arm_UMULL_VEC Q17 Q19 Q17 32 *)
  0x9ba35bd1;       (* arm_UMADDL X17 W30 W3 X22 *)
  0x2ea88059;       (* arm_UMLAL_VEC Q25 Q2 Q8 32 *)
  0x9ba341f9;       (* arm_UMADDL X25 W15 W3 X16 *)
  0x2ebd80b9;       (* arm_UMLAL_VEC Q25 Q5 Q29 32 *)
  0x9ba74dfa;       (* arm_UMADDL X26 W15 W7 X19 *)
  0x2eae8260;       (* arm_UMLAL_VEC Q0 Q19 Q14 32 *)
  0x9ba94451;       (* arm_UMADDL X17 W2 W9 X17 *)
  0x2ea881f1;       (* arm_UMLAL_VEC Q17 Q15 Q8 32 *)
  0xf94043f3;       (* arm_LDR X19 SP (Immediate_Offset (word 128)) *)
  0x2ebd8091;       (* arm_UMLAL_VEC Q17 Q4 Q29 32 *)
  0xf94047e7;       (* arm_LDR X7 SP (Immediate_Offset (word 136)) *)
  0x4f41575d;       (* arm_SHL_VEC Q29 Q26 1 64 128 *)
  0x9ba1454d;       (* arm_UMADDL X13 W10 W1 X17 *)
  0x2ead81e0;       (* arm_UMLAL_VEC Q0 Q15 Q13 32 *)
  0xd360fe62;       (* arm_LSR X2 X19 32 *)
  0x2ead819d;       (* arm_UMLAL_VEC Q29 Q12 Q13 32 *)
  0x9ba131fb;       (* arm_UMADDL X27 W15 W1 X12 *)
  0x2eab805d;       (* arm_UMLAL_VEC Q29 Q2 Q11 32 *)
  0x9ba835fe;       (* arm_UMADDL X30 W15 W8 X13 *)
  0x2eb280bd;       (* arm_UMLAL_VEC Q29 Q5 Q18 32 *)
  0x8b0700e4;       (* arm_ADD X4 X7 X7 *)
  0x2eb7821d;       (* arm_UMLAL_VEC Q29 Q16 Q23 32 *)
  0x9ba939fd;       (* arm_UMADDL X29 W15 W9 X14 *)
  0x2eab8080;       (* arm_UMLAL_VEC Q0 Q4 Q11 32 *)
  0x8b5e6b71;       (* arm_ADD X17 X27 (Shiftedreg X30 LSR 26) *)
  0x2eb28140;       (* arm_UMLAL_VEC Q0 Q10 Q18 32 *)
  0x9bab71f0;       (* arm_UMADDL X16 W15 W11 X28 *)
  0x2eb780c0;       (* arm_UMLAL_VEC Q0 Q6 Q23 32 *)
  0x8b5167a1;       (* arm_ADD X1 X29 (Shiftedreg X17 LSR 25) *)
  0x2ea18219;       (* arm_UMLAL_VEC Q25 Q16 Q1 32 *)
  0x9ba47e6b;       (* arm_UMULL X11 W19 W4 *)
  0xf94053e8;       (* arm_LDR X8 SP (Immediate_Offset (word 160)) *)
  0x0ebf9dda;       (* arm_MUL_VEC Q26 Q14 Q31 32 64 *)
  0x2ea18151;       (* arm_UMLAL_VEC Q17 Q10 Q1 32 *)
  0xf9404bef;       (* arm_LDR X15 SP (Immediate_Offset (word 144)) *)
  0x2eb480d1;       (* arm_UMLAL_VEC Q17 Q6 Q20 32 *)
  0x924067c9;       (* arm_AND X9 X30 (rvalue (word 67108863)) *)
  0xb3606229;       (* arm_BFM X9 X17 32 24 *)
  0x8b020051;       (* arm_ADD X17 X2 X2 *)
  0xd360fdea;       (* arm_LSR X10 X15 32 *)
  0x8b416b3b;       (* arm_ADD X27 X25 (Shiftedreg X1 LSR 26) *)
  0x2eb480f9;       (* arm_UMLAL_VEC Q25 Q7 Q20 32 *)
  0x8b0a014d;       (* arm_ADD X13 X10 X10 *)
  0x2ead8279;       (* arm_UMLAL_VEC Q25 Q19 Q13 32 *)
  0x8b5b66fd;       (* arm_ADD X29 X23 (Shiftedreg X27 LSR 25) *)
  0x2eab81f9;       (* arm_UMLAL_VEC Q25 Q15 Q11 32 *)
  0xd360fd1e;       (* arm_LSR X30 X8 32 *)
  0x2eb28099;       (* arm_UMLAL_VEC Q25 Q4 Q18 32 *)
  0x8b5d68b7;       (* arm_ADD X23 X5 (Shiftedreg X29 LSR 26) *)
  0x2eb78159;       (* arm_UMLAL_VEC Q25 Q10 Q23 32 *)
  0x924067ae;       (* arm_AND X14 X29 (rvalue (word 67108863)) *)
  0x2eba80d9;       (* arm_UMLAL_VEC Q25 Q6 Q26 32 *)
  0x8b576605;       (* arm_ADD X5 X16 (Shiftedreg X23 LSR 25) *)
  0x4f415628;       (* arm_SHL_VEC Q8 Q17 1 64 128 *)
  0x9bb12c4c;       (* arm_UMADDL X12 W2 W17 X11 *)
  0x924064bd;       (* arm_AND X29 X5 (rvalue (word 67108863)) *)
  0x9bb37e75;       (* arm_UMULL X21 W19 W19 *)
  0x2eba80fd;       (* arm_UMLAL_VEC Q29 Q7 Q26 32 *)
  0x0b0a0550;       (* arm_ADD W16 W10 (Shiftedreg W10 LSL 1) *)
  0x2eba8203;       (* arm_UMLAL_VEC Q3 Q16 Q26 32 *)
  0x0b0a1210;       (* arm_ADD W16 W16 (Shiftedreg W10 LSL 4) *)
  0xb36062ee;       (* arm_BFM X14 X23 32 24 *)
  0x0b18070a;       (* arm_ADD W10 W24 (Shiftedreg W24 LSL 1) *)
  0x8b456b56;       (* arm_ADD X22 X26 (Shiftedreg X5 LSR 26) *)
  0x0b18114a;       (* arm_ADD W10 W10 (Shiftedreg W24 LSL 4) *)
  0x2eae8188;       (* arm_UMLAL_VEC Q8 Q12 Q14 32 *)
  0x9bad5619;       (* arm_UMADDL X25 W16 W13 X21 *)
  0x2ead8048;       (* arm_UMLAL_VEC Q8 Q2 Q13 32 *)
  0xb36062dd;       (* arm_BFM X29 X22 32 24 *)
  0x2eab80a8;       (* arm_UMLAL_VEC Q8 Q5 Q11 32 *)
  0x8b18031a;       (* arm_ADD X26 X24 X24 *)
  0x2eb28208;       (* arm_UMLAL_VEC Q8 Q16 Q18 32 *)
  0xa906f7ee;       (* arm_STP X14 X29 SP (Immediate_Offset (iword (&104))) *)
  0x2eb780e8;       (* arm_UMLAL_VEC Q8 Q7 Q23 32 *)
  0x0b1e07d8;       (* arm_ADD W24 W30 (Shiftedreg W30 LSL 1) *)
  0x6f6617b9;       (* arm_USRA_VEC Q25 Q29 26 64 128 *)
  0x0b1e1318;       (* arm_ADD W24 W24 (Shiftedreg W30 LSL 4) *)
  0x9baf7dfd;       (* arm_UMULL X29 W15 W15 *)
  0x2eae805b;       (* arm_UMLAL_VEC Q27 Q2 Q14 32 *)
  0x9bad7de3;       (* arm_UMULL X3 W15 W13 *)
  0x2ead80bb;       (* arm_UMLAL_VEC Q27 Q5 Q13 32 *)
  0x8b140295;       (* arm_ADD X21 X20 X20 *)
  0x2eae81f8;       (* arm_UMLAL_VEC Q24 Q15 Q14 32 *)
  0x9bb57e65;       (* arm_UMULL X5 W19 W21 *)
  0x2ead8098;       (* arm_UMLAL_VEC Q24 Q4 Q13 32 *)
  0x9240642b;       (* arm_AND X11 X1 (rvalue (word 67108863)) *)
  0x6f671728;       (* arm_USRA_VEC Q8 Q25 25 64 128 *)
  0x92406001;       (* arm_AND X1 X0 (rvalue (word 33554431)) *)
  0x2eab821b;       (* arm_UMLAL_VEC Q27 Q16 Q11 32 *)
  0x9bad1637;       (* arm_UMADDL X23 W17 W13 X5 *)
  0x2eb280fb;       (* arm_UMLAL_VEC Q27 Q7 Q18 32 *)
  0x8b1e03c5;       (* arm_ADD X5 X30 X30 *)
  0x6f661500;       (* arm_USRA_VEC Q0 Q8 26 64 128 *)
  0x8b0f01e0;       (* arm_ADD X0 X15 X15 *)
  0x2eab8158;       (* arm_UMLAL_VEC Q24 Q10 Q11 32 *)
  0x9ba05cf7;       (* arm_UMADDL X23 W7 W0 X23 *)
  0x2eb280d8;       (* arm_UMLAL_VEC Q24 Q6 Q18 32 *)
  0xd360fcfe;       (* arm_LSR X30 X7 32 *)
  0x6f67141b;       (* arm_USRA_VEC Q27 Q0 25 64 128 *)
  0x8b1e03d0;       (* arm_ADD X16 X30 X30 *)
  0x4e3e1d14;       (* arm_AND_VEC Q20 Q8 Q30 128 *)
  0x9bb05fcf;       (* arm_UMADDL X15 W30 W16 X23 *)
  0x6f7f07d7;       (* arm_USHR_VEC Q23 Q30 1 64 128 *)
  0x0b080517;       (* arm_ADD W23 W8 (Shiftedreg W8 LSL 1) *)
  0x6f661778;       (* arm_USRA_VEC Q24 Q27 26 64 128 *)
  0x0b0812f7;       (* arm_ADD W23 W23 (Shiftedreg W8 LSL 4) *)
  0x9ba50e6e;       (* arm_UMADDL X14 W19 W5 X3 *)
  0x4e3e1f68;       (* arm_AND_VEC Q8 Q27 Q30 128 *)
  0x8b08011c;       (* arm_ADD X28 X8 X8 *)
  0x4e371c1b;       (* arm_AND_VEC Q27 Q0 Q23 128 *)
  0x9bb73d08;       (* arm_UMADDL X8 W8 W23 X15 *)
  0x4e371f05;       (* arm_AND_VEC Q5 Q24 Q23 128 *)
  0x9bbc3843;       (* arm_UMADDL X3 W2 W28 X14 *)
  0x2ebc81f6;       (* arm_UMLAL_VEC Q22 Q15 Q28 32 *)
  0xb360636b;       (* arm_BFM X11 X27 32 24 *)
  0x4e851905;       (* arm_UZP1 Q5 Q8 Q5 32 *)
  0x9ba5770e;       (* arm_UMADDL X14 W24 W5 X29 *)
  0x9bbc3a65;       (* arm_UMADDL X5 W19 W28 X14 *)
  0xfd4027f2;       (* arm_LDR D18 SP (Immediate_Offset (word 72)) *)
  0x6e180652;       (* arm_INS Q18 Q18 64 0 64 64 *)
  0x9bba0cef;       (* arm_UMADDL X15 W7 W26 X3 *)
  0x0ebf9dac;       (* arm_MUL_VEC Q12 Q13 Q31 32 64 *)
  0x2ead8215;       (* arm_UMLAL_VEC Q21 Q16 Q13 32 *)
  0xa905afe9;       (* arm_STP X9 X11 SP (Immediate_Offset (iword (&88))) *)
  0x2eab80f5;       (* arm_UMLAL_VEC Q21 Q7 Q11 32 *)
  0x9bba163d;       (* arm_UMADDL X29 W17 W26 X5 *)
  0x2eae8096;       (* arm_UMLAL_VEC Q22 Q4 Q14 32 *)
  0x0b14068e;       (* arm_ADD W14 W20 (Shiftedreg W20 LSL 1) *)
  0x2ead8156;       (* arm_UMLAL_VEC Q22 Q10 Q13 32 *)
  0x0b1411ce;       (* arm_ADD W14 W14 (Shiftedreg W20 LSL 4) *)
  0x9ba07e63;       (* arm_UMULL X3 W19 W0 *)
  0x2eab80d6;       (* arm_UMLAL_VEC Q22 Q6 Q11 32 *)
  0x9bb574fd;       (* arm_UMADDL X29 W7 W21 X29 *)
  0x6f671715;       (* arm_USRA_VEC Q21 Q24 25 64 128 *)
  0x9bae328b;       (* arm_UMADDL X11 W20 W14 X12 *)
  0x4e371f20;       (* arm_AND_VEC Q0 Q25 Q23 128 *)
  0x9bb53fc5;       (* arm_UMADDL X5 W30 W21 X15 *)
  0x4e3e1fae;       (* arm_AND_VEC Q14 Q29 Q30 128 *)
  0x9bad760c;       (* arm_UMADDL X12 W16 W13 X29 *)
  0x6f6616b6;       (* arm_USRA_VEC Q22 Q21 26 64 128 *)
  0x9bb00e3d;       (* arm_UMADDL X29 W17 W16 X3 *)
  0x2eac80e3;       (* arm_UMLAL_VEC Q3 Q7 Q12 32 *)
  0x8b1a0349;       (* arm_ADD X9 X26 X26 *)
  0x4e3e1ea1;       (* arm_AND_VEC Q1 Q21 Q30 128 *)
  0x8b4c68bb;       (* arm_ADD X27 X5 (Shiftedreg X12 LSR 26) *)
  0x4e771ec8;       (* arm_BIC_VEC Q8 Q22 Q23 128 *)
  0x9ba774fd;       (* arm_UMADDL X29 W7 W7 X29 *)
  0x4e371ed1;       (* arm_AND_VEC Q17 Q22 Q23 128 *)
  0x8b5b6725;       (* arm_ADD X5 X25 (Shiftedreg X27 LSR 25) *)
  0x6f671503;       (* arm_USRA_VEC Q3 Q8 25 64 128 *)
  0x9ba92319;       (* arm_UMADDL X25 W24 W9 X8 *)
  0x2eba8149;       (* arm_UMLAL_VEC Q9 Q10 Q26 32 *)
  0x8b0d01a8;       (* arm_ADD X8 X13 X13 *)
  0x4e912836;       (* arm_TRN1 Q22 Q1 Q17 32 128 *)
  0x9ba82d4b;       (* arm_UMADDL X11 W10 W8 X11 *)
  0x6f681503;       (* arm_USRA_VEC Q3 Q8 24 64 128 *)
  0x9bb07e74;       (* arm_UMULL X20 W19 W16 *)
  0x0eb286da;       (* arm_ADD_VEC Q26 Q22 Q18 32 64 *)
  0xfd402bfc;       (* arm_LDR D28 SP (Immediate_Offset (word 80)) *)
  0x2eac80c9;       (* arm_UMLAL_VEC Q9 Q6 Q12 32 *)
  0x9ba02ee3;       (* arm_UMADDL X3 W23 W0 X11 *)
  0x6f6b1503;       (* arm_USRA_VEC Q3 Q8 21 64 128 *)
  0x9bba755d;       (* arm_UMADDL X29 W10 W26 X29 *)
  0x4e9b1a8b;       (* arm_UZP1 Q11 Q20 Q27 32 *)
  0x9ba45054;       (* arm_UMADDL X20 W2 W4 X20 *)
  0x9bb55149;       (* arm_UMADDL X9 W10 W21 X20 *)
  0x6e0846d1;       (* arm_INS Q17 Q22 0 64 64 128 *)
  0x6f661469;       (* arm_USRA_VEC Q9 Q3 26 64 128 *)
  0x9bad7e6f;       (* arm_UMULL X15 W19 W13 *)
  0x4e3e1c67;       (* arm_AND_VEC Q7 Q3 Q30 128 *)
  0x8b10020b;       (* arm_ADD X11 X16 X16 *)
  0x4e855961;       (* arm_UZP2 Q1 Q11 Q5 32 *)
  0x9bad26f4;       (* arm_UMADDL X20 W23 W13 X9 *)
  0x4e371d28;       (* arm_AND_VEC Q8 Q9 Q23 128 *)
  0x9ba03c49;       (* arm_UMADDL X9 W2 W0 X15 *)
  0x6f67152e;       (* arm_USRA_VEC Q14 Q9 25 64 128 *)
  0x924064c6;       (* arm_AND X6 X6 (rvalue (word 67108863)) *)
  0x4e8818e7;       (* arm_UZP1 Q7 Q7 Q8 32 *)
  0x9bb576fd;       (* arm_UMADDL X29 W23 W21 X29 *)
  0x4e85197b;       (* arm_UZP1 Q27 Q11 Q5 32 *)
  0x9bba7e6f;       (* arm_UMULL X15 W19 W26 *)
  0x6f6615c0;       (* arm_USRA_VEC Q0 Q14 26 64 128 *)
  0x8b5664c6;       (* arm_ADD X6 X6 (Shiftedreg X22 LSR 25) *)
  0x4e3e1dc3;       (* arm_AND_VEC Q3 Q14 Q30 128 *)
  0x92679b76;       (* arm_AND X22 X27 (rvalue (word 18446744073675997184)) *)
  0x2eb18742;       (* arm_SUB_VEC Q2 Q26 Q17 32 64 *)
  0x0eb186c9;       (* arm_ADD_VEC Q9 Q22 Q17 32 64 *)
  0x4e80186e;       (* arm_UZP1 Q14 Q3 Q0 32 *)
  0x9bb53c42;       (* arm_UMADDL X2 W2 W21 X15 *)
  0x4eb28765;       (* arm_ADD_VEC Q5 Q27 Q18 32 128 *)
  0x8b5660a5;       (* arm_ADD X5 X5 (Shiftedreg X22 LSR 24) *)
  0x0e893856;       (* arm_ZIP1 Q22 Q2 Q9 32 64 *)
  0x6e010792;       (* arm_INS Q18 Q28 0 0 8 64 *)
  0x4e8e18e8;       (* arm_UZP1 Q8 Q7 Q14 32 *)
  0x8b5654b6;       (* arm_ADD X22 X5 (Shiftedreg X22 LSR 21) *)
  0x4e8e58e3;       (* arm_UZP2 Q3 Q7 Q14 32 *)
  0x9bb024e5;       (* arm_UMADDL X5 W7 W16 X9 *)
  0x4eb28519;       (* arm_ADD_VEC Q25 Q8 Q18 32 128 *)
  0x9ba059cf;       (* arm_UMADDL X15 W14 W0 X22 *)
  0x4ea1876c;       (* arm_ADD_VEC Q12 Q27 Q1 32 128 *)
  0x8b110229;       (* arm_ADD X9 X17 X17 *)
  0x6ea184ae;       (* arm_SUB_VEC Q14 Q5 Q1 32 128 *)
  0x9bb17e73;       (* arm_UMULL X19 W19 W17 *)
  0x6ea38732;       (* arm_SUB_VEC Q18 Q25 Q3 32 128 *)
  0xf94033f6;       (* arm_LDR X22 SP (Immediate_Offset (word 96)) *)
  0x4ea38514;       (* arm_ADD_VEC Q20 Q8 Q3 32 128 *)
  0x9bab3d4f;       (* arm_UMADDL X15 W10 W11 X15 *)
  0x4e8c39d0;       (* arm_ZIP1 Q16 Q14 Q12 32 128 *)
  0x9bad4dce;       (* arm_UMADDL X14 W14 W13 X19 *)
  0x4e8c79ce;       (* arm_ZIP2 Q14 Q14 Q12 32 128 *)
  0x92406371;       (* arm_AND X17 X27 (rvalue (word 33554431)) *)
  0x4e947a40;       (* arm_ZIP2 Q0 Q18 Q20 32 128 *)
  0x9ba43eef;       (* arm_UMADDL X15 W23 W4 X15 *)
  0x4e943a41;       (* arm_ZIP1 Q1 Q18 Q20 32 128 *)
  0x9ba0394a;       (* arm_UMADDL X10 W10 W0 X14 *)
  0x0e897845;       (* arm_ZIP2 Q5 Q2 Q9 32 64 *)
  0x0f215418;       (* arm_SHL_VEC Q24 Q0 1 32 64 *)
  0x6e084433;       (* arm_INS Q19 Q1 0 64 64 128 *)
  0x0f2156da;       (* arm_SHL_VEC Q26 Q22 1 32 64 *)
  0x0f215611;       (* arm_SHL_VEC Q17 Q16 1 32 64 *)
  0x6e08440f;       (* arm_INS Q15 Q0 0 64 64 128 *)
  0x0f2154a7;       (* arm_SHL_VEC Q7 Q5 1 32 64 *)
  0x0f215672;       (* arm_SHL_VEC Q18 Q19 1 32 64 *)
  0x2eb8c02b;       (* arm_UMULL_VEC Q11 Q1 Q24 32 *)
  0x9bb02af3;       (* arm_UMADDL X19 W23 W16 X10 *)
  0x2eb1c026;       (* arm_UMULL_VEC Q6 Q1 Q17 32 *)
  0x9bad08ea;       (* arm_UMADDL X10 W7 W13 X2 *)
  0x6e084604;       (* arm_INS Q4 Q16 0 64 64 128 *)
  0x6e0845ca;       (* arm_INS Q10 Q14 0 64 64 128 *)
  0x2ebac029;       (* arm_UMULL_VEC Q9 Q1 Q26 32 *)
  0xf9402fed;       (* arm_LDR X13 SP (Immediate_Offset (word 88)) *)
  0x0f2155fc;       (* arm_SHL_VEC Q28 Q15 1 32 64 *)
  0x0f215543;       (* arm_SHL_VEC Q3 Q10 1 32 64 *)
  0xf94037ee;       (* arm_LDR X14 SP (Immediate_Offset (word 104)) *)
  0x0ebf9d4c;       (* arm_MUL_VEC Q12 Q10 Q31 32 64 *)
  0x2ea7c039;       (* arm_UMULL_VEC Q25 Q1 Q7 32 *)
  0xf9403be2;       (* arm_LDR X2 SP (Immediate_Offset (word 112)) *)
  0x2ebc8246;       (* arm_UMLAL_VEC Q6 Q18 Q28 32 *)
  0x9ba02bdb;       (* arm_UMADDL X27 W30 W0 X10 *)
  0x9ba05310;       (* arm_UMADDL X16 W24 W0 X20 *)
  0x0f2155cd;       (* arm_SHL_VEC Q13 Q14 1 32 64 *)
  0x9bba16e5;       (* arm_UMADDL X5 W23 W26 X5 *)
  0x0ebf9ec2;       (* arm_MUL_VEC Q2 Q22 Q31 32 64 *)
  0x2eadc035;       (* arm_UMULL_VEC Q21 Q1 Q13 32 *)
  0x9ba87717;       (* arm_UMADDL X23 W24 W8 X29 *)
  0x2eb3824b;       (* arm_UMLAL_VEC Q11 Q18 Q19 32 *)
  0xb21f67ea;       (* arm_MOV X10 (rvalue (word 576460743847706622)) *)
  0xd100094a;       (* arm_SUB X10 X10 (rvalue (word 2)) *)
  0x9bb5171a;       (* arm_UMADDL X26 W24 W21 X5 *)
  0x0ebf9ddd;       (* arm_MUL_VEC Q29 Q14 Q31 32 64 *)
  0x2eba8279;       (* arm_UMLAL_VEC Q25 Q19 Q26 32 *)
  0x8b466827;       (* arm_ADD X7 X1 (Shiftedreg X6 LSR 26) *)
  0x0ebf9c94;       (* arm_MUL_VEC Q20 Q4 Q31 32 64 *)
  0x924064c6;       (* arm_AND X6 X6 (rvalue (word 67108863)) *)
  0x0f215648;       (* arm_SHL_VEC Q8 Q18 1 32 64 *)
  0x0f215484;       (* arm_SHL_VEC Q4 Q4 1 32 64 *)
  0x2eae83ab;       (* arm_UMLAL_VEC Q11 Q29 Q14 32 *)
  0xb36064e6;       (* arm_BFM X6 X7 32 25 *)
  0x2ea38019;       (* arm_UMLAL_VEC Q25 Q0 Q3 32 *)
  0x9ba44f00;       (* arm_UMADDL X0 W24 W4 X19 *)
  0x2ead81f9;       (* arm_UMLAL_VEC Q25 Q15 Q13 32 *)
  0xf9003fe6;       (* arm_STR X6 SP (Immediate_Offset (word 120)) *)
  0x2ea48255;       (* arm_UMLAL_VEC Q21 Q18 Q4 32 *)
  0x9bab0f08;       (* arm_UMADDL X8 W24 W11 X3 *)
  0x2eb18015;       (* arm_UMLAL_VEC Q21 Q0 Q17 32 *)
  0xf9403ffe;       (* arm_LDR X30 SP (Immediate_Offset (word 120)) *)
  0x0ebf9cae;       (* arm_MUL_VEC Q14 Q5 Q31 32 64 *)
  0x8b0a0042;       (* arm_ADD X2 X2 X10 *)
  0x0f215785;       (* arm_SHL_VEC Q5 Q28 1 32 64 *)
  0x0f21549b;       (* arm_SHL_VEC Q27 Q4 1 32 64 *)
  0x2ea08006;       (* arm_UMLAL_VEC Q6 Q0 Q0 32 *)
  0x9ba93f0b;       (* arm_UMADDL X11 W24 W9 X15 *)
  0x2ea38186;       (* arm_UMLAL_VEC Q6 Q12 Q3 32 *)
  0x8b0a03c4;       (* arm_ADD X4 X30 X10 *)
  0x2ea581cb;       (* arm_UMLAL_VEC Q11 Q14 Q5 32 *)
  0x8b0a02c3;       (* arm_ADD X3 X22 X10 *)
  0x2eb1804b;       (* arm_UMLAL_VEC Q11 Q2 Q17 32 *)
  0x8b4b6806;       (* arm_ADD X6 X0 (Shiftedreg X11 LSR 26) *)
  0x2ebb818b;       (* arm_UMLAL_VEC Q11 Q12 Q27 32 *)
  0x8b0a01ce;       (* arm_ADD X14 X14 X10 *)
  0x2ebb81c6;       (* arm_UMLAL_VEC Q6 Q14 Q27 32 *)
  0x8b466508;       (* arm_ADD X8 X8 (Shiftedreg X6 LSR 25) *)
  0x2ead8046;       (* arm_UMLAL_VEC Q6 Q2 Q13 32 *)
  0xf29ff68a;       (* arm_MOVK X10 (word 65460) 0 *)
  0x2ea48219;       (* arm_UMLAL_VEC Q25 Q16 Q4 32 *)
  0x8b486a1d;       (* arm_ADD X29 X16 (Shiftedreg X8 LSR 26) *)
  0x2ea3c03b;       (* arm_UMULL_VEC Q27 Q1 Q3 32 *)
  0x9240656b;       (* arm_AND X11 X11 (rvalue (word 67108863)) *)
  0x2ea38249;       (* arm_UMLAL_VEC Q9 Q18 Q3 32 *)
  0x8b0a01b3;       (* arm_ADD X19 X13 X10 *)
  0x2ead8009;       (* arm_UMLAL_VEC Q9 Q0 Q13 32 *)
  0x92406505;       (* arm_AND X5 X8 (rvalue (word 67108863)) *)
  0x2ea48389;       (* arm_UMLAL_VEC Q9 Q28 Q4 32 *)
  0xb36060cb;       (* arm_BFM X11 X6 32 24 *)
  0x2eb08209;       (* arm_UMLAL_VEC Q9 Q16 Q16 32 *)
  0x9bbc6f1e;       (* arm_UMADDL X30 W24 W28 X27 *)
  0x2ea781c9;       (* arm_UMLAL_VEC Q9 Q14 Q7 32 *)
  0xcb0b026d;       (* arm_SUB X13 X19 X11 *)
  0x2eb2c02a;       (* arm_UMULL_VEC Q10 Q1 Q18 32 *)
  0x8b5d66e7;       (* arm_ADD X7 X23 (Shiftedreg X29 LSR 25) *)
  0x2eaf8395;       (* arm_UMLAL_VEC Q21 Q28 Q15 32 *)
  0xd360fdb0;       (* arm_LSR X16 X13 32 *)
  0x2eb68055;       (* arm_UMLAL_VEC Q21 Q2 Q22 32 *)
  0x8b476b40;       (* arm_ADD X0 X26 (Shiftedreg X7 LSR 26) *)
  0x6f661539;       (* arm_USRA_VEC Q25 Q9 26 64 128 *)
  0x924064f4;       (* arm_AND X20 X7 (rvalue (word 67108863)) *)
  0x2ea1c036;       (* arm_UMULL_VEC Q22 Q1 Q1 32 *)
  0x8b406728;       (* arm_ADD X8 X25 (Shiftedreg X0 LSR 25) *)
  0x2ebcc027;       (* arm_UMULL_VEC Q7 Q1 Q28 32 *)
  0x924063a1;       (* arm_AND X1 X29 (rvalue (word 33554431)) *)
  0x4e771f32;       (* arm_BIC_VEC Q18 Q25 Q23 128 *)
  0x92406513;       (* arm_AND X19 X8 (rvalue (word 67108863)) *)
  0x4e3e1d30;       (* arm_AND_VEC Q16 Q9 Q30 128 *)
  0x92406587;       (* arm_AND X7 X12 (rvalue (word 67108863)) *)
  0x6f671656;       (* arm_USRA_VEC Q22 Q18 25 64 128 *)
  0x8b486bca;       (* arm_ADD X10 X30 (Shiftedreg X8 LSR 26) *)
  0x2eb88267;       (* arm_UMLAL_VEC Q7 Q19 Q24 32 *)
  0xb36063a5;       (* arm_BFM X5 X29 32 24 *)
  0x4e371f29;       (* arm_AND_VEC Q9 Q25 Q23 128 *)
  0x8b4a64fb;       (* arm_ADD X27 X7 (Shiftedreg X10 LSR 25) *)
  0x6f681656;       (* arm_USRA_VEC Q22 Q18 24 64 128 *)
  0xd29db435;       (* arm_MOV X21 (rvalue (word 60833)) *)
  0xd37ffab5;       (* arm_LSL X21 X21 1 *)
  0x8b5b6a2f;       (* arm_ADD X15 X17 (Shiftedreg X27 LSR 26) *)
  0x0f215479;       (* arm_SHL_VEC Q25 Q3 1 32 64 *)
  0x2eb181c7;       (* arm_UMLAL_VEC Q7 Q14 Q17 32 *)
  0x9240677d;       (* arm_AND X29 X27 (rvalue (word 67108863)) *)
  0x6f6b1656;       (* arm_USRA_VEC Q22 Q18 21 64 128 *)
  0xb36065fd;       (* arm_BFM X29 X15 32 25 *)
  0x2eb881ca;       (* arm_UMLAL_VEC Q10 Q14 Q24 32 *)
  0x924060d1;       (* arm_AND X17 X6 (rvalue (word 33554431)) *)
  0x2ebc804a;       (* arm_UMLAL_VEC Q10 Q2 Q28 32 *)
  0xcb050066;       (* arm_SUB X6 X3 X5 *)
  0x2eb1818a;       (* arm_UMLAL_VEC Q10 Q12 Q17 32 *)
  0x9bb54619;       (* arm_UMADDL X25 W16 W21 X17 *)
  0x2ea483aa;       (* arm_UMLAL_VEC Q10 Q29 Q4 32 *)
  0x2a0503ec;       (* arm_MOV W12 W5 *)
  0x2ea48296;       (* arm_UMLAL_VEC Q22 Q20 Q4 32 *)
  0xd360fcda;       (* arm_LSR X26 X6 32 *)
  0x2ea881d6;       (* arm_UMLAL_VEC Q22 Q14 Q8 32 *)
  0x92406018;       (* arm_AND X24 X0 (rvalue (word 33554431)) *)
  0x2eb88056;       (* arm_UMLAL_VEC Q22 Q2 Q24 32 *)
  0xa90817eb;       (* arm_STP X11 X5 SP (Immediate_Offset (iword (&128))) *)
  0x2ea58196;       (* arm_UMLAL_VEC Q22 Q12 Q5 32 *)
  0xb3606014;       (* arm_BFM X20 X0 32 24 *)
  0x2eb183b6;       (* arm_UMLAL_VEC Q22 Q29 Q17 32 *)
  0x9bb530cc;       (* arm_UMADDL X12 W6 W21 X12 *)
  0x2ea4c032;       (* arm_UMULL_VEC Q18 Q1 Q4 32 *)
  0xb3606153;       (* arm_BFM X19 X10 32 24 *)
  0x2ea48047;       (* arm_UMLAL_VEC Q7 Q2 Q4 32 *)
  0xcb1401c7;       (* arm_SUB X7 X14 X20 *)
  0x2ead827b;       (* arm_UMLAL_VEC Q27 Q19 Q13 32 *)
  0x2a1403e8;       (* arm_MOV W8 W20 *)
  0x6f6616ca;       (* arm_USRA_VEC Q10 Q22 26 64 128 *)
  0xd360fcee;       (* arm_LSR X14 X7 32 *)
  0x2eb18272;       (* arm_UMLAL_VEC Q18 Q19 Q17 32 *)
  0x9240615c;       (* arm_AND X28 X10 (rvalue (word 33554431)) *)
  0x2ead8187;       (* arm_UMLAL_VEC Q7 Q12 Q13 32 *)
  0xcb130045;       (* arm_SUB X5 X2 X19 *)
  0x6f67154b;       (* arm_USRA_VEC Q11 Q10 25 64 128 *)
  0x2a1303e2;       (* arm_MOV W2 W19 *)
  0x2ea4801b;       (* arm_UMLAL_VEC Q27 Q0 Q4 32 *)
  0x2eb981d5;       (* arm_UMLAL_VEC Q21 Q14 Q25 32 *)
  0xcb1d0097;       (* arm_SUB X23 X4 X29 *)
  0x6f661567;       (* arm_USRA_VEC Q7 Q11 26 64 128 *)
  0x2a1d03e0;       (* arm_MOV W0 W29 *)
  0x2ebc8012;       (* arm_UMLAL_VEC Q18 Q0 Q28 32 *)
  0xd360fef6;       (* arm_LSR X22 X23 32 *)
  0x2eb181fb;       (* arm_UMLAL_VEC Q27 Q15 Q17 32 *)
  0xf90053fd;       (* arm_STR X29 SP (Immediate_Offset (word 160)) *)
  0x6f6714e6;       (* arm_USRA_VEC Q6 Q7 25 64 128 *)
  0x2a0b03f1;       (* arm_MOV W17 W11 *)
  0x4e3e1ec0;       (* arm_AND_VEC Q0 Q22 Q30 128 *)
  0x9bb5075b;       (* arm_UMADDL X27 W26 W21 X1 *)
  0x2ead81d2;       (* arm_UMLAL_VEC Q18 Q14 Q13 32 *)
  0x9bb502fe;       (* arm_UMADDL X30 W23 W21 X0 *)
  0x2ea38052;       (* arm_UMLAL_VEC Q18 Q2 Q3 32 *)
  0xd360fcaa;       (* arm_LSR X10 X5 32 *)
  0x4e3e1cc4;       (* arm_AND_VEC Q4 Q6 Q30 128 *)
  0x4e371d41;       (* arm_AND_VEC Q1 Q10 Q23 128 *)
  0x9bb561c4;       (* arm_UMADDL X4 W14 W21 X24 *)
  0xf9402fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 88)) *)
  0x4e0c1c00;       (* arm_INS_GEN Q0 W0 32 32 *)
  0xd360fc00;       (* arm_LSR X0 X0 32 *)
  0x4e0c1c01;       (* arm_INS_GEN Q1 W0 32 32 *)
  0x9bb520e9;       (* arm_UMADDL X9 W7 W21 X8 *)
  0x6f6614d2;       (* arm_USRA_VEC Q18 Q6 26 64 128 *)
  0x9bb57158;       (* arm_UMADDL X24 W10 W21 X28 *)
  0x4e371ce3;       (* arm_AND_VEC Q3 Q7 Q23 128 *)
  0x9bb53ec8;       (* arm_UMADDL X8 W22 W21 X15 *)
  0x2eba81db;       (* arm_UMLAL_VEC Q27 Q14 Q26 32 *)
  0x9bb545af;       (* arm_UMADDL X15 W13 W21 X17 *)
  0x6f671655;       (* arm_USRA_VEC Q21 Q18 25 64 128 *)
  0xa9094ff4;       (* arm_STP X20 X19 SP (Immediate_Offset (iword (&144))) *)
  0x4e3e1d62;       (* arm_AND_VEC Q2 Q11 Q30 128 *)
  0xd359fd1d;       (* arm_LSR X29 X8 25 *)
  0xf94043e3;       (* arm_LDR X3 SP (Immediate_Offset (word 128)) *)
  0x4e0c1c6a;       (* arm_INS_GEN Q10 W3 32 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0x4e0c1c6b;       (* arm_INS_GEN Q11 W3 32 32 *)
  0x8b1d01f1;       (* arm_ADD X17 X15 X29 *)
  0x6f6616bb;       (* arm_USRA_VEC Q27 Q21 26 64 128 *)
  0x8b1d063c;       (* arm_ADD X28 X17 (Shiftedreg X29 LSL 1) *)
  0x4e3e1ea6;       (* arm_AND_VEC Q6 Q21 Q30 128 *)
  0x92406114;       (* arm_AND X20 X8 (rvalue (word 33554431)) *)
  0x4e371e45;       (* arm_AND_VEC Q5 Q18 Q23 128 *)
  0x8b1d1391;       (* arm_ADD X17 X28 (Shiftedreg X29 LSL 4) *)
  0x4e371f67;       (* arm_AND_VEC Q7 Q27 Q23 128 *)
  0xf94047e3;       (* arm_LDR X3 SP (Immediate_Offset (word 136)) *)
  0x4e0c1c76;       (* arm_INS_GEN Q22 W3 32 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0x4e0c1c77;       (* arm_INS_GEN Q23 W3 32 32 *)
  0x8b516b3d;       (* arm_ADD X29 X25 (Shiftedreg X17 LSR 26) *)
  0xf94013ef;       (* arm_LDR X15 SP (Immediate_Offset (word 32)) *)
  0x4e041dea;       (* arm_INS_GEN Q10 W15 0 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x4e041deb;       (* arm_INS_GEN Q11 W15 0 32 *)
  0x9240662b;       (* arm_AND X11 X17 (rvalue (word 67108863)) *)
  0x6f671770;       (* arm_USRA_VEC Q16 Q27 25 64 128 *)
  0x8b5d6588;       (* arm_ADD X8 X12 (Shiftedreg X29 LSR 25) *)
  0xf9404be3;       (* arm_LDR X3 SP (Immediate_Offset (word 144)) *)
  0x4e0c1c6e;       (* arm_INS_GEN Q14 W3 32 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0x4e0c1c6f;       (* arm_INS_GEN Q15 W3 32 32 *)
  0x924063ac;       (* arm_AND X12 X29 (rvalue (word 33554431)) *)
  0xf94017ef;       (* arm_LDR X15 SP (Immediate_Offset (word 40)) *)
  0x4e041df6;       (* arm_INS_GEN Q22 W15 0 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x4e041df7;       (* arm_INS_GEN Q23 W15 0 32 *)
  0x8b486b7c;       (* arm_ADD X28 X27 (Shiftedreg X8 LSR 26) *)
  0x4e3e1e08;       (* arm_AND_VEC Q8 Q16 Q30 128 *)
  0x9baa7d81;       (* arm_UMULL X1 W12 W10 *)
  0xf9404fe3;       (* arm_LDR X3 SP (Immediate_Offset (word 152)) *)
  0x4e0c1c71;       (* arm_INS_GEN Q17 W3 32 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0x4e0c1c72;       (* arm_INS_GEN Q18 W3 32 32 *)
  0x8b5c6539;       (* arm_ADD X25 X9 (Shiftedreg X28 LSR 25) *)
  0xf9401bef;       (* arm_LDR X15 SP (Immediate_Offset (word 48)) *)
  0x4e041dee;       (* arm_INS_GEN Q14 W15 0 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x4e041def;       (* arm_INS_GEN Q15 W15 0 32 *)
  0x9bb508b3;       (* arm_UMADDL X19 W5 W21 X2 *)
  0x6f661609;       (* arm_USRA_VEC Q9 Q16 26 64 128 *)
  0x8b596882;       (* arm_ADD X2 X4 (Shiftedreg X25 LSR 26) *)
  0xf94053e3;       (* arm_LDR X3 SP (Immediate_Offset (word 160)) *)
  0x4e0c1c78;       (* arm_INS_GEN Q24 W3 32 32 *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0x4e0c1c79;       (* arm_INS_GEN Q25 W3 32 32 *)
  0x9bb77d83;       (* arm_UMULL X3 W12 W23 *)
  0xf9401fef;       (* arm_LDR X15 SP (Immediate_Offset (word 56)) *)
  0x4e041df1;       (* arm_INS_GEN Q17 W15 0 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x4e041df2;       (* arm_INS_GEN Q18 W15 0 32 *)
  0x8b42667d;       (* arm_ADD X29 X19 (Shiftedreg X2 LSR 25) *)
  0x2eb7c01a;       (* arm_UMULL_VEC Q26 Q0 Q23 32 *)
  0x92406395;       (* arm_AND X21 X28 (rvalue (word 33554431)) *)
  0xf94033e0;       (* arm_LDR X0 SP (Immediate_Offset (word 96)) *)
  0x4e0c1c02;       (* arm_INS_GEN Q2 W0 32 32 *)
  0xd360fc00;       (* arm_LSR X0 X0 32 *)
  0x4e0c1c03;       (* arm_INS_GEN Q3 W0 32 32 *)
  0x9ba50ebb;       (* arm_UMADDL X27 W21 W5 X3 *)
  0xf94023ef;       (* arm_LDR X15 SP (Immediate_Offset (word 64)) *)
  0x4e041df8;       (* arm_INS_GEN Q24 W15 0 32 *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x4e041df9;       (* arm_INS_GEN Q25 W15 0 32 *)
  0x8b5d6b11;       (* arm_ADD X17 X24 (Shiftedreg X29 LSR 26) *)
  0x2eb2c03d;       (* arm_UMULL_VEC Q29 Q1 Q18 32 *)
  0x9240650f;       (* arm_AND X15 X8 (rvalue (word 67108863)) *)
  0x2eafc014;       (* arm_UMULL_VEC Q20 Q0 Q15 32 *)
  0x8b5167d3;       (* arm_ADD X19 X30 (Shiftedreg X17 LSR 25) *)
  0x92406223;       (* arm_AND X3 X17 (rvalue (word 33554431)) *)
  0x0ebf9f2c;       (* arm_MUL_VEC Q12 Q25 Q31 32 64 *)
  0xf94037e0;       (* arm_LDR X0 SP (Immediate_Offset (word 104)) *)
  0x4e0c1c04;       (* arm_INS_GEN Q4 W0 32 32 *)
  0xd360fc00;       (* arm_LSR X0 X0 32 *)
  0x4e0c1c05;       (* arm_INS_GEN Q5 W0 32 32 *)
  0x8b536a84;       (* arm_ADD X4 X20 (Shiftedreg X19 LSR 26) *)
  0x2eab805a;       (* arm_UMLAL_VEC Q26 Q2 Q11 32 *)
  0x0b03047c;       (* arm_ADD W28 W3 (Shiftedreg W3 LSL 1) *)
  0x2eb78054;       (* arm_UMLAL_VEC Q20 Q2 Q23 32 *)
  0x0b03139c;       (* arm_ADD W28 W28 (Shiftedreg W3 LSL 4) *)
  0x9ba57d88;       (* arm_UMULL X8 W12 W5 *)
  0xf9403be0;       (* arm_LDR X0 SP (Immediate_Offset (word 112)) *)
  0x4e0c1c06;       (* arm_INS_GEN Q6 W0 32 32 *)
  0xd360fc00;       (* arm_LSR X0 X0 32 *)
  0x4e0c1c07;       (* arm_INS_GEN Q7 W0 32 32 *)
  0x9240673e;       (* arm_AND X30 X25 (rvalue (word 67108863)) *)
  0x0ebf9e50;       (* arm_MUL_VEC Q16 Q18 Q31 32 64 *)
  0x0b040491;       (* arm_ADD W17 W4 (Shiftedreg W4 LSL 1) *)
  0x2eafc035;       (* arm_UMULL_VEC Q21 Q1 Q15 32 *)
  0x0b041231;       (* arm_ADD W17 W17 (Shiftedreg W4 LSL 4) *)
  0x9ba722b9;       (* arm_UMADDL X25 W21 W7 X8 *)
  0x2eab8094;       (* arm_UMLAL_VEC Q20 Q4 Q11 32 *)
  0x0b1506a8;       (* arm_ADD W8 W21 (Shiftedreg W21 LSL 1) *)
  0xf9403fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 120)) *)
  0x0b151108;       (* arm_ADD W8 W8 (Shiftedreg W21 LSL 4) *)
  0x4e0c1c08;       (* arm_INS_GEN Q8 W0 32 32 *)
  0xd360fc00;       (* arm_LSR X0 X0 32 *)
  0x4e0c1c09;       (* arm_INS_GEN Q9 W0 32 32 *)
  0x92406042;       (* arm_AND X2 X2 (rvalue (word 33554431)) *)
  0x2eaf807d;       (* arm_UMLAL_VEC Q29 Q3 Q15 32 *)
  0x9ba66458;       (* arm_UMADDL X24 W2 W6 X25 *)
  0x2eb9c00d;       (* arm_UMULL_VEC Q13 Q0 Q25 32 *)
  0x9ba76c59;       (* arm_UMADDL X25 W2 W7 X27 *)
  0x9ba66460;       (* arm_UMADDL X0 W3 W6 X25 *)
  0x0ebf9df3;       (* arm_MUL_VEC Q19 Q15 Q31 32 64 *)
  0x2eb2c01b;       (* arm_UMULL_VEC Q27 Q0 Q18 32 *)
  0x9bad6074;       (* arm_UMADDL X20 W3 W13 X24 *)
  0x2eac80d4;       (* arm_UMLAL_VEC Q20 Q6 Q12 32 *)
  0x9bae06b8;       (* arm_UMADDL X24 W21 W14 X1 *)
  0x2eb2804d;       (* arm_UMLAL_VEC Q13 Q2 Q18 32 *)
  0x9bad0089;       (* arm_UMADDL X9 W4 W13 X0 *)
  0x2eabc019;       (* arm_UMULL_VEC Q25 Q0 Q11 32 *)
  0x9bb75234;       (* arm_UMADDL X20 W17 W23 X20 *)
  0x2eaf805b;       (* arm_UMLAL_VEC Q27 Q2 Q15 32 *)
  0x9bba6040;       (* arm_UMADDL X0 W2 W26 X24 *)
  0x2eabc03c;       (* arm_UMULL_VEC Q28 Q1 Q11 32 *)
  0x9ba57e38;       (* arm_UMULL X24 W17 W5 *)
  0x2eb780bd;       (* arm_UMLAL_VEC Q29 Q5 Q23 32 *)
  0x9bb62569;       (* arm_UMADDL X9 W11 W22 X9 *)
  0x2eaf808d;       (* arm_UMLAL_VEC Q13 Q4 Q15 32 *)
  0x9bb0007b;       (* arm_UMADDL X27 W3 W16 X0 *)
  0x2eb7809b;       (* arm_UMLAL_VEC Q27 Q4 Q23 32 *)
  0x9bae7e20;       (* arm_UMULL X0 W17 W14 *)
  0x2eab80db;       (* arm_UMLAL_VEC Q27 Q6 Q11 32 *)
  0x9bae7d84;       (* arm_UMULL X4 W12 W14 *)
  0x2eac811b;       (* arm_UMLAL_VEC Q27 Q8 Q12 32 *)
  0x9baa5179;       (* arm_UMADDL X25 W11 W10 X20 *)
  0x2eb1803b;       (* arm_UMLAL_VEC Q27 Q1 Q17 32 *)
  0x9baa0380;       (* arm_UMADDL X0 W28 W10 X0 *)
  0x2eb780cd;       (* arm_UMLAL_VEC Q13 Q6 Q23 32 *)
  0x9ba67e23;       (* arm_UMULL X3 W17 W6 *)
  0x2eab810d;       (* arm_UMLAL_VEC Q13 Q8 Q11 32 *)
  0x9bba12a1;       (* arm_UMADDL X1 W21 W26 X4 *)
  0x2eb08114;       (* arm_UMLAL_VEC Q20 Q8 Q16 32 *)
  0x9bad6044;       (* arm_UMADDL X4 W2 W13 X24 *)
  0x2eac807c;       (* arm_UMLAL_VEC Q28 Q3 Q12 32 *)
  0x9ba70f94;       (* arm_UMADDL X20 W28 W7 X3 *)
  0x2eab80fd;       (* arm_UMLAL_VEC Q29 Q7 Q11 32 *)
  0x92406663;       (* arm_AND X3 X19 (rvalue (word 67108863)) *)
  0x2eac813d;       (* arm_UMLAL_VEC Q29 Q9 Q12 32 *)
  0x9bb66e33;       (* arm_UMADDL X19 W17 W22 X27 *)
  0x0b02045b;       (* arm_ADD W27 W2 (Shiftedreg W2 LSL 1) *)
  0x0ebf9f12;       (* arm_MUL_VEC Q18 Q24 Q31 32 64 *)
  0x0b02137b;       (* arm_ADD W27 W27 (Shiftedreg W2 LSL 4) *)
  0x2eb78075;       (* arm_UMLAL_VEC Q21 Q3 Q23 32 *)
  0x9ba77e38;       (* arm_UMULL X24 W17 W7 *)
  0x2eb8802d;       (* arm_UMLAL_VEC Q13 Q1 Q24 32 *)
  0x8b130273;       (* arm_ADD X19 X19 X19 *)
  0x4f4157bd;       (* arm_SHL_VEC Q29 Q29 1 64 128 *)
  0x9bb00441;       (* arm_UMADDL X1 W2 W16 X1 *)
  0x2eb7c02f;       (* arm_UMULL_VEC Q15 Q1 Q23 32 *)
  0x9bb60360;       (* arm_UMADDL X0 W27 W22 X0 *)
  0x2eb8801d;       (* arm_UMLAL_VEC Q29 Q0 Q24 32 *)
  0x9ba56382;       (* arm_UMADDL X2 W28 W5 X24 *)
  0x0ebf9ef8;       (* arm_MUL_VEC Q24 Q23 Q31 32 64 *)
  0x9bb71384;       (* arm_UMADDL X4 W28 W23 X4 *)
  0x2eab80b5;       (* arm_UMLAL_VEC Q21 Q5 Q11 32 *)
  0x9ba55378;       (* arm_UMADDL X24 W27 W5 X20 *)
  0x2eae8034;       (* arm_UMLAL_VEC Q20 Q1 Q14 32 *)
  0x9bb74d74;       (* arm_UMADDL X20 W11 W23 X19 *)
  0x2eac809a;       (* arm_UMLAL_VEC Q26 Q4 Q12 32 *)
  0x9bb70b73;       (* arm_UMADDL X19 W27 W23 X2 *)
  0x2eb080da;       (* arm_UMLAL_VEC Q26 Q6 Q16 32 *)
  0x9ba612a2;       (* arm_UMADDL X2 W21 W6 X4 *)
  0x2eb1805d;       (* arm_UMLAL_VEC Q29 Q2 Q17 32 *)
  0x9bb76118;       (* arm_UMADDL X24 W8 W23 X24 *)
  0x2eab806f;       (* arm_UMLAL_VEC Q15 Q3 Q11 32 *)
  0x9bb002a0;       (* arm_UMADDL X0 W21 W16 X0 *)
  0x9bad4ea4;       (* arm_UMADDL X4 W21 W13 X19 *)
  0x0ebf9d77;       (* arm_MUL_VEC Q23 Q11 Q31 32 64 *)
  0x2eb68074;       (* arm_UMLAL_VEC Q20 Q3 Q22 32 *)
  0x9ba70982;       (* arm_UMADDL X2 W12 W7 X2 *)
  0x2eaa80b4;       (* arm_UMLAL_VEC Q20 Q5 Q10 32 *)
  0x9bba0193;       (* arm_UMADDL X19 W12 W26 X0 *)
  0x2eae809d;       (* arm_UMLAL_VEC Q29 Q4 Q14 32 *)
  0x9bad6180;       (* arm_UMADDL X0 W12 W13 X24 *)
  0x2eb3811a;       (* arm_UMLAL_VEC Q26 Q8 Q19 32 *)
  0x9ba551f4;       (* arm_UMADDL X20 W15 W5 X20 *)
  0x2eb6803a;       (* arm_UMLAL_VEC Q26 Q1 Q22 32 *)
  0x9baa25f5;       (* arm_UMADDL X21 W15 W10 X9 *)
  0x2eaa807a;       (* arm_UMLAL_VEC Q26 Q3 Q10 32 *)
  0x924067a9;       (* arm_AND X9 X29 (rvalue (word 67108863)) *)
  0x2eb680dd;       (* arm_UMLAL_VEC Q29 Q6 Q22 32 *)
  0x9ba753d4;       (* arm_UMADDL X20 W30 W7 X20 *)
  0x9bb60781;       (* arm_UMADDL X1 W28 W22 X1 *)
  0x8b130278;       (* arm_ADD X24 X19 X19 *)
  0x2eacc02b;       (* arm_UMULL_VEC Q11 Q1 Q12 32 *)
  0x0b030473;       (* arm_ADD W19 W3 (Shiftedreg W3 LSL 1) *)
  0x2eb280ba;       (* arm_UMLAL_VEC Q26 Q5 Q18 32 *)
  0x0b031273;       (* arm_ADD W19 W19 (Shiftedreg W3 LSL 4) *)
  0x9ba65134;       (* arm_UMADDL X20 W9 W6 X20 *)
  0x2eaa811d;       (* arm_UMLAL_VEC Q29 Q8 Q10 32 *)
  0x0b09053d;       (* arm_ADD W29 W9 (Shiftedreg W9 LSL 1) *)
  0x2eb1806d;       (* arm_UMLAL_VEC Q13 Q3 Q17 32 *)
  0x0b0913bd;       (* arm_ADD W29 W29 (Shiftedreg W9 LSL 4) *)
  0x9baa0a62;       (* arm_UMADDL X2 W19 W10 X2 *)
  0x2eb0806b;       (* arm_UMLAL_VEC Q11 Q3 Q16 32 *)
  0x9bae57d5;       (* arm_UMADDL X21 W30 W14 X21 *)
  0x2eb380ab;       (* arm_UMLAL_VEC Q11 Q5 Q19 32 *)
  0x9bad5074;       (* arm_UMADDL X20 W3 W13 X20 *)
  0x2eb880eb;       (* arm_UMLAL_VEC Q11 Q7 Q24 32 *)
  0x9bb60ba2;       (* arm_UMADDL X2 W29 W22 X2 *)
  0x2eb7812b;       (* arm_UMLAL_VEC Q11 Q9 Q23 32 *)
  0x9bba5535;       (* arm_UMADDL X21 W9 W26 X21 *)
  0x6f7f07d7;       (* arm_USHR_VEC Q23 Q30 1 64 128 *)
  0x9baa0621;       (* arm_UMADDL X1 W17 W10 X1 *)
  0x2eae80ad;       (* arm_UMLAL_VEC Q13 Q5 Q14 32 *)
  0x9ba56278;       (* arm_UMADDL X24 W19 W5 X24 *)
  0x2eae807b;       (* arm_UMLAL_VEC Q27 Q3 Q14 32 *)
  0x9bb05475;       (* arm_UMADDL X21 W3 W16 X21 *)
  0x4f41556b;       (* arm_SHL_VEC Q11 Q11 1 64 128 *)
  0x0b1e07c3;       (* arm_ADD W3 W30 (Shiftedreg W30 LSL 1) *)
  0x2eb080bc;       (* arm_UMLAL_VEC Q28 Q5 Q16 32 *)
  0x0b1e1063;       (* arm_ADD W3 W3 (Shiftedreg W30 LSL 4) *)
  0x9bb763b8;       (* arm_UMADDL X24 W29 W23 X24 *)
  0x2eb380fc;       (* arm_UMLAL_VEC Q28 Q7 Q19 32 *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x2eb8813c;       (* arm_UMLAL_VEC Q28 Q9 Q24 32 *)
  0x9ba50561;       (* arm_UMADDL X1 W11 W5 X1 *)
  0x2eac80af;       (* arm_UMLAL_VEC Q15 Q5 Q12 32 *)
  0x9bad63d8;       (* arm_UMADDL X24 W30 W13 X24 *)
  0x2eb080ef;       (* arm_UMLAL_VEC Q15 Q7 Q16 32 *)
  0x9bae65f9;       (* arm_UMADDL X25 W15 W14 X25 *)
  0x2eb3812f;       (* arm_UMLAL_VEC Q15 Q9 Q19 32 *)
  0x9ba705e1;       (* arm_UMADDL X1 W15 W7 X1 *)
  0x4f41579c;       (* arm_SHL_VEC Q28 Q28 1 64 128 *)
  0x9ba661f8;       (* arm_UMADDL X24 W15 W6 X24 *)
  0x2eac80f5;       (* arm_UMLAL_VEC Q21 Q7 Q12 32 *)
  0x9bb00bc2;       (* arm_UMADDL X2 W30 W16 X2 *)
  0x2eb08135;       (* arm_UMLAL_VEC Q21 Q9 Q16 32 *)
  0x9bba67d9;       (* arm_UMADDL X25 W30 W26 X25 *)
  0x4f4155ef;       (* arm_SHL_VEC Q15 Q15 1 64 128 *)
  0x9ba607de;       (* arm_UMADDL X30 W30 W6 X1 *)
  0x2eb6801c;       (* arm_UMLAL_VEC Q28 Q0 Q22 32 *)
  0x9bba09e1;       (* arm_UMADDL X1 W15 W26 X2 *)
  0x2eaa805c;       (* arm_UMLAL_VEC Q28 Q2 Q10 32 *)
  0x9bb06522;       (* arm_UMADDL X2 W9 W16 X25 *)
  0x4f4156b5;       (* arm_SHL_VEC Q21 Q21 1 64 128 *)
  0x9ba76178;       (* arm_UMADDL X24 W11 W7 X24 *)
  0x2eae800f;       (* arm_UMLAL_VEC Q15 Q0 Q14 32 *)
  0x9bae0561;       (* arm_UMADDL X1 W11 W14 X1 *)
  0x2eb18015;       (* arm_UMLAL_VEC Q21 Q0 Q17 32 *)
  0x9bad7939;       (* arm_UMADDL X25 W9 W13 X30 *)
  0x2eb2809c;       (* arm_UMLAL_VEC Q28 Q4 Q18 32 *)
  0x9bba0260;       (* arm_UMADDL X0 W19 W26 X0 *)
  0x2eac8059;       (* arm_UMLAL_VEC Q25 Q2 Q12 32 *)
  0x8b586821;       (* arm_ADD X1 X1 (Shiftedreg X24 LSR 26) *)
  0x2eb08099;       (* arm_UMLAL_VEC Q25 Q4 Q16 32 *)
  0x9bb60a7e;       (* arm_UMADDL X30 W19 W22 X2 *)
  0x2eae8055;       (* arm_UMLAL_VEC Q21 Q2 Q14 32 *)
  0x9ba61184;       (* arm_UMADDL X4 W12 W6 X4 *)
  0x0ebf9dce;       (* arm_MUL_VEC Q14 Q14 Q31 32 64 *)
  0x9bb76679;       (* arm_UMADDL X25 W19 W23 X25 *)
  0x92406022;       (* arm_AND X2 X1 (rvalue (word 33554431)) *)
  0x0ebf9e30;       (* arm_MUL_VEC Q16 Q17 Q31 32 64 *)
  0x2eb380d9;       (* arm_UMLAL_VEC Q25 Q6 Q19 32 *)
  0x9bae1269;       (* arm_UMADDL X9 W19 W14 X4 *)
  0x2eb680ed;       (* arm_UMLAL_VEC Q13 Q7 Q22 32 *)
  0x8b416739;       (* arm_ADD X25 X25 (Shiftedreg X1 LSR 25) *)
  0x2eb68095;       (* arm_UMLAL_VEC Q21 Q4 Q22 32 *)
  0x9bae03a0;       (* arm_UMADDL X0 W29 W14 X0 *)
  0x2eb080fa;       (* arm_UMLAL_VEC Q26 Q7 Q16 32 *)
  0x8b596bde;       (* arm_ADD X30 X30 (Shiftedreg X25 LSR 26) *)
  0x2eae813a;       (* arm_UMLAL_VEC Q26 Q9 Q14 32 *)
  0x0b0f05e1;       (* arm_ADD W1 W15 (Shiftedreg W15 LSL 1) *)
  0x2eb080dc;       (* arm_UMLAL_VEC Q28 Q6 Q16 32 *)
  0x0b0f1021;       (* arm_ADD W1 W1 (Shiftedreg W15 LSL 4) *)
  0x8b5e6684;       (* arm_ADD X4 X20 (Shiftedreg X30 LSR 25) *)
  0x2eae811c;       (* arm_UMLAL_VEC Q28 Q8 Q14 32 *)
  0x92406739;       (* arm_AND X25 X25 (rvalue (word 67108863)) *)
  0x2eb6804f;       (* arm_UMLAL_VEC Q15 Q2 Q22 32 *)
  0x8b446ab5;       (* arm_ADD X21 X21 (Shiftedreg X4 LSR 26) *)
  0x2eaa800b;       (* arm_UMLAL_VEC Q11 Q0 Q10 32 *)
  0xb36063d9;       (* arm_BFM X25 X30 32 24 *)
  0x2eb2804b;       (* arm_UMLAL_VEC Q11 Q2 Q18 32 *)
  0x926696be;       (* arm_AND X30 X21 (rvalue (word 18446744073642442752)) *)
  0x6f66179a;       (* arm_USRA_VEC Q26 Q28 26 64 128 *)
  0xd35affd4;       (* arm_LSR X20 X30 26 *)
  0x2eaa808f;       (* arm_UMLAL_VEC Q15 Q4 Q10 32 *)
  0x8b5e6694;       (* arm_ADD X20 X20 (Shiftedreg X30 LSR 25) *)
  0x2eb280cf;       (* arm_UMLAL_VEC Q15 Q6 Q18 32 *)
  0x9baa27a9;       (* arm_UMADDL X9 W29 W10 X9 *)
  0x2eb0810f;       (* arm_UMLAL_VEC Q15 Q8 Q16 32 *)
  0x8b5e5a9e;       (* arm_ADD X30 X20 (Shiftedreg X30 LSR 22) *)
  0x2eb680bb;       (* arm_UMLAL_VEC Q27 Q5 Q22 32 *)
  0x9bba7e34;       (* arm_UMULL X20 W17 W26 *)
  0x2eb280f4;       (* arm_UMLAL_VEC Q20 Q7 Q18 32 *)
  0x9bb07a3e;       (* arm_UMADDL X30 W17 W16 X30 *)
  0x2eb08134;       (* arm_UMLAL_VEC Q20 Q9 Q16 32 *)
  0x9baa0071;       (* arm_UMADDL X17 W3 W10 X0 *)
  0x6f67174f;       (* arm_USRA_VEC Q15 Q26 25 64 128 *)
  0x9bae5380;       (* arm_UMADDL X0 W28 W14 X20 *)
  0x2eaa80fb;       (* arm_UMLAL_VEC Q27 Q7 Q10 32 *)
  0x9bba7b94;       (* arm_UMADDL X20 W28 W26 X30 *)
  0x2eb2813b;       (* arm_UMLAL_VEC Q27 Q9 Q18 32 *)
  0x0b0c059c;       (* arm_ADD W28 W12 (Shiftedreg W12 LSL 1) *)
  0x6f6615f4;       (* arm_USRA_VEC Q20 Q15 26 64 128 *)
  0x0b0c139c;       (* arm_ADD W28 W28 (Shiftedreg W12 LSL 4) *)
  0x9baa037e;       (* arm_UMADDL X30 W27 W10 X0 *)
  0x4e3e1df1;       (* arm_AND_VEC Q17 Q15 Q30 128 *)
  0x9bae537b;       (* arm_UMADDL X27 W27 W14 X20 *)
  0x9baa6d00;       (* arm_UMADDL X0 W8 W10 X27 *)
  0x0ebf9ecc;       (* arm_MUL_VEC Q12 Q22 Q31 32 64 *)
  0x4e371e8f;       (* arm_AND_VEC Q15 Q20 Q23 128 *)
  0x9bb6246e;       (* arm_UMADDL X14 W3 W22 X9 *)
  0x2eaa80d5;       (* arm_UMLAL_VEC Q21 Q6 Q10 32 *)
  0x9bb6791b;       (* arm_UMADDL X27 W8 W22 X30 *)
  0x4e8f2a2f;       (* arm_TRN1 Q15 Q17 Q15 32 128 *)
  0x9bb6038a;       (* arm_UMADDL X10 W28 W22 X0 *)
  0x2eb0808b;       (* arm_UMLAL_VEC Q11 Q4 Q16 32 *)
  0x9bb039fe;       (* arm_UMADDL X30 W15 W16 X14 *)
  0x4e371f5a;       (* arm_AND_VEC Q26 Q26 Q23 128 *)
  0x9bb06d9c;       (* arm_UMADDL X28 W12 W16 X27 *)
  0x2eb28115;       (* arm_UMLAL_VEC Q21 Q8 Q18 32 *)
  0x8b0a014a;       (* arm_ADD X10 X10 X10 *)
  0x2eb88119;       (* arm_UMLAL_VEC Q25 Q8 Q24 32 *)
  0x9ba62a74;       (* arm_UMADDL X20 W19 W6 X10 *)
  0x2eaa8039;       (* arm_UMLAL_VEC Q25 Q1 Q10 32 *)
  0x8b1c039c;       (* arm_ADD X28 X28 X28 *)
  0x2eb28079;       (* arm_UMLAL_VEC Q25 Q3 Q18 32 *)
  0x9ba7727c;       (* arm_UMADDL X28 W19 W7 X28 *)
  0x6f671695;       (* arm_USRA_VEC Q21 Q20 25 64 128 *)
  0x9ba753a0;       (* arm_UMADDL X0 W29 W7 X20 *)
  0x2eae80cb;       (* arm_UMLAL_VEC Q11 Q6 Q14 32 *)
  0x9bba796a;       (* arm_UMADDL X10 W11 W26 X30 *)
  0x2eaa812d;       (* arm_UMLAL_VEC Q13 Q9 Q10 32 *)
  0x9ba573b3;       (* arm_UMADDL X19 W29 W5 X28 *)
  0x6f6616bb;       (* arm_USRA_VEC Q27 Q21 26 64 128 *)
  0x9ba50060;       (* arm_UMADDL X0 W3 W5 X0 *)
  0x2eb080b9;       (* arm_UMLAL_VEC Q25 Q5 Q16 32 *)
  0x9bb64434;       (* arm_UMADDL X20 W1 W22 X17 *)
  0x4e3e1f94;       (* arm_AND_VEC Q20 Q28 Q30 128 *)
  0x9bb74c7d;       (* arm_UMADDL X29 W3 W23 X19 *)
  0x6f67177d;       (* arm_USRA_VEC Q29 Q27 25 64 128 *)
  0x9bb70023;       (* arm_UMADDL X3 W1 W23 X0 *)
  0x4e371f7b;       (* arm_AND_VEC Q27 Q27 Q23 128 *)
  0x2eac810b;       (* arm_UMLAL_VEC Q11 Q8 Q12 32 *)
  0x9bad75ec;       (* arm_UMADDL X12 W15 W13 X29 *)
  0x6f6617ad;       (* arm_USRA_VEC Q13 Q29 26 64 128 *)
  0x9bad0d67;       (* arm_UMADDL X7 W11 W13 X3 *)
  0x4e8728c6;       (* arm_TRN1 Q6 Q6 Q7 32 128 *)
  0x9bb05171;       (* arm_UMADDL X17 W11 W16 X20 *)
  0x2eae80f9;       (* arm_UMLAL_VEC Q25 Q7 Q14 32 *)
  0x92406497;       (* arm_AND X23 X4 (rvalue (word 67108863)) *)
  0x4e771db3;       (* arm_BIC_VEC Q19 Q13 Q23 128 *)
  0x9ba63173;       (* arm_UMADDL X19 W11 W6 X12 *)
  0x4e371dbc;       (* arm_AND_VEC Q28 Q13 Q23 128 *)
  0x8b476a23;       (* arm_ADD X3 X17 (Shiftedreg X7 LSR 26) *)
  0x6f67166b;       (* arm_USRA_VEC Q11 Q19 25 64 128 *)
  0x4e832842;       (* arm_TRN1 Q2 Q2 Q3 32 128 *)
  0x8b436671;       (* arm_ADD X17 X19 (Shiftedreg X3 LSR 25) *)
  0x4e3e1ead;       (* arm_AND_VEC Q13 Q21 Q30 128 *)
  0x924064e5;       (* arm_AND X5 X7 (rvalue (word 67108863)) *)
  0x6f68166b;       (* arm_USRA_VEC Q11 Q19 24 64 128 *)
  0x8b516947;       (* arm_ADD X7 X10 (Shiftedreg X17 LSR 26) *)
  0x4e812800;       (* arm_TRN1 Q0 Q0 Q1 32 128 *)
  0x92406713;       (* arm_AND X19 X24 (rvalue (word 67108863)) *)
  0x4e3e1fb5;       (* arm_AND_VEC Q21 Q29 Q30 128 *)
  0x8b47667d;       (* arm_ADD X29 X19 (Shiftedreg X7 LSR 25) *)
  0x6f6b166b;       (* arm_USRA_VEC Q11 Q19 21 64 128 *)
  0xb3606065;       (* arm_BFM X5 X3 32 24 *)
  0x4e9b29b1;       (* arm_TRN1 Q17 Q13 Q27 32 128 *)
  0x8b5d6853;       (* arm_ADD X19 X2 (Shiftedreg X29 LSR 26) *)
  0x4e9c2ab3;       (* arm_TRN1 Q19 Q21 Q28 32 128 *)
  0x924067a3;       (* arm_AND X3 X29 (rvalue (word 67108863)) *)
  0x6e0844d0;       (* arm_INS Q16 Q6 0 64 64 128 *)
  0x6e084626;       (* arm_INS Q6 Q17 0 64 64 128 *)
  0x4e892908;       (* arm_TRN1 Q8 Q8 Q9 32 128 *)
  0xb3606663;       (* arm_BFM X3 X19 32 25 *)
  0x4e3e1d75;       (* arm_AND_VEC Q21 Q11 Q30 128 *)
  0xb36066b7;       (* arm_BFM X23 X21 32 25 *)
  0x6e084512;       (* arm_INS Q18 Q8 0 64 64 128 *)
  0x6e084668;       (* arm_INS Q8 Q19 0 64 64 128 *)
  0x2eac8139;       (* arm_UMLAL_VEC Q25 Q9 Q12 32 *)
  0x4e081ee9;       (* arm_INS_GEN Q9 X23 0 64 *)
  0x4e081f27;       (* arm_INS_GEN Q7 X25 0 64 *)
  0xfd4027fd;       (* arm_LDR D29 SP (Immediate_Offset (word 72)) *)
  0x6e08444c;       (* arm_INS Q12 Q2 0 64 64 128 *)
  0x4e852884;       (* arm_TRN1 Q4 Q4 Q5 32 128 *)
  0x92406631;       (* arm_AND X17 X17 (rvalue (word 67108863)) *)
  0x6f661579;       (* arm_USRA_VEC Q25 Q11 26 64 128 *)
  0x6e08440a;       (* arm_INS Q10 Q0 0 64 64 128 *)
  0x6e08448e;       (* arm_INS Q14 Q4 0 64 64 128 *)
  0x6e0845e4;       (* arm_INS Q4 Q15 0 64 64 128 *)
  0x6f671734;       (* arm_USRA_VEC Q20 Q25 25 64 128 *)
  0x4e371f3b;       (* arm_AND_VEC Q27 Q25 Q23 128 *)
  0xb36060f1;       (* arm_BFM X17 X7 32 24 *)
  0x4e081c65;       (* arm_INS_GEN Q5 X3 0 64 *)
  0x4e081ca1;       (* arm_INS_GEN Q1 X5 0 64 *)
  0x6f66169a;       (* arm_USRA_VEC Q26 Q20 26 64 128 *)
  0x4e3e1e9c;       (* arm_AND_VEC Q28 Q20 Q30 128 *)
  0x4e9b2aab;       (* arm_TRN1 Q11 Q21 Q27 32 128 *)
  0x4e9a2b8d;       (* arm_TRN1 Q13 Q28 Q26 32 128 *)
  0x6e084560;       (* arm_INS Q0 Q11 0 64 64 128 *)
  0x4e081e23;       (* arm_INS_GEN Q3 X17 0 64 *)
  0x6e0845a2;       (* arm_INS Q2 Q13 0 64 64 128 *)
  0xfd402bfc;       (* arm_LDR D28 SP (Immediate_Offset (word 80)) *)
  0xf94067e0;       (* arm_LDR X0 SP (Immediate_Offset (word 200)) *)
  0xf1000400;       (* arm_SUBS X0 X0 (rvalue (word 1)) *)
  0xf90067e0;       (* arm_STR X0 SP (Immediate_Offset (word 200)) *)
  0x54ff8062;       (* arm_BCS (word 2093068) *)
  0x0e043c00;       (* arm_UMOV W0 Q0 0 4 *)
  0x0e0c3c01;       (* arm_UMOV W1 Q0 1 4 *)
  0x0e043c42;       (* arm_UMOV W2 Q2 0 4 *)
  0x0e0c3c43;       (* arm_UMOV W3 Q2 1 4 *)
  0x0e043c84;       (* arm_UMOV W4 Q4 0 4 *)
  0x0e0c3c85;       (* arm_UMOV W5 Q4 1 4 *)
  0x0e043cc6;       (* arm_UMOV W6 Q6 0 4 *)
  0x0e0c3cc7;       (* arm_UMOV W7 Q6 1 4 *)
  0x0e043d08;       (* arm_UMOV W8 Q8 0 4 *)
  0x0e0c3d09;       (* arm_UMOV W9 Q8 1 4 *)
  0x8b016800;       (* arm_ADD X0 X0 (Shiftedreg X1 LSL 26) *)
  0x8b036841;       (* arm_ADD X1 X2 (Shiftedreg X3 LSL 26) *)
  0x8b056882;       (* arm_ADD X2 X4 (Shiftedreg X5 LSL 26) *)
  0x8b0768c3;       (* arm_ADD X3 X6 (Shiftedreg X7 LSL 26) *)
  0x8b096904;       (* arm_ADD X4 X8 (Shiftedreg X9 LSL 26) *)
  0xab01cc00;       (* arm_ADDS X0 X0 (Shiftedreg X1 LSL 51) *)
  0xd34dfc26;       (* arm_LSR X6 X1 13 *)
  0xd35a6447;       (* arm_LSL X7 X2 38 *)
  0xba0700c1;       (* arm_ADCS X1 X6 X7 *)
  0xd35afc48;       (* arm_LSR X8 X2 26 *)
  0xd3679869;       (* arm_LSL X9 X3 25 *)
  0xba090102;       (* arm_ADCS X2 X8 X9 *)
  0xd367fc6a;       (* arm_LSR X10 X3 39 *)
  0xd374cc8b;       (* arm_LSL X11 X4 12 *)
  0x9a0b0143;       (* arm_ADC X3 X10 X11 *)
  0xa90807e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa9090fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&144))) *)
  0x0e043c20;       (* arm_UMOV W0 Q1 0 4 *)
  0x0e0c3c21;       (* arm_UMOV W1 Q1 1 4 *)
  0x0e043c62;       (* arm_UMOV W2 Q3 0 4 *)
  0x0e0c3c63;       (* arm_UMOV W3 Q3 1 4 *)
  0x0e043ca4;       (* arm_UMOV W4 Q5 0 4 *)
  0x0e0c3ca5;       (* arm_UMOV W5 Q5 1 4 *)
  0x0e043ce6;       (* arm_UMOV W6 Q7 0 4 *)
  0x0e0c3ce7;       (* arm_UMOV W7 Q7 1 4 *)
  0x0e043d28;       (* arm_UMOV W8 Q9 0 4 *)
  0x0e0c3d29;       (* arm_UMOV W9 Q9 1 4 *)
  0x5280026a;       (* arm_MOV W10 (rvalue (word 19)) *)
  0x8b016800;       (* arm_ADD X0 X0 (Shiftedreg X1 LSL 26) *)
  0xf267013f;       (* arm_TST X9 (rvalue (word 33554432)) *)
  0x8b036841;       (* arm_ADD X1 X2 (Shiftedreg X3 LSL 26) *)
  0x9a9f114a;       (* arm_CSEL X10 X10 XZR Condition_NE *)
  0x8b056882;       (* arm_ADD X2 X4 (Shiftedreg X5 LSL 26) *)
  0x92406129;       (* arm_AND X9 X9 (rvalue (word 33554431)) *)
  0x8b0768c3;       (* arm_ADD X3 X6 (Shiftedreg X7 LSL 26) *)
  0x8b0a0000;       (* arm_ADD X0 X0 X10 *)
  0x8b096904;       (* arm_ADD X4 X8 (Shiftedreg X9 LSL 26) *)
  0xab01cc00;       (* arm_ADDS X0 X0 (Shiftedreg X1 LSL 51) *)
  0xd34dfc26;       (* arm_LSR X6 X1 13 *)
  0xd35a6447;       (* arm_LSL X7 X2 38 *)
  0xba0700c1;       (* arm_ADCS X1 X6 X7 *)
  0xd35afc48;       (* arm_LSR X8 X2 26 *)
  0xd3679869;       (* arm_LSL X9 X3 25 *)
  0xba090102;       (* arm_ADCS X2 X8 X9 *)
  0xd367fc6a;       (* arm_LSR X10 X3 39 *)
  0xd374cc8b;       (* arm_LSL X11 X4 12 *)
  0x9a0b0143;       (* arm_ADC X3 X10 X11 *)
  0xa90a07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa90b0fe2;       (* arm_STP X2 X3 SP (Immediate_Offset (iword (&176))) *)
  0x910283e0;       (* arm_ADD X0 SP (rvalue (word 160)) *)
  0x910283e1;       (* arm_ADD X1 SP (rvalue (word 160)) *)
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
  0xa94813e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  0xa94a1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  0x9ba57c67;       (* arm_UMULL X7 W3 W5 *)
  0xd360fc60;       (* arm_LSR X0 X3 32 *)
  0x9ba57c0f;       (* arm_UMULL X15 W0 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9ba07e08;       (* arm_UMULL X8 W16 W0 *)
  0x9bb07c70;       (* arm_UMULL X16 W3 W16 *)
  0xab0f80e7;       (* arm_ADDS X7 X7 (Shiftedreg X15 LSL 32) *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x9a0f0108;       (* arm_ADC X8 X8 X15 *)
  0xab1080e7;       (* arm_ADDS X7 X7 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a100108;       (* arm_ADC X8 X8 X16 *)
  0x9b067c89;       (* arm_MUL X9 X4 X6 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xeb0600a3;       (* arm_SUBS X3 X5 X6 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b037c8f;       (* arm_MUL X15 X4 X3 *)
  0x9bc37c83;       (* arm_UMULH X3 X4 X3 *)
  0xab0900e8;       (* arm_ADDS X8 X7 X9 *)
  0xba0a0129;       (* arm_ADCS X9 X9 X10 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0801e8;       (* arm_ADCS X8 X15 X8 *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xba090069;       (* arm_ADCS X9 X3 X9 *)
  0x9a10014a;       (* arm_ADC X10 X10 X16 *)
  0xa94913e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0xa94b1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0x9ba57c6b;       (* arm_UMULL X11 W3 W5 *)
  0xd360fc60;       (* arm_LSR X0 X3 32 *)
  0x9ba57c0f;       (* arm_UMULL X15 W0 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9ba07e0c;       (* arm_UMULL X12 W16 W0 *)
  0x9bb07c70;       (* arm_UMULL X16 W3 W16 *)
  0xab0f816b;       (* arm_ADDS X11 X11 (Shiftedreg X15 LSL 32) *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x9a0f018c;       (* arm_ADC X12 X12 X15 *)
  0xab10816b;       (* arm_ADDS X11 X11 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a10018c;       (* arm_ADC X12 X12 X16 *)
  0x9b067c8d;       (* arm_MUL X13 X4 X6 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab0c01ad;       (* arm_ADDS X13 X13 X12 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xeb0600a3;       (* arm_SUBS X3 X5 X6 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b037c8f;       (* arm_MUL X15 X4 X3 *)
  0x9bc37c83;       (* arm_UMULH X3 X4 X3 *)
  0xab0d016c;       (* arm_ADDS X12 X11 X13 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0c01ec;       (* arm_ADCS X12 X15 X12 *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xba0d006d;       (* arm_ADCS X13 X3 X13 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xa94913e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&144))) *)
  0xa94843ef;       (* arm_LDP X15 X16 SP (Immediate_Offset (iword (&128))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa94a03ef;       (* arm_LDP X15 X0 SP (Immediate_Offset (iword (&160))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060006;       (* arm_SBCS X6 X0 X6 *)
  0xda9f23e0;       (* arm_CSETM X0 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca0000a5;       (* arm_EOR X5 X5 X0 *)
  0xeb0000a5;       (* arm_SUBS X5 X5 X0 *)
  0xca0000c6;       (* arm_EOR X6 X6 X0 *)
  0xda0000c6;       (* arm_SBC X6 X6 X0 *)
  0xca100010;       (* arm_EOR X16 X0 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c60;       (* arm_UMULH X0 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab0001ef;       (* arm_ADDS X15 X15 X0 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0040;       (* arm_ADDS X0 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba0000a0;       (* arm_ADCS X0 X5 X0 *)
  0xca0900c6;       (* arm_EOR X6 X6 X9 *)
  0xba0f00cf;       (* arm_ADCS X15 X6 X15 *)
  0x9a090021;       (* arm_ADC X1 X1 X9 *)
  0xab070169;       (* arm_ADDS X9 X11 X7 *)
  0xba08018a;       (* arm_ADCS X10 X12 X8 *)
  0xba0b01ab;       (* arm_ADCS X11 X13 X11 *)
  0xba0c01cc;       (* arm_ADCS X12 X14 X12 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca100042;       (* arm_EOR X2 X2 X16 *)
  0xba090049;       (* arm_ADCS X9 X2 X9 *)
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9ba37d64;       (* arm_UMULL X4 W11 W3 *)
  0x8b274084;       (* arm_ADD X4 X4 (Extendedreg W7 UXTW) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0xd360fd6b;       (* arm_LSR X11 X11 32 *)
  0x9ba31d6b;       (* arm_UMADDL X11 W11 W3 X7 *)
  0xaa0403e7;       (* arm_MOV X7 X4 *)
  0x9ba37d84;       (* arm_UMULL X4 W12 W3 *)
  0x8b284084;       (* arm_ADD X4 X4 (Extendedreg W8 UXTW) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9ba3218c;       (* arm_UMADDL X12 W12 W3 X8 *)
  0xaa0403e8;       (* arm_MOV X8 X4 *)
  0x9ba37da4;       (* arm_UMULL X4 W13 W3 *)
  0x8b294084;       (* arm_ADD X4 X4 (Extendedreg W9 UXTW) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9ba325ad;       (* arm_UMADDL X13 W13 W3 X9 *)
  0xaa0403e9;       (* arm_MOV X9 X4 *)
  0x9ba37dc4;       (* arm_UMULL X4 W14 W3 *)
  0x8b2a4084;       (* arm_ADD X4 X4 (Extendedreg W10 UXTW) *)
  0xd360fd4a;       (* arm_LSR X10 X10 32 *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9ba329ce;       (* arm_UMADDL X14 W14 W3 X10 *)
  0xaa0403ea;       (* arm_MOV X10 X4 *)
  0xd35ffdc0;       (* arm_LSR X0 X14 31 *)
  0xd2800265;       (* arm_MOV X5 (rvalue (word 19)) *)
  0x9ba014a5;       (* arm_UMADDL X5 W5 W0 X5 *)
  0x8b0500e7;       (* arm_ADD X7 X7 X5 *)
  0xab0b80e7;       (* arm_ADDS X7 X7 (Shiftedreg X11 LSL 32) *)
  0x93cb8183;       (* arm_EXTR X3 X12 X11 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x93cc81a3;       (* arm_EXTR X3 X13 X12 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x93cd81c3;       (* arm_EXTR X3 X14 X13 32 *)
  0xd3410005;       (* arm_LSL X5 X0 63 *)
  0xca05014a;       (* arm_EOR X10 X10 X5 *)
  0x9a03014a;       (* arm_ADC X10 X10 X3 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0xf241015f;       (* arm_TST X10 (rvalue (word 9223372036854775808)) *)
  0x9a9f5063;       (* arm_CSEL X3 X3 XZR Condition_PL *)
  0xeb0300e7;       (* arm_SUBS X7 X7 X3 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0x9240f94a;       (* arm_AND X10 X10 (rvalue (word 9223372036854775807)) *)
  0xa90a23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xa90b2be9;       (* arm_STP X9 X10 SP (Immediate_Offset (iword (&176))) *)
  0xf94063f1;       (* arm_LDR X17 SP (Immediate_Offset (word 192)) *)
  0xa94a2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&160))) *)
  0x3900022a;       (* arm_STRB W10 X17 (Immediate_Offset (word 0)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x3900062a;       (* arm_STRB W10 X17 (Immediate_Offset (word 1)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39000a2a;       (* arm_STRB W10 X17 (Immediate_Offset (word 2)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39000e2a;       (* arm_STRB W10 X17 (Immediate_Offset (word 3)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x3900122a;       (* arm_STRB W10 X17 (Immediate_Offset (word 4)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x3900162a;       (* arm_STRB W10 X17 (Immediate_Offset (word 5)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39001a2a;       (* arm_STRB W10 X17 (Immediate_Offset (word 6)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39001e2a;       (* arm_STRB W10 X17 (Immediate_Offset (word 7)) *)
  0x3900222b;       (* arm_STRB W11 X17 (Immediate_Offset (word 8)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x3900262b;       (* arm_STRB W11 X17 (Immediate_Offset (word 9)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39002a2b;       (* arm_STRB W11 X17 (Immediate_Offset (word 10)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39002e2b;       (* arm_STRB W11 X17 (Immediate_Offset (word 11)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x3900322b;       (* arm_STRB W11 X17 (Immediate_Offset (word 12)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x3900362b;       (* arm_STRB W11 X17 (Immediate_Offset (word 13)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39003a2b;       (* arm_STRB W11 X17 (Immediate_Offset (word 14)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39003e2b;       (* arm_STRB W11 X17 (Immediate_Offset (word 15)) *)
  0xa94b37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&176))) *)
  0x3900422c;       (* arm_STRB W12 X17 (Immediate_Offset (word 16)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x3900462c;       (* arm_STRB W12 X17 (Immediate_Offset (word 17)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39004a2c;       (* arm_STRB W12 X17 (Immediate_Offset (word 18)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39004e2c;       (* arm_STRB W12 X17 (Immediate_Offset (word 19)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x3900522c;       (* arm_STRB W12 X17 (Immediate_Offset (word 20)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x3900562c;       (* arm_STRB W12 X17 (Immediate_Offset (word 21)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39005a2c;       (* arm_STRB W12 X17 (Immediate_Offset (word 22)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39005e2c;       (* arm_STRB W12 X17 (Immediate_Offset (word 23)) *)
  0x3900622d;       (* arm_STRB W13 X17 (Immediate_Offset (word 24)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x3900662d;       (* arm_STRB W13 X17 (Immediate_Offset (word 25)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39006a2d;       (* arm_STRB W13 X17 (Immediate_Offset (word 26)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39006e2d;       (* arm_STRB W13 X17 (Immediate_Offset (word 27)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x3900722d;       (* arm_STRB W13 X17 (Immediate_Offset (word 28)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x3900762d;       (* arm_STRB W13 X17 (Immediate_Offset (word 29)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39007a2d;       (* arm_STRB W13 X17 (Immediate_Offset (word 30)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39007e2d;       (* arm_STRB W13 X17 (Immediate_Offset (word 31)) *)
  0x6d4e27e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&224))) *)
  0x6d4f2fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&240))) *)
  0x6d5037ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&256))) *)
  0x6d513fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&272))) *)
  0xa95253f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&288))) *)
  0xa9535bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&304))) *)
  0xa95463f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&320))) *)
  0xa9556bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&336))) *)
  0xa95673fb;       (* arm_LDP X27 X28 SP (Immediate_Offset (iword (&352))) *)
  0xa9577bfd;       (* arm_LDP X29 X30 SP (Immediate_Offset (iword (&368))) *)
  0x910603ff;       (* arm_ADD SP SP (rvalue (word 384)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CURVE25519_X25519_BYTE_EXEC = ARM_MK_EXEC_RULE curve25519_x25519_byte_mc;;

(* ------------------------------------------------------------------------- *)
(* Some abbreviations around the base-25.5 representation                    *)
(* ------------------------------------------------------------------------- *)

let ubignum_of_list = define
 `ubignum_of_list [d0;d1;d2;d3;d4;d5;d6;d7;d8;d9] =
   d0 +
   2 EXP 26 * d1 +
   2 EXP 51 * d2 +
   2 EXP 77 * d3 +
   2 EXP 102 * d4 +
   2 EXP 128 * d5 +
   2 EXP 153 * d6 +
   2 EXP 179 * d7 +
   2 EXP 204 * d8 +
   2 EXP 230 * d9`;;

let ubignum_of_int32list = define
 `ubignum_of_int32list (l:int32 list) = ubignum_of_list (MAP val l)`;;

(*** This is a paired representation using parts of the vector registers ***)

let ubignum_of_qreglist = define
 `ubignum_of_qreglist [q0:(armstate,int128)component;q2;q4;q6;q8] s =
    ubignum_of_int32list
     [word_subword (read q0 s) (0,32); word_subword (read q0 s) (32,32);
      word_subword (read q2 s) (0,32); word_subword (read q2 s) (32,32);
      word_subword (read q4 s) (0,32); word_subword (read q4 s) (32,32);
      word_subword (read q6 s) (0,32); word_subword (read q6 s) (32,32);
      word_subword (read q8 s) (0,32); word_subword (read q8 s) (32,32)]`;;

(**** This is a pure representation with one GPR per digit ***)

let ubignum_of_xreglist = define
 `ubignum_of_xreglist (l:((armstate,int64)component) list) s =
    ubignum_of_list (MAP (\c. val(read c s)) l)`;;

(**** Similar, but only looking at the W register form, the lowest 32 bits ***)

let ubignum_of_wreglist = define
 `ubignum_of_wreglist (l:((armstate,int64)component) list) s =
    ubignum_of_list (MAP (\c. val(word_subword (read c s) (0,32):int32)) l)`;;

(*** Simular, in the high and low 64-bits of 128-bit registers ***)

let ubignum_of_hreglist = define
 `ubignum_of_hreglist (l:((armstate,int128)component) list) s =
    ubignum_of_list (MAP (\c. val(word_subword (read c s) (64,64):int64)) l)`;;

let ubignum_of_lreglist = define
 `ubignum_of_lreglist (l:((armstate,int128)component) list) s =
    ubignum_of_list (MAP (\c. val(word_subword (read c s) (0,64):int64)) l)`;;

(*** Similar again, this time 32-bit chunks, which might be better ***)

let ubignum_of_h32reglist = define
 `ubignum_of_h32reglist (l:((armstate,int128)component) list) s =
    ubignum_of_list (MAP (\c. val(word_subword (read c s) (32,32):int32)) l)`;;

let ubignum_of_l32reglist = define
 `ubignum_of_l32reglist (l:((armstate,int128)component) list) s =
    ubignum_of_list (MAP (\c. val(word_subword (read c s) (0,32):int32)) l)`;;

(*** This is how they are sometimes packed in pairs into GPRs ***)

let ubignum_of_preglist = define
 `ubignum_of_preglist [p0:(armstate,int64)component;p2;p4;p6;p8] s =
    ubignum_of_int32list
     [word_subword (read p0 s) (0,32); word_subword (read p0 s) (32,32);
      word_subword (read p2 s) (0,32); word_subword (read p2 s) (32,32);
      word_subword (read p4 s) (0,32); word_subword (read p4 s) (32,32);
      word_subword (read p6 s) (0,32); word_subword (read p6 s) (32,32);
      word_subword (read p8 s) (0,32); word_subword (read p8 s) (32,32)]`;;

(*** There are two slightly different notions of normalization.
 *** The primed one comes up when using the scalar version of
 *** multiplication, which does nor repack right-to-left and so
 *** can have a larger top digit. Otherwise, the digit bounds
 *** are roughly alternating 25 and 26 bits plus a bit extra.
 ***)

let normalized_ubignum_list = define
 `normalized_ubignum_list [d0;d1;d2;d3;d4;d5;d6;d7;d8;d9] x <=>
    (&(ubignum_of_list [d0;d1;d2;d3;d4;d5;d6;d7;d8;d9]):int == x)
    (mod &p_25519) /\
    d0 <= 67108863 /\ d1 <= 34000000 /\
    d2 <= 67108863 /\ d3 <= 34000000 /\
    d4 <= 67108863 /\ d5 <= 34000000 /\
    d6 <= 67108863 /\ d7 <= 34000000 /\
    d8 <= 67108863 /\ d9 <= 34000000`;;

let normalized_ubignum_int32list = define
 `normalized_ubignum_int32list (l:int32 list) x =
    normalized_ubignum_list (MAP val l) x`;;

let normalized_ubignum_preglist = define
 `normalized_ubignum_preglist
   [p0:(armstate,int64)component;p2;p4;p6;p8] x s =
  normalized_ubignum_int32list
   [word_subword (read p0 s) (0,32); word_subword (read p0 s) (32,32);
    word_subword (read p2 s) (0,32); word_subword (read p2 s) (32,32);
    word_subword (read p4 s) (0,32); word_subword (read p4 s) (32,32);
    word_subword (read p6 s) (0,32); word_subword (read p6 s) (32,32);
    word_subword (read p8 s) (0,32); word_subword (read p8 s) (32,32)]
   x`;;

let normalized_ubignum_qreglist = define
 `normalized_ubignum_qreglist
   [q0:(armstate,int128)component;q2;q4;q6;q8] x s =
  normalized_ubignum_int32list
   [word_subword (read q0 s) (0,32); word_subword (read q0 s) (32,32);
    word_subword (read q2 s) (0,32); word_subword (read q2 s) (32,32);
    word_subword (read q4 s) (0,32); word_subword (read q4 s) (32,32);
    word_subword (read q6 s) (0,32); word_subword (read q6 s) (32,32);
    word_subword (read q8 s) (0,32); word_subword (read q8 s) (32,32)]
   x`;;

let normalized_ubignum_list' = define
 `normalized_ubignum_list' [d0;d1;d2;d3;d4;d5;d6;d7;d8;d9] x <=>
    (&(ubignum_of_list [d0;d1;d2;d3;d4;d5;d6;d7;d8;d9]):int == x)
    (mod &p_25519) /\
    d0 <= 67108863 /\ d1 <= 34000000 /\
    d2 <= 67108863 /\ d3 <= 34000000 /\
    d4 <= 67108863 /\ d5 <= 34000000 /\
    d6 <= 67108863 /\ d7 <= 34000000 /\
    d8 <= 67108863 /\ d9 <= 67108863`;;

let normalized_ubignum_int32list' = define
 `normalized_ubignum_int32list' (l:int32 list) x =
    normalized_ubignum_list' (MAP val l) x`;;

let normalized_ubignum_preglist' = define
 `normalized_ubignum_preglist'
   [p0:(armstate,int64)component;p2;p4;p6;p8] x s =
  normalized_ubignum_int32list'
   [word_subword (read p0 s) (0,32); word_subword (read p0 s) (32,32);
    word_subword (read p2 s) (0,32); word_subword (read p2 s) (32,32);
    word_subword (read p4 s) (0,32); word_subword (read p4 s) (32,32);
    word_subword (read p6 s) (0,32); word_subword (read p6 s) (32,32);
    word_subword (read p8 s) (0,32); word_subword (read p8 s) (32,32)]
   x`;;

let normalized_ubignum_qreglist' = define
 `normalized_ubignum_qreglist'
   [q0:(armstate,int128)component;q2;q4;q6;q8] x s =
  normalized_ubignum_int32list'
   [word_subword (read q0 s) (0,32); word_subword (read q0 s) (32,32);
    word_subword (read q2 s) (0,32); word_subword (read q2 s) (32,32);
    word_subword (read q4 s) (0,32); word_subword (read q4 s) (32,32);
    word_subword (read q6 s) (0,32); word_subword (read q6 s) (32,32);
    word_subword (read q8 s) (0,32); word_subword (read q8 s) (32,32)]
   x`;;

(* ------------------------------------------------------------------------- *)
(* Key state components in inner loop, extracted from code annotations.      *)
(* ------------------------------------------------------------------------- *)

let named_variables =
  [`x =
    ubignum_of_list
    [val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 32))) s0) (0,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 32))) s0) (32,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 40))) s0) (0,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 40))) s0) (32,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 48))) s0) (0,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 48))) s0) (32,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 56))) s0) (0,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 56))) s0) (32,32):int32);
     val(word_subword
       (read (memory :> bytes64(word_add stackpointer (word 64))) s0) (0,32):int32);
     val(word_subword
      (read (memory :> bytes64(word_add stackpointer (word 64))) s0) (32,32):int32)]`;
   `x2 =
    ubignum_of_list
    [val(word_subword (read Q0 s0) (0,32):int32);
     val(word_subword (read Q0 s0) (32,32):int32);
     val(word_subword (read Q2 s0) (0,32):int32);
     val(word_subword (read Q2 s0) (32,32):int32);
     val(word_subword (read Q4 s0) (0,32):int32);
     val(word_subword (read Q4 s0) (32,32):int32);
     val(word_subword (read Q6 s0) (0,32):int32);
     val(word_subword (read Q6 s0) (32,32):int32);
     val(word_subword (read Q8 s0) (0,32):int32);
     val(word_subword (read Q8 s0) (32,32):int32)]`;
   `x3 =
    ubignum_of_list
    [val(word_subword (read Q10 s0) (0,32):int32);
     val(word_subword (read Q10 s0) (32,32):int32);
     val(word_subword (read Q12 s0) (0,32):int32);
     val(word_subword (read Q12 s0) (32,32):int32);
     val(word_subword (read Q14 s0) (0,32):int32);
     val(word_subword (read Q14 s0) (32,32):int32);
     val(word_subword (read Q16 s0) (0,32):int32);
     val(word_subword (read Q16 s0) (32,32):int32);
     val(word_subword (read Q18 s0) (0,32):int32);
     val(word_subword (read Q18 s0) (32,32):int32)]`;
   `z2 =
    ubignum_of_list
    [val(word_subword (read Q1 s0) (0,32):int32);
     val(word_subword (read Q1 s0) (32,32):int32);
     val(word_subword (read Q3 s0) (0,32):int32);
     val(word_subword (read Q3 s0) (32,32):int32);
     val(word_subword (read Q5 s0) (0,32):int32);
     val(word_subword (read Q5 s0) (32,32):int32);
     val(word_subword (read Q7 s0) (0,32):int32);
     val(word_subword (read Q7 s0) (32,32):int32);
     val(word_subword (read Q9 s0) (0,32):int32);
     val(word_subword (read Q9 s0) (32,32):int32)]`;
   `z3 =
    ubignum_of_list
    [val(word_subword (read Q11 s0) (0,32):int32);
     val(word_subword (read Q11 s0) (32,32):int32);
     val(word_subword (read Q13 s0) (0,32):int32);
     val(word_subword (read Q13 s0) (32,32):int32);
     val(word_subword (read Q15 s0) (0,32):int32);
     val(word_subword (read Q15 s0) (32,32):int32);
     val(word_subword (read Q17 s0) (0,32):int32);
     val(word_subword (read Q17 s0) (32,32):int32);
     val(word_subword (read Q19 s0) (0,32):int32);
     val(word_subword (read Q19 s0) (32,32):int32)]`;
   `a =
    ubignum_of_list
    [val(word_subword (read Q25 s10) (0,32):int32);
     val(word_subword (read Q25 s10) (32,32):int32);
     val(word_subword (read Q22 s8) (0,32):int32);
     val(word_subword (read Q22 s8) (32,32):int32);
     val(word_subword (read Q28 s34) (0,32):int32);
     val(word_subword (read Q28 s34) (32,32):int32);
     val(word_subword (read Q23 s30) (0,32):int32);
     val(word_subword (read Q23 s30) (32,32):int32);
     val(word_subword (read Q9 s53) (0,32):int32);
     val(word_subword (read Q9 s53) (32,32):int32)]`;
   `aa =
    ubignum_of_list
    [val(word_subword (read X9 s258) (0,32):int32);
     val(word_subword (read X9 s258) (32,32):int32);
     val(word_subword (read X11 s335) (0,32):int32);
     val(word_subword (read X11 s335) (32,32):int32);
     val(word_subword (read X14 s282) (0,32):int32);
     val(word_subword (read X14 s282) (32,32):int32);
     val(word_subword (read X29 s289) (0,32):int32);
     val(word_subword (read X29 s289) (32,32):int32);
     val(word_subword (read X6 s478) (0,32):int32);
     val(word_subword (read X6 s478) (32,32):int32)]`;
   `ad =
    ubignum_of_list
    [val(word_subword (read Q7 s390) (0,64):int64);
     val(word_subword (read Q8 s394) (0,64):int64);
     val(word_subword (read Q3 s404) (0,64):int64);
     val(word_subword (read Q0 s402) (0,64):int64);
     val(word_subword (read Q20 s321) (0,64):int64);
     val(word_subword (read Q27 s330) (0,64):int64);
     val(word_subword (read Q8 s328) (0,64):int64);
     val(word_subword (read Q5 s332) (0,64):int64);
     val(word_subword (read Q1 s364) (0,64):int64);
     val(word_subword (read Q17 s368) (0,64):int64)]`;
   `b =
    ubignum_of_list
    [val(word_subword (read Q0 s13) (0,32):int32);
     val(word_subword (read Q0 s13) (32,32):int32);
     val(word_subword (read Q18 s22) (0,32):int32);
     val(word_subword (read Q18 s22) (32,32):int32);
     val(word_subword (read Q1 s57) (0,32):int32);
     val(word_subword (read Q1 s57) (32,32):int32);
     val(word_subword (read Q13 s46) (0,32):int32);
     val(word_subword (read Q13 s46) (32,32):int32);
     val(word_subword (read Q7 s36) (0,32):int32);
     val(word_subword (read Q7 s36) (32,32):int32)]`;
   `bb =
    ubignum_of_list
    [val(word_subword (read X11 s514) (0,32):int32);
     val(word_subword (read X11 s514) (32,32):int32);
     val(word_subword (read X5 s538) (0,32):int32);
     val(word_subword (read X5 s538) (32,32):int32);
     val(word_subword (read X20 s565) (0,32):int32);
     val(word_subword (read X20 s565) (32,32):int32);
     val(word_subword (read X19 s569) (0,32):int32);
     val(word_subword (read X19 s569) (32,32):int32);
     val(word_subword (read X29 s549) (0,32):int32);
     val(word_subword (read X29 s549) (32,32):int32)]`;
   `bbalt =
    ubignum_of_list
    [val(read X17 s592); val(read X17 s551); val(read X12 s557);
     val(read X1 s530); val(read X8 s573); val(read X24 s561);
     val(read X2 s581); val(read X28 s577); val(read X0 s586);
     val(read X15 s549)]`;
   `bc =
    ubignum_of_list
    [val(word_subword (read Q7 s390) (64,64):int64);
     val(word_subword (read Q8 s394) (64,64):int64);
     val(word_subword (read Q3 s404) (64,64):int64);
     val(word_subword (read Q0 s402) (64,64):int64);
     val(word_subword (read Q20 s321) (64,64):int64);
     val(word_subword (read Q27 s330) (64,64):int64);
     val(word_subword (read Q8 s328) (64,64):int64);
     val(word_subword (read Q5 s332) (64,64):int64);
     val(word_subword (read Q1 s364) (64,64):int64);
     val(word_subword (read Q17 s368) (64,64):int64)]`;
   `bce =
    ubignum_of_list
    [val(read X11 s638); val(read X12 s645); val(read X15 s688);
     val(read X21 s676); val(read X30 s707); val(read X2 s720);
     val(read X9 s803); val(read X3 s691); val(read X3 s760);
     val(read X4 s697)]`;
   `c =
    ubignum_of_list
    [val(word_subword (read Q19 s18) (0,32):int32);
     val(word_subword (read Q19 s18) (32,32):int32);
     val(word_subword (read Q24 s26) (0,32):int32);
     val(word_subword (read Q24 s26) (32,32):int32);
     val(word_subword (read Q14 s23) (0,32):int32);
     val(word_subword (read Q14 s23) (32,32):int32);
     val(word_subword (read Q15 s24) (0,32):int32);
     val(word_subword (read Q15 s24) (32,32):int32);
     val(word_subword (read Q3 s12) (0,32):int32);
     val(word_subword (read Q3 s12) (32,32):int32)]`;
   `d =
    ubignum_of_list
    [val(word_subword (read Q26 s27) (0,32):int32);
     val(word_subword (read Q26 s27) (32,32):int32);
     val(word_subword (read Q27 s32) (0,32):int32);
     val(word_subword (read Q27 s32) (32,32):int32);
     val(word_subword (read Q11 s19) (0,32):int32);
     val(word_subword (read Q11 s19) (32,32):int32);
     val(word_subword (read Q2 s25) (0,32):int32);
     val(word_subword (read Q2 s25) (32,32):int32);
     val(word_subword (read Q21 s20) (0,32):int32);
     val(word_subword (read Q21 s20) (32,32):int32)]`;
   `e =
    ubignum_of_list
    [val(word_subword (read X13 s522) (0,32):int32);
     val(word_subword (read X16 s522) (0,32):int32);
     val(word_subword (read X6 s559) (0,32):int32);
     val(word_subword (read X26 s559) (0,32):int32);
     val(word_subword (read X7 s575) (0,32):int32);
     val(word_subword (read X14 s575) (0,32):int32);
     val(word_subword (read X5 s598) (0,32):int32);
     val(word_subword (read X10 s598) (0,32):int32);
     val(word_subword (read X23 s588) (0,32):int32);
     val(word_subword (read X22 s588) (0,32):int32)]`;
   `f =
    ubignum_of_list
    [val(word_subword (read Q16 s37) (0,32):int32);
     val(word_subword (read Q16 s37) (32,32):int32);
     val(word_subword (read Q20 s33) (0,32):int32);
     val(word_subword (read Q20 s33) (32,32):int32);
     val(word_subword (read Q5 s39) (0,32):int32);
     val(word_subword (read Q5 s39) (32,32):int32);
     val(word_subword (read Q12 s35) (0,32):int32);
     val(word_subword (read Q12 s35) (32,32):int32);
     val(word_subword (read Q26 s104) (0,32):int32);
     val(word_subword (read Q26 s104) (32,32):int32)]`;
   `g =
    ubignum_of_list
    [val(word_subword (read Q29 s67) (0,32):int32);
     val(word_subword (read Q29 s67) (32,32):int32);
     val(word_subword (read Q10 s49) (0,32):int32);
     val(word_subword (read Q10 s49) (32,32):int32);
     val(word_subword (read Q27 s75) (0,32):int32);
     val(word_subword (read Q27 s75) (32,32):int32);
     val(word_subword (read Q8 s59) (0,32):int32);
     val(word_subword (read Q8 s59) (32,32):int32);
     val(word_subword (read Q29 s41) (0,32):int32);
     val(word_subword (read Q29 s41) (32,32):int32)]`;
   `t1 =
    ubignum_of_list
    [val(word_subword (read Q1 s434) (32,32):int32);
     val(word_subword (read Q19 s438) (32,32):int32);
     val(word_subword (read Q0 s432) (32,32):int32);
     val(word_subword (read Q15 s441) (32,32):int32);
     val(word_subword (read Q16 s428) (32,32):int32);
     val(word_subword (read Q4 s448) (32,32):int32);
     val(word_subword (read Q14 s430) (32,32):int32);
     val(word_subword (read Q10 s449) (32,32):int32);
     val(word_subword (read Q22 s412) (32,32):int32);
     val(word_subword (read Q5 s436) (32,32):int32)]`;
   `t2 =
    ubignum_of_list
    [val(word_subword (read Q1 s434) (0,32):int32);
     val(word_subword (read Q19 s438) (0,32):int32);
     val(word_subword (read Q0 s432) (0,32):int32);
     val(word_subword (read Q15 s441) (0,32):int32);
     val(word_subword (read Q16 s428) (0,32):int32);
     val(word_subword (read Q4 s448) (0,32):int32);
     val(word_subword (read Q14 s430) (0,32):int32);
     val(word_subword (read Q10 s449) (0,32):int32);
     val(word_subword (read Q22 s412) (0,32):int32);
     val(word_subword (read Q5 s436) (0,32):int32)]`;
   `t3 =
    ubignum_of_list
    [val(word_subword (read Q0 s593) (0,64):int64);
     val(word_subword (read Q1 s600) (0,64):int64);
     val(word_subword (read Q2 s615) (0,64):int64);
     val(word_subword (read Q3 s609) (0,64):int64);
     val(word_subword (read Q4 s599) (0,64):int64);
     val(word_subword (read Q5 s626) (0,64):int64);
     val(word_subword (read Q6 s624) (0,64):int64);
     val(word_subword (read Q7 s628) (0,64):int64);
     val(word_subword (read Q8 s651) (0,64):int64);
     val(word_subword (read Q9 s663) (0,64):int64)]`;
   `x4 =
    ubignum_of_list
    [val(word_subword (read Q21 s991) (64,64):int64);
     val(word_subword (read Q27 s1007) (64,64):int64);
     val(word_subword (read Q28 s1012) (64,64):int64);
     val(word_subword (read Q26 s1011) (64,64):int64);
     val(word_subword (read Q17 s921) (64,64):int64);
     val(word_subword (read Q15 s925) (64,64):int64);
     val(word_subword (read Q13 s973) (64,64):int64);
     val(word_subword (read Q27 s957) (64,64):int64);
     val(word_subword (read Q21 s979) (64,64):int64);
     val(word_subword (read Q28 s968) (64,64):int64)]`;
   `x5 =
    ubignum_of_list
    [val(word_subword (read Q0 s593) (64,64):int64);
     val(word_subword (read Q1 s600) (64,64):int64);
     val(word_subword (read Q2 s615) (64,64):int64);
     val(word_subword (read Q3 s609) (64,64):int64);
     val(word_subword (read Q4 s599) (64,64):int64);
     val(word_subword (read Q5 s626) (64,64):int64);
     val(word_subword (read Q6 s624) (64,64):int64);
     val(word_subword (read Q7 s628) (64,64):int64);
     val(word_subword (read Q8 s651) (64,64):int64);
     val(word_subword (read Q9 s663) (64,64):int64)]`;
   `z4 =
    ubignum_of_list
    [val(word_subword (read X5 s982) (0,32):int32);
     val(word_subword (read X5 s982) (32,32):int32);
     val(word_subword (read X17 s1008) (0,32):int32);
     val(word_subword (read X17 s1008) (32,32):int32);
     val(word_subword (read X3 s990) (0,32):int32);
     val(word_subword (read X3 s990) (32,32):int32);
     val(word_subword (read X25 s895) (0,32):int32);
     val(word_subword (read X25 s895) (32,32):int32);
     val(word_subword (read X23 s992) (0,32):int32);
     val(word_subword (read X23 s992) (32,32):int32)]`;
   `z5 =
    ubignum_of_list
    [val(word_subword (read Q21 s991) (0,64):int64);
     val(word_subword (read Q27 s1007) (0,64):int64);
     val(word_subword (read Q28 s1012) (0,64):int64);
     val(word_subword (read Q26 s1011) (0,64):int64);
     val(word_subword (read Q17 s921) (0,64):int64);
     val(word_subword (read Q15 s925) (0,64):int64);
     val(word_subword (read Q13 s973) (0,64):int64);
     val(word_subword (read Q27 s957) (0,64):int64);
     val(word_subword (read Q21 s979) (0,64):int64);
     val(word_subword (read Q28 s968) (0,64):int64)]`];;

(* ------------------------------------------------------------------------- *)
(* Other local variables (not many of these are really used)                 *)
(* ------------------------------------------------------------------------- *)

let lvs =
 ["resx",[`X17`;`0`];
  "xn",[`SP`;`128`];
  "zn",[`SP`;`160`]];;

(* ------------------------------------------------------------------------- *)
(* Additional definitions, lemmas and tactics to support spec and/or proofs. *)
(* ------------------------------------------------------------------------- *)

let SWAR_ADD_LEMMA = prove
 (`!(h1:int32) (l1:int32) h2 l2.
        val l1 + val l2 < 2 EXP 32
        ==> word_add (word_join h1 l1) (word_join h2 l2):int64 =
            word_join (word_add h1 h2) (word_add l1 l2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_JOIN; VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `(e * x1 + y1) + e * x2 + y2:num = e * (x1 + x2) + (y1 + y2)`] THEN
  REWRITE_TAC[GSYM CONG; ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(x':num == x) (mod e) ==> (e * x + l == e * x' + l) (mod (e * e))`) THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL]);;

let SWAR_SUB_LEMMA = prove
 (`!(h1:int32) (l1:int32) h2 l2.
        val l2 <= val l1
        ==> word_sub (word_join h1 l1) (word_join h2 l2):int64 =
            word_join (word_sub h1 h2) (word_sub l1 l2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub x y = z <=> word_add y z = x`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SWAR_ADD_LEMMA o lhand o snd) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM DIMINDEX_32] THEN WORD_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN CONV_TAC WORD_RULE]);;

let WORD_SUBWORD_SWAR_0_32 = prove
 (`(!x y. word_subword (word_add x y:int64) (0,32):int32 =
          word_add (word_subword x (0,32)) (word_subword y (0,32))) /\
   (!x y. word_subword (word_sub x y:int64) (0,32):int32 =
          word_sub (word_subword x (0,32)) (word_subword y (0,32)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; INT_VAL_WORD_SUB; VAL_WORD_ADD;
              GSYM INT_OF_NUM_CLAUSES; EXP; DIV_1; DIMINDEX_32; DIMINDEX_64;
              GSYM INT_OF_NUM_REM; INT_REM_REM_POW_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[]);;

let WORD_SUBWORD_SWAR_32_32 = prove
 (`(!x y. val(word_subword x (0,32):int32) + val(word_subword y (0,32):int32)
          < 2 EXP 32
          ==> word_subword (word_add x y:int64) (32,32):int32 =
              word_add (word_subword x (32,32)) (word_subword y (32,32))) /\
   (!x y. val(word_subword y (0,32):int32) <= val(word_subword x (0,32):int32)
          ==> word_subword (word_sub x y:int64) (32,32):int32 =
              word_sub (word_subword x (32,32)) (word_subword y (32,32)))`,
  CONJ_TAC THEN MESON_TAC[SWAR_ADD_LEMMA; SWAR_SUB_LEMMA; WORD_BLAST
    `(word_join:int32->int32->int64)
     (word_subword x (32,32)) (word_subword x (0,32)) = x /\
     word_subword((word_join:int32->int32->int64) h l) (0,32) = l /\
     word_subword((word_join:int32->int32->int64) h l) (32,32) = h`]);;

let EXTRA_SIMD_CLAUSES = prove
 (`(!x. word_subword ((word_zx:int64->int128) x) (0,32):int32 =
        word_subword x (0,32)) /\
   (!x. word_subword ((word_zx:int64->int128) x) (32,32):int32 =
        word_subword x (32,32)) /\
   (!x. word_zx (word_subword (x:int128) (0,64):int64):int32 =
        word_subword x (0,32)) /\
   (!x. word_ushr (word_subword (x:int128) (0,64):int64) 32 =
        word_subword x (32,32)) /\
   (!x. word_zx (word_subword (x:int128) (32,32):int64):int32 =
        word_subword x (32,32)) /\
   (!(x:int128) y.
        word_insert x (0,64)
              (word_subword (y:int128) (64,64):int128):int128 =
        word_join (word_subword x (64,64):int64)
                  (word_subword y (64,64):int64)) /\
   (!(x:int128) (y:int64).
        word_insert x (32,32) (word_zx y:int32):int128 =
        word_join (word_subword x (64,64):int64)
                  (word_join (word_subword y (0,32):int32)
                             (word_subword x (0,32):int32):int64)) /\
   (!(x:int128) (y:int64).
        word_insert x (0,32) (word_zx y:int32):int128 =
        word_join (word_subword x (64,64):int64)
                  (word_join (word_subword x (32,32):int32)
                             (word_subword y (0,32):int32):int64)) /\
   (!x:int64. word_subword (word_ushr x 32) (0,32):int32 =
              word_subword x (32,32))`,
  CONV_TAC WORD_BLAST);;

let EXTRA_SIMD_CONV ths =
  TOP_DEPTH_CONV
   (GEN_REWRITE_CONV I (EXTRA_SIMD_CLAUSES::ths) ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  REWRITE_CONV[];;

let UBIGNUM_PACK_UNPACK_CLAUSES = prove
 (`(word_subword:int64->num#num->int32)
      (word_insert (word_and l (word 0x3ffffff:int64)) (32,26) (h:int64))
      (0,32) =
    word(val l MOD 2 EXP 26) /\
   (word_subword:int64->num#num->int32)
      (word_insert (word_and l (word 0x3ffffff:int64)) (32,26) (h:int64))
      (32,32) =
    word(val h MOD 2 EXP 26) /\
   (word_subword:int64->num#num->int32)
      (word_insert (word_and l (word 0x3ffffff:int64)) (32,25) (h:int64))
      (0,32) =
      word(val l MOD 2 EXP 26) /\
   (word_subword:int64->num#num->int32)
      (word_insert (word_and l (word 0x3ffffff:int64)) (32,25) (h:int64))
      (32,32) =
   word(val h MOD 2 EXP 25)`,
  CONV_TAC WORD_BLAST);;

let SIMD_MASK_CLAUSES =
 ((fun th -> CONJ th (ONCE_REWRITE_RULE[WORD_AND_SYM] th)) o prove)
 (`(!(x:int64) (y:int64).
        word_subword (word_and (word 0x1ffffff0000000001ffffff:int128)
                               (word_join x y)) (0,64) =
        word_and (word 0x1ffffff) y) /\
   (!(x:int64) (y:int64).
        word_subword (word_and (word 0x1ffffff0000000001ffffff:int128)
                               (word_join x y)) (64,64) =
        word_and (word 0x1ffffff) x) /\
   (!(x:int64) (y:int64).
        word_subword (word_and (word 0x3ffffff0000000003ffffff:int128)
                               (word_join x y)) (0,64) =
        word_and (word 0x3ffffff) y) /\
   (!(x:int64) (y:int64).
        word_subword (word_and (word 0x3ffffff0000000003ffffff:int128)
                               (word_join x y)) (64,64) =
        word_and (word 0x3ffffff) x) /\
   (!(x:int64) (y:int64).
        word_subword (word_and (word 0xfffffffffe000000fffffffffe000000:int128)
                               (word_join x y)) (0,64) =
        word_and (word 0xfffffffffe000000) y) /\
   (!(x:int64) (y:int64).
        word_subword (word_and (word 0xfffffffffe000000fffffffffe000000:int128)
                               (word_join x y)) (64,64) =
        word_and (word 0xfffffffffe000000) x) /\
   (!(x:int64) (y:int64).
        word_subword (word_and (word 0xfffffffffc000000fffffffffc000000:int128)
                               (word_join x y)) (0,64) =
        word_and (word 0xfffffffffc000000) y) /\
   (!(x:int64) (y:int64).
        word_subword (word_and (word 0xfffffffffc000000fffffffffc000000:int128)
                               (word_join x y)) (64,64) =
        word_and (word 0xfffffffffc000000) x)`,
  CONV_TAC WORD_BLAST);;

let is_readcomponent tm =
  match tm with
    Comb(Comb(Const("read",_),c),s) -> true
  | _ -> false;;

let get_readcomponents =
  sort (<) o find_terms is_readcomponent;;

let rec process env tms =
  match tms with
    tm::otms ->
        let lv,rt = dest_eq tm in
        let nm = fst(dest_var lv) in
        let rcs = get_readcomponents(subst env rt) in
        let ixs = 0--(length rcs-1) in
        let nenv =
         map2 (fun rc i -> mk_var(nm^"_"^string_of_int i,type_of rc),rc)
         rcs ixs in
        process (nenv @ env) otms
  | [] -> env;;

let distinguished_components = process [] named_variables;;

let abbreviated_variables =
  map (subst distinguished_components) named_variables;;

let ABBREVIATE_STATE_COMPONENTS_TAC =
  let armstate_ty = `:armstate` in
  fun n ->
    let sv = mk_var("s"^string_of_int n,armstate_ty) in
    let this = filter (fun (v,t) -> rand t = sv) distinguished_components in
    MAP_EVERY (fun (v,sc) -> REABBREV_TAC(mk_eq(v,sc))) this;;

let ARM_NAMESTEPS_TAC execth =
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC execth [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(EXTRA_SIMD_CONV[])) THEN
    ABBREVIATE_STATE_COMPONENTS_TAC n);;

let find_abbrev s =
  let mfn tm =
    match tm with
      Comb(Comb(Const("=",_),_),Var(s',_)) -> s' = s
    | _ -> false in
  fun (asl,w) -> find mfn (map (concl o snd) asl);;

let USE_ABBREV cont s (asl,w) = cont (find_abbrev s (asl,w)) (asl,w);;

let STANDARDIZE_INEQ =
  let lemma = prove
   (`x:num < y ==> &x:real <= &y - &1`,
    REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN ARITH_TAC) in
  let rule0 = CONV_RULE (RAND_CONV REAL_INT_SUB_CONV) o MATCH_MP lemma
  and rule1 =
    CONV_RULE (RAND_CONV(NUM_REDUCE_CONV THENC REAL_INT_SUB_CONV)) o
    MATCH_MP lemma
  and rule2 = GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]
  and rule3 = MATCH_MP REAL_LT_IMP_LE
  and rule4 = MATCH_MP(TAUT `x:real <= y ==> x <= y`) in
  fun th ->
    let th' = tryfind (fun r -> r th) [rule0;rule1;rule2;rule3;rule4] in
    if is_ratconst(rand(concl th')) then th'
    else failwith "STANDARDIZE_INEQ";;

let BOUND_ABBREV_THEN cont th (asl,w) =
  let th1 = AP_TERM `real_of_int` (AP_TERM `int_of_num`
               (GEN_REWRITE_RULE I [GSYM VAL_EQ] th)) in
  let th2 = GEN_REWRITE_RULE (LAND_CONV o TOP_DEPTH_CONV)
   [GSYM INT_OF_NUM_CLAUSES; INT_VAL_WORD_SUB;
    VAL_WORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD_SHL;
    VAL_WORD_USHR; GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_REM] th1 in
  let th3 = CONV_RULE(INT_REM_DOWN_CONV THENC
                       ONCE_DEPTH_CONV(!word_SIZE_CONV)) th2 in
  let th4 = BOUNDER_RULE (mapfilter (STANDARDIZE_INEQ o snd) asl)
                         (lhand(concl th3)) in
  let th5 = GEN_REWRITE_RULE LAND_CONV [th3] (CONJUNCT2 th4) in
  let th6 = GEN_REWRITE_RULE LAND_CONV [int_of_num_th] th5 in
  let th7 = GEN_REWRITE_RULE I [REAL_OF_NUM_LE] th6 in
  cont th7 (asl,w);;

let (DEDUCE_DIGITBOUNDS_TAC:thm list->string->tactic) =
  let is_localdef s tm =
    match tm with
      Comb(Comb(Const("=",_),Comb(Const("ubignum_of_list",_),l)),
           Var(s',Tyapp("num",[]))) -> s' = s
    | _ -> false
  and is_remmy = can (term_match [] `x rem p`)
  and ic_tm = `int_of_num`
  and ri_tm = `real_of_int`
  and yemma = prove
   (`&x = i rem p /\
     real_of_int i = r /\
     a <= r /\ r <= &b
     ==> &0 <= a ==> x <= b`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    TRANS_TAC INT_LE_TRANS `i:int` THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_REM_LE_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN ASM_REAL_ARITH_TAC)
  and nemma = prove
   (`&x = i /\
     real_of_int i = r /\
     a <= r /\ r <= &b
     ==> x <= b`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES]) in
  fun ths s (asl,w) ->
    let sdef = concl(snd(find (is_localdef s o concl o snd) asl))
    and bths = mapfilter (STANDARDIZE_INEQ o snd) asl
    and EXPANSION_RULE v =
      SYM(snd(find (fun (_,th) -> let t = concl th in is_eq t && rand t = v)
                   asl)) in
    let FINDBOUND conv tm =
      let th =
       (conv THENC
        REWRITE_CONV[COND_RAND; COND_RATOR] THENC
        EXTRA_SIMD_CONV [SIMD_MASK_CLAUSES; UBIGNUM_PACK_UNPACK_CLAUSES] THENC
        SUBS_CONV ths THENC
        REWRITE_CONV[GSYM INT_OF_NUM_CLAUSES; INT_VAL_WORD_SUB;
                     VAL_WORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
                     VAL_WORD_SHL; VAL_WORD_USHR;
                     GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_REM] THENC
        INT_REM_DOWN_CONV THENC
        ONCE_DEPTH_CONV(!word_SIZE_CONV))
       (mk_comb(ic_tm,tm)) in
      let etm = rand(concl th) in
      let itm = if is_remmy etm then lhand etm else etm in
      let ith = REWRITE_CONV [COND_RAND; COND_RATOR; GSYM REAL_OF_INT_CLAUSES]
                             (mk_comb(ri_tm,itm)) in
      let bth = BOUNDER_RULE bths (rand(concl ith)) in
      if is_remmy etm then
        let lth = MATCH_MP yemma (CONJ th (CONJ ith bth)) in
        MP lth (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl lth))))
      else
        MATCH_MP nemma (CONJ th (CONJ ith bth)) in
    let eqs = mapfilter EXPANSION_RULE (frees(rand(lhand sdef))) in
    let conv = PURE_REWRITE_CONV eqs in
    MAP_EVERY (ASSUME_TAC o FINDBOUND conv)
               (dest_list(rand(lhand sdef))) (asl,w);;

let GEN_DEMODULATE_TAC pats =
  let moks = map (can o term_match []) pats in
  let patx tm = exists (fun f -> f tm) moks in
  fun (asl,w) ->
    let tms = sort free_in (find_terms patx w) in
    MAP_FIRST (fun t ->
      MP_TAC(PART_MATCH (lhand o rand) MOD_LT t) THEN ANTS_TAC THENL
       [ASM BOUNDER_TAC[]; DISCH_THEN SUBST1_TAC]) tms (asl,w);;

let DEMODULATE_TAC = GEN_DEMODULATE_TAC [`x MOD 2 EXP 32`; `x MOD 2 EXP 64`];;

let FULL_DEMODULATE_TAC = GEN_DEMODULATE_TAC [`x MOD 2 EXP n`];;

let GEN_DEREMULATE_TAC pats =
  let moks = map (can o term_match []) pats in
  let patx tm = exists (fun f -> f tm) moks in
  fun (asl,w) ->
    let tms = sort free_in (find_terms patx w) in
    MAP_FIRST (fun t ->
      MP_TAC(PART_MATCH (lhand o rand) INT_REM_LT t) THEN ANTS_TAC THENL
       [CONJ_TAC THENL [DISCH_THEN(K ALL_TAC); ALL_TAC] THEN ASM BOUNDER_TAC[];
        DISCH_THEN SUBST1_TAC]) tms (asl,w);;

let DEREMULATE_TAC = GEN_DEREMULATE_TAC [`x rem &2 pow 32`; `x rem &2 pow 64`];;

let FULL_DEREMULATE_TAC = GEN_DEREMULATE_TAC [`x rem &2 pow n`];;

let FULLEXPAND_TAC names =
  REPEAT(W(fun (asl,w) ->
    let names' = intersect names (map name_of (frees(lhand(rator w)))) in
    if names' <> [] then MAP_EVERY EXPAND_TAC names'
    else failwith "FULLEXPAND_TAC: expansion over"));;

let ARITHBLOCK_TAC =
  let word_simps =
   ((fun th -> CONJ th (ONCE_REWRITE_RULE[WORD_AND_SYM] th)) o WORD_BLAST)
    `val(word_and x (word 0x1FFFFFF):int64) = val x MOD 2 EXP 25 /\
     val(word_and x (word 0x3FFFFFF):int64) = val x MOD 2 EXP 26 /\
     val(word_and x (word 0xfffffffffc000000):int64) =
     2 EXP 26 * val x DIV 2 EXP 26 /\
     val(word_and x (word 0xfffffffffe000000):int64) =
     2 EXP 25 * val x DIV 2 EXP 25`
  and muldiv_simps = prove
   (`(&2 pow 25 * x) div &2 pow 25 = x /\
     (&2 pow 26 * x) div &2 pow 26 = x /\
     (&2 pow 26 * x) div &2 pow 25 = &2 * x /\
     (&2 pow 26 * x) div &2 pow 22 = &16 * x /\
     (&2 pow 25 * x) div &2 pow 24 = &2 * x /\
     (&2 pow 25 * x) div &2 pow 21 = &16 * x`,
    REPEAT CONJ_TAC THEN INT_ARITH_TAC) in
  fun ths ->
    W(MAP_EVERY (EXPAND_TAC o name_of) o frees o snd) THEN
    W(FULLEXPAND_TAC o map name_of o frees o lhand o rator o snd) THEN
    REWRITE_TAC[ubignum_of_list] THEN
    CONV_TAC
     (EXTRA_SIMD_CONV [SIMD_MASK_CLAUSES; UBIGNUM_PACK_UNPACK_CLAUSES]) THEN
    CONV_TAC(SUBS_CONV ths) THEN
    REWRITE_TAC[word_simps; GSYM INT_OF_NUM_CLAUSES;
                GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_REM;
                VAL_WORD; VAL_WORD_ADD; VAL_WORD_MUL; INT_VAL_WORD_SUB;
                VAL_WORD_ZX_GEN; VAL_WORD_SHL; VAL_WORD_USHR] THEN
    CONV_TAC(ONCE_DEPTH_CONV(!word_SIZE_CONV)) THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REPEAT DEREMULATE_TAC THEN
    REWRITE_TAC[muldiv_simps] THEN
    TRY FULL_DEREMULATE_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(W(fun (asl,w) ->
      let dmotms =
         find_terms (can (term_match [] `m div n`)) w @
         find_terms (can (term_match [] `m rem n`)) w in
      let tm = hd(sort free_in dmotms) in
      let th1 = SPECL [lhand tm; rand tm] INT_DIVISION_SIMP in
      let qtm = lhand(lhand(lhand(concl th1)))
      and rtm = rand(lhand(concl th1)) in
      MP_TAC th1 THEN
      ABBREV_TAC(mk_eq(genvar(type_of qtm),qtm)) THEN
      ABBREV_TAC(mk_eq(genvar(type_of rtm),rtm)) THEN
      POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN DISCH_TAC)) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (INT_ARITH
     `n * q + r:int = x ==> r = x - n * q`))) THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; p_25519; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN REAL_INTEGER_TAC;;

let extra = prove
 (`(word_zx:int64->int32) (word_add x x) =
   word_zx (word_mul (word 2:int32) (word_zx x))`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD_MUL] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `MIN 64 32 = 32`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics for the inlined field multiplication proof.            *)
(* ------------------------------------------------------------------------- *)

let lemma0 = prove
 (`!x0 x1:int64.
        &(val(if val x0 <= val x1 then word_sub x1 x0
         else word_neg(word_sub x1 x0))):real = abs(&(val x1) - &(val x0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[WORD_NEG_SUB; REAL_ARITH
   `abs(x - y):real = if y <= x then x - y else y - x`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES; NOT_LE]) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; LT_IMP_LE; REAL_OF_NUM_SUB]);;

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
 (`!p x0 x1 y0 y1:real.
    (x0 + p * x1) * (y0 + p * y1) =
    x0 * y0 + p pow 2 * x1 * y1 +
    p * (x0 * y0 + x1 * y1 +
         --(&1) pow bitval(y1 <= y0 <=> x1 < x0) *
         abs(x1 - x0) * abs(y0 - y1))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`y1:real <= y0`; `x1:real < x0`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ASM_REAL_ARITH_TAC);;

let VAL_WORD_MADDL_0 = prove
 (`!x y. val(word(0 + val(x:int32) * val(y:int32)):int64) = val x * val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; VAL_WORD_EQ_EQ] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[GSYM DIMINDEX_32; VAL_BOUND]);;

let DIVMOD_32_32 = prove
 (`!n. (2 EXP 32 * n) MOD 2 EXP 64 = 2 EXP 32 * n MOD 2 EXP 32`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let DIVMOD_33_31 = prove
 (`!n. (2 EXP 33 * n) MOD 2 EXP 64 = 2 EXP 33 * n MOD 2 EXP 31`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let DIVMOD_63_64 = prove
 (`!n. (2 EXP 63 * n) MOD 2 EXP 64 = 2 EXP 63 * n MOD 2`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let VAL_WORD_SPLIT32 = prove
 (`!x. 2 EXP 32 * val(word_zx(word_ushr x 32):int32) + val(word_zx x:int32) =
       val(x:int64)`,
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM MOD_MULT_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND_64]);;

let p25519redlemma32 = prove
 (`!h l. h < 2 EXP 256 /\ l < 2 EXP 256
         ==> let q = (38 * h DIV 2 EXP 224 + l DIV 2 EXP 224) DIV 2 EXP 31 in
             q <= 77 /\
             q < 2 EXP 64 /\
             (q + 1) * p_25519 <= (38 * h + l) + p_25519 /\
             38 * h + l < (q + 1) * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let endp25519redlemma = prove
 (`(&z == &2 pow 255 + x) (mod (&2 pow 256)) /\
   --(&p_25519) <= x /\ x < &p_25519 /\ z < 2 EXP 256
   ==> x rem &p_25519 =
       if z < 2 EXP 255 then &z - &19  else &z - &2 pow 255`,
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&z:int < &2 pow 255 <=> x:int < &0` SUBST1_TAC THENL
   [ALL_TAC;
   COND_CASES_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
    [EXISTS_TAC `--(&1):int`; EXISTS_TAC `&0:int`]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_IMP_EQ)) THEN
  REWRITE_TAC[p_25519] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p_25519]) THEN ASM_INT_ARITH_TAC);;

let KARATSUBA12_TAC =
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[lemma2; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ACCUMULATOR_POP_ASSUM_LIST(fun thl ->
    MP_TAC(end_itlist CONJ(rev thl)) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; GSYM NOT_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC(filter(is_ratconst o rand o concl) (DECARRY_RULE thl)) THEN
    REAL_INTEGER_TAC);;

let p25519weakredlemma = prove
 (`!n. n <= 2 EXP 62 * 2 EXP 256
       ==> let q = n DIV 2 EXP 255 in
           q < 2 EXP 64 /\
           q * p_25519 <= n /\
           n < q * p_25519 + 2 * p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let LOCAL_MUL_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_mc 180 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x27f8) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X17 s = read X17 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                     X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "y_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "x_" o lhand o concl) THEN

  (*** Retrofitted insertion for the 32-bit fiddling (1 of 2) ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC [9;11;12;14] (1--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; VAL_WORD_USHR; VAL_WORD_SHL;
    DIVMOD_32_32; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s14:int64)) + &(val(sum_s12:int64)):real =
    &(val(x_0:int64)) * &(val(y_0:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `y_0:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`sum_s12:int64`,`mullo_s3:int64`) THEN
    SPEC_TAC(`sum_s14:int64`,`mulhi_s3:int64`) THEN
    SPEC_TAC(`s14:armstate`,`s4:armstate`) THEN REPEAT STRIP_TAC] THEN

  (*** First nested block multiplying the lower halves ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC
   [5;10;11;15;17;18;19;22;24;25] (5--25) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = bignum_of_wordlist[mullo_s3;sum_s22]`;
    `q1 = bignum_of_wordlist[sum_s24;sum_s25]`] THEN
  SUBGOAL_THEN
   `2 EXP 128 * q1 + q0 =
    bignum_of_wordlist [x_0;x_1] * bignum_of_wordlist[y_0;y_1]`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q0"; "q1"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Retrofitted insertion for the 32-bit fiddling (2 of 2) ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC [34;36;37;39] (26--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; VAL_WORD_USHR; VAL_WORD_SHL;
    DIVMOD_32_32; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s39:int64)) + &(val(sum_s37:int64)):real =
    &(val(x_2:int64)) * &(val(y_2:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_2:int64`; `y_2:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`sum_s37:int64`,`mullo_s28:int64`) THEN
    SPEC_TAC(`sum_s39:int64`,`mulhi_s28:int64`) THEN
    SPEC_TAC(`s39:armstate`,`s29:armstate`) THEN REPEAT STRIP_TAC] THEN

  (*** Second nested block multiplying the upper halves ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC
   [30;35;36;40;42;43;44;47;49;50] (30--50) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN

  ABBREV_TAC
   `q23 = bignum_of_wordlist[mullo_s28;sum_s47; sum_s49;sum_s50]` THEN
  SUBGOAL_THEN
   `q23 = bignum_of_wordlist [x_2;x_3] * bignum_of_wordlist[y_2;y_3]`
  ASSUME_TAC THENL
   [EXPAND_TAC "q23" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The sign-magnitude difference computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC
    [53;54; 57;58; 61;63; 65;67] (51--68) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN

  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s58 <=> carry_s54)`;
   `xd = bignum_of_wordlist[sum_s61;sum_s63]`;
   `yd = bignum_of_wordlist[sum_s65;sum_s67]`] THEN
  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_2;x_3]) -
     &(bignum_of_wordlist[x_0;x_1])) *
    (&(bignum_of_wordlist[y_0;y_1]) -
     &(bignum_of_wordlist[y_2;y_3])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s54 * &xd) *
      (--(&1) pow bitval carry_s58 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s54 <=>
       bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1]) /\
      (carry_s58 <=>
       bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])`
     (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    BINOP_TAC THEN REWRITE_TAC[bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = --(&1) pow 1 * z <=> y - x = z`] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
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

  (*** Clean up the overall sign ***)

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_XOR_MASKS]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** The augmented H' = H + L_top ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC (69--72) (69--72) THEN
  MAP_EVERY ABBREV_TAC
   [`q2 = bignum_of_wordlist[sum_s69;sum_s70]`;
    `q3 = bignum_of_wordlist[sum_s71;sum_s72]`] THEN
  SUBGOAL_THEN
   `2 EXP 128 * q3 + q2 =
    bignum_of_wordlist [x_2;x_3] * bignum_of_wordlist[y_2;y_3] + q1`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "q2"; "q3"] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    REPEAT(CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o LAND_CONV) [SYM th]) THEN
    MAP_EVERY EXPAND_TAC ["q23"] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Third nested block multiplying the absolute differences ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC
   [73;75;80;81;85;87;88;89;92;94;95] (73--95) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN
  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist[mullo_s73; sum_s92; sum_s94; sum_s95])`
  SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The rest of the basic 4x4->8 multiply computation and its proof ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC
   [96;97;98;99;100;101;104;106;108;110;111;112] (96--112) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s22; sum_s104; sum_s106]`;
    `h = bignum_of_wordlist[sum_s108; sum_s110; sum_s111; sum_s112]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [DISCARD_STATE_TAC "s112" THEN MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    SUBGOAL_THEN
     `&m * &n:real =
      (&1 + &2 pow 128) * (&q0 + &2 pow 128 * &q2 + &2 pow 256 * &q3) +
      &2 pow 128 *
      (&(bignum_of_wordlist [x_2; x_3]) -
       &(bignum_of_wordlist [x_0; x_1])) *
      (&(bignum_of_wordlist [y_0; y_1]) -
       &(bignum_of_wordlist [y_2; y_3]))`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`2 EXP 128 * q1 + q0 =
         bignum_of_wordlist[x_0; x_1] * bignum_of_wordlist[y_0; y_1]`;
        `2 EXP 128 * q3 + q2 =
         bignum_of_wordlist[x_2; x_3] * bignum_of_wordlist[y_2; y_3] +
         q1`] THEN
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[]] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"; "q0"; "q2"; "q3"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPECL [`h:num`; `l:num`] p25519redlemma32) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    LET_TAC THEN STRIP_TAC] THEN

  (*** The somewhat fiddly reduction with 32-bit operations etc. ***)

  ARM_STEPS_TAC CURVE25519_X25519_BYTE_EXEC (113--137) THEN

  MAP_EVERY (fun t -> REABBREV_TAC t THEN POP_ASSUM MP_TAC)
   [`u0 = read X7 s137`;
    `u1 = read X8 s137`;
    `u2 = read X9 s137`;
    `u3 = read X10 s137`;
    `u4 = read X11 s137`;
    `u5 = read X12 s137`;
    `u6 = read X13 s137`;
    `u7 = read X14 s137`] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [word_add; modular; ADD_CLAUSES; VAL_WORD; VAL_WORD_ZX_GEN;
    VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
   `n < 2 EXP 64 ==> n MOD 2 EXP 32 * 38 < 2 EXP 64`] THEN
  STRIP_TAC THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC [142;144;146;150] (138--150) THEN
  SUBGOAL_THEN `word_ushr u7 31:int64 = word q` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_USHR] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT] THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s106:int64) DIV 2 EXP 32 +
           val(sum_s112:int64) DIV 2 EXP 32 * 38):int64 = u7`)) THEN
    MAP_EVERY EXPAND_TAC ["q"; "l"; "h"] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD; ARITH_RULE `a + b * 38 = 38 * b + a`] THEN
    MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN
    REWRITE_TAC[GSYM VAL_WORD_USHR] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_add (u0:int64)
       (word(19 + 19 * val((word_zx:int64->int32)(word q)))))):real =
    &(val u0) + &19 * (&q + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; VAL_WORD; VAL_WORD_ZX_GEN;
                DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[ARITH_RULE `q <= 77 ==> q < 2 EXP MIN 64 32`; MOD_LT] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `19 + 19 * q = 19 * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s108:int64) MOD 2 EXP 32 * 38 +
           val(mullo_s3:int64) MOD 2 EXP 32):int64 = u0`)) THEN
    MATCH_MP_TAC(ARITH_RULE
     `w <= 2 EXP 63 /\ q <= 77 ==> w + 19 * (q + 1) < 2 EXP 64`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_LE; FIRST_ASSUM ACCEPT_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  REWRITE_TAC[REAL_VAL_WORD_XOR; WORD_AND_POW2_BITVAL;
              REWRITE_RULE[DIMINDEX_64; NUM_REDUCE_CONV `64 - 1`]
                (ISPEC `x:int64` WORD_SHL_LSB)] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIVMOD_63_64] THEN
  SIMP_TAC[MOD_LT; BITVAL_BOUND_ALT; GSYM REAL_OF_NUM_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM VAL_MOD_2; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `r = bignum_of_wordlist[sum_s142; sum_s144; sum_s146; sum_s150]` THEN

  SUBGOAL_THEN
   `(&r:int == &2 pow 255 + &(38 * h + l) - (&q + &1) * &p_25519)
    (mod (&2 pow 256))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `38 * h + l =
      bignum_of_wordlist[u0;u1;u2;u3] +
      2 EXP 32 * bignum_of_wordlist[u4;u5;u6;u7]`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (can (term_match [] `word x = n`) o concl))) THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD; DIMINDEX_64] THEN
      SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
        `m < 2 EXP 64 /\ n < 2 EXP 64
         ==> m DIV 2 EXP 32 + n DIV 2 EXP 32 * 38 < 2 EXP 64`;
        ARITH_RULE `m MOD 2 EXP 32 * 38 + n MOD 2 EXP 32 < 2 EXP 64`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 32 * bignum_of_wordlist [u4; u5; u6; u7] =
      bignum_of_wordlist
       [word_shl u4 32;
        word_subword ((word_join:int64->int64->int128) u5 u4) (32,64);
        word_subword ((word_join:int64->int64->int128) u6 u5) (32,64);
        word_subword ((word_join:int64->int64->int128) u7 u6) (32,64);
        word_ushr u7 32]`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
                int_mul_th; int_pow_th] THEN
    EXPAND_TAC "r" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final optional correction ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC (154--157) (151--160) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`255`;
    `(if r < 2 EXP 255 then &r - &19 else &r - &2 pow 255):real`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s160" THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `r < 2 EXP 255 <=> r DIV 2 EXP 192 < 2 EXP 63`] THEN
    EXPAND_TAC "r" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
    ABBREV_TAC `bb <=> val(sum_s150:int64) < 2 EXP 63` THEN
    SUBGOAL_THEN
     `ival(word_and sum_s150 (word 9223372036854775808):int64) < &0 <=> ~bb`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM MSB_IVAL; BIT_WORD_AND] THEN
      REWRITE_TAC[MSB_VAL] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "bb" THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        endp25519redlemma)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_ARITH `--p:int <= x - y <=> y <= x + p`] THEN
      REWRITE_TAC[INT_ARITH `x - y:int < p <=> x < y + p`] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "r" THEN BOUNDER_TAC[];
      REWRITE_TAC[INT_ARITH `x - q * p:int = --q * p + x`] THEN
      REWRITE_TAC[INT_REM_MUL_ADD] THEN
      REWRITE_TAC[int_eq; int_of_num_th; INT_OF_NUM_REM] THEN
      DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[int_of_num_th; int_sub_th; int_pow_th]]]);;

(* ------------------------------------------------------------------------- *)
(* Inlined modular inverse proof.                                            *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MODINV_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (curve25519_x25519_byte_mc,CURVE25519_X25519_BYTE_EXEC,0x13f4,
    (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_mc] THENC TRIM_LIST_CONV)
    `TRIM_LIST (12,16) bignum_inv_p25519_mc`,
    CORE_INV_P25519_CORRECT)
   [`read X0 s`; `read X1 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `pc + 0x13f4`; `stackpointer:int64`];;

(* ------------------------------------------------------------------------- *)
(* The swapping-based Montgomery ladder more abstractly.                     *)
(* ------------------------------------------------------------------------- *)

let flipladder = define
 `flipladder x n 0 = ((&1,&0),(&x rem &p_25519,&1)) /\
  flipladder x n (i + 1) =
        let (x2,z2),(x3,z3) = flipladder x n i in
        montgomery_xzdouble curve25519
          (if ODD(n DIV 2 EXP (255 - (i + 1))) <=> ODD(n DIV 2 EXP (255 - i))
           then (x2,z2) else (x3,z3)),
        montgomery_xzdiffadd curve25519 (&x,&1) (x2,z2) (x3,z3)`;;

let ladder_x2 = define
  `ladder_x2 x n i = FST(FST(flipladder x n (255 - i)))`;;

let ladder_z2 = define
  `ladder_z2 x n i = SND(FST(flipladder x n (255 - i)))`;;

let ladder_x3 = define
  `ladder_x3 x n i = FST(SND(flipladder x n (255 - i)))`;;

let ladder_z3 = define
  `ladder_z3 x n i = SND(SND(flipladder x n (255 - i)))`;;

let deproject = define
 `deproject (x,z) =
   (x * (if p_25519 divides z then 0 else inverse_mod p_25519 z))
   MOD p_25519`;;

let curve25519x_represents = define
 `curve25519x_represents (f:A ring) P n (X,Z) <=>
        P IN group_carrier(montgomery_group (curve25519x f)) /\
        montgomery_xz f (group_pow (montgomery_group (curve25519x f)) P n)
                        (ring_of_int f X,ring_of_int f Z)`;;

let CURVE25519X_REPRESENTS_DOUBLE = prove
 (`!(f:A ring) P n Q.
        field f /\ ring_char f = p_25519 /\
        curve25519x_represents f P n Q
        ==> curve25519x_represents f P (2 * n)
                (montgomery_xzdouble curve25519 Q)`,
  REWRITE_TAC[FORALL_PAIR_THM; curve25519x_represents] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `P:(A#A)option`; `n:num`; `X:int`; `Z:int`] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM PAIR] THEN
  PURE_REWRITE_TAC[curve25519x_represents] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`f:A ring`; `ring_of_num (f:A ring) A_25519`; `ring_of_num (f:A ring) 1`;
    `P:(A#A)option`; `n:num`; `ring_of_int f X:A,ring_of_int f Z`]
   MONTGOMERY_XZDOUBLE_GROUP) THEN
  ASM_SIMP_TAC[GSYM curve25519x; MONTGOMERY_NONSINGULAR_CURVE25519X] THEN
  REWRITE_TAC[RING_OF_NUM; p_25519; ARITH_EQ] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[montgomery_xzdouble; curve25519x; curve25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RING_OF_INT_REM] THEN
  REWRITE_TAC[GSYM RING_OF_INT_CLAUSES] THEN
  REWRITE_TAC[RING_OF_INT_OF_NUM]);;

let CURVE25519X_REPRESENTS_DIFFADD_LEFT = prove
 (`!(f:A ring) P n X Qm Qn.
        field f /\ ring_char f = p_25519 /\ ~(&p_25519 divides X) /\
        curve25519x_represents f P 1 (X,&1) /\
        curve25519x_represents f P (n + 1) Qm /\
        curve25519x_represents f P n Qn
        ==> curve25519x_represents f P (2 * n + 1)
                (montgomery_xzdiffadd curve25519 (X,&1) Qm Qn)`,
  REWRITE_TAC[FORALL_PAIR_THM; curve25519x_represents] THEN
  MAP_EVERY X_GEN_TAC
   [`f:A ring`; `P:(A#A)option`; `n:num`; `X:int`;
    `Xm:int`; `Zm:int`; `Xn:int`; `Zn:int`] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM PAIR] THEN
  PURE_REWRITE_TAC[curve25519x_represents] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`f:A ring`; `ring_of_num (f:A ring) A_25519`; `ring_of_num (f:A ring) 1`;
    `P:(A#A)option`; `n:num`;
    `ring_of_int f X:A,ring_of_int f (&1)`;
    `ring_of_int f Xm:A,ring_of_int f Zm`;
    `ring_of_int f Xn:A,ring_of_int f Zn`]
   MONTGOMERY_XZDIFFADD_GROUP) THEN
  ASM_SIMP_TAC[GSYM curve25519x; MONTGOMERY_NONSINGULAR_CURVE25519X] THEN
  ASM_REWRITE_TAC[RING_OF_NUM; p_25519; ARITH_EQ] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INT_EQ_0] THEN
    REWRITE_TAC[GSYM num_divides; DIVIDES_MOD; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[GROUP_POW_1];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC] THEN
  REWRITE_TAC[montgomery_xzdiffadd; curve25519x; curve25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; PAIR_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RING_OF_INT_REM] THEN
  REWRITE_TAC[GSYM RING_OF_INT_CLAUSES] THEN
  REWRITE_TAC[RING_OF_INT_OF_NUM]);;

let CURVE25519X_REPRESENTS_DIFFADD_RIGHT = prove
 (`!(f:A ring) P n X Qm Qn.
        field f /\ ring_char f = p_25519 /\ ~(&p_25519 divides X) /\
        curve25519x_represents f P 1 (X,&1) /\
        curve25519x_represents f P n Qm /\
        curve25519x_represents f P (n + 1) Qn
        ==> curve25519x_represents f P (2 * n + 1)
                (montgomery_xzdiffadd curve25519 (X,&1) Qm Qn)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT
   `p /\ q /\ r /\ s /\ t /\ u <=> p /\ q /\ r /\ s /\ u /\ t`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CURVE25519X_REPRESENTS_DIFFADD_LEFT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[montgomery_xzdiffadd; curve25519] THEN
  REWRITE_TAC[PAIR_EQ; INTEGER_MOD_RING_CLAUSES] THEN CONJ_TAC THEN
  CONV_TAC INT_REM_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  INT_ARITH_TAC);;

let FLIPLADDER_MAIN = prove
 (`!(f:A ring) P x n i.
        field f /\ ring_char f = p_25519 /\ ~(p_25519 divides x) /\
        curve25519x_represents f P 1 (&x,&1) /\ n < 2 EXP 255 /\ i <= 255
        ==> curve25519x_represents f P (n DIV 2 EXP (255 - i))
                ((if ODD(n DIV 2 EXP (255 - i)) then SND else FST)
                 (flipladder x n i)) /\
            curve25519x_represents f P (n DIV 2 EXP (255 - i) + 1)
                ((if ODD(n DIV 2 EXP (255 - i)) then FST else SND)
                 (flipladder x n i))`,
  REWRITE_TAC[num_divides] THEN REPLICATE_TAC 4 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  INDUCT_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[flipladder] THEN
    ASM_SIMP_TAC[SUB_0; DIV_LT; ARITH_ODD; ADD_CLAUSES] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [curve25519x_represents]) THEN
    SIMP_TAC[curve25519x_represents; group_pow] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_OF_INT_REM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[CURVE25519X_GROUP; GSYM curve25519x_group] THEN
    REWRITE_TAC[montgomery_xz; RING_OF_INT_1; RING_OF_INT_0] THEN
    REWRITE_TAC[RING_0; RING_1] THEN ASM_MESON_TAC[field];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
  REWRITE_TAC[flipladder; ADD1] THEN
  ASM_SIMP_TAC[ARITH_RULE
     `SUC i <= 255 ==> 255 - i = SUC(255 - (i + 1))`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP)] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ABBREV_TAC `m = n DIV 2 EXP (255 - (i + 1)) DIV 2` THEN
  MP_TAC(SPECL [`n DIV 2 EXP (255 - (i + 1))`; `2`]
   (CONJUNCT1 DIVISION_SIMP)) THEN
  ASM_REWRITE_TAC[MOD_2_CASES; GSYM NOT_ODD; COND_SWAP] THEN
  MAP_EVERY ABBREV_TAC
   [`b <=> ODD m`; `c <=> ODD(n DIV 2 EXP (255 - (i + 1)))`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MAP_EVERY ASM_CASES_TAC [`b:bool`; `c:bool`] THEN
  ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `m * 2 = 2 * m`;
              ARITH_RULE `(2 * m + 1) + 1 = 2 * (m + 1)`] THEN
  ASM_MESON_TAC[CURVE25519X_REPRESENTS_DOUBLE;
        CURVE25519X_REPRESENTS_DIFFADD_LEFT;
        CURVE25519X_REPRESENTS_DIFFADD_RIGHT]);;

let FLIPLADDER_DEGENERATE = prove
 (`!x n i xm zm xn zn.
        p_25519 divides x /\ flipladder x n i = (xm,zm),(xn,zn)
        ==> zm = &0 /\ xn = &0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[num_divides; GSYM INT_REM_EQ_0] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[flipladder; PAIR_EQ] THENL
   [MESON_TAC[]; REWRITE_TAC[flipladder; ADD1]] THEN
  REPEAT GEN_TAC THEN LET_TAC THEN
  SUBGOAL_THEN `z2:int = &0 /\ x3:int = &0` MP_TAC THENL
   [ASM_MESON_TAC[]; REPLICATE_TAC 2 (POP_ASSUM(K ALL_TAC))] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[montgomery_xzdouble; curve25519; montgomery_xzdouble;
                  PAIR_EQ; montgomery_xzdiffadd; INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; INT_SUB_REFL; INT_POW_ZERO;
              ARITH_EQ; INT_REM_ZERO]);;

let DEPROJECT_LADDER_EVEN = prove
 (`!x n x2 z2.
        n < 2 EXP 255 /\ EVEN n /\
        (&x2 == ladder_x2 x n 0) (mod &p_25519) /\
        (&z2 == ladder_z2 x n 0) (mod &p_25519)
        ==> purex25519(n,x) = deproject(x2,z2)`,
  REWRITE_TAC[ladder_x2; ladder_z2; SUB_0] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PUREX25519_UNIQUE_IMP THEN CONJ_TAC THENL
   [REWRITE_TAC[deproject; p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`f:(int#int)ring`; `Q:((int#int)#(int#int))option`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `p_25519 divides x` THENL
   [MP_TAC(ISPECL [`x:num`; `n:num`; `255`] FLIPLADDER_DEGENERATE) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`ladder_x2 x n 0`; `ladder_z2 x n 0`;
      `ladder_x3 x n 0`; `ladder_z3 x n 0`]) THEN
    ASM_REWRITE_TAC[ladder_x2; ladder_z2; ladder_x3; ladder_z3] THEN
    ASM_REWRITE_TAC[SUB_0] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[deproject; num_divides; GSYM INT_CONG_0_DIVIDES] THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_0; RING_OF_NUM_0] THEN
    REWRITE_TAC[curve25519x_group; curve25519x] THEN
    MATCH_MP_TAC MONTGOMERY_XMAP_EQ_0_POW THEN
    ASM_REWRITE_TAC[GSYM curve25519x_group; GSYM curve25519x; RING_OF_NUM] THEN
    ASM_SIMP_TAC[MONTGOMERY_NONSINGULAR_CURVE25519X; RING_OF_NUM_EQ_0] THEN
    REWRITE_TAC[p_25519; ARITH_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(int#int)ring`; `Q:((int#int)#(int#int))option`;
                 `x:num`; `n:num`; `255`]
         FLIPLADDER_MAIN) THEN
  ASM_REWRITE_TAC[SUB_REFL; EXP; DIV_1; LE_REFL] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[curve25519x_represents; GROUP_POW_1;
      GSYM curve25519x_group; RING_OF_INT_OF_NUM; RING_OF_NUM_1] THEN
    ASM_SIMP_TAC[MONTGOMERY_XZ_XMAP; RING_OF_NUM_EQ_0; RING_OF_NUM];
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN]] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM PAIR] THEN
  REWRITE_TAC[curve25519x_represents] THEN
  ONCE_REWRITE_TAC[GSYM RING_OF_INT_REM] THEN
  ASM_REWRITE_TAC[GSYM curve25519x_group] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
        GEN_REWRITE_RULE I [GSYM INT_REM_EQ])) THEN
  SUBST1_TAC(SYM(ASSUME `ring_char(f:(int#int)ring) = p_25519`)) THEN
  REWRITE_TAC[RING_OF_INT_REM; RING_OF_INT_OF_NUM] THEN
  SPEC_TAC(`group_pow (curve25519x_group(f:(int#int)ring)) Q n`,
           `P:((int#int)#(int#int))option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  GEN_REWRITE_TAC RAND_CONV [FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[montgomery_xmap; montgomery_xz; deproject;
               RING_OF_NUM_EQ_0; MULT_CLAUSES; MOD_0; RING_OF_NUM_0] THEN
  X_GEN_TAC `y:int#int` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBST1_TAC(SYM(ASSUME `ring_char(f:(int#int)ring) = p_25519`)) THEN
  REWRITE_TAC[RING_OF_NUM_MOD; RING_OF_NUM_MUL; ring_div] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RING_LINV_UNIQUE THEN
  REWRITE_TAC[RING_OF_NUM; GSYM RING_OF_NUM_1] THEN
  ASM_REWRITE_TAC[GSYM RING_OF_NUM_MUL; RING_OF_NUM_EQ] THEN
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ] THEN
  ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519]);;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let CURVE25519_X25519_BYTE_CORRECT = time prove
 (`!res scalar n point X pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,224))
        [(word pc,0x27f8); (res,32); (scalar,32); (point,32)] /\
    nonoverlapping (res,32) (word pc,0x27f8)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_mc /\
              read PC s = word(pc + 0x2c) /\
              read SP s = stackpointer /\
              C_ARGUMENTS [res; scalar; point] s /\
              read (memory :> bytes(scalar,32)) s = n /\
              read (memory :> bytes(point,32)) s = X)
         (\s. read PC s = word (pc + 0x27c8) /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,X))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10;
                      Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20;
                      Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(res,32);
                      memory :> bytes(stackpointer,224)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `n_input:num`; `point:int64`; `X_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  (*** Modified inputs, though nn is not literally computed ***)

  ABBREV_TAC `nn = 2 EXP 254 + n_input MOD 2 EXP 254 - n_input MOD 8` THEN
  ABBREV_TAC `X = X_input MOD 2 EXP 255` THEN
  REWRITE_TAC[rfcx25519] THEN ONCE_REWRITE_TAC[GSYM PUREX25519_MOD] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_PDOWN_TAC `255` `pc + 0x308` `pc + 0x12fc`
   `\i s.
      (read SP s = stackpointer /\
       read (memory :> bytes64(word_add stackpointer (word 192))) s = res /\
       (bignum_from_memory(stackpointer,4) s == nn) (mod (2 EXP 255)) /\
       read Q31 s = word 0x1300000013 /\
       read Q30 s = word 0x3ffffff0000000003ffffff /\
       read Q29 s = word 0x07fffffe07fffffc /\
       read (memory :> bytes64(word_add stackpointer (word 72))) s =
       word 0x07fffffe07fffffc /\
       read Q28 s = word 0x07fffffe07ffffb4 /\
       read (memory :> bytes64(word_add stackpointer (word 80))) s =
       word 0x07fffffe07ffffb4 /\
       read X0 s = word_sub (word i) (word 1) /\
       read (memory :> bytes64(word_add stackpointer (word 200))) s =
       word_sub (word i) (word 1) /\
       read (memory :> bytes64(word_add stackpointer (word 208))) s =
       word(bitval(ODD(nn DIV 2 EXP i))) /\
       normalized_ubignum_preglist
        [memory :> bytes64 (word_add stackpointer (word 32));
         memory :> bytes64 (word_add stackpointer (word 40));
         memory :> bytes64 (word_add stackpointer (word 48));
         memory :> bytes64 (word_add stackpointer (word 56));
         memory :> bytes64 (word_add stackpointer (word 64))] (&X) s /\
       normalized_ubignum_qreglist[Q0;Q2;Q4;Q6;Q8] (ladder_x2 X nn i) s /\
       normalized_ubignum_qreglist[Q10;Q12;Q14;Q16;Q18] (ladder_x3 X nn i) s /\
       normalized_ubignum_qreglist'[Q1;Q3;Q5;Q7;Q9] (ladder_z2 X nn i) s /\
       normalized_ubignum_qreglist[Q11;Q13;Q15;Q17;Q19] (ladder_z3 X nn i) s) /\
      (read CF s <=> 0 < i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    MAP_EVERY (fun n -> GHOST_INTRO_TAC
      (mk_var("init_q"^string_of_int n,`:int128`))
      (list_mk_icomb "read" [mk_const("Q"^string_of_int n,[])])) (0--31) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BYTES_DIGITIZE_TAC "nb_" `read (memory :> bytes (scalar,32)) s0` THEN
    BYTES_DIGITIZE_TAC "xb_" `read (memory :> bytes (point,32)) s0` THEN
    ARM_STEPS_TAC CURVE25519_X25519_BYTE_EXEC (1--183) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "nn" THEN REWRITE_TAC[CONG] THEN
      SIMP_TAC[MOD_LT; ARITH_RULE
       `2 EXP 254 + n_input MOD 2 EXP 254 - n_input MOD 8 < 2 EXP 255`] THEN
      MATCH_MP_TAC(ARITH_RULE
       `m <= b /\ x + m:num = a + b ==> x = a + b - m`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `8 = 2 EXP (MIN 254 3)`] THEN
        REWRITE_TAC[GSYM MOD_MOD_EXP_MIN; MOD_LE];
        ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE
       `x MOD 2 EXP 255 + n MOD 8 = 2 EXP 254 + n MOD 2 EXP 254 <=>
        x + 2 EXP 254 * n DIV 2 EXP 254 + n MOD 8 =
        2 EXP 254 + 2 EXP 255 * x DIV 2 EXP 255 + n`] THEN
      SUBGOAL_THEN `n_input MOD 8 = val(nb_0:byte) MOD 8` SUBST1_TAC THENL
       [EXPAND_TAC "n_input" THEN REWRITE_TAC[GSYM CONG] THEN
        MATCH_MP_TAC(NUMBER_RULE
         `n divides y ==> (x + y:num == x) (mod n)`) THEN
        REPEAT(MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC) THEN
        MATCH_MP_TAC DIVIDES_RMUL THEN
        REWRITE_TAC[DIVIDES_MOD] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `n_input DIV 2 EXP 254 = val(nb_31:byte) DIV 2 EXP 6`
      SUBST1_TAC THENL
       [EXPAND_TAC "n_input" THEN REWRITE_TAC[ADD_ASSOC] THEN
        REWRITE_TAC[ARITH_RULE `2 EXP 254 = 2 EXP 248 * 2 EXP 6`] THEN
        SIMP_TAC[GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC[EQ_ADD_RCANCEL_0; DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
        BOUNDER_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "n_input" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; WORD_BLAST
       `val(word_and x (word 18446744073709551608:int64)) =
        8 * val x DIV 8`] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `2 EXP 64 * h = 2 EXP 3 * 2 EXP 61 * h`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[WORD_BLAST
       `val(word_or n (word 4611686018427387904:int64)) =
        2 EXP 63 * bitval(bit 63 n) + 2 EXP 62 + val(n) MOD 2 EXP 62`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; DIV_LT; ARITH_RULE
       `2 EXP 62 + n MOD 2 EXP 62 < 2 EXP 63`] THEN
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    SUBGOAL_THEN `nn DIV 2 EXP 255 = 0` SUBST1_TAC THENL
     [REWRITE_TAC[DIV_EQ_0] THEN EXPAND_TAC "nn" THEN ARITH_TAC;
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)] THEN
    REWRITE_TAC[BITVAL_CLAUSES; normalized_ubignum_preglist';
                normalized_ubignum_preglist] THEN
    ASM_REWRITE_TAC[normalized_ubignum_qreglist; normalized_ubignum_qreglist';
                    normalized_ubignum_int32list; normalized_ubignum_int32list';
                    normalized_ubignum_list; normalized_ubignum_list';
                    MAP; ubignum_of_list; INT_CONG_RREM] THEN
    REWRITE_TAC[WORD_BLAST
     `word_subword (word_insert (h:int128) (0,64) (l:int64):int128)
                   (0,32):int32 = word_subword l (0,32) /\
      word_subword (word_insert (h:int128) (0,64) (l:int64):int128)
                   (32,32):int32 = word_subword l (32,32)`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ladder_x2; ladder_z2; ladder_x3; ladder_z3] THEN
    REWRITE_TAC[SUB_REFL; flipladder; INT_CONG_REFL; INT_CONG_RREM] THEN
    REWRITE_TAC[WORD_BLAST
       `word_subword (word_or x (word_shl y 32):int64) (0,32):int32 =
        word_zx x /\
        word_subword (word_or (word_and x (word 67108863))
                              (word_shl y 32):int64) (32,32):int32 =
        word_zx y /\
        word_subword (word_or (word_ushr x 38)
                              (word_shl y 32):int64) (32,32):int32 =
        word_zx y /\
        word_subword (word_or (word_subword (x:int64) (25,26))
                              (word_shl y 32):int64) (32,32):int32 =
        word_zx y /\
        word_subword (word_or (word_subword (x:int64) (12,26))
                              (word_shl y 32):int64) (32,32):int32 =
        word_zx y`] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_SHL;
                    VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM BOUNDER_TAC[]) THEN
    MATCH_MP_TAC INT_EQ_IMP_CONG THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    EXPAND_TAC "X" THEN
    REWRITE_TAC[ARITH_RULE
     `x = y MOD 2 EXP 255 <=> x + 2 EXP 255 * y DIV 2 EXP 255 = y`] THEN
    SUBGOAL_THEN `X_input DIV 2 EXP 255 = val(xb_31:byte) DIV 2 EXP 7`
    SUBST1_TAC THENL
     [EXPAND_TAC "X_input" THEN REWRITE_TAC[ADD_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 255 = 2 EXP 248 * 2 EXP 7`] THEN
      SIMP_TAC[GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[EQ_ADD_RCANCEL_0; DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "X_input" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;

    (*** The main loop invariant for the Montgomery ladder ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[normalized_ubignum_qreglist; normalized_ubignum_qreglist';
                normalized_ubignum_int32list; normalized_ubignum_int32list';
                normalized_ubignum_list; normalized_ubignum_list';
                normalized_ubignum_preglist; normalized_ubignum_preglist';
                MAP; ALL] THEN
    REWRITE_TAC[WORD_RULE `word_sub (word(i + 1)) (word 1) = word i`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

    (*** Introduce zero-state abbreviations ***)

    ABBREVIATE_STATE_COMPONENTS_TAC 0 THEN

    (*** Manually simulate and analyze the scalar bit selection ***)

    ABBREV_TAC `n = read (memory :> bytes (stackpointer,8 * 4)) s0` THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add stackpointer
       (word(8 * val(word_ushr (word i:int64) 6))))) s0 =
      word(n DIV (2 EXP (64 * i DIV 64)) MOD 2 EXP (64 * 1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 255 ==> MIN (4 - i DIV 64) 1 = 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
      VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC CURVE25519_X25519_BYTE_EXEC (1--7) THEN
    SUBGOAL_THEN
     `word_and
        (word_jushr (word((n DIV 2 EXP (64 * i DIV 64)) MOD 2 EXP 64))
                    (word i))
        (word 1:int64) =
      word(bitval(ODD(nn DIV 2 EXP i)))`
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
      MATCH_MP_TAC(TAUT `p /\ (q <=> q') ==> (p /\ q <=> q')`) THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM CONG_MOD_2_ALT] THEN MATCH_MP_TAC CONG_DIV2 THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONG_DIVIDES_MODULUS)) THEN
      REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP))] THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
      UNDISCH_TAC `i < 255` THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [VAL_WORD_SUB_EQ_0; VAL_WORD_BITVAL; EQ_BITVAL]) THEN
    RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE
     [TAUT `read ZF s = p <=> read ZF s = ~ ~ p`]) THEN
    ABBREV_TAC
     `flip <=> ~(ODD(nn DIV 2 EXP (i + 1)) <=> ODD(nn DIV 2 EXP i))` THEN

    (*** Now simulate all the rest of the inner loop instructions ***)

    ARM_NAMESTEPS_TAC CURVE25519_X25519_BYTE_EXEC (8--1021) THEN

    (*** Also introduce the full abbreviations ***)

    MAP_EVERY ABBREV_TAC abbreviated_variables THEN

    (*** Finish the simulation and throw away machine states ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC
     (EXTRA_SIMD_CONV [SIMD_MASK_CLAUSES; UBIGNUM_PACK_UNPACK_CLAUSES]) THEN
    REWRITE_TAC[WORD_BLAST
     `word_subword (word_insert (x:int128) (0,64) (y:int64):int128)
                   (0,32):int32 =
      word_subword y (0,32) /\
      word_subword (word_insert (x:int128) (0,64) (y:int64):int128)
                   (32,32):int32 =
      word_subword y (32,32)`] THEN
    DISCARD_STATE_TAC "s1021" THEN

    (*** Apply a few standard simplifications eagerly ***)

    RULE_ASSUM_TAC(REWRITE_RULE[extra; EXTRA_SIMD_CLAUSES;
      ADD_CLAUSES; WORD_RULE `word_add x x = word_mul (word 2) x`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_BLAST
      `(word_zx:int64->int32) ((word_zx:int128->int64) x) =
       word_subword x (0,32)`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_BLAST
      `(word_zx:int64->int32) (word_ushr ((word_zx:int128->int64) x) 32) =
       word_subword x (32,32)`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_BLAST
      `(word_zx:int64->int32) ((word_zx:int32->int64) x) = word_zx x`]) THEN

    (*** The initial linear and selection blocks ***)

    SUBGOAL_THEN
      `(&b:int == &x2 - &z2) (mod &p_25519) /\
       (&d:int == &x3 - &z3) (mod &p_25519) /\
       (&a:int == &x2 + &z2) (mod &p_25519) /\
       (&c:int == &x3 + &z3) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN ARITHBLOCK_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `(&f:int == if flip then &c else &a) (mod &p_25519) /\
      (&g:int == if flip then &d else &b) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      W(MAP_EVERY (EXPAND_TAC o name_of) o
        filter (not o (=) `:bool` o type_of) o frees o snd) THEN
      W(MAP_EVERY (EXPAND_TAC o name_of) o
        filter (not o (=) `:bool` o type_of) o frees o lhand o rator o snd) THEN
      REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN
      CONV_TAC
        (EXTRA_SIMD_CONV [SIMD_MASK_CLAUSES; UBIGNUM_PACK_UNPACK_CLAUSES]) THEN
      REWRITE_TAC[GSYM INT_REM_EQ];
      ALL_TAC] THEN

    MAP_EVERY (DEDUCE_DIGITBOUNDS_TAC []) ["a"; "b"; "c"; "d"; "f"; "g"] THEN

    (*** aa = f^2 ***)

    SUBGOAL_THEN
      `(&aa:int == &f pow 2) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [ARITHBLOCK_TAC[];
      DEDUCE_DIGITBOUNDS_TAC [] "aa"] THEN

    (*** bb = g^2 ***)

    SUBGOAL_THEN
      `(&bb:int == &g pow 2) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [ARITHBLOCK_TAC[];
      DEDUCE_DIGITBOUNDS_TAC [] "bb"] THEN

    (*** Alternative form bbalt of bb, proof a bit ad-hoc ***)

    MAP_EVERY (USE_ABBREV (MP_TAC o ASSUME)) ["bbalt"; "bb"] THEN
    W(fun (asl,w) ->
      let l1 = dest_list(rand(lhand(lhand w)))
      and l2 = dest_list(rand(lhand(lhand(rand w)))) in
      SUBGOAL_THEN (list_mk_conj(map2 (curry mk_eq) l1 l2)) MP_TAC)
    THENL
     [W(MAP_EVERY (EXPAND_TAC o name_of) o frees o snd) THEN
      REPEAT
       (CONJ_TAC THENL
         [CONV_TAC(ONCE_DEPTH_CONV VAL_EXPAND_CONV) THEN
          CONV_TAC(TOP_DEPTH_CONV (BIT_WORD_CONV o
            check (not o can (term_match [] `bit i (word_add x y)`)))) THEN
          REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC;
          ALL_TAC]) THEN
      REWRITE_TAC[UBIGNUM_PACK_UNPACK_CLAUSES] THEN
      REWRITE_TAC[VAL_WORD; VAL_WORD_ADD; VAL_WORD_USHR] THEN
      CONV_TAC(ONCE_DEPTH_CONV(!word_SIZE_CONV)) THEN
      REPEAT DEMODULATE_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM BOUNDER_TAC[];
      DISCH_THEN(fun th ->
       GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th] THEN
       DISCH_THEN SUBST1_TAC THEN MP_TAC th THEN
       GEN_REWRITE_TAC I [IMP_IMP]) THEN
      DISCH_THEN(fun th ->
       REPLICATE_TAC 11 (POP_ASSUM MP_TAC) THEN
       REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN MP_TAC th) THEN
      DISCH_THEN(fun eth -> DISCH_THEN(fun th ->
       STRIP_ASSUME_TAC th THEN STRIP_ASSUME_TAC(SUBS(CONJUNCTS eth) th)))] THEN

    (*** e = aa - bb. This is a bit messy with explicit SWAR ***)

    MAP_EVERY (USE_ABBREV
     (MP_TAC o AP_TERM `\x. val((word_subword:int64->num#num->int32) x (0,32))` o
      ASSUME)) (map (fun n -> "e_"^string_of_int n) (0--9)) THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[WORD_BLAST
     `word_subword (word_ushr (x:int64) 32) (0,32):int32 =
      word_subword x (32,32)`] THEN
    REWRITE_TAC[WORD_SUBWORD_SWAR_0_32] THEN
    MAP_EVERY (fun th ->
      let f = PART_MATCH (lhand o rand) th in
      REPEAT(W(fun (asl,w) -> MP_TAC(f (find_term (can f) (lhand w)))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[WORD_SUBWORD_SWAR_0_32; VAL_WORD_ADD; VAL_WORD;
          GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM; DIMINDEX_32] THEN
        CONV_TAC WORD_REDUCE_CONV THEN REPEAT DEREMULATE_TAC THEN
        ASM BOUNDER_TAC[];
        DISCH_THEN SUBST1_TAC])) (rev(CONJUNCTS WORD_SUBWORD_SWAR_32_32)) THEN
    CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [VAL_EQ] THEN
    DISCH_THEN(fun th ->
      MAP_EVERY (BOUND_ABBREV_THEN MP_TAC) (CONJUNCTS th) THEN
      REPEAT DISCH_TAC THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN
     `(&e:int == &aa - &bb) (mod &p_25519)`
    MP_TAC THENL
     [W(MAP_EVERY (EXPAND_TAC o name_of) o frees o snd) THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN(fun th -> REWRITE_TAC[GSYM th])) THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[ubignum_of_list; GSYM INT_OF_NUM_CLAUSES; DIMINDEX_32;
              INT_VAL_WORD_SUB; VAL_WORD_ADD; VAL_WORD; GSYM INT_OF_NUM_REM] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REPEAT DEREMULATE_TAC THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; p_25519; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      REAL_INTEGER_TAC;
      POP_ASSUM(K ALL_TAC) THEN DISCH_TAC] THEN

    (*** bce = bb + 121666 * e ***)

    SUBGOAL_THEN
      `(&bce:int == &bbalt + &121666 * &e) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [ARITHBLOCK_TAC
       (map (C SPEC (WORD_BLAST
       `!x. (word_zx:int64->int32) x = word_subword x (0,32)`) o
       (fun n -> mk_var("e_"^string_of_int n,`:int64`))) (0--9));
      DEDUCE_DIGITBOUNDS_TAC
       (map (C SPEC (WORD_BLAST
       `!x. (word_zx:int64->int32) x = word_subword x (0,32)`) o
       (fun n -> mk_var("e_"^string_of_int n,`:int64`))) (0--9)) "bce"] THEN

    (*** z4 = bce * e ***)

    SUBGOAL_THEN
      `(&z4:int == &bce * &e) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [ARITHBLOCK_TAC
       (map (C SPEC (WORD_BLAST
       `!x. (word_zx:int64->int32) x = word_subword x (0,32)`) o
       (fun n -> mk_var("e_"^string_of_int n,`:int64`))) (0--9));
      DEDUCE_DIGITBOUNDS_TAC
       (map (C SPEC (WORD_BLAST
       `!x. (word_zx:int64->int32) x = word_subword x (0,32)`) o
       (fun n -> mk_var("e_"^string_of_int n,`:int64`))) (0--9)) "z4"] THEN

    (*** bc = b * c and ad = a * d ***)

    SUBGOAL_THEN
      `(&bc:int == &b * &c) (mod &p_25519) /\
       (&ad:int == &a * &d) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN ARITHBLOCK_TAC[];
      MAP_EVERY (DEDUCE_DIGITBOUNDS_TAC []) ["bc"; "ad"]] THEN

    (*** t1 = ad + bc; t2 = ad - bc ***)

    SUBGOAL_THEN
      `(&t1:int == &ad + &bc) (mod &p_25519) /\
       (&t2:int == &ad - &bc) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     (let ths =
      map (C SPEC (WORD_BLAST
       `!x:int128. word_subword x (0,32):int32 =
                   word_zx(word_subword x (0,64):int64)`) o
       (fun n -> mk_var("ad_"^string_of_int n,`:int128`))) (0--9) @
      map (C SPEC (WORD_BLAST
       `!x:int128. word_subword x (64,32):int32 =
                   word_zx(word_subword x (64,64):int64)`) o
       (fun n -> mk_var("ad_"^string_of_int n,`:int128`))) (0--9) in
      [CONJ_TAC THEN ARITHBLOCK_TAC ths;
       MAP_EVERY (DEDUCE_DIGITBOUNDS_TAC ths) ["t1"; "t2"]]) THEN

    (*** x5 = t1^2; t3 = t2^2 ***)

    SUBGOAL_THEN
      `(&x5:int == &t1 pow 2) (mod &p_25519) /\
       (&t3:int == &t2 pow 2) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN ARITHBLOCK_TAC[];
      MAP_EVERY (DEDUCE_DIGITBOUNDS_TAC []) ["x5"; "t3"]] THEN

    (*** x4 = aa * bb and z5 = x * t3 ***)

    SUBGOAL_THEN
      `(&x4:int == &aa * &bb) (mod &p_25519) /\
       (&z5:int == &x * &t3) (mod &p_25519)`
    STRIP_ASSUME_TAC THENL
    (let ths = map (C SPEC (WORD_BLAST
       `!x:int128. word_subword x (0,32):int32 =
                   word_zx(word_subword x (0,64):int64)`) o
       (fun n -> mk_var("t3_"^string_of_int n,`:int128`))) (0--9) in
      [CONJ_TAC THEN ARITHBLOCK_TAC ths;
       MAP_EVERY (DEDUCE_DIGITBOUNDS_TAC ths) ["x4"; "z5"]]) THEN

    (*** The odd goal out, the looping criterion ***)

    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONJ_ASSOC];
      VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN

    (*** Regularize the form of the digits ***)

    REWRITE_TAC(map (C SPEC (WORD_BLAST
       `!x:int128. word_subword x (0,32):int32 =
                   word_zx(word_subword x (0,64):int64)`) o
       (fun n -> mk_var("t3_"^string_of_int n,`:int128`))) (0--9)) THEN
    REWRITE_TAC[WORD_BLAST
     `!x:int128. word_subword x (64,32):int32 =
                 word_zx(word_subword x (64,64):int64)`] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
    REPEAT DEMODULATE_TAC THEN ASM_REWRITE_TAC[] THEN

    (*** Separate the bound properties and prove those first ***)

    W(fun (asl,w) ->
      let w1,w2 = partition (can (term_match [] `x:num <= b`)) (conjuncts w) in
      GEN_REWRITE_TAC I
       [CONJ_ACI_RULE(mk_eq(w,mk_conj(list_mk_conj w1,list_mk_conj w2)))]) THEN
    CONJ_TAC THENL [REPEAT CONJ_TAC THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN

    (*** Now the main mathematics ***)

    REWRITE_TAC[ladder_x2; ladder_x3; ladder_z2; ladder_z3] THEN
    SUBGOAL_THEN `255 - i = ((255 - (i + 1)) + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `i < 255` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[flipladder] THEN
    LET_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 255 ==> 255 - (255 - (i + 1) + 1) = i`;
                 ARITH_RULE `i < 255 ==> 255 - (255 - (i + 1)) = i + 1`] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
      (can (term_match [] `(x:int == y) (mod &p)`) o concl))) THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(AP_TERM `(FST o FST):(int#int)#(int#int)->int` th) THEN
      MP_TAC(AP_TERM `(SND o FST):(int#int)#(int#int)->int` th) THEN
      MP_TAC(AP_TERM `(FST o SND):(int#int)#(int#int)->int` th) THEN
      MP_TAC(AP_TERM `(SND o SND):(int#int)#(int#int)->int` th)) THEN
    REWRITE_TAC[o_THM; GSYM ladder_x2; GSYM ladder_z2;
                GSYM ladder_x3; GSYM ladder_z3] THEN
    REPLICATE_TAC 4 (DISCH_THEN SUBST1_TAC) THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[COND_SWAP] THEN
    COND_CASES_TAC THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[curve25519; montgomery_xzdouble; montgomery_xzdiffadd] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; A_25519] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[A_25519] THEN INT_ARITH_TAC;

    (*** The trivial loop-back subgoal ***)

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[normalized_ubignum_preglist; normalized_ubignum_preglist';
                normalized_ubignum_qreglist; normalized_ubignum_qreglist';
                normalized_ubignum_int32list; normalized_ubignum_int32list';
                normalized_ubignum_list; normalized_ubignum_list';
                MAP; ubignum_of_list] THEN
    ARM_SIM_TAC CURVE25519_X25519_BYTE_EXEC [1];

    ALL_TAC] THEN

  (*** Now the final recoding, inversion and multiplication ***)

  REWRITE_TAC[normalized_ubignum_qreglist; normalized_ubignum_qreglist';
              normalized_ubignum_int32list; normalized_ubignum_int32list';
              normalized_ubignum_list; normalized_ubignum_list';
              LT_REFL; MAP; ubignum_of_list] THEN
  GHOST_INTRO_TAC `q0:int128` `read Q0` THEN
  GHOST_INTRO_TAC `q1:int128` `read Q1` THEN
  GHOST_INTRO_TAC `q2:int128` `read Q2` THEN
  GHOST_INTRO_TAC `q3:int128` `read Q3` THEN
  GHOST_INTRO_TAC `q4:int128` `read Q4` THEN
  GHOST_INTRO_TAC `q5:int128` `read Q5` THEN
  GHOST_INTRO_TAC `q6:int128` `read Q6` THEN
  GHOST_INTRO_TAC `q7:int128` `read Q7` THEN
  GHOST_INTRO_TAC `q8:int128` `read Q8` THEN
  GHOST_INTRO_TAC `q9:int128` `read Q9` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN

  (*** Recoding of X2 -> xn ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC
    [12;13;14;15;16;17;18;20;21;23;24;26] (1--28) THEN
  SUBGOAL_THEN
   `(&(bignum_from_memory(word_add stackpointer (word 128),4) s28):int ==
     ladder_x2 X nn 0) (mod (&p_25519))`
  MP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(x:int == n) (mod p) ==> x' = x ==> (x':int == n) (mod p)`)) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_ZX_GEN; DIMINDEX_64] THEN
    REPEAT DEMODULATE_TAC THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    STRIP_TAC THEN
    ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
      MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ABBREV_TAC
   `x2 =
    read(memory :> bytes(word_add stackpointer (word 128),8 * 4)) s28` THEN
  DISCH_TAC THEN

  (*** Recoding of Z2 -> zn, similar but slightly more elaborate ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_EXEC
    [40;42;44;46;47;48;49;50;52;53;55;56;58] (29--60) THEN
  SUBGOAL_THEN
   `(&(bignum_from_memory(word_add stackpointer (word 160),4) s60):int ==
     ladder_z2 X nn 0) (mod (&p_25519))`
  MP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(x:int == n) (mod p)
       ==> (x' == x) (mod p) ==> (x':int == n) (mod p)`)) THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    MP_TAC(SPEC `word_subword (q9:int128) (32,32):int32` (WORD_BLAST
     `!x:int32. val x <= 67108863
       ==> val x = 2 EXP 25 * bitval(bit 25 x) + val x MOD 2 EXP 25`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(NUMBER_RULE `!d:num. x + d * p = y ==> (x == y) (mod p)`) THEN
    EXISTS_TAC `bitval(bit 25 (word_subword (q9:int128) (32,32):int32))` THEN
    REWRITE_TAC[ADD_ASSOC] THEN MATCH_MP_TAC(ARITH_RULE
     `b * 2 EXP 255 = b * p_25519 + b * 19 /\
      x = y + 2 EXP 230 * c + 19 * b
      ==> x + b * p_25519 = y + 2 EXP 230 * (2 EXP 25 * b + c)`) THEN
    CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REWRITE_TAC[VAL_WORD_SHL; WORD_BLAST
     `val(word_and x (word 33554431):int64) = val x MOD 2 EXP 25`] THEN
    REWRITE_TAC[WORD_BLAST
     `val(word_and (word_zx (x:int32)) (word 33554432):int64) =
      2 EXP 25 * bitval(bit 25 x)`] THEN
    REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; BITVAL_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_ZX_GEN; DIMINDEX_64] THEN
    REPEAT DEMODULATE_TAC THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    STRIP_TAC THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ABBREV_TAC
   `z2 =
    read(memory :> bytes(word_add stackpointer (word 160),8 * 4)) s60` THEN
  DISCH_TAC THEN

  (*** Inlined modular inverse ***)

  ARM_STEPS_TAC CURVE25519_X25519_BYTE_EXEC (61--62) THEN
  LOCAL_MODINV_TAC 63 THEN
  ABBREV_TAC
   `zn' =
    read(memory :> bytes(word_add stackpointer (word 160),8 * 4)) s63` THEN

  (*** Inlined final field multiplication ***)

  LOCAL_MUL_P25519_TAC 0 ["zn"; "xn"; "zn"] THEN

  (*** Bytewise store to the output ***)

  BIGNUM_LDIGITIZE_TAC "res_"
   `read(memory :> bytes(word_add stackpointer (word 160),8 * 4)) s64` THEN
  ARM_STEPS_TAC CURVE25519_X25519_BYTE_EXEC (65--127) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `zn:num` THEN CONJ_TAC THENL
   [CONV_TAC(LAND_CONV BYTES_EXPAND_CONV) THEN EXPAND_TAC "zn" THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN

  (*** Completing the mathematics ***)

  CONV_TAC SYM_CONV THEN REWRITE_TAC[PUREX25519_MOD] THEN
  ASM_REWRITE_TAC[GSYM deproject] THEN MATCH_MP_TAC DEPROJECT_LADDER_EVEN THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "nn" THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[EVEN_ADD; EVEN_SUB; EVEN_EXP; ARITH; EVEN_MOD_EVEN]);;

let CURVE25519_X25519_BYTE_SUBROUTINE_CORRECT = time prove
 (`!res scalar n point X pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 384),384))
        [(word pc,0x27f8); (res,32); (scalar,32); (point,32)] /\
    nonoverlapping (res,32) (word pc,0x27f8)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [res; scalar; point] s /\
              read (memory :> bytes(scalar,32)) s = n /\
              read (memory :> bytes(point,32)) s = X)
         (\s. read PC s = returnaddress /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,X))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,32);
                      memory :> bytes(word_sub stackpointer (word 384),384)])`,
  ARM_ADD_RETURN_STACK_TAC CURVE25519_X25519_BYTE_EXEC
    CURVE25519_X25519_BYTE_CORRECT
    `[D8; D9; D10; D11; D12; D13; D14; D15;
      X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 384);;
