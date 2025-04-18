(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The x25519 function for curve25519 (byte array arguments).                *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bignum_inv_p25519.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/x25519.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(**** print_literal_from_elf "arm/curve25519/curve25519_x25519_byte_alt.o";;
 ****)

let curve25519_x25519_byte_alt_mc = define_assert_from_elf
  "curve25519_x25519_byte_alt_mc" "arm/curve25519/curve25519_x25519_byte_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd10503ff;       (* arm_SUB SP SP (rvalue (word 320)) *)
  0xaa0003f7;       (* arm_MOV X23 X0 *)
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
  0xa90137ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  0x3940004a;       (* arm_LDRB W10 X2 (Immediate_Offset (word 0)) *)
  0x39400440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 1)) *)
  0xaa00214a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 8) *)
  0x39400840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 2)) *)
  0xaa00414a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 16) *)
  0x39400c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 3)) *)
  0xaa00614a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 24) *)
  0x39401040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 4)) *)
  0xaa00814a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 32) *)
  0x39401440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 5)) *)
  0xaa00a14a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 40) *)
  0x39401840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 6)) *)
  0xaa00c14a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 48) *)
  0x39401c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 7)) *)
  0xaa00e14a;       (* arm_ORR X10 X10 (Shiftedreg X0 LSL 56) *)
  0x3940204b;       (* arm_LDRB W11 X2 (Immediate_Offset (word 8)) *)
  0x39402440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 9)) *)
  0xaa00216b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 8) *)
  0x39402840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 10)) *)
  0xaa00416b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 16) *)
  0x39402c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 11)) *)
  0xaa00616b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 24) *)
  0x39403040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 12)) *)
  0xaa00816b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 32) *)
  0x39403440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 13)) *)
  0xaa00a16b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 40) *)
  0x39403840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 14)) *)
  0xaa00c16b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 48) *)
  0x39403c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 15)) *)
  0xaa00e16b;       (* arm_ORR X11 X11 (Shiftedreg X0 LSL 56) *)
  0xa9022fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&32))) *)
  0x3940404c;       (* arm_LDRB W12 X2 (Immediate_Offset (word 16)) *)
  0x39404440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 17)) *)
  0xaa00218c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 8) *)
  0x39404840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 18)) *)
  0xaa00418c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 16) *)
  0x39404c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 19)) *)
  0xaa00618c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 24) *)
  0x39405040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 20)) *)
  0xaa00818c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 32) *)
  0x39405440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 21)) *)
  0xaa00a18c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 40) *)
  0x39405840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 22)) *)
  0xaa00c18c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 48) *)
  0x39405c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 23)) *)
  0xaa00e18c;       (* arm_ORR X12 X12 (Shiftedreg X0 LSL 56) *)
  0x3940604d;       (* arm_LDRB W13 X2 (Immediate_Offset (word 24)) *)
  0x39406440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 25)) *)
  0xaa0021ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 8) *)
  0x39406840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 26)) *)
  0xaa0041ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 16) *)
  0x39406c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 27)) *)
  0xaa0061ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 24) *)
  0x39407040;       (* arm_LDRB W0 X2 (Immediate_Offset (word 28)) *)
  0xaa0081ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 32) *)
  0x39407440;       (* arm_LDRB W0 X2 (Immediate_Offset (word 29)) *)
  0xaa00a1ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 40) *)
  0x39407840;       (* arm_LDRB W0 X2 (Immediate_Offset (word 30)) *)
  0xaa00c1ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 48) *)
  0x39407c40;       (* arm_LDRB W0 X2 (Immediate_Offset (word 31)) *)
  0xaa00e1ad;       (* arm_ORR X13 X13 (Shiftedreg X0 LSL 56) *)
  0x9240f9ad;       (* arm_AND X13 X13 (rvalue (word 9223372036854775807)) *)
  0xa90337ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&48))) *)
  0xd2800035;       (* arm_MOV X21 (rvalue (word 1)) *)
  0xa90e2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&224))) *)
  0xa90f37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&240))) *)
  0xa9047ff5;       (* arm_STP X21 XZR SP (Immediate_Offset (iword (&64))) *)
  0xa9057fff;       (* arm_STP XZR XZR SP (Immediate_Offset (iword (&80))) *)
  0xa94e1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&224))) *)
  0xa9440fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&64))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94f23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&240))) *)
  0xa9450fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&80))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9101be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa91123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xa94e13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&224))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94f1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa91213e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa9131be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa9500fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&256))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&272))) *)
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
  0xa91027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&256))) *)
  0xa9112fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&272))) *)
  0xa9520fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&288))) *)
  0xa9132fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&304))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa9500fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&256))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9510fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&272))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa90c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0x9b077c23;       (* arm_MUL X3 X1 X7 *)
  0x9b087c24;       (* arm_MUL X4 X1 X8 *)
  0x9b097c25;       (* arm_MUL X5 X1 X9 *)
  0x9b0a7c26;       (* arm_MUL X6 X1 X10 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0600df;       (* arm_CMN X6 X6 *)
  0x9240f8c6;       (* arm_AND X6 X6 (rvalue (word 9223372036854775807)) *)
  0x9a0a0148;       (* arm_ADC X8 X10 X10 *)
  0xd2800269;       (* arm_MOV X9 (rvalue (word 19)) *)
  0x9b097d07;       (* arm_MUL X7 X8 X9 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9512be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&288))) *)
  0xa9133fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&304))) *)
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
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
  0xa94d1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
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
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  0xd2801fb4;       (* arm_MOV X20 (rvalue (word 253)) *)
  0xa94e1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&224))) *)
  0xa9440fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&64))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94f23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&240))) *)
  0xa9450fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&80))) *)
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
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa94b23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
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
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa94a0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&160))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa94b0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&176))) *)
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
  0xa94e13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&224))) *)
  0xa94423e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94f1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa94523e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&80))) *)
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
  0xa90c37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&192))) *)
  0xa90d3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&208))) *)
  0xd346fe80;       (* arm_LSR X0 X20 6 *)
  0xf8607be2;       (* arm_LDR X2 SP (Shiftreg_Offset X0 3) *)
  0x9ad42442;       (* arm_LSRV X2 X2 X20 *)
  0x92400042;       (* arm_AND X2 X2 (rvalue (word 1)) *)
  0xeb0202bf;       (* arm_CMP X21 X2 *)
  0xaa0203f5;       (* arm_MOV X21 X2 *)
  0xa94807e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  0xa94a0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&160))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91007e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&256))) *)
  0xa94907e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&144))) *)
  0xa94b0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&176))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91107e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&272))) *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa9460fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&96))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa94507e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&80))) *)
  0xa9470fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91307e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&304))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
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
  0xa90e37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&224))) *)
  0xa90f3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&240))) *)
  0xa9500fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&256))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&272))) *)
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
  0xa91027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&256))) *)
  0xa9112fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&272))) *)
  0xa94c1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa94e0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&224))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa94d23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa94f0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&240))) *)
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
  0xa9520fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&288))) *)
  0xa9132fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&304))) *)
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
  0xa94e23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&224))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa94d1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
  0xa94f23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&240))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90e13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&224))) *)
  0xa90f1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  0xa9440fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&64))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94517e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&80))) *)
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
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa9500fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&256))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9510fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&272))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa90c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa94e0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&224))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa94f17e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&240))) *)
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
  0xa90e27e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&224))) *)
  0xa90f2fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&240))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0x9b077c23;       (* arm_MUL X3 X1 X7 *)
  0x9b087c24;       (* arm_MUL X4 X1 X8 *)
  0x9b097c25;       (* arm_MUL X5 X1 X9 *)
  0x9b0a7c26;       (* arm_MUL X6 X1 X10 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0600df;       (* arm_CMN X6 X6 *)
  0x9240f8c6;       (* arm_AND X6 X6 (rvalue (word 9223372036854775807)) *)
  0x9a0a0148;       (* arm_ADC X8 X10 X10 *)
  0xd2800269;       (* arm_MOV X9 (rvalue (word 19)) *)
  0x9b097d07;       (* arm_MUL X7 X8 X9 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9512be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&288))) *)
  0xa9133fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&304))) *)
  0xa94413e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&64))) *)
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
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
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
  0xa94d1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
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
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  0xd1000694;       (* arm_SUB X20 X20 (rvalue (word 1)) *)
  0xf1000e9f;       (* arm_CMP X20 (rvalue (word 3)) *)
  0x54ff8b82;       (* arm_BCS (word 2093424) *)
  0xeb1f02bf;       (* arm_CMP X21 XZR *)
  0xa94e07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&224))) *)
  0xa9520fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91207e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&288))) *)
  0xa94f07e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&240))) *)
  0xa9530fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&304))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa91307e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&304))) *)
  0xa94407e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  0xa94a0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&160))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa90a07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  0xa94507e0;       (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&80))) *)
  0xa94b0fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&176))) *)
  0x9a821000;       (* arm_CSEL X0 X0 X2 Condition_NE *)
  0x9a831021;       (* arm_CSEL X1 X1 X3 Condition_NE *)
  0xa90b07e0;       (* arm_STP X0 X1 SP (Immediate_Offset (iword (&176))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa94a0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&160))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa94b0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&176))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9101be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa91123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa94b23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa91213e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa9131be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa9500fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&256))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&272))) *)
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
  0xa91027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&256))) *)
  0xa9112fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&272))) *)
  0xa9520fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&288))) *)
  0xa9132fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&304))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa9500fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&256))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9510fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&272))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa90c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0x9b077c23;       (* arm_MUL X3 X1 X7 *)
  0x9b087c24;       (* arm_MUL X4 X1 X8 *)
  0x9b097c25;       (* arm_MUL X5 X1 X9 *)
  0x9b0a7c26;       (* arm_MUL X6 X1 X10 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0600df;       (* arm_CMN X6 X6 *)
  0x9240f8c6;       (* arm_AND X6 X6 (rvalue (word 9223372036854775807)) *)
  0x9a0a0148;       (* arm_ADC X8 X10 X10 *)
  0xd2800269;       (* arm_MOV X9 (rvalue (word 19)) *)
  0x9b097d07;       (* arm_MUL X7 X8 X9 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9512be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&288))) *)
  0xa9133fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&304))) *)
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
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
  0xa94d1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
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
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa94a0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&160))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa94b0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&176))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9101be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa91123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa94b23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa91213e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa9131be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa9500fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&256))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&272))) *)
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
  0xa91027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&256))) *)
  0xa9112fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&272))) *)
  0xa9520fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&288))) *)
  0xa9132fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&304))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa9500fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&256))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9510fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&272))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa90c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0x9b077c23;       (* arm_MUL X3 X1 X7 *)
  0x9b087c24;       (* arm_MUL X4 X1 X8 *)
  0x9b097c25;       (* arm_MUL X5 X1 X9 *)
  0x9b0a7c26;       (* arm_MUL X6 X1 X10 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0600df;       (* arm_CMN X6 X6 *)
  0x9240f8c6;       (* arm_AND X6 X6 (rvalue (word 9223372036854775807)) *)
  0x9a0a0148;       (* arm_ADC X8 X10 X10 *)
  0xd2800269;       (* arm_MOV X9 (rvalue (word 19)) *)
  0x9b097d07;       (* arm_MUL X7 X8 X9 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9512be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&288))) *)
  0xa9133fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&304))) *)
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
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
  0xa94d1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
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
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa94a0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&160))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa94b0fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&176))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa9101be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  0xa91123e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa94a23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&160))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa94b23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xd28004c9;       (* arm_MOV X9 (rvalue (word 38)) *)
  0x9a9f2129;       (* arm_CSEL X9 X9 XZR Condition_CS *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa91213e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa9131be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  0xa9500fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&256))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95117e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&272))) *)
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
  0xa91027e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&256))) *)
  0xa9112fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&272))) *)
  0xa9520fe2;       (* arm_LDP X2 X3 SP (Immediate_Offset (iword (&288))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa95317e4;       (* arm_LDP X4 X5 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91227e8;       (* arm_STP X8 X9 SP (Immediate_Offset (iword (&288))) *)
  0xa9132fea;       (* arm_STP X10 X11 SP (Immediate_Offset (iword (&304))) *)
  0xa9521be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  0xa9500fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&256))) *)
  0xeb0400a5;       (* arm_SUBS X5 X5 X4 *)
  0xfa0300c6;       (* arm_SBCS X6 X6 X3 *)
  0xa95323e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  0xa9510fe4;       (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&272))) *)
  0xfa0400e7;       (* arm_SBCS X7 X7 X4 *)
  0xfa030108;       (* arm_SBCS X8 X8 X3 *)
  0xd28004c4;       (* arm_MOV X4 (rvalue (word 38)) *)
  0x9a9f3083;       (* arm_CSEL X3 X4 XZR Condition_CC *)
  0xeb0300a5;       (* arm_SUBS X5 X5 X3 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xa90c1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0xd29b6841;       (* arm_MOV X1 (rvalue (word 56130)) *)
  0xb2700021;       (* arm_ORR X1 X1 (rvalue (word 65536)) *)
  0xa94c23e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&192))) *)
  0xa94d2be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&208))) *)
  0x9b077c23;       (* arm_MUL X3 X1 X7 *)
  0x9b087c24;       (* arm_MUL X4 X1 X8 *)
  0x9b097c25;       (* arm_MUL X5 X1 X9 *)
  0x9b0a7c26;       (* arm_MUL X6 X1 X10 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xa95123e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0600df;       (* arm_CMN X6 X6 *)
  0x9240f8c6;       (* arm_AND X6 X6 (rvalue (word 9223372036854775807)) *)
  0x9a0a0148;       (* arm_ADC X8 X10 X10 *)
  0xd2800269;       (* arm_MOV X9 (rvalue (word 19)) *)
  0x9b097d07;       (* arm_MUL X7 X8 X9 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xa90a13e3;       (* arm_STP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  0xa90b1be5;       (* arm_STP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  0xa95023e7;       (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  0x9b077c6c;       (* arm_MUL X12 X3 X7 *)
  0x9bc77c6d;       (* arm_UMULH X13 X3 X7 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c6e;       (* arm_UMULH X14 X3 X8 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9512be9;       (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c6f;       (* arm_UMULH X15 X3 X9 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c70;       (* arm_UMULH X16 X3 X10 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
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
  0xa91237ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&288))) *)
  0xa9133fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&304))) *)
  0xa94c13e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
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
  0xa94d1be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
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
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
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
  0xa95213e3;       (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
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
  0xa9531be5;       (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
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
  0xa90a37ec;       (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  0xa90b3fee;       (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  0xa94a2fea;       (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&160))) *)
  0x390002ea;       (* arm_STRB W10 X23 (Immediate_Offset (word 0)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x390006ea;       (* arm_STRB W10 X23 (Immediate_Offset (word 1)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39000aea;       (* arm_STRB W10 X23 (Immediate_Offset (word 2)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39000eea;       (* arm_STRB W10 X23 (Immediate_Offset (word 3)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x390012ea;       (* arm_STRB W10 X23 (Immediate_Offset (word 4)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x390016ea;       (* arm_STRB W10 X23 (Immediate_Offset (word 5)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39001aea;       (* arm_STRB W10 X23 (Immediate_Offset (word 6)) *)
  0xd348fd4a;       (* arm_LSR X10 X10 8 *)
  0x39001eea;       (* arm_STRB W10 X23 (Immediate_Offset (word 7)) *)
  0x390022eb;       (* arm_STRB W11 X23 (Immediate_Offset (word 8)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x390026eb;       (* arm_STRB W11 X23 (Immediate_Offset (word 9)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39002aeb;       (* arm_STRB W11 X23 (Immediate_Offset (word 10)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39002eeb;       (* arm_STRB W11 X23 (Immediate_Offset (word 11)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x390032eb;       (* arm_STRB W11 X23 (Immediate_Offset (word 12)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x390036eb;       (* arm_STRB W11 X23 (Immediate_Offset (word 13)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39003aeb;       (* arm_STRB W11 X23 (Immediate_Offset (word 14)) *)
  0xd348fd6b;       (* arm_LSR X11 X11 8 *)
  0x39003eeb;       (* arm_STRB W11 X23 (Immediate_Offset (word 15)) *)
  0xa94b37ec;       (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&176))) *)
  0x390042ec;       (* arm_STRB W12 X23 (Immediate_Offset (word 16)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x390046ec;       (* arm_STRB W12 X23 (Immediate_Offset (word 17)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39004aec;       (* arm_STRB W12 X23 (Immediate_Offset (word 18)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39004eec;       (* arm_STRB W12 X23 (Immediate_Offset (word 19)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x390052ec;       (* arm_STRB W12 X23 (Immediate_Offset (word 20)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x390056ec;       (* arm_STRB W12 X23 (Immediate_Offset (word 21)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39005aec;       (* arm_STRB W12 X23 (Immediate_Offset (word 22)) *)
  0xd348fd8c;       (* arm_LSR X12 X12 8 *)
  0x39005eec;       (* arm_STRB W12 X23 (Immediate_Offset (word 23)) *)
  0x390062ed;       (* arm_STRB W13 X23 (Immediate_Offset (word 24)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x390066ed;       (* arm_STRB W13 X23 (Immediate_Offset (word 25)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39006aed;       (* arm_STRB W13 X23 (Immediate_Offset (word 26)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39006eed;       (* arm_STRB W13 X23 (Immediate_Offset (word 27)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x390072ed;       (* arm_STRB W13 X23 (Immediate_Offset (word 28)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x390076ed;       (* arm_STRB W13 X23 (Immediate_Offset (word 29)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39007aed;       (* arm_STRB W13 X23 (Immediate_Offset (word 30)) *)
  0xd348fdad;       (* arm_LSR X13 X13 8 *)
  0x39007eed;       (* arm_STRB W13 X23 (Immediate_Offset (word 31)) *)
  0x910503ff;       (* arm_ADD SP SP (rvalue (word 320)) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let CURVE25519_X25519_BYTE_ALT_EXEC = ARM_MK_EXEC_RULE curve25519_x25519_byte_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Common lemmas and tactics for the component proofs.                       *)
(* ------------------------------------------------------------------------- *)

let p25519weakredlemma = prove
 (`!n. n <= 2 EXP 62 * 2 EXP 256
       ==> let q = n DIV 2 EXP 255 in
           q < 2 EXP 64 /\
           q * p_25519 <= n /\
           n < q * p_25519 + 2 * p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let lvs =
 ["resx",[`X23`;`0`];
  "x",[`SP`;`32`];
  "zm",[`SP`;`64`];
  "sm",[`SP`;`64`];
  "dpro",[`SP`;`64`];
  "sn",[`SP`;`96`];
  "dm",[`SP`;`128`];
  "zn",[`SP`;`160`];
  "dn",[`SP`;`160`];
  "e",[`SP`;`160`];
  "dmsn",[`SP`;`192`];
  "p",[`SP`;`192`];
  "xm",[`SP`;`224`];
  "dnsm",[`SP`;`224`];
  "spro",[`SP`;`224`];
  "d",[`SP`;`256`];
  "xn",[`SP`;`288`];
  "s",[`SP`;`288`]];;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_alt_mc 100 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x3d94) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--67) (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (68--92) (68--92) THEN
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (93--100) (93--100) THEN
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
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s92:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_alt_mc 94 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x3d94) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--67) (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (68--92) (68--94) THEN
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sqr_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SQR_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_alt_mc 72 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n.
      read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x3d94) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--45) (1--45) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s31; sum_s33; sum_s35; sum_s37]`;
    `h = bignum_of_wordlist[sum_s39; sum_s41; sum_s43; sum_s45]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (46--70) (46--72) THEN
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
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
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
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add_twice4 (slightly sharper disjunctive hypothesis).        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_alt_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x3d94) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
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
  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (11--14) (9--16) THEN
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
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4 (slightly sharper hypothesis distinctions).       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_alt_mc 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x3d94) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < 2 * p_25519 /\ n < 2 * p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519) /\
                (n < 2 * p_25519
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
  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (11--14) (9--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == &m - &n) (mod p) /\
             (m < p2 /\ n < p2 ==> x' < &p2) /\
             (n < p2 ==> &x = x')
             ==> (m < p2 /\ n < p2 ==> x < p2) /\
                 (n:num < p2 ==> (&x:int == &m - &n) (mod p))`) THEN
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
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of cmadd_4 (actually there is only one, specific constant).     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CMADD_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_alt_mc 32 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x3d94) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read X1 s = word 121666 /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s <
                2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 121666 * m + n) (mod p_25519))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC
   [3;4;5;6;11;12;13;14;16;17;19;20;21] (1--21) THEN

  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s16; sum_s17; sum_s19; sum_s20; sum_s21]` THEN
  SUBGOAL_THEN `121666 * m + n < 2 EXP 17 * 2 EXP 256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `121666 * m + n = ca` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 320` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `121666 * m + n < 2 EXP 17 * 2 EXP 256` THEN ARITH_TAC;
      EXPAND_TAC "ca" THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `ca:num` p25519weakredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `ca < 2 EXP 17 * 2 EXP 256` THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (22--24) (22--24) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s24:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `ca < 2 EXP 17 * 2 EXP 256
      ==> ca DIV 2 EXP 192 DIV 2 EXP 63 < 2 EXP 59`)) THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s22; sum_s24] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (25--26) THEN
  ABBREV_TAC `qm:int64 = word(0 + val(sum_s24:int64) * 19)` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(sum_s24:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC MOD_LT THEN MAP_EVERY UNDISCH_TAC
     [`val(sum_s24:int64) * p_25519 <= ca`;
      `ca < 2 EXP 17 * 2 EXP 256`] THEN
    REWRITE_TAC[p_25519] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (27--30) (27--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s24:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(sum_s24:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of mux_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUX_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519_byte_alt_mc 10 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
     !b. read ZF t = b
     ==>
     !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
     ==>
     !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
     ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x3d94) (word_add (read p3 t) (word n3),8 * 4) /\
      nonoverlapping (stackpointer:int64,320) (res,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read ZF s = b /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (if b then n else m))
        (MAYCHANGE [PC; X0; X1; X2; X3] ,, MAYCHANGE [events] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Instances of modular inverse inlining                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MODINV_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (curve25519_x25519_byte_alt_mc,CURVE25519_X25519_BYTE_ALT_EXEC,0x2af0,
    (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_mc] THENC TRIM_LIST_CONV)
    `TRIM_LIST (12,16) bignum_inv_p25519_mc`,
    CORE_INV_P25519_CORRECT)
   [`read X0 s`; `read X1 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `pc + 0x2af0`; `stackpointer:int64`];;

(* ------------------------------------------------------------------------- *)
(* The swapping-based Montgomery ladder more abstractly.                     *)
(* ------------------------------------------------------------------------- *)

(*** This version has the i = 0 split to handle the short-cut of the
 *** 255th bit, where the values are not exactly the same as the usual
 *** ladder, just projectively equivalent to them.
 ***)

let flipladder = define
 `flipladder x n 0 = ((&1,&0),(&x rem &p_25519,&1)) /\
  flipladder x n (i + 1) =
        let (x2,z2),(x3,z3) = flipladder x n i in
        montgomery_xzdouble curve25519
          (if ODD(n DIV 2 EXP (255 - (i + 1))) <=> ODD(n DIV 2 EXP (255 - i))
           then (x2,z2) else (x3,z3)),
        (if i = 0 then (&x rem &p_25519,&1)
         else montgomery_xzdiffadd curve25519 (&x,&1) (x2,z2) (x3,z3))`;;

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
        curve25519x_represents f P 1 (&x,&1) /\
        n < 2 EXP 255 /\ n DIV 2 EXP 254 = 1 /\ i <= 255
        ==> curve25519x_represents f P (n DIV 2 EXP (255 - i))
                ((if ODD(n DIV 2 EXP (255 - i)) then SND else FST)
                 (flipladder x n i)) /\
            curve25519x_represents f P (n DIV 2 EXP (255 - i) + 1)
                ((if ODD(n DIV 2 EXP (255 - i)) then FST else SND)
                 (flipladder x n i))`,
  REWRITE_TAC[num_divides] THEN REPLICATE_TAC 4 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  INDUCT_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[flipladder] THEN
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
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `255 - 1 = 254`] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 254 * 2 = 2 EXP 255`] THEN
    LET_TAC THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    SUBST1_TAC(ARITH_RULE `2 = 2 * 1`) THEN
    ASM_SIMP_TAC[CURVE25519X_REPRESENTS_DOUBLE] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [curve25519x_represents]) THEN
    SIMP_TAC[curve25519x_represents] THEN ASM_MESON_TAC[RING_OF_INT_REM];
    ALL_TAC] THEN
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
  STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[montgomery_xzdouble; curve25519; montgomery_xzdouble;
                  PAIR_EQ; montgomery_xzdiffadd; INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; INT_SUB_REFL; INT_POW_ZERO;
              ARITH_EQ; INT_REM_ZERO]);;

let DEPROJECT_LADDER_EVEN = prove
 (`!x n x2 z2.
        n < 2 EXP 255 /\ n DIV 2 EXP 254 = 1 /\ EVEN n /\
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

let CURVE25519_X25519_BYTE_ALT_CORRECT = time prove
 (`!res scalar n point X pc stackpointer.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (stackpointer,320))
        [(word pc,0x3d94); (res,32); (scalar,32); (point,32)] /\
    nonoverlapping (res,32) (word pc,0x3d94)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
              read PC s = word(pc + 0x10) /\
              read SP s = stackpointer /\
              C_ARGUMENTS [res; scalar; point] s /\
              read (memory :> bytes(scalar,32)) s = n /\
              read (memory :> bytes(point,32)) s = X)
         (\s. read PC s = word (pc + 0x3d80) /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,X))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(res,32);
                      memory :> bytes(stackpointer,320)])`,
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

  ENSURES_WHILE_ADOWN_TAC `254` `3` `pc + 0x898` `pc + 0x1724`
  `\i s.
      read SP s = stackpointer /\
      read X23 s = res /\
      read X20 s = word_sub (word i) (word 1) /\
      bignum_from_memory (stackpointer,4) s = n_input /\
      bignum_from_memory (word_add stackpointer (word 32),4) s = X /\
      read X21 s = word(bitval(ODD(nn DIV 2 EXP i))) /\
      bignum_from_memory(word_add stackpointer (word 64),4) s < 2 * p_25519 /\
      bignum_from_memory(word_add stackpointer (word 160),4) s < 2 * p_25519 /\
      bignum_from_memory(word_add stackpointer (word 224),4) s < 2 * p_25519 /\
      bignum_from_memory(word_add stackpointer (word 288),4) s < 2 * p_25519 /\
      (&(bignum_from_memory(word_add stackpointer (word 288),4) s) ==
       ladder_x2 X nn i) (mod &p_25519) /\
      (&(bignum_from_memory(word_add stackpointer (word 160),4) s) ==
       ladder_z2 X nn i) (mod &p_25519) /\
      (&(bignum_from_memory(word_add stackpointer (word 224),4) s) ==
       ladder_x3 X nn i) (mod &p_25519) /\
      (&(bignum_from_memory(word_add stackpointer (word 64),4) s) ==
       ladder_z3 X nn i) (mod &p_25519)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial setup, modification of the inputs and doubling ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BYTES_DIGITIZE_TAC "nb_" `read (memory :> bytes (scalar,32)) s0` THEN
    BYTES_DIGITIZE_TAC "xb_" `read (memory :> bytes (point,32)) s0` THEN
    ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--131) THEN
    SUBGOAL_THEN
     `bignum_from_memory (stackpointer,4) s131 = n_input /\
      bignum_from_memory (word_add stackpointer (word 32),4) s131 = X /\
      bignum_from_memory(word_add stackpointer (word 224),4) s131 = X /\
      bignum_from_memory(word_add stackpointer (word 64),4) s131 = 1`
    STRIP_ASSUME_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["X"; "X_input"] THEN
      MATCH_MP_TAC(TAUT `r /\ q /\ p ==> p /\ q /\ q /\ r`) THEN CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE
          `m = n MOD 2 EXP 255 <=> m + 2 EXP 255 * n DIV 2 EXP 255 = n`] THEN
        SUBGOAL_THEN
         `X_input DIV 2 EXP 255 = bitval(bit 7 (xb_31:byte))` MP_TAC THEN
        EXPAND_TAC "X_input" THENL
         [REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; ARITH_RULE `255 = 248 + 7`] THEN
          REWRITE_TAC[ADD_ASSOC] THEN
          SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
          W(MP_TAC o PART_MATCH (lhand o rand) DIV_LT o
            funpow 3 lhand o snd) THEN
          ANTS_TAC THENL
           [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
            DISCH_THEN SUBST1_TAC] THEN
          REWRITE_TAC[ADD_CLAUSES; BITVAL_ODD; BIT_VAL] THEN
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
          REWRITE_TAC[ARITH_RULE `x DIV 2 EXP 7 < 2 <=> x < 256`] THEN
          BOUNDER_TAC[];
          DISCH_THEN SUBST1_TAC];
        EXPAND_TAC "n_input"] THEN
      REWRITE_TAC[bignum_of_wordlist; val_def] THEN
      REWRITE_TAC[DIMINDEX_8; ARITH_RULE `i < 8 <=> 0 <= i /\ i <= 7`] THEN
      REWRITE_TAC[DIMINDEX_64; ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_ZX] THEN
      ONCE_REWRITE_TAC[BIT_GUARD] THEN
      REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["d"; "xm"; "zm"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["s"; "xm"; "zm"] THEN
    LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN
    LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
    LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
    LOCAL_MUL_4_TAC 0 ["xn"; "s"; "d"] THEN
    LOCAL_MUL_4_TAC 0 ["zn"; "p"; "e"] THEN
    ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC [142] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s142" THEN
    DISCARD_MATCHING_ASSUMPTIONS [`nonoverlapping_modulo a b c`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    SUBGOAL_THEN `X < 2 * p_25519` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[p_25519] THEN ARITH_TAC;
      ALL_TAC] THEN
   REWRITE_TAC[ladder_x2; ladder_z2; ladder_x3; ladder_z3] THEN
    REWRITE_TAC[flipladder; ARITH_RULE `255 - 254 = 0 + 1`] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[SUB_0; ADD_CLAUSES; ARITH_RULE `255 - 1 = 254`] THEN
    SUBGOAL_THEN `nn DIV 2 EXP 255 = 0` SUBST1_TAC THENL
     [EXPAND_TAC "nn" THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nn DIV 2 EXP 254 = 1` SUBST1_TAC THENL
     [EXPAND_TAC "nn" THEN SIMP_TAC[DIV_ADD; DIVIDES_REFL] THEN
      SIMP_TAC[DIV_LT; ARITH_RULE `x:num < n ==> x - k < n`;
               MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
     CONV_TAC NUM_REDUCE_CONV;
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_CONG_REFL] THEN
    REWRITE_TAC[montgomery_xzdouble; curve25519; A_25519] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REPEAT
     (ANTS_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; STRIP_TAC]) THEN
    STRIP_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`a:num < 2 * b`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXP_2]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[num_congruent; GSYM INT_OF_NUM_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;

    (*** The main loop invariant for the Montgomery ladder ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add stackpointer (word 288),4)` THEN
    GHOST_INTRO_TAC `zn:num`
     `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
    GHOST_INTRO_TAC `xm:num`
     `bignum_from_memory (word_add stackpointer (word 224),4)` THEN
    GHOST_INTRO_TAC `zm:num`
     `bignum_from_memory(word_add stackpointer (word 64),4)` THEN
    REWRITE_TAC[WORD_RULE `word_sub (word (i + 1)) (word 1) = word i`] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    LOCAL_SUB_TWICE4_TAC 0 ["dm"; "xm"; "zm"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["sn"; "xn"; "zn"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["dn"; "xn"; "zn"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["sm"; "xm"; "zm"] THEN
    LOCAL_MUL_4_TAC 0 ["dmsn"; "sn"; "dm"] THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add stackpointer
       (word(8 * val(word_ushr (word i:int64) 6))))) s5 =
      word(n_input DIV (2 EXP (64 * i DIV 64)) MOD 2 EXP (64 * 1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "n_input" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 254 ==> MIN (4 - i DIV 64) 1 = 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
      VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (6--11) THEN
    SUBGOAL_THEN
     `word_and
        (word_jushr (word((n_input DIV 2 EXP (64 * i DIV 64)) MOD 2 EXP 64))
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
      REWRITE_TAC[GSYM CONG_MOD_2_ALT] THEN
      EXPAND_TAC "nn" THEN
      SIMP_TAC[DIV_ADD; DIVIDES_EXP_LE_IMP; LT_IMP_LE; ASSUME `i < 254`;
               DIV_EXP; EXP_EQ_0; ARITH_EQ] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `n divides e /\ (y == z) (mod n) ==> (z:num == e + y) (mod n)`) THEN
      ASM_REWRITE_TAC[DIVIDES_2; EVEN_EXP; ARITH_EVEN; SUB_EQ_0; NOT_LE] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 254 = 8 * 2 EXP 251`; MOD_MULT_MOD] THEN
      REWRITE_TAC[ADD_SUB] THEN
      SUBGOAL_THEN `i = 3 + i - 3` SUBST1_TAC THENL
       [UNDISCH_TAC `3 <= i` THEN ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
      REWRITE_TAC[GSYM DIV_DIV; NUM_REDUCE_CONV `2 EXP 3`] THEN
      REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`] THEN
      MATCH_MP_TAC CONG_DIV2 THEN
      MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `2 EXP 251` THEN
      REWRITE_TAC[CONG_LMOD; CONG_REFL] THEN
      REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[MULT_SYM] (CONJUNCT2 EXP))] THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
      UNDISCH_TAC `i < 254` THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_SUB_EQ_0;
      MESON[VAL_WORD_BITVAL; VAL_EQ; EQ_BITVAL]
       `word(bitval b) = word(bitval c) <=> (b <=> c)`]) THEN
    LOCAL_MUX_4_TAC 0 ["d"; "dm"; "dn"] THEN
    LOCAL_MUX_4_TAC 0 ["s"; "sm"; "sn"] THEN
    LOCAL_MUL_4_TAC 0 ["dnsm"; "sm"; "dn"] THEN
    LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["dpro"; "dmsn"; "dnsm"] THEN
    LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["spro"; "dmsn"; "dnsm"] THEN
    LOCAL_SQR_4_TAC 0 ["dpro"; "dpro"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
    LOCAL_SQR_4_TAC 0 ["xm"; "spro"] THEN
    LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
    LOCAL_MUL_4_TAC 0 ["xn"; "s"; "d"] THEN
    LOCAL_MUL_4_TAC 0 ["zm"; "dpro"; "x"] THEN
    LOCAL_MUL_4_TAC 0 ["zn"; "p"; "e"] THEN
    ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC [28] THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `(MAYCHANGE a ,, b) s s'` o concl))) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN MP_TAC th) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s28" THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`aligned a b`; `val(word i) = i`; `nonoverlapping_modulo a b c`] THEN
    REWRITE_TAC[ladder_x2; ladder_z2; ladder_x3; ladder_z3] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 254 ==> 255 - i = (255 - (i + 1)) + 1`] THEN
    REWRITE_TAC[flipladder] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 254 ==> ~(255 - (i + 1) = 0)`] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 254 ==> 255 - (255 - (i + 1)) = i + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 254 ==> 255 - (255 - (i + 1) + 1) = i`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
      [ladder_x2; ladder_z2; ladder_x3; ladder_z3]) THEN
    LET_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REPEAT
     (ANTS_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; STRIP_TAC]) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REWRITE_TAC[ISPEC `p:bool` EQ_SYM_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXP_2]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[num_congruent; GSYM INT_OF_NUM_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    ASM_REWRITE_TAC[montgomery_xzdouble; montgomery_xzdiffadd;
                    curve25519; A_25519; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;

    (*** The trivial loop-back subgoal ***)

    REPEAT STRIP_TAC THEN ARM_SIM_TAC CURVE25519_X25519_BYTE_ALT_EXEC (1--2) THEN
    REWRITE_TAC[COND_RAND; COND_RATOR] THEN
    MATCH_MP_TAC(TAUT `p ==> (if p then T else x)`) THEN
    MATCH_MP_TAC(WORD_ARITH
     `3 < val x /\ val x < 254 ==> 3 <= val(word_sub x (word 1):int64)`) THEN
    VAL_INT64_TAC `i:num` THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN

  (*** Multiplexing before last doublings ***)

  GHOST_INTRO_TAC `xn:num`
   `bignum_from_memory (word_add stackpointer (word 288),4)` THEN
  GHOST_INTRO_TAC `zn:num`
   `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
  GHOST_INTRO_TAC `xm:num`
   `bignum_from_memory (word_add stackpointer (word 224),4)` THEN
  GHOST_INTRO_TAC `zm:num`
   `bignum_from_memory(word_add stackpointer (word 64),4)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  LOCAL_MUX_4_TAC 3 ["xn"; "xm"; "xn"] THEN
  LOCAL_MUX_4_TAC 0 ["zn"; "zm"; "zn"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [WORD_SUB_0; VAL_WORD_BITVAL; BITVAL_EQ_0; COND_SWAP]) THEN

  (*** The first doubling to get from nn/8 to nn/4 ***)

  LOCAL_SUB_TWICE4_TAC 0 ["d"; "xn"; "zn"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["s"; "xn"; "zn"] THEN
  LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN
  LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
  LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
  LOCAL_MUL_4_TAC 0 ["xn"; "s"; "d"] THEN
  LOCAL_MUL_4_TAC 0 ["zn"; "p"; "e"] THEN
  MAP_EVERY (fun t -> REABBREV_TAC t THEN POP_ASSUM SUBST_ALL_TAC)
   [`xn4 = read(memory :> bytes(word_add stackpointer (word 288),8 * 4)) s15`;
    `zn4 =
     read(memory :> bytes(word_add stackpointer (word 160),8 * 4)) s15`] THEN
  SUBGOAL_THEN `8 divides nn` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN REWRITE_TAC[DIVIDES_MOD] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 254 = 8 * 2 EXP 251`; MOD_MULT_MOD] THEN
    REWRITE_TAC[ADD_SUB; GSYM LEFT_ADD_DISTRIB; MOD_MULT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&xn4 == ladder_x2 X nn 2) (mod &p_25519) /\
    (&zn4 == ladder_z2 X nn 2) (mod &p_25519)`
  MP_TAC THENL
   [REWRITE_TAC[ladder_x2; ladder_z2; ladder_x3; ladder_z3] THEN
    REWRITE_TAC[ARITH_RULE `255 - 2 = (255 - 3) + 1`; flipladder] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ladder_x2; ladder_z2; ladder_x3; ladder_z3]) THEN
    LET_TAC THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `ODD(nn DIV 4) <=> F` SUBST_ALL_TAC THENL
     [REWRITE_TAC[NOT_ODD; GSYM DIVIDES_2] THEN
      MATCH_MP_TAC DIVIDES_DIVIDES_DIV_IMP THEN ASM_REWRITE_TAC[ARITH];
      ALL_TAC] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN
    REPEAT
     (ANTS_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; STRIP_TAC]) THEN
    REPEAT DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXP_2]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[num_congruent; GSYM INT_OF_NUM_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    ASM_REWRITE_TAC[montgomery_xzdouble; montgomery_xzdiffadd;
                    curve25519; A_25519; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (fun th -> intersect (frees (concl th))
                [`xn:num`; `zn:num`; `xm:num`; `zm:num`;
                 `xn':num`; `zn':num`; `d:num`; `d':num`;
                 `s:num`; `s':num`; `p:num`; `e:num`] <> []))) THEN
    STRIP_TAC] THEN

  (*** The next doubling to get from nn/4 to nn/2 ***)

  LOCAL_SUB_TWICE4_TAC 0 ["d"; "xn"; "zn"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["s"; "xn"; "zn"] THEN
  LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN
  LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
  LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
  LOCAL_MUL_4_TAC 0 ["xn"; "s"; "d"] THEN
  LOCAL_MUL_4_TAC 0 ["zn"; "p"; "e"] THEN
  MAP_EVERY (fun t -> REABBREV_TAC t THEN POP_ASSUM SUBST_ALL_TAC)
   [`xn2 = read(memory :> bytes(word_add stackpointer (word 288),8 * 4)) s25`;
    `zn2 =
     read(memory :> bytes(word_add stackpointer (word 160),8 * 4)) s25`] THEN
  SUBGOAL_THEN
   `(&xn2 == ladder_x2 X nn 1) (mod &p_25519) /\
    (&zn2 == ladder_z2 X nn 1) (mod &p_25519)`
  MP_TAC THENL
   [REWRITE_TAC[ladder_x2; ladder_z2; ladder_x3; ladder_z3] THEN
    REWRITE_TAC[ARITH_RULE `255 - 1 = (255 - 2) + 1`; flipladder] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ladder_x2; ladder_z2; ladder_x3; ladder_z3]) THEN
    LET_TAC THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `nn = 8 * nn DIV 8` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n = 8 * n DIV 8 <=> n MOD 8 = 0`] THEN
      ASM_REWRITE_TAC[GSYM DIVIDES_MOD];
      REWRITE_TAC[ARITH_RULE `(8 * n) DIV 2 = 2 * 2 * n`] THEN
      REWRITE_TAC[ARITH_RULE `(8 * n) DIV 4 = 2 * n`] THEN
      REWRITE_TAC[ODD_MULT; ARITH_ODD; ARITH_EVEN]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXP_2]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[num_congruent; GSYM INT_OF_NUM_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    ASM_REWRITE_TAC[montgomery_xzdouble; montgomery_xzdiffadd;
                    curve25519; A_25519; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (fun th -> intersect (frees (concl th))
                [`xn4:num`; `zn4:num`;  `d:num`; `d':num`;
                 `s:num`; `s':num`; `p:num`; `e:num`] <> []))) THEN
    STRIP_TAC] THEN

  (*** The final doubling to get from nn/2 to nn ***)

  LOCAL_SUB_TWICE4_TAC 0 ["d"; "xn"; "zn"] THEN
  LOCAL_ADD_TWICE4_TAC 0 ["s"; "xn"; "zn"] THEN
  LOCAL_SQR_4_TAC 0 ["d"; "d"] THEN
  LOCAL_SQR_4_TAC 0 ["s"; "s"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["p"; "s"; "d"] THEN
  LOCAL_CMADD_4_TAC 2 ["e"; "p"; "d"] THEN
  LOCAL_MUL_4_TAC 0 ["xn"; "s"; "d"] THEN
  LOCAL_MUL_4_TAC 0 ["zn"; "p"; "e"] THEN
  SUBGOAL_THEN
   `(&xn == ladder_x2 X nn 0) (mod &p_25519) /\
    (&zn == ladder_z2 X nn 0) (mod &p_25519)`
  MP_TAC THENL
   [REWRITE_TAC[ladder_x2; ladder_z2; ladder_x3; ladder_z3] THEN
    REWRITE_TAC[ARITH_RULE `255 - 0 = (255 - 1) + 1`; flipladder] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ladder_x2; ladder_z2; ladder_x3; ladder_z3]) THEN
    LET_TAC THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `nn = 8 * nn DIV 8` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n = 8 * n DIV 8 <=> n MOD 8 = 0`] THEN
      ASM_REWRITE_TAC[GSYM DIVIDES_MOD];
      REWRITE_TAC[ARITH_RULE `(8 * n) DIV 2 = 2 * 2 * n`] THEN
      REWRITE_TAC[ODD_MULT; ARITH_ODD; ARITH_EVEN; DIV_1]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EXP_2]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[num_congruent; GSYM INT_OF_NUM_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN
    ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    ASM_REWRITE_TAC[montgomery_xzdouble; montgomery_xzdiffadd;
                    curve25519; A_25519; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (fun th -> intersect (frees (concl th))
                [`xn2:num`; `zn2:num`;  `d:num`; `d':num`;
                 `s:num`; `s':num`; `p:num`; `e:num`] <> []))) THEN
    STRIP_TAC] THEN

  (*** The inlining of modular inverse ***)

  ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (36--37) THEN
  LOCAL_MODINV_TAC 38 THEN

  (*** The final multiplication ***)

  LOCAL_MUL_P25519_TAC 0 ["zn"; "xn"; "zn"] THEN

  (*** Bytewise store and finish of simulation ***)

  BIGNUM_LDIGITIZE_TAC "res_"
   `read(memory :> bytes(word_add stackpointer (word 160),8 * 4)) s39` THEN
  ARM_STEPS_TAC CURVE25519_X25519_BYTE_ALT_EXEC (40--101) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `zn':num` THEN CONJ_TAC THENL
   [CONV_TAC(LAND_CONV BYTES_EXPAND_CONV) THEN EXPAND_TAC "zn'" THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; val_def] THEN
    REWRITE_TAC[DIMINDEX_8; ARITH_RULE `i < 8 <=> 0 <= i /\ i <= 7`] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_ZX] THEN
    REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN

  (*** Finishing the mathematics ***)

  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM deproject; PUREX25519_MOD] THEN
  MATCH_MP_TAC DEPROJECT_LADDER_EVEN THEN ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL [EXPAND_TAC "nn" THEN ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[GSYM DIVIDES_2] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        DIVIDES_TRANS)) THEN
  REWRITE_TAC[DIVIDES_MOD] THEN ARITH_TAC);;

let CURVE25519_X25519_BYTE_ALT_SUBROUTINE_CORRECT = time prove
 (`!res scalar n point X pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 368),368))
        [(word pc,0x4420); (res,32); (scalar,32); (point,32)] /\
    nonoverlapping (res,32) (word pc,0x4420)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) curve25519_x25519_byte_alt_mc /\
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
                      memory :> bytes(word_sub stackpointer (word 368),368)])`,
  ARM_ADD_RETURN_STACK_TAC CURVE25519_X25519_BYTE_ALT_EXEC
    CURVE25519_X25519_BYTE_ALT_CORRECT
    `[X19; X20; X21; X22; X23; X24]` 368);;
