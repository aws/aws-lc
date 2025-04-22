(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Karatsuba (multi-level) 32x32->64 squaring.                               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/fastmul/bignum_ksqr_32_64.o";;
 ****)

let bignum_ksqr_32_64_mc =
  define_assert_from_elf "bignum_ksqr_32_64_mc" "arm/fastmul/bignum_ksqr_32_64.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf5;       (* arm_STP X21 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0xaa0103f4;       (* arm_MOV X20 X1 *)
  0xaa0203f5;       (* arm_MOV X21 X2 *)
  0x94000161;       (* arm_BL (word 1412) *)
  0x91040260;       (* arm_ADD X0 X19 (rvalue (word 256)) *)
  0x91020281;       (* arm_ADD X1 X20 (rvalue (word 128)) *)
  0xaa1503e2;       (* arm_MOV X2 X21 *)
  0x9400015d;       (* arm_BL (word 1396) *)
  0xa9500660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&256))) *)
  0xa9480e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&128))) *)
  0xab020000;       (* arm_ADDS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9100660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&256))) *)
  0xa9510660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&272))) *)
  0xa9490e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&144))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9110660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&272))) *)
  0xa9520660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&288))) *)
  0xa94a0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&160))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9120660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&288))) *)
  0xa9530660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&304))) *)
  0xa94b0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&176))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9130660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&304))) *)
  0xa9540660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&320))) *)
  0xa94c0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&192))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9140660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&320))) *)
  0xa9550660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&336))) *)
  0xa94d0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&208))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9150660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&336))) *)
  0xa9560660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&352))) *)
  0xa94e0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&224))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9160660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&352))) *)
  0xa9570660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&368))) *)
  0xa94f0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&240))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9170660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&368))) *)
  0xa9580660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&384))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa9180660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&384))) *)
  0xa9590660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&400))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa9190660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&400))) *)
  0xa95a0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&416))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa91a0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&416))) *)
  0xa95b0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&432))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa91b0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&432))) *)
  0xa95c0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&448))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa91c0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&448))) *)
  0xa95d0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&464))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa91d0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&464))) *)
  0xa95e0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&480))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa91e0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&480))) *)
  0xa95f0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&496))) *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xa91f0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&496))) *)
  0xa9480680;       (* arm_LDP X0 X1 X20 (Immediate_Offset (iword (&128))) *)
  0xa9404690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&0))) *)
  0xeb100000;       (* arm_SUBS X0 X0 X16 *)
  0xfa110021;       (* arm_SBCS X1 X1 X17 *)
  0xa9490e82;       (* arm_LDP X2 X3 X20 (Immediate_Offset (iword (&144))) *)
  0xa9414690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&16))) *)
  0xfa100042;       (* arm_SBCS X2 X2 X16 *)
  0xfa110063;       (* arm_SBCS X3 X3 X17 *)
  0xa94a1684;       (* arm_LDP X4 X5 X20 (Immediate_Offset (iword (&160))) *)
  0xa9424690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&32))) *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xfa1100a5;       (* arm_SBCS X5 X5 X17 *)
  0xa94b1e86;       (* arm_LDP X6 X7 X20 (Immediate_Offset (iword (&176))) *)
  0xa9434690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&48))) *)
  0xfa1000c6;       (* arm_SBCS X6 X6 X16 *)
  0xfa1100e7;       (* arm_SBCS X7 X7 X17 *)
  0xa94c2688;       (* arm_LDP X8 X9 X20 (Immediate_Offset (iword (&192))) *)
  0xa9444690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&64))) *)
  0xfa100108;       (* arm_SBCS X8 X8 X16 *)
  0xfa110129;       (* arm_SBCS X9 X9 X17 *)
  0xa94d2e8a;       (* arm_LDP X10 X11 X20 (Immediate_Offset (iword (&208))) *)
  0xa9454690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&80))) *)
  0xfa10014a;       (* arm_SBCS X10 X10 X16 *)
  0xfa11016b;       (* arm_SBCS X11 X11 X17 *)
  0xa94e368c;       (* arm_LDP X12 X13 X20 (Immediate_Offset (iword (&224))) *)
  0xa9464690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&96))) *)
  0xfa10018c;       (* arm_SBCS X12 X12 X16 *)
  0xfa1101ad;       (* arm_SBCS X13 X13 X17 *)
  0xa94f3e8e;       (* arm_LDP X14 X15 X20 (Immediate_Offset (iword (&240))) *)
  0xa9474690;       (* arm_LDP X16 X17 X20 (Immediate_Offset (iword (&112))) *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xfa1101ef;       (* arm_SBCS X15 X15 X17 *)
  0xda1f03f0;       (* arm_NGC X16 XZR *)
  0xab10021f;       (* arm_CMN X16 X16 *)
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba1f0000;       (* arm_ADCS X0 X0 XZR *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba1f0021;       (* arm_ADCS X1 X1 XZR *)
  0xa90006a0;       (* arm_STP X0 X1 X21 (Immediate_Offset (iword (&0))) *)
  0xca100042;       (* arm_EOR X2 X2 X16 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xa9010ea2;       (* arm_STP X2 X3 X21 (Immediate_Offset (iword (&16))) *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xca1000a5;       (* arm_EOR X5 X5 X16 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xa90216a4;       (* arm_STP X4 X5 X21 (Immediate_Offset (iword (&32))) *)
  0xca1000c6;       (* arm_EOR X6 X6 X16 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xca1000e7;       (* arm_EOR X7 X7 X16 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xa9031ea6;       (* arm_STP X6 X7 X21 (Immediate_Offset (iword (&48))) *)
  0xca100108;       (* arm_EOR X8 X8 X16 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xca100129;       (* arm_EOR X9 X9 X16 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xa90426a8;       (* arm_STP X8 X9 X21 (Immediate_Offset (iword (&64))) *)
  0xca10014a;       (* arm_EOR X10 X10 X16 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca10016b;       (* arm_EOR X11 X11 X16 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa9052eaa;       (* arm_STP X10 X11 X21 (Immediate_Offset (iword (&80))) *)
  0xca10018c;       (* arm_EOR X12 X12 X16 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xca1001ad;       (* arm_EOR X13 X13 X16 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xa90636ac;       (* arm_STP X12 X13 X21 (Immediate_Offset (iword (&96))) *)
  0xca1001ce;       (* arm_EOR X14 X14 X16 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xa9073eae;       (* arm_STP X14 X15 X21 (Immediate_Offset (iword (&112))) *)
  0x910202a0;       (* arm_ADD X0 X21 (rvalue (word 128)) *)
  0xaa1503e1;       (* arm_MOV X1 X21 *)
  0x910602a2;       (* arm_ADD X2 X21 (rvalue (word 384)) *)
  0x940000c7;       (* arm_BL (word 796) *)
  0xa9500660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&256))) *)
  0xa9400e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&0))) *)
  0xab020000;       (* arm_ADDS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9080660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&128))) *)
  0xa9510660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&272))) *)
  0xa9410e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&16))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9090660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&144))) *)
  0xa9520660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&288))) *)
  0xa9420e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&32))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa90a0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&160))) *)
  0xa9530660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&304))) *)
  0xa9430e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&48))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa90b0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&176))) *)
  0xa9540660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&320))) *)
  0xa9440e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&64))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa90c0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&192))) *)
  0xa9550660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&336))) *)
  0xa9450e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&80))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa90d0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&208))) *)
  0xa9560660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&352))) *)
  0xa9460e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&96))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa90e0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&224))) *)
  0xa9570660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&368))) *)
  0xa9470e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&112))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa90f0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&240))) *)
  0xa9500660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&256))) *)
  0xa9580e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&384))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9100660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&256))) *)
  0xa9510660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&272))) *)
  0xa9590e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&400))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9110660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&272))) *)
  0xa9520660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&288))) *)
  0xa95a0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&416))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9120660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&288))) *)
  0xa9530660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&304))) *)
  0xa95b0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&432))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9130660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&304))) *)
  0xa9540660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&320))) *)
  0xa95c0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&448))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9140660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&320))) *)
  0xa9550660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&336))) *)
  0xa95d0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&464))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9150660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&336))) *)
  0xa9560660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&352))) *)
  0xa95e0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&480))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9160660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&352))) *)
  0xa9570660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&368))) *)
  0xa95f0e62;       (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&496))) *)
  0xba020000;       (* arm_ADCS X0 X0 X2 *)
  0xba030021;       (* arm_ADCS X1 X1 X3 *)
  0xa9170660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&368))) *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0xa9480660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&128))) *)
  0xa9480ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&128))) *)
  0xeb020000;       (* arm_SUBS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9080660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&128))) *)
  0xa9490660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&144))) *)
  0xa9490ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&144))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9090660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&144))) *)
  0xa94a0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&160))) *)
  0xa94a0ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&160))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa90a0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&160))) *)
  0xa94b0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&176))) *)
  0xa94b0ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&176))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa90b0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&176))) *)
  0xa94c0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&192))) *)
  0xa94c0ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&192))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa90c0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&192))) *)
  0xa94d0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&208))) *)
  0xa94d0ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&208))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa90d0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&208))) *)
  0xa94e0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&224))) *)
  0xa94e0ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&224))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa90e0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&224))) *)
  0xa94f0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&240))) *)
  0xa94f0ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&240))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa90f0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&240))) *)
  0xa9500660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&256))) *)
  0xa9500ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&256))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9100660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&256))) *)
  0xa9510660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&272))) *)
  0xa9510ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&272))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9110660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&272))) *)
  0xa9520660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&288))) *)
  0xa9520ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&288))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9120660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&288))) *)
  0xa9530660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&304))) *)
  0xa9530ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&304))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9130660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&304))) *)
  0xa9540660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&320))) *)
  0xa9540ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&320))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9140660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&320))) *)
  0xa9550660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&336))) *)
  0xa9550ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&336))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9150660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&336))) *)
  0xa9560660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&352))) *)
  0xa9560ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&352))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9160660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&352))) *)
  0xa9570660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&368))) *)
  0xa9570ea2;       (* arm_LDP X2 X3 X21 (Immediate_Offset (iword (&368))) *)
  0xfa020000;       (* arm_SBCS X0 X0 X2 *)
  0xfa030021;       (* arm_SBCS X1 X1 X3 *)
  0xa9170660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&368))) *)
  0xfa1f0294;       (* arm_SBCS X20 X20 XZR *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa9580660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&384))) *)
  0xab140000;       (* arm_ADDS X0 X0 X20 *)
  0xba100021;       (* arm_ADCS X1 X1 X16 *)
  0xa9180660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&384))) *)
  0xa9590660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&400))) *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0xba100021;       (* arm_ADCS X1 X1 X16 *)
  0xa9190660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&400))) *)
  0xa95a0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&416))) *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0xba100021;       (* arm_ADCS X1 X1 X16 *)
  0xa91a0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&416))) *)
  0xa95b0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&432))) *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0xba100021;       (* arm_ADCS X1 X1 X16 *)
  0xa91b0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&432))) *)
  0xa95c0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&448))) *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0xba100021;       (* arm_ADCS X1 X1 X16 *)
  0xa91c0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&448))) *)
  0xa95d0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&464))) *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0xba100021;       (* arm_ADCS X1 X1 X16 *)
  0xa91d0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&464))) *)
  0xa95e0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&480))) *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0xba100021;       (* arm_ADCS X1 X1 X16 *)
  0xa91e0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&480))) *)
  0xa95f0660;       (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&496))) *)
  0xba100000;       (* arm_ADCS X0 X0 X16 *)
  0x9a100021;       (* arm_ADC X1 X1 X16 *)
  0xa91f0660;       (* arm_STP X0 X1 X19 (Immediate_Offset (iword (&496))) *)
  0xa8c17bf5;       (* arm_LDP X21 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf9;       (* arm_STP X25 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa0003f7;       (* arm_MOV X23 X0 *)
  0xaa0103f8;       (* arm_MOV X24 X1 *)
  0xaa0203f9;       (* arm_MOV X25 X2 *)
  0x940000a9;       (* arm_BL (word 676) *)
  0xa9402f0a;       (* arm_LDP X10 X11 X24 (Immediate_Offset (iword (&0))) *)
  0xa9442708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&64))) *)
  0xeb08014a;       (* arm_SUBS X10 X10 X8 *)
  0xfa09016b;       (* arm_SBCS X11 X11 X9 *)
  0xa941370c;       (* arm_LDP X12 X13 X24 (Immediate_Offset (iword (&16))) *)
  0xa9452708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&80))) *)
  0xfa08018c;       (* arm_SBCS X12 X12 X8 *)
  0xfa0901ad;       (* arm_SBCS X13 X13 X9 *)
  0xa9423f0e;       (* arm_LDP X14 X15 X24 (Immediate_Offset (iword (&32))) *)
  0xa9462708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&96))) *)
  0xfa0801ce;       (* arm_SBCS X14 X14 X8 *)
  0xfa0901ef;       (* arm_SBCS X15 X15 X9 *)
  0xa9434710;       (* arm_LDP X16 X17 X24 (Immediate_Offset (iword (&48))) *)
  0xa9472708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&112))) *)
  0xfa080210;       (* arm_SBCS X16 X16 X8 *)
  0xfa090231;       (* arm_SBCS X17 X17 X9 *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xab13027f;       (* arm_CMN X19 X19 *)
  0xca13014a;       (* arm_EOR X10 X10 X19 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca13016b;       (* arm_EOR X11 X11 X19 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa9002f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&0))) *)
  0xca13018c;       (* arm_EOR X12 X12 X19 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xca1301ad;       (* arm_EOR X13 X13 X19 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xa901372c;       (* arm_STP X12 X13 X25 (Immediate_Offset (iword (&16))) *)
  0xca1301ce;       (* arm_EOR X14 X14 X19 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xca1301ef;       (* arm_EOR X15 X15 X19 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xa9023f2e;       (* arm_STP X14 X15 X25 (Immediate_Offset (iword (&32))) *)
  0xca130210;       (* arm_EOR X16 X16 X19 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xca130231;       (* arm_EOR X17 X17 X19 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xa9034730;       (* arm_STP X16 X17 X25 (Immediate_Offset (iword (&48))) *)
  0x910202e0;       (* arm_ADD X0 X23 (rvalue (word 128)) *)
  0x91010301;       (* arm_ADD X1 X24 (rvalue (word 64)) *)
  0x94000080;       (* arm_BL (word 512) *)
  0xa9482eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&128))) *)
  0xa94436ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&64))) *)
  0xab0c014a;       (* arm_ADDS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9082eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&128))) *)
  0xa9492eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94536ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&80))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9092eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94a2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&160))) *)
  0xa94636ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&96))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90a2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&160))) *)
  0xa94b2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&176))) *)
  0xa94736ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&112))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90b2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&176))) *)
  0xa94c2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90c2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xa94d2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90d2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xa94e2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90e2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xa94f2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90f2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0x91010320;       (* arm_ADD X0 X25 (rvalue (word 64)) *)
  0xaa1903e1;       (* arm_MOV X1 X25 *)
  0x94000059;       (* arm_BL (word 356) *)
  0xa94006e0;       (* arm_LDP X0 X1 X23 (Immediate_Offset (iword (&0))) *)
  0xa94846f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&128))) *)
  0xab100000;       (* arm_ADDS X0 X0 X16 *)
  0xba110021;       (* arm_ADCS X1 X1 X17 *)
  0xa9410ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&16))) *)
  0xa94946f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&144))) *)
  0xba100042;       (* arm_ADCS X2 X2 X16 *)
  0xba110063;       (* arm_ADCS X3 X3 X17 *)
  0xa94216e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&32))) *)
  0xa94a46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&160))) *)
  0xba100084;       (* arm_ADCS X4 X4 X16 *)
  0xba1100a5;       (* arm_ADCS X5 X5 X17 *)
  0xa9431ee6;       (* arm_LDP X6 X7 X23 (Immediate_Offset (iword (&48))) *)
  0xa94b46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&176))) *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0xba1100e7;       (* arm_ADCS X7 X7 X17 *)
  0xa94826e8;       (* arm_LDP X8 X9 X23 (Immediate_Offset (iword (&128))) *)
  0xa94c46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&192))) *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba110129;       (* arm_ADCS X9 X9 X17 *)
  0xa9492eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94d46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&208))) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xa94a36ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&160))) *)
  0xa94e46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&224))) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xa94b3eee;       (* arm_LDP X14 X15 X23 (Immediate_Offset (iword (&176))) *)
  0xa94f46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&240))) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0xa9444730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&64))) *)
  0xeb100000;       (* arm_SUBS X0 X0 X16 *)
  0xfa110021;       (* arm_SBCS X1 X1 X17 *)
  0xa90406e0;       (* arm_STP X0 X1 X23 (Immediate_Offset (iword (&64))) *)
  0xa9454730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&80))) *)
  0xfa100042;       (* arm_SBCS X2 X2 X16 *)
  0xfa110063;       (* arm_SBCS X3 X3 X17 *)
  0xa9050ee2;       (* arm_STP X2 X3 X23 (Immediate_Offset (iword (&80))) *)
  0xa9464730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&96))) *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xfa1100a5;       (* arm_SBCS X5 X5 X17 *)
  0xa90616e4;       (* arm_STP X4 X5 X23 (Immediate_Offset (iword (&96))) *)
  0xa9474730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&112))) *)
  0xfa1000c6;       (* arm_SBCS X6 X6 X16 *)
  0xfa1100e7;       (* arm_SBCS X7 X7 X17 *)
  0xa9071ee6;       (* arm_STP X6 X7 X23 (Immediate_Offset (iword (&112))) *)
  0xa9484730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&128))) *)
  0xfa100108;       (* arm_SBCS X8 X8 X16 *)
  0xfa110129;       (* arm_SBCS X9 X9 X17 *)
  0xa90826e8;       (* arm_STP X8 X9 X23 (Immediate_Offset (iword (&128))) *)
  0xa9494730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&144))) *)
  0xfa10014a;       (* arm_SBCS X10 X10 X16 *)
  0xfa11016b;       (* arm_SBCS X11 X11 X17 *)
  0xa9092eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94a4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&160))) *)
  0xfa10018c;       (* arm_SBCS X12 X12 X16 *)
  0xfa1101ad;       (* arm_SBCS X13 X13 X17 *)
  0xa90a36ec;       (* arm_STP X12 X13 X23 (Immediate_Offset (iword (&160))) *)
  0xa94b4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&176))) *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xfa1101ef;       (* arm_SBCS X15 X15 X17 *)
  0xa90b3eee;       (* arm_STP X14 X15 X23 (Immediate_Offset (iword (&176))) *)
  0xfa1f0318;       (* arm_SBCS X24 X24 XZR *)
  0xda9f23f9;       (* arm_CSETM X25 Condition_CC *)
  0xa94c2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xab18014a;       (* arm_ADDS X10 X10 X24 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90c2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xa94d2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90d2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xa94e2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90e2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xa94f2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90f2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xa8c17bf9;       (* arm_LDP X25 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc00034;       (* arm_LDR Q20 X1 (Immediate_Offset (word 0)) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x3dc00435;       (* arm_LDR Q21 X1 (Immediate_Offset (word 16)) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x3dc00836;       (* arm_LDR Q22 X1 (Immediate_Offset (word 32)) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x3dc00c37;       (* arm_LDR Q23 X1 (Immediate_Offset (word 48)) *)
  0x6f00e5fe;       (* arm_MOVI Q30 (word 4294967295) *)
  0x9b047c51;       (* arm_MUL X17 X2 X4 *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x6e144281;       (* arm_EXT Q1 Q20 Q20 64 *)
  0x9bc47c54;       (* arm_UMULH X20 X2 X4 *)
  0x0f208682;       (* arm_SHRN Q2 Q20 32 32 *)
  0xeb030055;       (* arm_SUBS X21 X2 X3 *)
  0x0e813a80;       (* arm_ZIP1 Q0 Q20 Q1 32 64 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x6e1542a1;       (* arm_EXT Q1 Q21 Q21 64 *)
  0x9bc57c75;       (* arm_UMULH X21 X3 X5 *)
  0x0f2086a2;       (* arm_SHRN Q2 Q21 32 32 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x0e813aa0;       (* arm_ZIP1 Q0 Q21 Q1 32 64 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9b037c4f;       (* arm_MUL X15 X2 X3 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0x9bc37c50;       (* arm_UMULH X16 X2 X3 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9002c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&0))) *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x6e1642c1;       (* arm_EXT Q1 Q22 Q22 64 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x0f2086c2;       (* arm_SHRN Q2 Q22 32 32 *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
  0x0e813ac0;       (* arm_ZIP1 Q0 Q22 Q1 32 64 *)
  0x9b057c8f;       (* arm_MUL X15 X4 X5 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0x9bc57c90;       (* arm_UMULH X16 X4 X5 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xa9022c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&32))) *)
  0x6e1742e1;       (* arm_EXT Q1 Q23 Q23 64 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x0f2086e2;       (* arm_SHRN Q2 Q23 32 32 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x0e813ae0;       (* arm_ZIP1 Q0 Q23 Q1 32 64 *)
  0xa903380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&48))) *)
  0x9b087cd1;       (* arm_MUL X17 X6 X8 *)
  0x2ea2c050;       (* arm_UMULL_VEC Q16 Q2 Q2 32 *)
  0x9b097cee;       (* arm_MUL X14 X7 X9 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0x9bc87cd4;       (* arm_UMULH X20 X6 X8 *)
  0x2ea0c012;       (* arm_UMULL_VEC Q18 Q0 Q0 32 *)
  0xeb0700d5;       (* arm_SUBS X21 X6 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb08012c;       (* arm_SUBS X12 X9 X8 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x6f601641;       (* arm_USRA_VEC Q1 Q18 32 64 128 *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x4e3e1c24;       (* arm_AND_VEC Q4 Q1 Q30 128 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0x6f601490;       (* arm_USRA_VEC Q16 Q4 32 64 128 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x6f605492;       (* arm_SLI_VEC Q18 Q4 32 64 *)
  0x9bc97cf5;       (* arm_UMULH X21 X7 X9 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x6f601430;       (* arm_USRA_VEC Q16 Q1 32 64 128 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x4e975ab1;       (* arm_UZP2 Q17 Q21 Q23 32 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x0ea12ae4;       (* arm_XTN Q4 Q23 32 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x4e083e16;       (* arm_UMOV X22 Q16 0 8 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x0ea12aa5;       (* arm_XTN Q5 Q21 32 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4ea00aa1;       (* arm_REV64_VEC Q1 Q21 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa9042c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&64))) *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0x4e183e4d;       (* arm_UMOV X13 Q18 1 8 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x4e183e0e;       (* arm_UMOV X14 Q16 1 8 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0x4e083e4c;       (* arm_UMOV X12 Q18 0 8 *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0xa9054c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&80))) *)
  0x2eb1c087;       (* arm_UMULL_VEC Q7 Q4 Q17 32 *)
  0x9b097d0f;       (* arm_MUL X15 X8 X9 *)
  0x4e975af0;       (* arm_UZP2 Q16 Q23 Q23 32 *)
  0x9bc97d10;       (* arm_UMULH X16 X8 X9 *)
  0x4eb79c20;       (* arm_MUL_VEC Q0 Q1 Q23 32 *)
  0xab0f02cb;       (* arm_ADDS X11 X22 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x2eb1c201;       (* arm_UMULL_VEC Q1 Q16 Q17 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0x4e3e1ce2;       (* arm_AND_VEC Q2 Q7 Q30 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f605400;       (* arm_SHL_VEC Q0 Q0 32 64 *)
  0x6f6014e1;       (* arm_USRA_VEC Q1 Q7 32 64 128 *)
  0x2ea58080;       (* arm_UMLAL_VEC Q0 Q4 Q5 32 *)
  0x4e183c10;       (* arm_UMOV X16 Q0 1 8 *)
  0x4e083c0f;       (* arm_UMOV X15 Q0 0 8 *)
  0x6f601441;       (* arm_USRA_VEC Q1 Q2 32 64 128 *)
  0x4e083c34;       (* arm_UMOV X20 Q1 0 8 *)
  0x4e183c35;       (* arm_UMOV X21 Q1 1 8 *)
  0xa9062c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&96))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa907380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&112))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9bc67c51;       (* arm_UMULH X17 X2 X6 *)
  0xab1101ce;       (* arm_ADDS X14 X14 X17 *)
  0x9bc77c71;       (* arm_UMULH X17 X3 X7 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a1f02b1;       (* arm_ADC X17 X21 XZR *)
  0xab0a01cb;       (* arm_ADDS X11 X14 X10 *)
  0xba0e01ee;       (* arm_ADCS X14 X15 X14 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xab0a01cc;       (* arm_ADDS X12 X14 X10 *)
  0xba0b01ed;       (* arm_ADCS X13 X15 X11 *)
  0xba0e020e;       (* arm_ADCS X14 X16 X14 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba1003f0;       (* arm_ADCS X16 XZR X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xeb050096;       (* arm_SUBS X22 X4 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb080134;       (* arm_SUBS X20 X9 X8 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb030056;       (* arm_SUBS X22 X2 X3 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb0600f4;       (* arm_SUBS X20 X7 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba14018c;       (* arm_ADCS X12 X12 X20 *)
  0xba1301ad;       (* arm_ADCS X13 X13 X19 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050076;       (* arm_SUBS X22 X3 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070134;       (* arm_SUBS X20 X9 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040056;       (* arm_SUBS X22 X2 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060114;       (* arm_SUBS X20 X8 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15018c;       (* arm_ADCS X12 X12 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050056;       (* arm_SUBS X22 X2 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060134;       (* arm_SUBS X20 X9 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040076;       (* arm_SUBS X22 X3 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070114;       (* arm_SUBS X20 X8 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xab0a014a;       (* arm_ADDS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xa9420c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&32))) *)
  0xab02014a;       (* arm_ADDS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa9430c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&48))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xa903340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xa9440c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&64))) *)
  0xba0201ce;       (* arm_ADCS X14 X14 X2 *)
  0xba0301ef;       (* arm_ADCS X15 X15 X3 *)
  0xa9043c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&64))) *)
  0xa9450c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&80))) *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba030231;       (* arm_ADCS X17 X17 X3 *)
  0xa9054410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&80))) *)
  0xa9460c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xba130042;       (* arm_ADCS X2 X2 X19 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xa9060c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xa9470c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9070c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_KSQR_32_64_EXEC = ARM_MK_EXEC_RULE bignum_ksqr_32_64_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof for the inner-level 8->16 squaring.                                 *)
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

needs "arm/proofs/neon_helper.ml";;


let BIGNUM_KSQR_32_64_SUBLEMMA = prove
 (`!z x a pc returnaddress.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc,3596); (x,8 * 8)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word(pc + 0x0)) bignum_ksqr_32_64_mc /\
                read PC s = word(pc + 0x858) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,8) s = a)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                      Q21; Q22; Q23; Q30] ,,
            MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[ADD_CLAUSES] THEN

  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 x) s0` `x_1:(64)word` `x_0:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 16:(64)word))) s0`
    `x_3:(64)word` `x_2:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 32:(64)word))) s0`
    `x_5:(64)word` `x_4:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 48:(64)word))) s0`
    `x_7:(64)word` `x_6:(64)word` THEN

  (*** First nested mini-ADK 4x4 squaring block ***)

  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
    [49;51;53;55;79;81;83;85]
    [WORD_SQR64_HI; WORD_SQR64_LO]
    [10;11;25;35;37;41;43;44;45;46;48;49;50;52;53;54;56;58;60;62;
     64;68;70;72;74;76;77;80;81;82;84;85;86;88;92;96;98;100;102;104;
     106;108;110;114;116]
    (1--118) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2 =
    bignum_of_wordlist [mullo_s53; sum_s74; sum_s80; sum_s82;
                        sum_s108; sum_s110; sum_s114; sum_s116]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Second nested mini-ADK 4x4 squaring block ***)


  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [148;152;154;156;167;178;180;182]
   [WORD_SQR64_HI; WORD_SQR64_LO]
   [119;121;132;140;141;144;145;146;147;149;151;153;155;157;158;160;161;
    162;154;152;164;168;169;171;172;174;175;177;179;181;183;184;182;178;
    188;192;193;195;196;198;199;201;202]
   (119--207) THEN
  RULE_ASSUM_TAC (REWRITE_RULE
      [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO]) THEN
  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [208;209] [WORD_SQR64_HI; WORD_SQR64_LO] [208;209]
   (208--210) THEN
  RULE_ASSUM_TAC (REWRITE_RULE
      [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_HI]) THEN
  ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [211;212] [WORD_SQR64_HI; WORD_SQR64_LO] [211;212;214;215]
   (211--216) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2 =
    bignum_of_wordlist [mullo_s154;sum_s172;sum_s177;sum_s179;
                        sum_s201;sum_s202;sum_s214;sum_s215]`
  ASSUME_TAC THENL
    [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    let is_acc_thm_for_next acc_thm =
      List.exists (contains_str (string_of_term (concl acc_thm)))
        ["208";"209";"211";"212"] in
    let filter_acc_thms_for_next acc_thms =
      List.filter is_acc_thm_for_next acc_thms in
    let wpat = `word a = b` in
    ACCUMULATOR_POP_ASSUM_LIST(
      fun acc_thms ->
        let acc_thms = filter_acc_thms_for_next acc_thms in
        List.iter (fun t -> Printf.printf "assuming: %s\n" t)
          (List.map string_of_thm acc_thms);
        MAP_EVERY ASSUME_TAC acc_thms) THEN
    DISCARD_ASSUMPTIONS_TAC
      (fun th -> can (term_match [] wpat) (concl th) &&
                 not (is_acc_thm_for_next th))] THEN

  (*** Nested ADK 4x4 multiplication block ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [217;218;220;222;223;224;225;226;227;228;229;230;231;232;233;
    234;235;241;246;248;249;255;260;262;263;264;265;266;267;273;278;
    280;281;282;288;293;295;296;297;298;299;305;310;312;313;314;315;
    321;326;328;329;330;331]
   (217--331) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] *
    bignum_of_wordlist [x_4;x_5;x_6;x_7] =
    bignum_of_wordlist
     [mullo_s217; sum_s260; sum_s293; sum_s326;
      sum_s328; sum_s329; sum_s330; sum_s331]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Final accumulation simulation and 16-digit focusing ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC (332--364) (332--365) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s365" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`1024`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN

  (*** The core rearrangement we are using ***)

  SUBGOAL_THEN
   `(&a:real) pow 2 =
    &(bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2) +
    &2 pow 512 * &(bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2) +
    &2 pow 257 * &(bignum_of_wordlist [x_0;x_1;x_2;x_3] *
                   bignum_of_wordlist [x_4;x_5;x_6;x_7])`
  SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KSQR_32_64_SUBLEMMA_TAC =
  ARM_SUBROUTINE_SIM_TAC
    (bignum_ksqr_32_64_mc,BIGNUM_KSQR_32_64_EXEC,
     0x0,bignum_ksqr_32_64_mc,BIGNUM_KSQR_32_64_SUBLEMMA)
    [`read X0 s`; `read X1 s`;
     `bignum_from_memory (read X1 s,8) s`;
     `pc:num`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* Proof now of the 16->32 squaring (like bignum_ksqr_16_32 proof).          *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_KSQR_32_64_LEMMA = prove
 (`!z x a t pc.
        nonoverlapping (z,8 * 32) (t,8 * 24) /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 24)]
         [(word pc,3596); (x,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_ksqr_32_64_mc /\
                   read PC s = word(pc + 0x5a8) /\
                   C_ARGUMENTS [z; x; t] s /\
                   bignum_from_memory (x,16) s = a)
              (\s. read PC s = word (pc + 0x844) /\
                   bignum_from_memory (z,32) s = a EXP 2)
              (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                          X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                          X22; X23; X24; X25; X30] ,,
               MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                          Q21; Q22; Q23; Q30] ,,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 24)] ,,
               MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `t:int64`;`pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,16) s0` THEN

  (*** First nested 8x8 squaring block ***)

  ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (1--4) THEN
  BIGNUM_KSQR_32_64_SUBLEMMA_TAC 5 THEN
  BIGNUM_LDIGITIZE_TAC "l_" `read (memory :> bytes (z,8 * 16)) s5` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [8;9;12;13;16;17;20;21; 25;27;30;32;35;37;40;42] (6--43) THEN
  SUBGOAL_THEN
   `&(bignum_from_memory(t,8) s43):real =
    abs(&(bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7]) -
        &(bignum_of_wordlist [x_8;x_9;x_10;x_11;x_12;x_13;x_14;x_15]))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 8`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC(REAL_ARITH
       `&x < e /\ &y < e ==> abs(&x - &y):real < e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &x < &y then &y - &x else &x - &y`] THEN
    SUBGOAL_THEN
     `carry_s21 <=>
      bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] <
      bignum_of_wordlist [x_8;x_9;x_10;x_11;x_12;x_13;x_14;x_15]`
    (SUBST_ALL_TAC o SYM) THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_UNMASK_64; WORD_XOR_MASK] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM)] THEN

  (*** Second nested squaring ***)

  ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (44--46) THEN
  BIGNUM_KSQR_32_64_SUBLEMMA_TAC 47 THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 128),8 * 16)) s47` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Computation of H' = H + L_top ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [50;51;55;56;60;61;65;66;69;70;73;74;77;78;81;82] (48--83) THEN
  SUBGOAL_THEN
   `bignum_from_memory(word_add z (word 128),16) s83 =
    bignum_of_wordlist
     [h_0;h_1;h_2;h_3;h_4;h_5;h_6;h_7;h_8;h_9;h_10;h_11;h_12;h_13;h_14;h_15] +
    bignum_of_wordlist[l_8;l_9;l_10;l_11;l_12;l_13;l_14;l_15]`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 16`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN

  (*** Third and final nested squaring ***)

  ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (84--86) THEN
  BIGNUM_KSQR_32_64_SUBLEMMA_TAC 87 THEN
  BIGNUM_LDIGITIZE_TAC "m_"
   `read (memory :> bytes (word_add t (word 64),8 * 16)) s87` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** All remaining accumulation of sub-results ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [90;91;94;95;98;99;102;103;106;107;110;111;114;115;118;119;
    122;123;126;127;130;131;134;135;138;139;142;143;146;147;150;151; 153;
    156;157;160;161;164;165;168;169]
   (88--170) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * 32`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `(&a:real) pow 2 =
    (&(bignum_of_wordlist[l_0; l_1; l_2; l_3; l_4; l_5; l_6; l_7]) +
     &2 pow 512 *
     &(bignum_of_wordlist
       [sum_s50; sum_s51; sum_s55; sum_s56; sum_s60; sum_s61; sum_s65;
        sum_s66; sum_s69; sum_s70; sum_s73; sum_s74; sum_s77; sum_s78;
        sum_s81; sum_s82])) *
    (&2 pow 512 + &1) -
    &2 pow 512 *
    &(bignum_of_wordlist
      [m_0; m_1; m_2; m_3; m_4; m_5; m_6; m_7; m_8; m_9; m_10; m_11; m_12;
       m_13; m_14; m_15])`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
     `l + e * (h + m):num = (l + e * m) + e * h`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(8,8))] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `x EXP 2 = y ==> y = x EXP 2`))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[]
     `abs x:real = y ==> y = abs x`)) THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_UNMASK_64; REAL_VAL_WORD_MASK; DIMINDEX_64;
              COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KSQR_32_64_SUBROUTINE_LEMMA = prove
 (`!z x a t pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(z,8 * 32); (t,8 * 24); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 24); (word_sub stackpointer (word 64),64)]
         [(word pc,3596); (x,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s
                    (word (pc + 0x0)) bignum_ksqr_32_64_mc /\
                   read PC s = word(pc + 0x598) /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [z; x; t] s /\
                   bignum_from_memory (x,16) s = a)
              (\s. read PC s = returnaddress /\
                   bignum_from_memory (z,32) s = a EXP 2)
              (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                          X11; X12; X13; X14; X15; X16; X17] ,,
               MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                          Q21; Q22; Q23; Q30] ,,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 24);
                     memory :> bytes(word_sub stackpointer (word 64),64)] ,,
               MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[ADD_CLAUSES] THEN
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_KSQR_32_64_EXEC BIGNUM_KSQR_32_64_LEMMA
    `[X19;X20;X21;X22;X23;X24;X25;X30]` 64);;

let BIGNUM_KSQR_32_64_LEMMA_TAC =
  ARM_SUBROUTINE_SIM_TAC
    (bignum_ksqr_32_64_mc,BIGNUM_KSQR_32_64_EXEC,
     0x0,bignum_ksqr_32_64_mc,BIGNUM_KSQR_32_64_SUBROUTINE_LEMMA)
    [`read X0 s`; `read X1 s`;
     `read (memory :> bytes (read X1 s,8 * 16)) s`;
     `read X2 s`; `pc:num`; `read SP s`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* Now the overall proof                                                     *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_KSQR_32_64_SUBROUTINE_CORRECT = prove
 (`!z x t a pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(z,8 * 64); (t,8 * 72); (word_sub stackpointer (word 96),96)] /\
        ALLPAIRS nonoverlapping
         [(z,8 * 64); (t,8 * 72); (word_sub stackpointer (word 96),96)]
         [(word pc,3596); (x,8 * 32)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_ksqr_32_64_mc /\
                   read PC s = word pc /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [z; x; t] s /\
                   bignum_from_memory (x,32) s = a)
              (\s. read PC s = returnaddress /\
                   bignum_from_memory (z,64) s = a EXP 2)
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(z,8 * 64);
                          memory :> bytes(t,8 * 72);
                     memory :> bytes(word_sub stackpointer (word 96),96)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `t:int64`; `a:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 96 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  STRIP_TAC THEN

  (*** Start and end boilerplate for save and restore of registers ***)

  SUBGOAL_THEN
   `ensures arm
     (\s. aligned_bytes_loaded s (word pc) bignum_ksqr_32_64_mc /\
          read PC s = word(pc + 0x8) /\
          read SP s = word_add stackpointer (word 64) /\
          C_ARGUMENTS [z; x; t] s /\
          bignum_from_memory (x,32) s = a)
     (\s. read PC s = word(pc + 0x58c) /\
          bignum_from_memory (z,64) s = a EXP 2)
     (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                 X11; X12; X13; X14; X15; X16; X17; X19; X20; X21; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20;
                Q21; Q22; Q23; Q30] ,,
      MAYCHANGE [memory :> bytes(z,8 * 64); memory :> bytes(t,8 * 72);
                 memory :> bytes(stackpointer,64)] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
  MP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THENL
   [ENSURES_EXISTING_PRESERVED_TAC `SP`;
    DISCH_THEN(fun th ->
      ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
      ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
      ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
      ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
      ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (1--2) THEN
      MP_TAC th) THEN
    ARM_BIGSTEP_TAC BIGNUM_KSQR_32_64_EXEC "s3" THEN
    ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  (*** Initialization and splitting of the input ***)

  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  BIGNUM_TERMRANGE_TAC `32` `a:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  MP_TAC(ISPECL [`x:int64`; `16`; `16`] BIGNUM_FROM_MEMORY_SPLIT) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY ABBREV_TAC
   [`ahi = read (memory :> bytes (word_add x (word 128),8 * 16)) s0`;
    `alo = read (memory :> bytes (x,8 * 16)) s0`] THEN

  (*** First nested squaring: low part ***)

  ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (1--4) THEN
  BIGNUM_KSQR_32_64_LEMMA_TAC 5 THEN

  (*** Second nested squaring: high part ***)

  ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (6--9) THEN
  BIGNUM_KSQR_32_64_LEMMA_TAC 10 THEN

  (*** Split L into L_top and L_bot and form H' = H + L_top ***)

  MP_TAC(ISPECL [`z:int64`; `16`; `16`; `s10:armstate`]
    BIGNUM_FROM_MEMORY_SPLIT) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV))) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`ltop = read (memory :> bytes (word_add z (word 128),8 * 16)) s10`;
    `lbot = read (memory :> bytes (z,8 * 16)) s10`;
    `h = read (memory :> bytes (word_add z (word 256),8 * 32)) s10`] THEN

  BIGNUM_LDIGITIZE_TAC "ltop_"
   `read (memory :> bytes (word_add z (word 128),8 * 16)) s10` THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 256),8 * 32)) s10` THEN

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [13; 14; 18; 19; 23; 24; 28; 29; 33; 34; 38; 39; 43; 44; 48; 49;
    52; 53; 56; 57; 60; 61; 64; 65; 68; 69; 72; 73; 76; 77; 80; 81]
   (11--82) THEN

  SUBGOAL_THEN `bignum_from_memory(word_add z (word 256),32) s82 = h + ltop`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 32`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      MAP_EVERY EXPAND_TAC ["ahi"; "ltop"] THEN
      MATCH_MP_TAC(ARITH_RULE
       `x <= (2 EXP (64 * 16) - 1) EXP 2 /\
        y + (2 EXP 1024 - 1) EXP 2 < e
        ==> x + y < e`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EXP_MONO_LE_IMP THEN
        MATCH_MP_TAC(ARITH_RULE `x < e ==> x <= e - 1`) THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; GSYM BIGNUM_FROM_MEMORY_BYTES];
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["h"; "ltop"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Throw away h and digitizations, use h in place of h' now ***)

  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes64 x) s = y`] THEN
  UNDISCH_THEN `h = ahi EXP 2` SUBST1_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`bignum_of_wordlist l = n`] THEN
  ABBREV_TAC `h = ahi EXP 2 + ltop` THEN DISCH_TAC THEN

  (*** Absolute difference computation ***)

  BIGNUM_LDIGITIZE_TAC "xl_" `read (memory :> bytes (x,8 * 16)) s82` THEN
  BIGNUM_LDIGITIZE_TAC "xh_"
   `read (memory :> bytes (word_add x (word 128),8 * 16)) s82` THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [85; 86; 89; 90; 93; 94; 97; 98; 101; 102; 105; 106; 109; 110; 113; 114]
   (83--116) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_SUB_LZERO]) THEN
  SUBGOAL_THEN
   `2 EXP 64 <= val(word_neg (word (bitval carry_s114)):int64) +
                val(word_neg (word (bitval carry_s114)):int64) <=>
    carry_s114`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN BOOL_CASES_TAC `carry_s114:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s114 <=> ahi < alo` (ASSUME_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["ahi"; "alo"] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `1024` THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [118; 120; 123; 125; 128; 130; 133; 135; 138; 140;
    143; 145; 148; 150; 153; 155]
   (117--156) THEN
  SUBGOAL_THEN
   `&(read (memory :> bytes (t,8 * 16)) s156):real = abs(&alo - &ahi)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 16`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC(REAL_ARITH
       `&x < e /\ &y < e ==> abs(&x - &y):real < e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      MAP_EVERY EXPAND_TAC ["ahi"; "alo"] THEN
      CONJ_TAC THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &y < &x then &x - &y else &y - &x`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ahi"; "alo"] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN
    ASM_CASES_TAC `carry_s114:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Discard elementwise assignments and things to do with x ***)

  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes64 x) s = y`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`bignum_of_wordlist l = n`] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `x:int64` o concl))) THEN

  (*** Third and final nested squaring ***)

  ABBREV_TAC `m = read (memory :> bytes (t,8 * 16)) s156` THEN
  ARM_STEPS_TAC BIGNUM_KSQR_32_64_EXEC (157--160) THEN
  BIGNUM_KSQR_32_64_LEMMA_TAC 161 THEN

  (*** All remaining accumulation of sub-results ***)

  BIGNUM_LDIGITIZE_TAC "l_" `read (memory :> bytes (z,8 * 16)) s161` THEN
  BIGNUM_LDIGITIZE_TAC "m_"
   `read (memory :> bytes (word_add t (word 128),8 * 32)) s161` THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 256),8 * 32)) s161` THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_32_64_EXEC
   [164; 165; 169; 170; 174; 175; 179; 180; 184; 185; 189; 190;
    194; 195; 199; 200; 204; 205; 209; 210; 214; 215; 219; 220;
    224; 225; 229; 230; 234; 235; 239; 240; 245; 246; 250; 251;
    255; 256; 260; 261; 265; 266; 270; 271; 275; 276; 280; 281;
    285; 286; 290; 291; 295; 296; 300; 301; 305; 306; 310; 311;
    315; 316; 320; 321; 323; 326; 327; 330; 331; 334; 335; 338;
    339; 342; 343; 346; 347; 350; 351; 354; 355]
   (162--356) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * 64`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * 64 = 64 * 32 + 64 * 32`] THEN
    ASM_SIMP_TAC[EXP_2; LT_MULT2];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  UNDISCH_THEN `2 EXP 1024 * ahi + alo = a` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(e * h + l:real) pow 2 =
    l pow 2 + e pow 2 * h pow 2 +
    e * (h pow 2 + l pow 2 - (l - h) pow 2)`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  UNDISCH_THEN `&m:real = abs(&alo - &ahi)` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `a = b EXP 2 ==> b EXP 2 = a`))) THEN
  UNDISCH_TAC `ahi EXP 2 + ltop = h` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP
   (REAL_ARITH `a + b:real = c ==> a = c - b`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["lbot"; "h"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;
