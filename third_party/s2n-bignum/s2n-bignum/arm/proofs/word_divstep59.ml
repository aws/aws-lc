(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 59 divstep iterations.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "Divstep/idivstep.ml";;

(* ------------------------------------------------------------------------- *)
(* The code.                                                                 *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/generic/word_divstep59.o";;
 ****)

let word_divstep59_mc = define_assert_from_elf "word_divstep59_mc" "arm/generic/word_divstep59.o"
[
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
  0x9b0a19ea;       (* arm_MADD X10 X15 X10 X6 *)
  0x9b0b1deb;       (* arm_MADD X11 X15 X11 X7 *)
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
  0x9b0a89a8;       (* arm_MSUB X8 X13 X10 X2 *)
  0x9b0b8da9;       (* arm_MSUB X9 X13 X11 X3 *)
  0x9b0a91ea;       (* arm_MSUB X10 X15 X10 X4 *)
  0x9b0b95eb;       (* arm_MSUB X11 X15 X11 X5 *)
  0xa9002408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&16))) *)
  0xaa0103e0;       (* arm_MOV X0 X1 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let WORD_DIVSTEP59_EXEC = ARM_MK_EXEC_RULE word_divstep59_mc;;

(* ------------------------------------------------------------------------- *)
(* Some not-very-general lemmas.                                             *)
(* ------------------------------------------------------------------------- *)

let BIT_1_WORD_ISHR = prove
 (`!x:int64. bit 1 x = bit 0 (word_ishr x 1)`,
  CONV_TAC WORD_BLAST);;

let VAL_WORD_AND_2_ISHR = prove
 (`!x:int64. val(word_and x (word 2)) = 0 <=> ~bit 0 (word_ishr x 1)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `2 = 2 EXP 1`] THEN
  REWRITE_TAC[VAL_WORD_AND_POW2; GSYM BIT_1_WORD_ISHR] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let lemma1,lemma2 = (CONJ_PAIR o prove)
 (`(--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 43
    ==> word_ishr (iword(&2 pow 43 * h + l):int64) 43 = iword h) /\
   (--(&2 pow 20) <= h /\ h < &2 pow 20 /\ &0 <= l /\ l < &2 pow 42
    ==> word_ishr (iword(&2 pow 42 * h + l):int64) 42 = iword h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `l:int` THEN ASM_REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_MUL_SYM] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Definitions and lemmas about packed representations, and common tactics.  *)
(* ------------------------------------------------------------------------- *)

let divstep_fvec = define
 `divstep_fvec n (d,f,g) =
    divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$1$2`;;

let divstep_gvec = define
 `divstep_gvec n (d,f,g) =
    divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) -
    &2 pow (41 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$1 -
    &2 pow (62 - n) *
    (divstep_mat n (d,f rem &2 pow 20,g rem &2 pow 20))$2$2`;;

let divstep_dvec = define
 `divstep_dvec n (d,f,g) =
  divstep_d n (d,f rem &2 pow 20,g rem &2 pow 20)`;;

let DIVSTEP_DVEC_BOUND = prove
 (`!n d f g. abs(divstep_dvec n (d,f,g)) <= abs(d) + &2 * &n`,
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_D; GSYM INT_OF_NUM_SUC] THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_FVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_fvec n (d,f,g) rem &2 =
            divstep_f n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_fvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_GVEC_PARITY = prove
 (`!n d f g.
        n <= 20
        ==> divstep_gvec n (d,f,g) rem &2 =
            divstep_g n (d,f rem &2 pow 20,g rem &2 pow 20) rem &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[divstep_gvec; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `n pow 1 divides p /\ n pow 1 divides q
    ==> (x - p * a - q * b:int == x) (mod n)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC);;

let DIVSTEP_DVEC = prove
 (`(!d f g. divstep_dvec 0 (d,f,g) = d) /\
   (!n t. n <= 20
          ==> divstep_dvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then &2 - divstep_dvec n t else &2 + divstep_dvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_dvec; DIVSTEP_D] THEN
  SIMP_TAC[DIVSTEP_GVEC_PARITY]);;

let DIVSTEP_FVEC = prove
 (`(!d f g. divstep_fvec 0 (d,f,g) = f rem &2 pow 20 - &2 pow 41) /\
   (!n t. n <= 20
          ==> divstep_fvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then divstep_gvec n t else divstep_fvec n t)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_fvec; DIVSTEP_F; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[divstep_dvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = (41 - SUC n) + 1`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = (62 - SUC n) + 1`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_GVEC = prove
 (`(!d f g. divstep_gvec 0 (d,f,g) = g rem &2 pow 20 - &2 pow 62) /\
   (!n t. n <= 20
          ==> divstep_gvec (SUC n) t =
              if divstep_dvec n t >= &0 /\ divstep_gvec n t rem &2 = &1
              then (divstep_gvec n t - divstep_fvec n t) div &2
              else (divstep_gvec n t +
                    divstep_gvec n t rem &2 * divstep_fvec n t) div &2)`,
  REWRITE_TAC[FORALL_PAIR_THM; divstep_gvec; DIVSTEP_G; divstep_mat] THEN
  REWRITE_TAC[GSYM divstep_gvec] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONJ_TAC THENL [CONV_TAC INT_ARITH; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `d:int`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIVSTEP_GVEC_PARITY] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[divstep_dvec; divstep_fvec; divstep_gvec] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 41 - n = 1 + (41 - SUC n)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 20 ==> 62 - n = 1 + (62 - SUC n)`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_MUL_ASSOC] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) - (x' - &2 * y' - &2 * z'):int =
    (x - x') + &2 * ((y' + z') - (y + z))`] THEN
  REWRITE_TAC[INT_ARITH
   `(x - &2 * y - &2 * z) + b * (x' - &2 * y' - &2 * z'):int =
    (x + b * x') + &2 * --(b * (y' + z') + (y + z))`] THEN
  SIMP_TAC[INT_DIV_MUL_ADD; INT_OF_NUM_EQ; ARITH_EQ] THEN
  SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_FGVEC_PACK = prove
 (`!d f g. word_or (word_and (iword f) (word 1048575))
                   (word 18446741874686296064):int64 =
           iword(divstep_fvec 0 (d,f,g)) /\
           word_or (word_and (iword g) (word 1048575))
                   (word 13835058055282163712):int64 =
           iword(divstep_gvec 0 (d,f,g))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC;
              DIVSTEP_F; DIVSTEP_G; divstep_mat] THEN
  SIMP_TAC[imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  W(MP_TAC o PART_MATCH (rand o rand) WORD_ADD_OR o lhand o snd) THEN
  (ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  REWRITE_TAC[INT_SUB] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[IWORD_INT_ADD] THEN
  CONV_TAC WORD_REDUCE_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; GSYM(NUM_REDUCE_CONV `2 EXP 20 - 1`)] THEN
  REWRITE_TAC[WORD_IWORD; IWORD_EQ; GSYM INT_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC INT_EQ_IMP_CONG THEN REWRITE_TAC[INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN REWRITE_TAC[VAL_IWORD_CONG] THEN
  REWRITE_TAC[DIMINDEX_64; GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV);;

let IVAL_IWORD_DVEC = prove
 (`!n d f g.
        abs(d) < &2 pow 63 - &2 * &n
        ==> ival(iword(divstep_dvec n (d,f,g)):int64) =
            divstep_dvec n (d,f,g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`n:num`; `d:int`; `f:int`; `g:int`] DIVSTEP_DVEC_BOUND) THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_FVEC_BOUNDS,DIVSTEP_GVEC_BOUNDS = (CONJ_PAIR o prove)
 (`(!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_fvec n (d,f,g) /\
            divstep_fvec n (d,f,g) < &2 pow 62) /\
   (!n d f g.
        n <= 20
        ==> --(&2 pow 62) <= divstep_gvec n (d,f,g) /\
            divstep_gvec n (d,f,g) < &2 pow 62)`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[divstep_dvec] THEN INDUCT_TAC THENL
   [REWRITE_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC; ARITH] THEN
    MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_DIVISION) THEN
    INT_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o MATCH_MP
     (ARITH_RULE `SUC n <= 20 ==> n <= 20`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_SIMP_TAC[DIVSTEP_FVEC; DIVSTEP_GVEC] THEN STRIP_TAC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ;  INT_ARITH `(&0:int) < &2`] THEN
  DISJ_CASES_THEN SUBST1_TAC
   (SPEC `divstep_gvec n (d,f,g)` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

let PACKED_DIVSTEP_TAC n shf s =
  let s' = if mem n shf then s+7 else s+8 in
  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (s--s') THEN
  SUBGOAL_THEN
   (subst [mk_small_numeral(n-1),`n:num`;
           mk_var("s"^string_of_int s',`:armstate`),`s:armstate`]
     `read X1 s = iword(divstep_dvec (SUC n) (d,f,g)) /\
      read X4 s = iword(divstep_fvec (SUC n) (d,f,g)) /\
      read X5 s = iword(divstep_gvec (SUC n) (d,f,g))`)
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB_0; WORD_AND_1_BITVAL] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
    REWRITE_TAC[TAUT `(if p then x else T) <=> p ==> x`] THEN
    REWRITE_TAC[TAUT `(if p then x else F) <=> p /\ x`] THEN
    REWRITE_TAC[INT_SUB_RZERO] THEN
    SIMP_TAC(ARITH::map CONJUNCT2
     [DIVSTEP_DVEC; DIVSTEP_FVEC; DIVSTEP_GVEC]) THEN
    REWRITE_TAC[TAUT `p ==> q <=> ~(~q /\ p)`] THEN
    REWRITE_TAC[COND_SWAP; INT_ARITH `~(x:int < &0) <=> x >= &0`] THEN
    REWRITE_TAC[BIT_LSB_IWORD] THEN
    MP_TAC(ISPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
      IVAL_IWORD_DVEC) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THENL
     [ALL_TAC;
      DISJ_CASES_THEN SUBST1_TAC
       (SPEC(subst [mk_small_numeral(n - 1),`n:num`] `divstep_gvec n (d,f,g)`)
          INT_REM_2_CASES) THEN
      CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC[INT_MUL_LZERO; INT_MUL_LID; INT_ADD_RID]] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[word_ishr] THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_ADD_0; INT_POW_1] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_RULE `word_add x (word_neg y) = word_sub x y`] THEN
    REWRITE_TAC[GSYM IWORD_INT_ADD; GSYM IWORD_INT_SUB] THEN
    MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_FVEC_BOUNDS) THEN
    MP_TAC(SPECL [mk_small_numeral(n-1); `d:int`; `f:int`; `g:int`]
     DIVSTEP_GVEC_BOUNDS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read X5 s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read X4 s = x`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o
     check (can (term_match [] `read X1 s = x`) o concl)) THEN
    RULE_ASSUM_TAC(PURE_REWRITE_RULE [VAL_WORD_AND_2_ISHR]) THEN
    REPLICATE_TAC 3 (DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_SUC_CONV)) THEN
    DISCH_THEN(fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN STRIP_ASSUME_TAC th)];;

let RENAME_DFG_TAC d0 f0 g0 =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`f:int`,f0) THEN
  SPEC_TAC(`g:int`,g0) THEN
  SPEC_TAC(`d:int`,d0) THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read X1 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read X2 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   (`read X3 s = iword a ==> ?a'. a = a'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th));;

let DIVSTEP_MAT_UNPACK_20 = prove
 (`word_sxfrom 20
    (word_subword (word_add (iword(divstep_fvec 20 (d,f,g)):int64)
                            (word 1048576))
                  (21,21)):int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword (divstep_fvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_sxfrom 20
    (word_subword (word_add (iword(divstep_gvec 20 (d,f,g)):int64)
                            (word 1048576))
                  (21,21)):int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword (divstep_gvec 20 (d,f,g))) (word 2199024304128))
             42:int64 =
   iword(--(divstep_mat 20 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  MP_TAC(GENL [`x:int64`; `pos:num`]
   (ISPECL [`x:int64`; `pos:num`; `21`] WORD_SXFROM_SUBWORD_AS_ISHR_SHL)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> SIMP_TAC[th; ARITH]) THEN
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 22 * (l - &2 pow 21 * m - &2 pow 42 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 22 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 21 * m - &2 pow 42 * h + z:int =
    &2 pow 42 * --h + &2 pow 21 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC lemma1 ORELSE MATCH_MP_TAC lemma2) THEN
  MP_TAC(SPECL [`20`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `20`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let DIVSTEP_MAT_UNPACK_19 = prove
 (`word_sxfrom 20
    (word_subword (word_add (iword(divstep_fvec 19 (d,f,g)):int64)
                            (word 1048576))
                  (22,21)):int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$1)) /\
   word_ishr (word_add (iword(divstep_fvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$1$2)) /\
   word_sxfrom 20
    (word_subword (word_add (iword(divstep_gvec 19 (d,f,g)):int64)
                            (word 1048576))
                  (22,21)):int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$1)) /\
   word_ishr (word_add (iword(divstep_gvec 19 (d,f,g)):int64)
                       (word 2199024304128)) 43:int64 =
   iword(--(divstep_mat 19 (d,f rem &2 pow 20,g rem &2 pow 20)$2$2))`,
  MP_TAC(GENL [`x:int64`; `pos:num`]
   (ISPECL [`x:int64`; `pos:num`; `21`] WORD_SXFROM_SUBWORD_AS_ISHR_SHL)) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> SIMP_TAC[th; ARITH]) THEN
  REWRITE_TAC[WORD_RULE `word_add (iword x) (word y) = iword(x + &y)`] THEN
  REWRITE_TAC[WORD_SHL_IWORD] THEN
  REWRITE_TAC[divstep_fvec; divstep_gvec] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH
   `&2 pow 21 * (l - &2 pow 22 * m - &2 pow 43 * h + z):int =
    &2 pow 64 * --h + &2 pow 43 * --m + &2 pow 21 * (l + z)`] THEN
  REWRITE_TAC[INT_ARITH
   `l - &2 pow 22 * m - &2 pow 43 * h + z:int =
    &2 pow 43 * --h + &2 pow 22 * --m + (l + z)`] THEN
  ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; INT_REM_MUL_ADD] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; IWORD_REM_SIZE] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC lemma1 THEN
  MP_TAC(SPECL [`19`; `(d:int,f rem &2 pow 20,g rem &2 pow 20)`]
        DIVSTEP_MAT_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_F_BOUNDS) THEN
  MP_TAC(SPECL [`(&2:int) pow 20`; `19`; `d:int`; `f rem &2 pow 20`;
                `g rem &2 pow 20`] DIVSTEP_G_BOUNDS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`f:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_REM_POS) THEN
  MP_TAC(SPECL [`g:int`; `(&2:int) pow 20`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The overall correctness proof.                                            *)
(* ------------------------------------------------------------------------- *)

let WORD_DIVSTEP59_CORRECT = prove
 (`!m d f g pc.
   nonoverlapping (word pc,0x984) (m,32)
   ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) word_divstep59_mc /\
             read PC s = word pc /\
             C_ARGUMENTS [m; d; f; g] s)
        (\s. read PC s = word(pc + 0x980) /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62 ==>
              C_RETURN s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read (memory :> bytes64(m)) s = iword(M$1$1) /\
              read (memory :> bytes64(word_add m (word 8))) s = iword(M$1$2) /\
              read (memory :> bytes64(word_add m (word 16))) s = iword(M$2$1) /\
              read (memory :> bytes64(word_add m (word 24))) s = iword(M$2$2)))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE [memory :> bytes(m,32)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  X_GEN_TAC `m:int64` THEN
  MAP_EVERY
    (fun t -> GEN_REWRITE_TAC I [FORALL_IVAL_GEN] THEN
              X_GEN_TAC t THEN STRIP_TAC)
    [`d:int`; `f:int`; `g:int`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`]) THEN
  X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  STRIP_TAC THEN

  (*** Globalize the odd(d), odd(f) and |d| < 2^62 assumption ***)

  ASM_CASES_TAC `d rem &2 = &1 /\ f rem &2 = &1 /\ abs(d:int) < &2 pow 62` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    ARM_QUICKSIM_TAC WORD_DIVSTEP59_EXEC [`read X0 s = x`] (1--608)] THEN

  (*** The first packing ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first block of 20 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (9*n-3)) (1--20) THEN

  (*** The unpacking of the first block ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (185--194) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of first update matrix to f and g ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (195--202) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word(0 + val(iword(--x):int64) * val(iword g:int64)):int64 =
    iword(--(x * g))`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr; GSYM IWORD_INT_ADD]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &40`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d0:int` `f0:int` `g0:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN
   `(divstep_f 20 (d0,f0,g0) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d0,f0,g0) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d0:int`; `f0:int`; `g0:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    REWRITE_TAC[GSYM INT_NEG_ADD] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d0,f0,g0) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The second packing ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (203--207) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The second block of 20 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [20] (9*n+199)) (1--20) THEN

  (*** The unpacking of the second block ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (387--396) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_20]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** Application of second update matrix to f and g ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (397--404) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word(0 + val(iword(--x):int64) * val(iword g:int64)):int64 =
    iword(--(x * g))`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ishr; GSYM IWORD_INT_ADD]) THEN

  (*** Renaming new values and checking d bound ***)

  SUBGOAL_THEN
    `abs(divstep_d 20 (d,f,g)) < &2 pow 62 + &80`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`20`; `d:int`; `f:int`; `g:int`] DIVSTEP_D_BOUND) THEN
    UNDISCH_TAC `abs(d:int) < &2 pow 62 + &40` THEN CONV_TAC INT_ARITH;
    ALL_TAC] THEN
  RENAME_DFG_TAC `d1:int` `f1:int` `g1:int` THEN

  (*** Get congruences on the new f and g, and prove oddness ***)

  SUBGOAL_THEN
   `(divstep_f 20 (d1,f1,g1) == --f) (mod (&2 pow 40)) /\
    (divstep_g 20 (d1,f1,g1) == --g) (mod (&2 pow 40))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d1:int`; `f1:int`; `g1:int`; `20`] DIVSTEP_MAT) THEN
    ASM_SIMP_TAC[CART_EQ; FORALL_2; VECTOR_2; imat_vmul;
                 DIMINDEX_2; LAMBDA_BETA; ISUM_2] THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    SIMP_TAC[GSYM IWORD_INT_NEG; GSYM IWORD_INT_ADD; GSYM IWORD_INT_MUL] THEN
    REWRITE_TAC[GSYM INT_NEG_ADD] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[INTEGER_RULE
     `(a:int == --b) (mod p) <=> (b == --a) (mod p)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_DIV THEN
    (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[INT_MUL_RNEG] THEN MATCH_MP_TAC(INTEGER_RULE
     `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:64)` THEN
    REWRITE_TAC[IVAL_IWORD_CONG; GSYM INT_POW_ADD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `f rem &2 = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_REM_2_NEG] THEN
    TRANS_TAC EQ_TRANS `divstep_f 20 (d1,f1,g1) rem &2` THEN
    REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[DIVSTEP_F_ODD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(d:int == f) (mod p) ==> q pow 1 divides p ==> (f == d) (mod q)`)) THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The third and final packing ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (405--409) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_FGVEC_PACK]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `iword(divstep_dvec 0 (d,f,g)):int64` o
    MATCH_MP(MESON[] `read X1 s = a ==> !x. a = x ==> read X1 s = x`)) THEN
  ANTS_TAC THENL [REWRITE_TAC[divstep_dvec; DIVSTEP_D]; DISCH_TAC] THEN

  (*** The first 10 of the third block of 19 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (9*n+401)) (1--10) THEN

  (*** The interspersed matrix multiplication ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (500--507) THEN

  (*** The final 9 of the third block of 19 divsteps ***)

  MAP_EVERY (fun n -> PACKED_DIVSTEP_TAC n [19] (9*n+409)) (11--19) THEN

  (*** The final unpacking is a little different as it's 19 not 20 ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (588--597) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIVSTEP_MAT_UNPACK_19]) THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [DIVSTEP_MAT_MOD; divstep_dvec; DIVSTEP_D_MOD; ARITH_LE; ARITH_LT]) THEN

  (*** The final matrix multiplication and writeback ***)

  ARM_STEPS_TAC WORD_DIVSTEP59_EXEC (598--608) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s608" THEN

  (*** The ending mathematics ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[IWORD_IVAL; IWORD_INT_SUB; IWORD_INT_NEG; IWORD_INT_ADD;
           IWORD_INT_MUL; WORD_ADD; WORD_MUL; ADD_CLAUSES; WORD_VAL] THEN
  REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_MUL; GSYM IWORD_INT_ADD;
              GSYM IWORD_INT_SUB; GSYM IWORD_INT_NEG] THEN
  SUBGOAL_THEN
   `divstep_d 59 (d0,f0,g0) = divstep_d 19 (d,f,g) /\
    divstep_mat 59 (d0,f0,g0) =
    imat_mul (divstep_mat 19 (d,f,g))
             (imat_mul (divstep_mat 20 (d1,f1,g1))
                       (divstep_mat 20 (d0,f0,g0)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[ARITH_RULE `59 = 19 + 40`; DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD];
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[imat_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; ISUM_2] THEN
    INT_ARITH_TAC] THEN
  SUBGOAL_THEN
   `divstep_d 40 (d0,f0,g0) = d /\
    (divstep_f 40 (d0,f0,g0) == f) (mod (&2 pow 19)) /\
    (divstep_g 40 (d0,f0,g0) == g) (mod (&2 pow 19)) /\
    divstep_mat 40 (d0,f0,g0) =
    imat_mul (divstep_mat 20 (d1,f1,g1))
             (divstep_mat 20 (d0,f0,g0))`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `59 = 19 + 40`;
                    DIVSTEP_MAT_ADD; DIVSTEP_DFG_ADD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIVSTEP_D_CONGRUENCE;
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE] THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL
   [`40`; `d1:int`; `divstep_f 20 (d0,f0,g0)`; `divstep_g 20 (d0,f0,g0)`;
    `f1:int`; `g1:int`; `20`]
   DIVSTEP_CONGRUENCE_NEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[DIVSTEP_F_ODD]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `40 = 20 + 20`;
                  DIVSTEP_DFG_ADD; DIVSTEP_MAT_ADD] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> (y == z) (mod p) /\ q divides p
    ==> (x == z) (mod q)`)) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(--x:int == y) (mod p) <=> (x == --y) (mod p)`] THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod p) ==> q divides p ==> (x == y) (mod q)`)) THEN
  SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT]);;

let WORD_DIVSTEP59_SUBROUTINE_CORRECT = prove
 (`!m d f g pc returnaddress.
   nonoverlapping (word pc,0x984) (m,32)
   ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) word_divstep59_mc /\
             read PC s = word pc /\
             read X30 s = returnaddress /\
             C_ARGUMENTS [m; d; f; g] s)
        (\s. read PC s = returnaddress /\
             (ival d rem &2 = &1 /\
              ival f rem &2 = &1 /\
              abs(ival d) < &2 pow 62 ==>
              C_RETURN s = iword(divstep_d 59 (ival d,ival f,ival g)) /\
              let M = divstep_mat 59 (ival d,ival f,ival g) in
              read (memory :> bytes64(m)) s = iword(M$1$1) /\
              read (memory :> bytes64(word_add m (word 8))) s = iword(M$1$2) /\
              read (memory :> bytes64(word_add m (word 16))) s = iword(M$2$1) /\
              read (memory :> bytes64(word_add m (word 24))) s = iword(M$2$2)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(m,32)])`,
  ARM_ADD_RETURN_NOSTACK_TAC WORD_DIVSTEP59_EXEC WORD_DIVSTEP59_CORRECT);;
