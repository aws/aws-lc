(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum. Compared to            *)
(* bignum_emontredc_8n, this function has (1) expensive multiplications      *)
(* properly vectorized with NEON instructions (2) instructions rescheduled   *)
(* using SLOTHY (3) multiplied differences used in ADK cached in a temporary *)
(* buffer. The inner loop is also software-pipelined using the SLOTHY tool.  *)
(* bignum_emontredc_8n_neon also uses the NEON instructions to               *)
(* vectorize multiplications, but other optimizations are not applied.       *)
(*                                                                           *)
(* The proof structure is as follows:                                        *)
(* 1. Prove the 'ensures_n' version of BIGNUM_EMONTREDC_8N_MAINLOOP_CORRECT  *)
(*    using symbolic simulation tactics that are variants of ensures_n.      *)
(*    The resulting lemma is BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N.         *)
(* 2. Prove the equivalence between the outerloop body of scalar machine code*)
(*    and its optimized (vectorized & software-pipelined) version.           *)
(*    The resulting lemma is MAINLOOP_EQUIV.                                 *)
(* 3. Combine BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N and MAINLOOP_EQUIV      *)
(*    to derive the functional correctness of the optimized loop.            *)
(*    The resulting lemma is BIGNUM_EMONTREDC_8N_CDIFF_CORE_CORRECT.         *)
(* 4. Compose BIGNUM_EMONTREDC_8N_CDIFF_CORE_CORRECT with                    *)
(*    correctness of precomputation, BIGNUM_EMONTREDC_8N_CDIFF_PRECALCLOOP,  *)
(*    and eventually derive the full functional correctness of the           *)
(*    subroutine.                                                            *)
(*                                                                           *)
(* Proving the equivalence of the original/optimized main loops is done by   *)
(* (1) Introducing three 'intermediate' programs that are supposed to        *)
(*     be equivalent to the original and fully optimized programs.           *)
(*     This progressively changes the program so that existing equivalence   *)
(*     checking tactics can handle the differences.                          *)
(*     The first intermediate version is the vectorized version of original  *)
(*     bignum_emontredc_8n. The vectorized version is stored at              *)
(*     arm/fastmul/unopt/bignum_emontredc_8n_cdiff_base.S.                   *)
(*     Only the loop body of outerloop of the program is used in this proof. *)
(*     The second intermediate program is reordering the instructions of     *)
(*     inner loop's so that, after software pipelining, instructions running *)
(*     for the next iteration is located at the end of the basic block of    *)
(*     inner loop. The third intermediate program has the rotated inner loop.*)
(*     The final, fully optimized program has the three basic blocks         *)
(*     (outerloop, maddloop, inner_loop_postamble) all rescheduled.          *)
(* (2) Proving the equivalence between basic blocks. The outerloop           *)
(*     consists of three basic blocks                                        *)
(* (3) Composing the equalities. This relies on two different compositions:  *)
(*   - Horizontal composition: If P1 ~= P2 and P2 ~= P3, then P1 ~= P3       *)
(*     (Pn are programs).                                                    *)
(*   - Vertical composition: If P1 ~= P2 and P3 ~= P4, (P1;P3) ~= (P2;P4)    *)
(*     where (.;,) is a sequential composition of two programs.              *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;


let _org_extra_word_CONV_backup = !extra_word_CONV;;


(* ------------------------------------------------------------------------- *)
(*                             The base version.                             *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_from_elf "arm/fastmul/unopt/bignum_emontredc_8n_base.o";;
 ****)

let bignum_emontredc_8n_mc =
  define_assert_from_elf "bignum_emontredc_8n_mc" "arm/fastmul/unopt/bignum_emontredc_8n_base.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf73fb;       (* arm_STP X27 X28 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd342fc00;       (* arm_LSR X0 X0 2 *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xf100040c;       (* arm_SUBS X12 X0 (rvalue (word 1)) *)
  0x54001e23;       (* arm_BCC (word 964) *)
  0xaa1f03fc;       (* arm_MOV X28 XZR *)
  0xd37be980;       (* arm_LSL X0 X12 5 *)
  0xa9404c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x9b037e24;       (* arm_MUL X4 X17 X3 *)
  0x9b087c8c;       (* arm_MUL X12 X4 X8 *)
  0x9b097c8d;       (* arm_MUL X13 X4 X9 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0x9b0b7c8f;       (* arm_MUL X15 X4 X11 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0x9bc87c8c;       (* arm_UMULH X12 X4 X8 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x9bc97c8d;       (* arm_UMULH X13 X4 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0x9bcb7c8f;       (* arm_UMULH X15 X4 X11 *)
  0x9a1f03f6;       (* arm_ADC X22 XZR XZR *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9a0f02d6;       (* arm_ADC X22 X22 X15 *)
  0x9b037e65;       (* arm_MUL X5 X19 X3 *)
  0x9b087cac;       (* arm_MUL X12 X5 X8 *)
  0x9b097cad;       (* arm_MUL X13 X5 X9 *)
  0x9b0a7cae;       (* arm_MUL X14 X5 X10 *)
  0x9b0b7caf;       (* arm_MUL X15 X5 X11 *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0x9bc87cac;       (* arm_UMULH X12 X5 X8 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0x9bc97cad;       (* arm_UMULH X13 X5 X9 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bca7cae;       (* arm_UMULH X14 X5 X10 *)
  0xba0f02d6;       (* arm_ADCS X22 X22 X15 *)
  0x9bcb7caf;       (* arm_UMULH X15 X5 X11 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9a0f02f7;       (* arm_ADC X23 X23 X15 *)
  0x9b037e86;       (* arm_MUL X6 X20 X3 *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9b097ccd;       (* arm_MUL X13 X6 X9 *)
  0x9b0a7cce;       (* arm_MUL X14 X6 X10 *)
  0x9b0b7ccf;       (* arm_MUL X15 X6 X11 *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0x9bc87ccc;       (* arm_UMULH X12 X6 X8 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0x9bc97ccd;       (* arm_UMULH X13 X6 X9 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0f02f7;       (* arm_ADCS X23 X23 X15 *)
  0x9bcb7ccf;       (* arm_UMULH X15 X6 X11 *)
  0x9a1f03f8;       (* arm_ADC X24 XZR XZR *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9a0f0318;       (* arm_ADC X24 X24 X15 *)
  0x9b037ea7;       (* arm_MUL X7 X21 X3 *)
  0x9b087cec;       (* arm_MUL X12 X7 X8 *)
  0x9b097ced;       (* arm_MUL X13 X7 X9 *)
  0x9b0a7cee;       (* arm_MUL X14 X7 X10 *)
  0x9b0b7cef;       (* arm_MUL X15 X7 X11 *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0x9bc87cec;       (* arm_UMULH X12 X7 X8 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bc97ced;       (* arm_UMULH X13 X7 X9 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bca7cee;       (* arm_UMULH X14 X7 X10 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0x9bcb7cef;       (* arm_UMULH X15 X7 X11 *)
  0x9a1f03f9;       (* arm_ADC X25 XZR XZR *)
  0xab0c02cc;       (* arm_ADDS X12 X22 X12 *)
  0xba0d02ed;       (* arm_ADCS X13 X23 X13 *)
  0xba0e030e;       (* arm_ADCS X14 X24 X14 *)
  0x9a0f032f;       (* arm_ADC X15 X25 X15 *)
  0xa9001424;       (* arm_STP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xa9011c26;       (* arm_STP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xaa0003fb;       (* arm_MOV X27 X0 *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x9b087c91;       (* arm_MUL X17 X4 X8 *)
  0x9b097cb6;       (* arm_MUL X22 X5 X9 *)
  0x9b0a7cd7;       (* arm_MUL X23 X6 X10 *)
  0x9b0b7cf8;       (* arm_MUL X24 X7 X11 *)
  0x9bc87c90;       (* arm_UMULH X16 X4 X8 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9bc97cb0;       (* arm_UMULH X16 X5 X9 *)
  0xba1002f7;       (* arm_ADCS X23 X23 X16 *)
  0x9bca7cd0;       (* arm_UMULH X16 X6 X10 *)
  0xba100318;       (* arm_ADCS X24 X24 X16 *)
  0x9bcb7cf0;       (* arm_UMULH X16 X7 X11 *)
  0x9a1f0219;       (* arm_ADC X25 X16 XZR *)
  0xa9405434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&0))) *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0x9a1f03f0;       (* arm_ADC X16 XZR XZR *)
  0xab1102d3;       (* arm_ADDS X19 X22 X17 *)
  0xba1602f6;       (* arm_ADCS X22 X23 X22 *)
  0xba170317;       (* arm_ADCS X23 X24 X23 *)
  0xba180338;       (* arm_ADCS X24 X25 X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab1102d4;       (* arm_ADDS X20 X22 X17 *)
  0xba1302f5;       (* arm_ADCS X21 X23 X19 *)
  0xba160316;       (* arm_ADCS X22 X24 X22 *)
  0xba170337;       (* arm_ADCS X23 X25 X23 *)
  0xba1803f8;       (* arm_ADCS X24 XZR X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xba1002d6;       (* arm_ADCS X22 X22 X16 *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0xba1f0318;       (* arm_ADCS X24 X24 XZR *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xeb0700cf;       (* arm_SUBS X15 X6 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb0a016d;       (* arm_SUBS X13 X11 X10 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d0318;       (* arm_ADCS X24 X24 X13 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb05008f;       (* arm_SUBS X15 X4 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08012d;       (* arm_SUBS X13 X9 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb0700af;       (* arm_SUBS X15 X5 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb09016d;       (* arm_SUBS X13 X11 X9 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02f7;       (* arm_ADCS X23 X23 X13 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb06008f;       (* arm_SUBS X15 X4 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08014d;       (* arm_SUBS X13 X10 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb07008f;       (* arm_SUBS X15 X4 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08016d;       (* arm_SUBS X13 X11 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb09014d;       (* arm_SUBS X13 X10 X9 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02ed;       (* arm_ADCS X13 X23 X12 *)
  0xba0c030e;       (* arm_ADCS X14 X24 X12 *)
  0x9a0c032f;       (* arm_ADC X15 X25 X12 *)
  0xaa1603ec;       (* arm_MOV X12 X22 *)
  0xa9004c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0xa9015434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xf100837b;       (* arm_SUBS X27 X27 (rvalue (word 32)) *)
  0x54ffee41;       (* arm_BNE (word 2096584) *)
  0xa9424c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&32))) *)
  0xa9435434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xab1c039f;       (* arm_CMN X28 X28 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xda9f33fc;       (* arm_CSETM X28 Condition_CS *)
  0xa9024c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&32))) *)
  0xa9035434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xcb000021;       (* arm_SUB X1 X1 X0 *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xd100075a;       (* arm_SUB X26 X26 (rvalue (word 1)) *)
  0xb5ffe29a;       (* arm_CBNZ X26 (word 2096208) *)
  0xcb1c03e0;       (* arm_NEG X0 X28 *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EMONTREDC_8N_EXEC = ARM_MK_EXEC_RULE bignum_emontredc_8n_mc;;

let bignum_emontredc_8n_labels = [
  (* BIGNUM_EMONTREDC_8N_MAINLOOP_CORRECT's begin *)
  ("main", (0x24, new_definition `bignum_emontredc_8n_label_main = 0x24`));

  ("outerloop", (0x2c, new_definition `bignum_emontredc_8n_label_outerloop = 0x2c`));
  ("maddloop", (0x168, new_definition `bignum_emontredc_8n_label_maddloop = 0x168`));
  ("madddone", (0x3a4, new_definition `bignum_emontredc_8n_label_madddone = 0x3a4`));
  ("outerloop_end", (0x3dc, new_definition `bignum_emontredc_8n_label_outerloop_end = 0x3dc`));

  (* BIGNUM_EMONTREDC_8N_MAINLOOP_CORRECT's end *)
  ("main_end", (0x3e4, new_definition `bignum_emontredc_8n_label_main_end = 0x3e4`))
];;


(* ------------------------------------------------------------------------- *)
(*                          The optimized version.                           *)
(* ------------------------------------------------------------------------- *)

let bignum_emontredc_8n_cdiff_mc =
  define_from_elf "bignum_emontredc_8n_cdiff_mc"
    "arm/fastmul/bignum_emontredc_8n_cdiff.o";;

let BIGNUM_EMONTREDC_8N_CDIFF_EXEC =
    ARM_MK_EXEC_RULE bignum_emontredc_8n_cdiff_mc;;

let bignum_emontredc_8n_cdiff_labels = [
  (* Corresponding to BIGNUM_EMONTREDC_8N_MAINLOOP_CORRECT's begin.
     Also the beginning point of precomputation loop *)
  ("main", (0x44, new_definition `slothy_main = 0x44`));
  ("precomp_loop_end", (0xd0, new_definition `slothy_precomp_loop_end = 0xd0`));

  ("outerloop", (0xe4, new_definition `slothy_outerloop = 0xe4`));
  ("maddloop_neon", (0x434, new_definition `slothy_maddloop_neon = 0x434`));
  ("inner_loop_postamble",
    (0x690, new_definition `slothy_inner_loop_postamble = 0x690`));
  ("outerloop_end",
    (0x878, new_definition `slothy_outerloop_end = 0x878`));

  (* Corresponding to BIGNUM_EMONTREDC_8N_MAINLOOP_CORRECT's end *)
  ("main_end",
    (0x880, new_definition `slothy_main_end = 0x880`));
];;


let update_key_list (k:'a) (v:'b list) (l:('a*'b list) list) =
  let x,y = partition (fun p,q -> p = k) l in
  if x = [] then (k,v)::l
  else if length x > 1 then failwith "multiple keys" else
  let _,v2 = hd x in (k,v@v2)::l;;

let DESTRUCT_EXISTS_ASSUMS_TAC =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let cth = concl th in
    if is_exists cth then MP_TAC th THEN STRIP_TAC
    else NO_TAC));;

let FIND_ABBREV_THEN (varname:string) (ttac:thm_tactic): tactic =
  fun (asl,g) ->
    let _,the_th = find (fun (_,th) -> let c = concl th in
      is_eq c && is_var (rhs c) && name_of (rhs c) = varname)
      asl in
    ttac the_th (asl,g);;

let REMOVE_ABBREV_THEN (varname:string) (ttac:thm_tactic): tactic =
  fun (asl,g) ->
    let asl1,asl2 = partition (fun (_,th) -> let c = concl th in
      is_eq c && is_var (rhs c) && name_of (rhs c) = varname)
      asl in
    let (_,the_th),asl2 = hd asl1,(asl2 @ tl asl1) in
    ttac the_th (asl2,g);;

let WORD_ADD_SUB = WORD_RULE
    `word_add (word_sub x (word y)) (word z):(N)word = word_add x (word_sub (word z) (word y))`;;

let VAL_WORD_EQ_ZERO = prove (`!i. i < 2 EXP 64 ==> (val (word i:int64) = 0 <=> i = 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `i MOD 2 EXP 64 = i` (fun thm -> REWRITE_TAC[thm]) THEN IMP_REWRITE_TAC[MOD_LT]);;

let READ_MEMORY_BYTES_0 = prove(`forall z s.
    read (memory :> bytes (z,0)) s = 0`,
  TARGET_REWRITE_TAC[ARITH_RULE`0 = 8*0`;GSYM BIGNUM_FROM_MEMORY_BYTES]
      BIGNUM_FROM_MEMORY_TRIVIAL);;

let BIGNUM_FROM_MEMORY_EQ_SPLIT = prove(
  `!(z:int64) (n:num) (idx:num) (s:armstate) (s2:armstate).
      idx <= n ==>
      ((exists a. bignum_from_memory (z,n) s = a /\ bignum_from_memory (z,n) s2 = a)
        <=>
       ((exists a1. bignum_from_memory (z,idx) s = a1 /\ bignum_from_memory (z,idx) s2 = a1) /\
        (exists a2. bignum_from_memory (word_add z (word (8*idx)),n - idx) s = a2 /\
                     bignum_from_memory (word_add z (word (8*idx)),n - idx) s2 = a2)))`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL [
    STRIP_TAC THEN CONJ_TAC THENL [
      SUBGOAL_THEN `MIN n idx = idx` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
      ASM_MESON_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY];

      ASM_MESON_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY]
    ];

    STRIP_TAC THEN
    SUBGOAL_THEN `n = idx + (n - idx)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_MESON_TAC[BIGNUM_FROM_MEMORY_SPLIT]
  ]);;

let BIGNUM_FROM_MEMORY_EQ_SPLIT3 = prove(
  `!(z:int64) (n:num) (idx:num) (idx2:num) (s:armstate) (s2:armstate).
      idx <= idx2 /\ idx2 <= n ==>
      ((exists a. bignum_from_memory (z,n) s = a /\ bignum_from_memory (z,n) s2 = a)
        <=>
       ((exists a1. bignum_from_memory (z,idx) s = a1 /\ bignum_from_memory (z,idx) s2 = a1) /\
        (exists a2. bignum_from_memory (word_add z (word (8*idx)), (idx2 - idx)) s = a2 /\
                     bignum_from_memory (word_add z (word (8*idx)), (idx2 - idx)) s2 = a2) /\
        (exists a3. bignum_from_memory (word_add z (word (8*idx2)), (n - idx2)) s = a3 /\
                     bignum_from_memory (word_add z (word (8*idx2)), (n - idx2)) s2 = a3)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `idx <= n` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP BIGNUM_FROM_MEMORY_EQ_SPLIT (ASSUME `idx <= n`)] THEN
  MATCH_MP_TAC (TAUT `(P <=> Q) ==> ((R /\ P) <=> (R /\ Q))`) THEN
  SUBGOAL_THEN `idx2 - idx <= n - idx` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP BIGNUM_FROM_MEMORY_EQ_SPLIT (ASSUME `idx2 - idx <= n - idx`)] THEN
  MATCH_MP_TAC (TAUT `(P <=> Q) ==> ((R /\ P) <=> (R /\ Q))`) THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  SUBGOAL_THEN `n - idx - (idx2 - idx) = n - idx2` SUBST_ALL_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `8 * idx + 8 * (idx2 - idx) = 8 * idx2` SUBST_ALL_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[]);;


(*** Lemma to justify zeros in the Montgomery steps
      (copied from bignum_emontredc_8n.ml) ***)

let montgomery_lemma = prove
 (`!w n.
    (n * w + 1 == 0) (mod (2 EXP 64))
    ==> !h l x.
            &2 pow 64 * &h + &l:real =
            &(val (word(x * w):int64)) *
            &(val(word(bigdigit n 0):int64))
            ==> !h' l'. &2 pow 64 * &h' + &(val l'):real = &x + &l
                        ==> val(l':int64) = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; GSYM LOWDIGITS_1; lowdigits] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_MOD_REFL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`)) THEN
  REWRITE_TAC[MOD_MULT_ADD; DIMINDEX_128; DIMINDEX_64; MULT_CLAUSES] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 64 = 64 /\ MIN 128 64 = 64`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG; GSYM DIVIDES_MOD] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`2 EXP 64`,`p:num`) THEN
  CONV_TAC NUMBER_RULE);;

(*** Lemmas for the case splits in the ADK blocks
      (copied from bignum_emontredc_8n.ml)  ***)

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



(* ========================================================================= *)
(*          Prove the ensures_n version of the mainloop correctness.         *)
(* ========================================================================= *)

(* A few ensures_n variants of tactics...
   Q: Having this ensures_n variant of symbolic simulation tactics introduces
      a lot of redundancy... One possible solution would be, to update
      existing symbolic simulation tactics to detect whether the goal is
      using ensures or ensures_n, and properly apply corresponding lemmas. *)

let ENSURES_N_BIGNUM_TERMRANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND]) in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_N_TRIVIAL] THEN NO_TAC)
     (SPECL [k; m] pth);;


let ENSURES_N_CONSTANT_PRECONDITION = prove
 (`!step p (q:A->bool) r n.
        ensures_n step (\s. p) q r n <=> p ==> ensures_n step (\s. T) q r n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[ENSURES_N_TRIVIAL]);;

let ENSURES_N_CONSTANT_PRECONDITION_CONJUNCTS = prove
 (`(!step p p' (q:A->bool) r n.
        ensures_n step (\s. p /\ p' s) q r n <=>
        p ==> ensures_n step (\s. p' s) q r n) /\
   (!step p p' (q:A->bool) r n.
        ensures_n step (\s. p' s /\ p) q r n <=>
        p ==> ensures_n step (\s. p' s) q r n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[ENSURES_N_TRIVIAL]);;

let (ENSURES_N_GLOBALIZE_PRECONDITION_TAC:tactic) =
  let tac1 = GEN_REWRITE_TAC I [ENSURES_N_CONSTANT_PRECONDITION] THEN
             DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
  and tac2 = GEN_REWRITE_TAC I
              [CONJUNCT2 ENSURES_N_CONSTANT_PRECONDITION_CONJUNCTS] THEN
             DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) in
  fun (_,w as gl) ->
    let mom,nstep = dest_comb w in
    let pap,fra = dest_comb mom in
    let enp,pos = dest_comb pap in
    let ens,pre = dest_comb enp in
    let sv,pbod = dest_abs pre in
    let cjs1,cjs2 = partition (free_in sv) (conjuncts pbod) in
    if cjs1 = [] then tac1 gl else if cjs2 = [] then ALL_TAC gl else
    let th1 = CONJ_ACI_RULE
     (mk_eq(pbod,mk_conj(list_mk_conj cjs1,list_mk_conj cjs2))) in
    let th2 = AP_THM (AP_THM (AP_THM (AP_TERM ens (ABS sv th1)) pos) fra) nstep in
    (CONV_TAC(K th2) THEN tac2) gl;;

let ARM_N_SIM_TAC execth stnames =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_N_INIT_TAC "s0" THEN
  ARM_N_STEPS_TAC execth stnames "" [] None THEN
  ENSURES_N_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[];;

let ENSURES_N_FORGET_COMPONENTS_TAC =
  let lemma = prove
   (`!p' q'. ensures_n step p' q' c n /\
             (!s. p s ==> p' s) /\ (!s s'. p s /\ q' s' /\ c s s' ==> q s')
             ==> ensures_n step p q c n`,
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_N_SUBLEMMA_THM THEN
    ASM_REWRITE_TAC[SUBSUMED_REFL]) in
  fun ctm ->
    let rec funch tm =
      match tm with
        Comb(Const("read",_),c) -> mem c ctm
      | Comb(s,t) -> funch s && funch t
      | Abs(x,t) -> funch t
      | Const("bytes_loaded",_) -> false
      | Const("aligned_bytes_loaded",_) -> false
      | _ -> true in
    fun (_,w as gl) ->
      let mom,nsteps = dest_comb w in
      let pap,fra = dest_comb mom in
      let enp,pos = dest_comb pap in
      let ens,pre = dest_comb enp in
      let sv,pbod = dest_abs pre
      and tv,qbod = dest_abs pos in
      let pcjs = filter (not o funch) (conjuncts pbod)
      and qcjs = filter (not o funch) (conjuncts qbod) in
     (MATCH_MP_TAC lemma THEN
      EXISTS_TAC(mk_abs(sv,list_mk_conj pcjs)) THEN
      EXISTS_TAC(mk_abs(tv,list_mk_conj qcjs)) THEN
      CONJ_TAC THENL
       [ALL_TAC;
        CONJ_TAC THENL
         [REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[] THEN NO_TAC;
          REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
          REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2
           (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC)) THEN
          REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
          REWRITE_TAC[GSYM SEQ_ASSOC] THEN
          REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
          REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
          ASSUMPTION_STATE_UPDATE_TAC THEN ASM_REWRITE_TAC[] THEN
          NO_TAC]]) gl;;



let ARM_N_VERBOSE_STEP_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  ARM_N_STEP_TAC (exth1,exth2) [] sname None None g;;

let ARM_N_SINGLE_STEP_TAC th s =
  time (ARM_N_VERBOSE_STEP_TAC th s) THEN
  DISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

let ARM_N_XACCSTEP_TAC th excs aflag s =
  ARM_N_SINGLE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATEX_ARITH_TAC excs s THEN CLARIFY_TAC)
   else ALL_TAC);;

let ARM_N_XACCSTEPS_TAC th excs anums snums =
  MAP_EVERY
   (fun n -> ARM_N_XACCSTEP_TAC th excs (mem n anums) ("s"^string_of_int n))
   snums;;

let ARM_N_ACCSTEPS_TAC th anums snums =
  ARM_N_XACCSTEPS_TAC th [`SP`] anums snums;;


(* BIGNUM_EMONTREDC_8N_MAINLOOP_CORRECT, but its ensures_n version. The proof
   is copied from BIGNUM_EMONTREDC_8N_MAINLOOP_CORRECT and properly updated
   to use the tactics of ensures_n version and additionally reason about
   the number of steps. *)

let BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N = prove(
  `forall k k4 z m w a n pc.
      w < 2 EXP 64 /\ ~(k4 = 0) /\ ~(k4 = 1) /\ 4 * k4 = k /\
      nonoverlapping_modulo (2 EXP 64) (val z,8 * 2 * k) (pc,1020) /\
      nonoverlapping_modulo (2 EXP 64) (val z,8 * 2 * k) (val m,8 * k) /\
      a < 2 EXP (64 * 2 * k) /\
      n < 2 EXP (64 * k)
      ==> ensures_n arm
        (\s.
              aligned_bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
              read PC s = word (pc + 36) /\
              read X12 s = word (k4 - 1) /\
              read X26 s = word k4 /\
              read X1 s = z /\
              read X2 s = m /\
              read X3 s = word w /\
              bignum_from_memory (z,2 * k) s = a /\
              bignum_from_memory (m,k) s = n)
        (\s.
              aligned_bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
              read PC s = word (pc + 996) /\
              ((n * w + 1 == 0) (mod (2 EXP 64))
              ==> n * bignum_from_memory (z,k) s + a =
                  2 EXP (64 * k) *
                  (2 EXP (64 * k) * val (read X0 s) +
                    bignum_from_memory (word_add z (word (8 * k)),k) s)))
        (MAYCHANGE
          [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16;
          X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
          MAYCHANGE [memory :> bytes (z,8 * 2 * k)] ,,
          MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])
        (\s. 4 + (k4 * (93 + (k4 - 1) * 143) + (k4 - 1)))`,

  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `val (word w:int64) = w` ASSUME_TAC THENL [
    IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN NO_TAC; ALL_TAC ] THEN

  (*** Get a basic bound on k and k4 from the nonoverlapping assumptions ***)

  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64)
     (val(z:int64),8 * 2 * k) (val(m:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `k4 < 2 EXP 58` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Main loop invariant for "outerloop" ***)

  ENSURES_N_WHILE_UP_TAC `k4:num` `pc + 0x2c` `pc + 0x3dc`
   `\i s. (read X2 s = m /\
           read X3 s = word w /\
           bignum_from_memory (m,k) s = n /\
           read X0 s = word(32 * (k4 - 1)) /\
           read X26 s = word(k4 - i) /\
           read X1 s = word_add z (word(8 * 4 * i)) /\
           bignum_from_memory(word_add z (word(8 * (k + 4 * i))),
                              2 * k - (k + 4 * i)) s =
           highdigits a (k + 4 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                (2 EXP (64 * k) * val(word_neg(read X28 s)) +
                 bignum_from_memory(word_add z (word(8 * 4 * i)),k) s) =
               bignum_from_memory(z,4 * i) s * n + lowdigits a (k + 4 * i)))`
   `\(i:num). 93 + (k4 - 1) * 143` `2` `1` `2`  THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_N_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    ARM_N_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) "" [] None THEN
    ENSURES_N_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; WORD_NEG_0] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; ADD_CLAUSES; EXP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC WORD_RULE;

    ALL_TAC; (*** This is the main loop invariant: save for later ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_N_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1] THEN
    COND_CASES_TAC THENL [REFL_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MP_TAC THEN
    MP_TAC (ASSUME `val (word i:int64) = i`) THEN
    REWRITE_TAC[VAL_WORD_EQ_EQ;DIMINDEX_64] THEN
    IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC;

    ENSURES_N_GHOST_INTRO_TAC `ncout:int64` `read X28` THEN
    ARM_N_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2; WORD_SUB_LZERO] THEN
    REWRITE_TAC[MULT_SYM];

    (* num steps *)
    REWRITE_TAC[NSUM_CONST_NUMSEG;SUB_0] THEN
    IMP_REWRITE_TAC[SUB_ADD] THEN
    SIMPLE_ARITH_TAC] THEN

  (*** Start on the main outer loop invariant, rebase at z + 32 * i = rsi ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * (k + 4 * i))) =
    word_add (word_add z (word(8 * 4 * i))) (word(8 * k))`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 4 * (i + 1))) =
    word_add (word_add z (word(8 * 4 * i))) (word(8 * 4))`] THEN
  ABBREV_TAC `z':int64 = word_add z (word (8 * 4 * i))` THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word (8 * 4))) (word (8 * k)) =
    word_add z (word (8 * (k + 4)))`] THEN
  REWRITE_TAC[ARITH_RULE `2 * k - (k  + i) = k - i`] THEN

  ENSURES_N_GHOST_INTRO_TAC `cout:num` `\s. val (word_neg (read X28 s))` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[WORD_RULE `word_neg x = y <=> x = word_neg y`] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory(z',k) s =
        lowdigits (bignum_from_memory(z',k+4) s) k`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[ARITH_RULE `MIN (k + 4) k = k`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (z,4 * (i + 1)) s =
        2 EXP (64 * 4 * i) * bignum_from_memory(z',4) s +
        bignum_from_memory(z,4 * i) s`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (word_add z' (word (8 * k)),k - 4 * i) s =
        highdigits a (k + 4 * i) <=>
        highdigits (bignum_from_memory(z',k+4) s) k =
        lowdigits (highdigits a (k + 4 * i)) 4 /\
        bignum_from_memory
         (word_add z' (word (8 * (k + 4))),k - 4 * (i + 1)) s =
        highdigits a (k + 4 * (i + 1))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB2] THEN
    SUBGOAL_THEN
     `k - 4 * i = 4 + (k - 4 * (i + 1))`
    SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    MP_TAC(SPECL [`highdigits a (k + 4 * i)`; `4`]
     (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM th]) THEN
    SIMP_TAC[LEXICOGRAPHIC_EQ; BIGNUM_FROM_MEMORY_BOUND; LOWDIGITS_BOUND] THEN
    REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN
    REWRITE_TAC[ARITH_RULE `(k + 4 * i) + 4 = k + 4 * (i + 1)`] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add z (word (8 * k))) (word (8 * 4)) =
      word_add z (word (8 * (k + 4)))`] THEN
    MATCH_ACCEPT_TAC CONJ_SYM;
    ALL_TAC] THEN

  ENSURES_N_GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z',k+4)` THEN
  ENSURES_N_BIGNUM_TERMRANGE_TAC `k + 4` `z1:num` THEN
  ENSURES_N_GHOST_INTRO_TAC `q1:num` `bignum_from_memory(z,4 * i)` THEN
  ENSURES_N_BIGNUM_TERMRANGE_TAC `4 * i` `q1:num` THEN
  ENSURES_N_GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_N_SEQUENCE_TAC `pc + 0x3dc`
   `\s. read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = word (k4 - (i + 1)) /\
        read X1 s = word_add z' (word (8 * 4)) /\
        bignum_from_memory (word_add z' (word (8 * (k + 4))),k - 4 * (i + 1))
        s =
        highdigits a (k + 4 * (i + 1)) /\
        bignum_from_memory (z,4 * i) s = q1 /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             (2 EXP (64 * k) *
              val(word_neg(read X28 s)) +
              bignum_from_memory(word_add z' (word(8 * 4)),k) s) =
             bignum_from_memory(z',4) s * n + 2 EXP (64 * k) * cout + z1)`
   `93 + (k4 - 1) * 143` `0` THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;

    ARM_N_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [] THEN
    DISCH_THEN(fun th ->
     REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th))) THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE
     `64 * 4 * (i + 1) = 64 * 4 * i + 64 * 4`] THEN
    ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; EQ_ADD_LCANCEL] THEN
    MP_TAC(SPECL [`z1:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `ee * e * c + ee * (e * h + l):num =
      (ee * (e * c + l)) + (ee * e) * h`] THEN
    REWRITE_TAC[GSYM EXP_ADD; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[lowdigits; highdigits; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `64 * 4 * i + 64 * k = 64 * k + 64 * 4 * i`] THEN
    SPEC_TAC(`64 * k + 64 * 4 * i`,`j:num`) THEN
    REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC;

    (* Steps *)
    ARITH_TAC] THEN

  (*** Now discard no-longer-relevant things outside the window ***)

  MATCH_MP_TAC ENSURES_N_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
     X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
    MAYCHANGE [memory :> bytes(z',8 * (k + 4))] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z':int64,8 * (k + 4)) (z,8 * 4 * i) /\
    nonoverlapping (z':int64,8 * (k + 4)) (word pc,0x3fc) /\
    nonoverlapping (z':int64,8 * (k + 4)) (m,8 * k) /\
    nonoverlapping (z':int64,8 * (k + 4))
     (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1)))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_N_FORGET_COMPONENTS_TAC
   [`memory :> bytes (z,8 * 4 * i)`;
    `memory :>
     bytes (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1)))`] THEN

  (*** Get the cout < 2 before we forget too much context ***)

  SUBGOAL_THEN `(n * w + 1 == 0) (mod (2 EXP 64)) ==> cout < 2`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `2 EXP (64 * 4 * i) * (2 EXP (64 * k) * cout + lowdigits z1 k) <
      2 EXP (64 * 4 * i) * 2 EXP (64 * k) * 2`
    MP_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC (ARITH_RULE
       `x < d * e /\ y < e * d ==> x + y < d * e * 2`) THEN
      ASM_SIMP_TAC[LT_MULT2] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_BOUND; GSYM LEFT_ADD_DISTRIB];
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `d * (e * c + l):num < x ==> d * e * c < x`)) THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN

  (*** Now forget more things; back up a few steps and forget i as well ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `z:int64`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `q1:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `r1:num`) o concl)) THEN

  ENSURES_N_SEQUENCE_TAC `pc + 0x3cc`
   `\s. read X2 s = word_add m (word(32 * (k4 - 1))) /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = word (k4 - i) /\
        read X1 s = word_add z' (word(32 * (k4 - 1))) /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             (2 EXP (64 * k) * val(word_neg (read X28 s)) +
              bignum_from_memory(word_add z' (word(8 * 4)),k) s) =
              bignum_from_memory(z',4) s * n +
              2 EXP (64 * k) * cout + z1)` `89 + (k4 - 1) * 143` `4` THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ARM_N_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--4) THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
      CONV_TAC WORD_RULE];
    (* num steps *)ARITH_TAC] THEN

  ABBREV_TAC `wouter:int64 = word (k4 - i)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `i:num`) o concl)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  MAP_EVERY SPEC_TAC
    [(`z1:num`,`a:num`); (`z':int64`,`z:int64`)] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `4 <= k` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `4 * k4 = k`)) THEN UNDISCH_TAC `~(k4 = 0)` THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The initial Montgomery 4-block ***)

  ENSURES_N_SEQUENCE_TAC `pc + 0x164`
   `\s. read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = wouter /\
        read X1 s = z /\
        read X28 s = word_neg(word cout) /\
        bignum_from_memory(word_add z (word (8 * 4)),k) s =
        highdigits a 4 /\
        read X4 s = word(bigdigit (bignum_from_memory(z,4) s) 0) /\
        read X5 s = word(bigdigit (bignum_from_memory(z,4) s) 1) /\
        read X6 s = word(bigdigit (bignum_from_memory(z,4) s) 2) /\
        read X7 s = word(bigdigit (bignum_from_memory(z,4) s) 3) /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] =
             bignum_from_memory(z,4) s * lowdigits n 4 + lowdigits a 4)`
    `78` `11 + (k4 - 1) * 143` THEN
  REPEAT CONJ_TAC THENL
  [ REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_N_INIT_TAC "s0" THEN
    SUBGOAL_THEN
      `highdigits (bignum_from_memory(z,k+4) s0) 4 = highdigits a 4`
    MP_TAC THENL
      [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[NUM_REDUCE_CONV `8 * 4`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
      `(!i. i < 4
            ==> bigdigit (bignum_from_memory(z,k+4) s0) i = bigdigit a i) /\
      (!i. i < 4
            ==> bigdigit (bignum_from_memory(m,k) s0) i = bigdigit n i)`
    MP_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
      [BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `!i. i < 4 ==> i < k /\ i < k + 4` MP_TAC THENL
      [UNDISCH_TAC `4 <= k` THEN ARITH_TAC; SIMP_TAC[]] THEN
    DISCH_THEN(K ALL_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV EXPAND_CASES_CONV)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
    STRIP_TAC THEN
    ARM_N_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--78) (1--78) THEN
    ENSURES_N_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_LT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_REWRITE_TAC[WORD_VAL; WORD_ADD_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RAND_CONV(TOP_DEPTH_CONV num_CONV) `lowdigits x 4`] THEN
    REWRITE_TAC[ADD1; LOWDIGITS_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP montgomery_lemma) THEN
    DISCH_THEN(fun ith ->
      EVERY_ASSUM(fun th ->
        try let th' = MATCH_MP ith th in
            EVERY_ASSUM(fun th'' ->
              try MP_TAC(MATCH_MP th' th'')
              with Failure _ -> ALL_TAC)
        with Failure _ -> ALL_TAC)) THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
      (MP_TAC o MATCH_MP (MESON[REAL_ADD_LID]
        `n = 0 ==> !x:real. &n + x = x`))) THEN
    REPEAT(DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;

    ALL_TAC;

    (* num steps *) ARITH_TAC] THEN

  (*** Shared tail to handle the final carry chaining in k4 = 1 too ***)

  ENSURES_N_GHOST_INTRO_TAC `q:num` `bignum_from_memory(z,4)` THEN
  ENSURES_N_BIGNUM_TERMRANGE_TAC `4` `q:num` THEN

  (*** Set up a version with the whole z buffer ***)

  ENSURES_N_SEQUENCE_TAC `pc + 0x3a4`
   `\s. read X1 s = word_add z (word (32 * (k4 - 1))) /\
        read X2 s = word_add m (word (32 * (k4 - 1))) /\
        read X3 s = word w /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = wouter /\
        read X28 s = word_neg(word cout) /\
        bignum_from_memory (word_add z (word (8 * k)),4) s =
        highdigits a k /\
        bignum_from_memory (z,4) s = q /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * k) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] +
             bignum_from_memory(z,k) s =
             q * n + lowdigits a k + q)`
    `1 + (k4 - 1) * 143` `10` THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;

    ENSURES_N_GHOST_INTRO_TAC `g8:int64` `read X12` THEN
    ENSURES_N_GHOST_INTRO_TAC `g9:int64` `read X13` THEN
    ENSURES_N_GHOST_INTRO_TAC `g10:int64` `read X14` THEN
    ENSURES_N_GHOST_INTRO_TAC `g11:int64` `read X15` THEN

    (*** Rebase once again to avoid indexing messiness a bit ***)

    ABBREV_TAC `z':int64 = word_add z (word (8 * k))` THEN
    MATCH_MP_TAC ENSURES_N_FRAME_SUBSUMED THEN EXISTS_TAC
      `MAYCHANGE
        [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
        X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [memory :> bytes (z',8 * 4)] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
      [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      MAP_EVERY EXPAND_TAC ["z'"] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
      `nonoverlapping (z':int64,8 * 4) (word pc,1020) /\
      nonoverlapping (z':int64,8 * 4) (m,8 * k) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * 4) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * k)`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
      [MAP_EVERY EXPAND_TAC ["z'"] THEN
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      STRIP_TAC] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_N_INIT_TAC "s0" THEN
    SUBGOAL_THEN
      `!j. j < 4
          ==> bigdigit (bignum_from_memory(z',4) s0) j =
              bigdigit a (k + j)`
    MP_TAC THENL
      [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS];
      SIMP_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY]] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; GSYM WORD_ADD_ASSOC;
      GSYM WORD_ADD] THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0]) THEN
    SUBGOAL_THEN
      `word_add z (word (32 * (k4 - 1) + 32)):int64 = z' /\
      word_add z (word (32 * (k4 - 1) + 40)):int64 = word_add z' (word 8) /\
      word_add z (word (32 * (k4 - 1) + 48)):int64 = word_add z' (word 16) /\
      word_add z (word (32 * (k4 - 1) + 56)):int64 = word_add z' (word 24) /\
      word_add (word_add z (word (32 * (k4 - 1)))) (word 32):int64 =
      z' /\
      word_add (word_add z (word (32 * (k4 - 1)))) (word 48):int64 =
      word_add z' (word 16)`
    STRIP_ASSUME_TAC THENL
      [REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      SUBST1_TAC(SYM(ASSUME `word_add z (word (8 * k)):int64 = z'`)) THEN
      SUBGOAL_THEN `8 * k = 32 * (k4 - 1) + 32` SUBST1_TAC THENL
        [MAP_EVERY UNDISCH_TAC [`4 * k4 = k`; `~(k4 = 0)`] THEN ARITH_TAC;
        CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    ARM_N_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (4--7) (1--10) THEN
    ENSURES_N_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
      ASSUME_TAC th) THEN
    ABBREV_TAC `bout <=> ~(word cout:int64 = word 0)` THEN
    SUBGOAL_THEN `cout = bitval bout` SUBST_ALL_TAC THENL
      [EXPAND_TAC "bout" THEN UNDISCH_TAC `cout < 2` THEN
      SPEC_TAC(`cout:num`,`c:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `bitval
        (2 EXP 64 <=
        val (word_neg(word (bitval bout):int64)) +
        val (word_neg(word (bitval bout):int64))) =
      bitval bout`
    SUBST_ALL_TAC THENL
      [POP_ASSUM_LIST(K ALL_TAC) THEN AP_TERM_TAC THEN
      BOOL_CASES_TAC `bout:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
      CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_UNMASK_64; WORD_NEG_NEG; VAL_WORD_BITVAL]] THEN
    MP_TAC(SPECL [`a:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (ARITH_RULE
        `z = q * n + a + q
        ==> x + q = z + b + h
            ==> x = q * n + b + h + a`)) THEN
    SUBST1_TAC(SYM(ASSUME `read (memory :> bytes (z,8 * 4)) s10 = q`)) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SPLIT] THEN
    ONCE_REWRITE_TAC[MESON[ADD_SYM]
      `bignum_from_memory (z,4 + k) = bignum_from_memory (z,k + 4)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
    REWRITE_TAC[EQ_ADD_RCANCEL; ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a * b * c:num = b * a * c`] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; VAL_WORD_BITVAL] THEN
    AP_TERM_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN
    REPLICATE_TAC 4
      (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP]) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;

    (* num steps *)ARITH_TAC
  ] THEN

  (* a b pc1 pc2 p q f_nsteps nsteps_pre nsteps_post *)
  ENSURES_N_WHILE_PAUP_TAC `1` `k4:num` `pc + 0x168` `pc + 0x3a0`
   `\i s. (read X1 s = word_sub (word_add z (word(32 * i))) (word 32) /\
           read X2 s = word_sub (word_add m (word(32 * i))) (word 32) /\
           read X3 s = word w /\
           bignum_from_memory(m,k) s = n /\
           read X0 s = word (32 * (k4 - 1)) /\
           read X26 s = wouter /\
           read X28 s = word_neg(word cout) /\
           bignum_from_memory (z,4) s = q /\
           read X4 s = word (bigdigit q 0) /\
           read X5 s = word (bigdigit q 1) /\
           read X6 s = word (bigdigit q 2) /\
           read X7 s = word (bigdigit q 3) /\
           read X27 s = word (32 * (k4 - i)) /\
           bignum_from_memory (word_add z (word (8 * 4 * i)),
                               (k + 4) - 4 * i) s =
           highdigits a (4 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                bignum_of_wordlist
                [read X12 s; read X13 s; read X14 s; read X15 s] +
                bignum_from_memory(z,4 * i) s =
                q * lowdigits n (4 * i) + lowdigits a (4 * i) + q))`
  `\(i:num) (s:armstate). read ZF s <=> i = k4`
  `\(i:num). 142` `1` `1` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0) /\ ~(k = 1)`];

    ARM_N_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--1) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_SUB] THEN
    ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    CONV_TAC WORD_RULE;

    ALL_TAC; (*** The main loop invariant preservation ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_N_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1];

    ARM_N_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
    ASM_REWRITE_TAC[] THEN

    REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `32 * 1 <= 32 * k4 <=> ~(k4 = 0)`] THEN
    SUBST1_TAC(SYM(ASSUME `4 * k4 = k`)) THEN CONV_TAC WORD_RULE;

    (*steps*)
    REWRITE_TAC[NSUM_CONST_NUMSEG;ADD_SUB] THEN
    SUBGOAL_THEN `((k4 - 1) * 142 + k4 - 1 - 1) + 1 = (k4-1) * 143`
    SUBST1_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC] THEN
    ARITH_TAC
    ] THEN

  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `4 * i < k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(k + 4) - 4 * (i + 1) = k - 4 * i`] THEN

  ABBREV_TAC `z':int64 = word_add z (word (32 * i))` THEN
  ABBREV_TAC `m':int64 = word_add m (word (32 * i))` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = 4 * (i + 1)`] THEN
  ASM_REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 4 * i)) = word_add z (word(32 * i))`] THEN

  SUBGOAL_THEN
   `ALL (nonoverlapping (z':int64,32))
        [(z,32); (z,8 * 4 * i); (m,8 * k); (word pc,1020);
         (m',32); (word_add z (word (32 * (i + 1))),8 * (k - 4 * i))]`
  MP_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["z'"; "m'"] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_N_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE
       [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
        X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [memory :> bytes (z',8 * 4)] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,,
      MAYCHANGE [events]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  ENSURES_N_GHOST_INTRO_TAC `g8:int64` `read X12` THEN
  ENSURES_N_GHOST_INTRO_TAC `g9:int64` `read X13` THEN
  ENSURES_N_GHOST_INTRO_TAC `g10:int64` `read X14` THEN
  ENSURES_N_GHOST_INTRO_TAC `g11:int64` `read X15` THEN
  ENSURES_N_GHOST_INTRO_TAC `zlo:num` `bignum_from_memory (z,4 * i)` THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_N_INIT_TAC "s0" THEN

  ABBREV_TAC `z'':int64 = word_add z (word (32 * (i + 1)))` THEN

  SUBGOAL_THEN
   `bignum_from_memory(z'',k - 4 * i) s0 = highdigits a (4 * (i + 1))`
  MP_TAC THENL
   [EXPAND_TAC "z''" THEN REWRITE_TAC[WORD_RULE
     `word_add z (word (32 * (i + 1))) =
      word_add (word_add z (word(8 * 4 * i))) (word(8 * 4))`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * i = 32 * i`] THEN
    SUBGOAL_THEN `k - 4 * i = ((k + 4) - 4 * i) - 4` SUBST1_TAC THENL
     [UNDISCH_TAC `4 * i < k` THEN ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV]] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC] THEN

  SUBGOAL_THEN
   `(!j. j < 4
         ==> bigdigit (bignum_from_memory(z,4) s0) j = bigdigit q j) /\
    (!j. j < 4
         ==> bigdigit
              (bignum_from_memory(z',((k + 4) - 4 * i)) s0) j =
             bigdigit a (4 * i + j)) /\
    (!j. j < 4
         ==> bigdigit (highdigits (bignum_from_memory(m,k) s0) (4 * i)) j =
             bigdigit n (4 * i + j))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_HIGHDIGITS];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [HIGHDIGITS_BIGNUM_FROM_MEMORY; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  SUBGOAL_THEN `!j. j < 4 ==> j < (k + 4) - 4 * i /\ j < k - 4 * i`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC;
    SIMP_TAC[]] THEN
  DISCH_THEN(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [BIGDIGIT_HIGHDIGITS; VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * i = 32 * i`] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_CLAUSES; WORD_ADD_0] THEN
  STRIP_TAC THEN

  ARM_N_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) "" [] None THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 32)) (word 32) = x`]) THEN

  ARM_N_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC
   ((5--8) @ [10;12;14;16;18;19] @ (21--42) @
    [48;53;55;56;62;67] @ (69--74) @
    [80;85;87;88;89] @
    [95;100;102;103;104;105;106] @
    [112;117;119;120;121;122] @
    [128;133;135;136;137;138])
   (3--142) THEN
  ENSURES_N_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add z (word (32 * (i + 1))):int64 = z''`)) THEN
    SUBST1_TAC(SYM(ASSUME `word_add z (word (32 * i)):int64 = z'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add m (word (32 * i)):int64 = m'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word(32 * x)) (word 32) =
      word_mul (word 32) (word_sub (word x) (word 1))`] THEN
    REWRITE_TAC[WORD_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
    DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    VAL_INT64_TAC `32 * (k4 - (i + 1))` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC] THEN

  DISCH_THEN(fun th ->
   REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
   ASSUME_TAC th) THEN

  SUBST1_TAC(ARITH_RULE `32 * i = 8 * 4 * i`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV
   [ARITH_RULE `(q * (x1 + l1) + (x2 + l2)) + q =
                (x1 * q + x2) + (q * l1 + l2 + q)`] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;
              EXP_ADD; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN AP_TERM_TAC THEN
  UNDISCH_TAC `read (memory :> bytes (z,8 * 4)) s142 = q` THEN
  CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN

  ONCE_REWRITE_TAC[GSYM VAL_WORD_BIGDIGIT] THEN REWRITE_TAC[WORD_VAL] THEN
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
  REWRITE_TAC[VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;



(* ========================================================================= *)
(*                      Precomputed buffer contents                          *)
(* ========================================================================= *)

(* Returns (|x-y|:int64, x-y >= 0) *)
let cdiff (x,y:term*term): term * term =
  let subres = subst [(x,`__t1__:num`);(y,`__t2__:num`)]
      `word_sub (word __t1__) (word __t2__):int64` in
  let cmpres = subst [(x,`__t1__:num`);(y,`__t2__:num`)]
      `val (word __t2__:int64) <= val (word __t1__:int64)` in
  let absdiff = subst [(cmpres,`__isnonneg__:bool`);(subres,`__sub__:int64`)]
      `if __isnonneg__ then (__sub__:int64) else word_neg __sub__` in
  (absdiff, cmpres);;

(* Returns (|d|, d >= 0) where d = n[m_ofs_div_4*4 + i0] - n[m_ofs_div_4*4 + i1] *)
let cdiff_from_bignum (n:term) (m_ofs_div_4:term) (i0:int) (i1:int): term * term =
  assert (type_of m_ofs_div_4 = `:num` && type_of n = `:num`);
  let template = `bigdigit __n__ (__m_ofs_div_4__ * 4 + __idx__)` in
  let operands = [(n,`__n__:num`); (m_ofs_div_4,`__m_ofs_div_4__:num`)] in
  let i0num, i1num = mk_small_numeral i0, mk_small_numeral i1 in
  let tfst, tsnd =
    subst ((i0num,`__idx__:num`)::operands) template,
    subst ((i1num,`__idx__:num`)::operands) template in
  cdiff (tfst, tsnd);;

let precalc_sign_template =
  `(if __isnonneg__ then (word 0) else (word 18446744073709551615):int64)`;;

let precalc_diffs =
  let full_expr = mk_list
       (List.concat_map (fun (i0, i1) ->
            let absdiff, isneg = cdiff_from_bignum `n:num` `i_div_4:num` i0 i1 in
            [absdiff; subst [isneg, mk_var("__isnonneg__",`:bool`)] precalc_sign_template])
          [(1,0);(2,0);(3,0);(2,1);(3,1);(3,2)],
        `:(64)word`) in
  new_definition (subst [full_expr,`__full_expr__:((64)word)list`]
    `precalc_diffs (n:num) (i_div_4:num) = (__full_expr__:((64)word)list)`);;

let precalc_diffs_rev =
  let full_expr = mk_list
       (List.concat_map (fun (i0, i1) ->
            let absdiff, isneg = cdiff_from_bignum `n:num` `i_div_4:num` i0 i1 in
            [absdiff; subst [isneg, mk_var("__isnonneg__",`:bool`)] precalc_sign_template])
          [(0,1);(0,2);(0,3);(1,2);(1,3);(2,3)],
        `:(64)word`) in
  new_definition (subst [full_expr,`__full_expr__:((64)word)list`]
    `precalc_diffs_rev (n:num) (i_div_4:num) = (__full_expr__:((64)word)list)`);;

let get_m_precalc: thm =
  define
     `(get_m_precalc (n:num) 0 = 0) /\
      (get_m_precalc (n:num) (i_div_4 + 1) =
            get_m_precalc n i_div_4 +
            (2 EXP (64 * 12 * i_div_4)) *
            (bignum_of_wordlist (precalc_diffs n (i_div_4 + 1))))`;;

let GET_M_PRECALC_BOUND = prove(
  `forall len n. get_m_precalc n len < 2 EXP (64 * 12 * len)`,

  INDUCT_TAC THENL [
    REWRITE_TAC[get_m_precalc] THEN ARITH_TAC;

    REWRITE_TAC[ADD1;get_m_precalc] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC `n:num` th)) THEN
    TRANS_TAC LET_TRANS
      `get_m_precalc n len + 2 EXP (64 * 12 * len) * (2 EXP (64 * 12) - 1)`
      THEN CONJ_TAC THENL [
      REWRITE_TAC[LE_ADD_LCANCEL] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN
      REWRITE_TAC[EXP_2_NE_0] THEN
      TRANS_TAC LE_TRANS
        `2 EXP (64 * LENGTH (precalc_diffs n (len + 1))) - 1` THEN CONJ_TAC THENL [
        IMP_REWRITE_TAC[ARITH_RULE`0<y ==> (x <= (y-1) <=> x < y)`] THEN
        REWRITE_TAC[BIGNUM_OF_WORDLIST_BOUND_LENGTH] THEN
        REWRITE_TAC[ARITH_RULE`0 < x <=> ~(x = 0)`;EXP_2_NE_0]
        THEN NO_TAC;

        IMP_REWRITE_TAC[LE_SUB_RCANCEL; ONE_LE_EXP_2] THEN
        REWRITE_TAC[LE_EXP;ARITH_RULE`~(2=0)`;ARITH_RULE`~(2=1)`]
        THEN
        REWRITE_TAC[LE_MULT_LCANCEL;ARITH_RULE`~(64=0)`] THEN
        REWRITE_TAC[precalc_diffs] THEN
        CONV_TAC (ONCE_DEPTH_CONV LENGTH_CONV) THEN
        MATCH_ACCEPT_TAC LE_REFL
      ];

      TRANS_TAC LTE_TRANS `2 EXP (64 * 12 * len) * (2 EXP ((64 * 12 - 1) + 1))` THEN CONJ_TAC THENL [
        ASM_ARITH_TAC;

        REWRITE_TAC[ARITH_RULE`(64 * 12 - 1) + 1 = 64 * 12`] THEN
        REWRITE_TAC[GSYM EXP_ADD] THEN
        REWRITE_TAC[LE_EXP;ARITH_RULE`~(2=0)`;ARITH_RULE`~(2=1)`]
        THEN ARITH_TAC
      ]
    ]
  ]);;


let BIGDIGIT_GET_M_PRECALC = prove(
  `forall len n i j. j < 12 /\ i < len ==>
    bigdigit (get_m_precalc n len) (12 * i + j) =
    bigdigit (bignum_of_wordlist (precalc_diffs n (i + 1))) j`,

  INDUCT_TAC THENL [
    ARITH_TAC;

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ADD1; get_m_precalc] THEN
    ASM_CASES_TAC `(i:num) = len` THENL [
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[bigdigit] THEN
      SUBGOAL_THEN `2 EXP (64 * (12 * len + j)) = (2 EXP (64 * 12 * len)) * (2 EXP (64 * j))` SUBST_ALL_TAC THENL [
        MESON_TAC[LEFT_ADD_DISTRIB;EXP_ADD];

        ALL_TAC
      ] THEN
      REWRITE_TAC[GSYM DIV_DIV] THEN
      IMP_REWRITE_TAC[DIV_MULT_ADD;EXP_2_NE_0] THEN
      IMP_REWRITE_TAC[SPECL [`get_m_precalc n len`] DIV_LT;GET_M_PRECALC_BOUND;ADD_CLAUSES] THEN
      NO_TAC;

      SUBGOAL_THEN `i < len` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
      IMP_REWRITE_TAC[BIGDIGIT_ADD_LEFT] THEN
      ASM_ARITH_TAC
    ]
  ]);;

(* Precalculated differences and signs in the current iteration of buffer z *)
let get_z_precalc: thm = define
    `get_z_precalc (z1:num) = bignum_of_wordlist (precalc_diffs_rev z1 0)`;;

let get_z_precalc_terms,get_m_precalc_terms =
  let tz =
    let get_z_precalc_simp =
        (CONV_RULE (ONCE_DEPTH_CONV NUM_ADD_CONV) o REWRITE_RULE[precalc_diffs_rev;MULT])
          get_z_precalc in
     rhs(concl (get_z_precalc_simp)) in
  let mz =
    let get_m_precalc_simp = REWRITE_RULE[precalc_diffs;ADD_0] get_m_precalc in
    let c = snd (dest_conj (concl get_m_precalc_simp)) in
    let c = snd (dest_binary "+" (rhs c)) in
    snd (dest_binary "*" c) in
  dest_list (snd (dest_comb tz)),
  dest_list (snd (dest_comb mz));;



let bigdigit_get_z_precalc_thms =
  let the_constructor = fst (strip_comb (lhs (concl get_z_precalc))) in
  let el_conv =
    let rw = Compute.bool_compset() in
    num_compute_add_convs rw;
    Compute.add_thms [EL_CONS] rw;
    Compute.WEAK_CBV_CONV rw in
  List.mapi
    (fun i z_precalc_ith ->
      let the_lhs = mk_comb(
          mk_comb(`bigdigit`,mk_comb(the_constructor,`z1:num`)),
          mk_small_numeral(i)) in
      prove(list_mk_forall(
        [`z1:num`],mk_eq(the_lhs,mk_comb(`val:int64->num`,z_precalc_ith))),
        REPEAT GEN_TAC THEN
        REWRITE_TAC[get_z_precalc;precalc_diffs_rev] THEN
        IMP_REWRITE_TAC[BIGDIGIT_BIGNUM_OF_WORDLIST] THEN
        CONJ_TAC THENL [
          (* EL *)
          CONV_TAC el_conv;
          (* LENGTH *)
          CONV_TAC (ONCE_DEPTH_CONV LENGTH_CONV) THEN
          ARITH_TAC
        ]))
    get_z_precalc_terms;;

let bigdigit_get_m_precalc_thms =
  let the_constructor =
    let c = concl get_m_precalc in
    fst (strip_comb (lhs (snd (dest_conj c)))) in
  let el_conv =
    let rw = Compute.bool_compset() in
    num_compute_add_convs rw;
    Compute.add_thms [EL_CONS] rw;
    Compute.WEAK_CBV_CONV rw in
  List.mapi
    (fun i m_precalc_ith ->
      let the_lhs = mk_comb(
          mk_comb(`bigdigit`,
            mk_comb(mk_comb(the_constructor,`n:num`),`len:num`)),
          mk_binary "+" (`12 * i`,mk_small_numeral(i))) in
      let the_rhs = mk_comb (`val:int64->num`,
          subst[`i:num`,`i_div_4:num`] m_precalc_ith) in
      let the_goal = list_mk_forall([`i:num`;`len:num`;`n:num`],
            mk_imp(`(i+1) <= len`,mk_eq(the_lhs,the_rhs))) in
      CONV_RULE (REWRITE_CONV[RIGHT_ADD_DISTRIB;GSYM ADD_ASSOC; ADD_CLAUSES] THENC
                 NUM_REDUCE_CONV THENC
                 REWRITE_CONV[ARITH_RULE`i*4 = 4*i`])
        (prove(the_goal,
          REPEAT STRIP_TAC THEN
          IMP_REWRITE_TAC[BIGDIGIT_GET_M_PRECALC] THEN
          REPEAT CONJ_TAC THENL [
            (* goal 1. bigdigit(bignum_of_wordlist(precalc_diffs)) *)
            IMP_REWRITE_TAC[BIGDIGIT_BIGNUM_OF_WORDLIST] THEN
            REWRITE_TAC[precalc_diffs;ADD_0] THEN
            CONJ_TAC THENL [
              (* EL *)
              CONV_TAC el_conv;
              (* LENGTH *)
              CONV_TAC (ONCE_DEPTH_CONV LENGTH_CONV) THEN
              ARITH_TAC
            ];

            (* the const offset < 12 *)
            ARITH_TAC;

            (* i < len *)
            ASM_ARITH_TAC
          ])))
    get_m_precalc_terms;;


(* ========================================================================= *)
(*                  Correctness of the precalculation loop                   *)
(* ========================================================================= *)

let BIGNUM_EMONTREDC_8N_CDIFF_PRECALCLOOP = prove(
  `forall z m_precalc m (k:int64) k4 w zn mn pc stackpointer.
    ALL (nonoverlapping (m_precalc, 8 * 12 * (val k DIV 4 - 1)))
      [(word pc, LENGTH bignum_emontredc_8n_cdiff_mc);
      (z, 8 * 2 * val k); sp:int64,128; m:int64,8*val k] /\
      val k = 4 * k4 /\ 2 <= k4 /\ val k < 2 EXP 32
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_cdiff_mc /\
                read PC s = word (pc + slothy_main) /\
                read SP s = word_sub stackpointer (word 0x80) /\
                read X0 s = word (val k DIV 4) /\
                read X1 s = z /\
                read X2 s = m /\
                read X3 s = w /\
                read X4 s = m_precalc /\
                read X26 s = word (val k DIV 4) /\
                read X12 s = word (val k DIV 4 - 1) /\
                read (memory :> bytes (z, 8 * 2 * val k)) s = zn /\
                read (memory :> bytes (m, 8 * val k)) s = mn)
          (\s. read PC s = word (pc + slothy_precomp_loop_end) /\
                read SP s = word_sub stackpointer (word 0x80) /\
                read X0 s = word (val k DIV 4) /\
                read X1 s = z /\
                read X2 s = m /\
                read X3 s = w /\
                read X26 s = word (val k DIV 4) /\
                read X12 s = word (val k DIV 4 - 1) /\
                read X30 s = m_precalc /\
                read (memory :> bytes (z, 8 * 2 * val k)) s = zn /\
                read (memory :> bytes (m, 8 * val k)) s = mn /\
                read (memory :> bytes (m_precalc, 8 * 12 * (val k DIV 4 - 1))) s =
                    get_m_precalc mn (val k DIV 4 - 1))
          (MAYCHANGE [PC; X2; X4; X5; X6; X7; X24; X25; X27; X28; X29; X30] ,,
            MAYCHANGE [memory :> bytes (m_precalc, 8 * 12 * (val k DIV 4 - 1))] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REWRITE_TAC(map (snd o snd) bignum_emontredc_8n_cdiff_labels) THEN
  REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES;SOME_FLAGS;
      fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
  REPEAT STRIP_TAC THEN ASSUME_TAC (SPEC `k:int64` VAL_BOUND_64) THEN
  SUBGOAL_THEN `val (k:int64) DIV 4 = k4` SUBST_ALL_TAC THENL [
    UNDISCH_TAC `val (k:int64) = 4 * k4` THEN
    ARITH_TAC;
    ALL_TAC
  ] THEN
  UNDISCH_THEN `val (k:int64) = 4 * k4` SUBST_ALL_TAC THEN
  ENSURES_WHILE_PDOWN_TAC `k4 - 1` `pc + 0x54` `pc + 0xc4`
        `\i s. // Preservation of original data
              (read X0 s = word k4 /\
                read X12 s = word(k4 - 1) /\
                read X26 s = word k4 /\
                read X1 s = z /\
                read X25 s = m /\
                read X3 s = w /\
                read X24 s = m_precalc /\
                read SP s = word_sub stackpointer (word 128) /\
                read (memory :> bytes (z, 8 * 2 * 4 * k4)) s = zn /\
                read (memory :> bytes (m, 8 * 4 * k4)) s = mn /\
                // Loop-dependent data
                read X27 s = word i /\
                read X30 s = word_add m_precalc (word (8 * 12 * (k4 - 1 - i))) /\
                read X2 s = word_add m (word (8 * 4 * (k4 - 1 - i))) /\
                bignum_from_memory (m_precalc,12*(k4-1-i)) s = get_m_precalc mn (k4-1-i)) /\
              (read ZF s <=> i = 0)` THEN
  REPEAT CONJ_TAC THENL [
    (* loop counter *)
    SIMPLE_ARITH_TAC;

    (* to header *)
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC (1--4) THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
    ASM_SIMP_TAC[get_m_precalc;ARITH_RULE`8*12*0=0`;READ_MEMORY_BYTES_0] THEN
    FAIL_TAC "fail0";

    (* loop body *)
    ALL_TAC;

    (* back edge *)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC [1] THEN
    MATCH_MP_TAC (TAUT `a ==> ((if a then b else c) = b)`) THEN
    IMP_REWRITE_TAC[VAL_WORD_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC [`4 * k4 < 2 EXP 64`; `i < k4 - 1`] THEN ARITH_TAC;

    (* to the end *)
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC (1--3) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUB_0]) THEN
    ASM_REWRITE_TAC[] THEN FAIL_TAC "term to end"
  ] THEN

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  (* two ldps *)
  SUBGOAL_THEN
      `read (memory :> bytes64
          (word_add m (word (8 * 4 * (k4 - 1 - (i + 1)) + 32)))) s0 =
        word (bigdigit mn (4 * (k4 - 1 - (i + 1)) + 4)) /\
      read (memory :> bytes64
          (word_add m (word (8 * 4 * (k4 - 1 - (i + 1)) + 40)))) s0 =
        word (bigdigit mn (4 * (k4 - 1 - (i + 1)) + 5)) /\
      read (memory :> bytes64
          (word_add m (word (8 * 4 * (k4 - 1 - (i + 1)) + 48)))) s0 =
        word (bigdigit mn (4 * (k4 - 1 - (i + 1)) + 6)) /\
      read (memory :> bytes64
          (word_add (word_add m (word (8 * 4 * (k4 - 1 - (i + 1))))) (word 56))) s0 =
        word (bigdigit mn (4 * (k4 - 1 - (i + 1)) + 7))`
    (LABEL_TAC "H_a0_to_a3") THENL [
    GEN_REWRITE_TAC (DEPTH_BINOP_CONV `(/\):bool->bool->bool`) [GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    EXPAND_TAC "mn" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    IMP_REWRITE_TAC[TAUT `c = T ==> (if c then x else y) = x`] THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    IMP_REWRITE_TAC[WORD_RULE
      `i0=j0 ==> val (read (memory :> bytes64 (word_add m (word i0))) s0) =
                val (read (memory :> bytes64 (word_add m (word j0))) s0)`] THEN
    REPEAT CONJ_TAC THEN ASM_ARITH_TAC;

    ALL_TAC
  ] THEN
  FIRST_X_ASSUM MP_TAC THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC (1--28) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    CONV_TAC WORD_RULE;

    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN AP_TERM_TAC THEN AP_TERM_TAC
        THEN UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;

    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN AP_TERM_TAC THEN AP_TERM_TAC
        THEN UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;

    SUBGOAL_THEN `k4 - 1 - i = k4 - 1 - (i+1) + 1` SUBST1_TAC THENL [
      SIMPLE_ARITH_TAC; ALL_TAC
    ] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM BIGNUM_FROM_MEMORY_BYTES]) THEN
    ASM_REWRITE_TAC[] THEN

    REWRITE_TAC[ARITH_RULE`12 * 1 = (((((((((((0+1)+1)+1)+1)+1)+1)+1)+1)+1)+1)+1)+1`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    CONV_TAC (DEPTH_CONV NUM_ADD_CONV) THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `x+0=x`] THEN
    REWRITE_TAC[get_m_precalc] THEN
    IMP_REWRITE_TAC[ARITH_RULE`x=y ==> x+z=z+y`] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL] THEN DISJ2_TAC THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[bignum_of_wordlist;precalc_diffs] THEN
    REWRITE_TAC[ARITH_RULE`2 EXP 0 = 1`;MULT_CLAUSES;ADD_CLAUSES;ADD_ASSOC] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;ARITH_RULE`1*4=4`] THEN
    REWRITE_TAC[MULT_ASSOC;GSYM EXP_ADD] THEN
    CONV_TAC (DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    CONV_TAC (DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[ARITH_RULE`x*4=4*x`] THEN NO_TAC;

    REWRITE_TAC[WORD_SUB_ADD] THEN
    MATCH_MP_TAC VAL_WORD_EQ_ZERO THEN
    SIMPLE_ARITH_TAC
  ]);;


(* ========================================================================= *)
(*                      Equivalence of outer loops                           *)
(* ========================================================================= *)


(* The body of the main loop. Consists of three basic blocks
    'outerloop' + 'maddloop' + 'loop_postamble'. *)
let outerloop_step1_ops:int list = [
  0xf94003e3; (* ldr    x3, [sp] *)
  0xa9404c31; (* ldp    x17, x19, [x1] *)
  0xa9415434; (* ldp    x20, x21, [x1, #16] *)
  0xa9402448; (* ldp    x8, x9, [x2] *)
  0xa9412c4a; (* ldp    x10, x11, [x2, #16] *)
  0x3dc00455; (* ldr    q21, [x2, #16] *)
  0x9b037e24; (* mul    x4, x17, x3 *)
  0x4e080c80; (* dup    v0.2d, x4 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58080; (* umlal  v0.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083c0e; (* mov    x14, v0.d[0] *)
  0x4e183c0f; (* mov    x15, v0.d[1] *)
  0x9b087c8c; (* mul    x12, x4, x8 *)
  0xab0c0231; (* adds   x17, x17, x12 *)
  0x9bc87c8c; (* umulh  x12, x4, x8 *)
  0x9b097c8d; (* mul    x13, x4, x9 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0x9bc97c8d; (* umulh  x13, x4, x9 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xba0f02b5; (* adcs   x21, x21, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f6; (* adc    x22, xzr, xzr *)
  0xab0c0273; (* adds   x19, x19, x12 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0x9a0f02d6; (* adc    x22, x22, x15 *)
  0x9b037e65; (* mul    x5, x19, x3 *)
  0x4e080ca0; (* dup    v0.2d, x5 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58080; (* umlal  v0.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083c0e; (* mov    x14, v0.d[0] *)
  0x4e183c0f; (* mov    x15, v0.d[1] *)
  0x9b087cac; (* mul    x12, x5, x8 *)
  0xab0c0273; (* adds   x19, x19, x12 *)
  0x9bc87cac; (* umulh  x12, x5, x8 *)
  0x9b097cad; (* mul    x13, x5, x9 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0x9bc97cad; (* umulh  x13, x5, x9 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0xba0f02d6; (* adcs   x22, x22, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f7; (* adc    x23, xzr, xzr *)
  0xab0c0294; (* adds   x20, x20, x12 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0xba0e02d6; (* adcs   x22, x22, x14 *)
  0x9a0f02f7; (* adc    x23, x23, x15 *)
  0xa9001424; (* stp    x4, x5, [x1] *)
  0x9b037e86; (* mul    x6, x20, x3 *)
  0x4e080cc0; (* dup    v0.2d, x6 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605415; (* shl    v21.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58095; (* umlal  v21.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083eae; (* mov    x14, v21.d[0] *)
  0x4e183eaf; (* mov    x15, v21.d[1] *)
  0x9b087ccc; (* mul    x12, x6, x8 *)
  0xab0c0294; (* adds   x20, x20, x12 *)
  0x9bc87ccc; (* umulh  x12, x6, x8 *)
  0x9b097ccd; (* mul    x13, x6, x9 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0x9bc97ccd; (* umulh  x13, x6, x9 *)
  0xba0e02d6; (* adcs   x22, x22, x14 *)
  0xba0f02f7; (* adcs   x23, x23, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f8; (* adc    x24, xzr, xzr *)
  0xab0c02b5; (* adds   x21, x21, x12 *)
  0x9b037ea7; (* mul    x7, x21, x3 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0xba0e02f7; (* adcs   x23, x23, x14 *)
  0x9a0f0318; (* adc    x24, x24, x15 *)
  0xa9011c26; (* stp    x6, x7, [x1, #16] *)
  0x9b087cec; (* mul    x12, x7, x8 *)
  0x9b097ced; (* mul    x13, x7, x9 *)
  0x9b0a7cee; (* mul    x14, x7, x10 *)
  0x9b0b7cef; (* mul    x15, x7, x11 *)
  0xab0c02b5; (* adds   x21, x21, x12 *)
  0x9bc87cec; (* umulh  x12, x7, x8 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0x9bc97ced; (* umulh  x13, x7, x9 *)
  0xba0e02f7; (* adcs   x23, x23, x14 *)
  0x9bca7cee; (* umulh  x14, x7, x10 *)
  0xba0f0318; (* adcs   x24, x24, x15 *)
  0x9bcb7cef; (* umulh  x15, x7, x11 *)
  0x9a1f03f9; (* adc    x25, xzr, xzr *)
  0xab0c02cc; (* adds   x12, x22, x12 *)
  0xba0d02ed; (* adcs   x13, x23, x13 *)
  0xba0e030e; (* adcs   x14, x24, x14 *)
  0x9a0f032f; (* adc    x15, x25, x15 *)
  0xd345fc1b; (* lsr    x27, x0, #5 *)
  0x3dc00034; (* ldr    q20, [x1] *)
  0x3dc00435; (* ldr    q21, [x1, #16] *)
  0xeb050090; (* subs   x16, x4, x5 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9026bf0; (* stp    x16, x26, [sp, #32] *)
  0xeb060090; (* subs   x16, x4, x6 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9036bf0; (* stp    x16, x26, [sp, #48] *)
  0xeb070090; (* subs   x16, x4, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9046bf0; (* stp    x16, x26, [sp, #64] *)
  0xeb0600b0; (* subs   x16, x5, x6 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9056bf0; (* stp    x16, x26, [sp, #80] *)
  0xeb0700b0; (* subs   x16, x5, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9066bf0; (* stp    x16, x26, [sp, #96] *)
  0xeb0700d0; (* subs   x16, x6, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9076bf0; (* stp    x16, x26, [sp, #112] *)
  0x4e945a9e; (* uzp2   v30.4s, v20.4s, v20.4s *)
  0x0ea12a9c; (* xtn    v28.2s, v20.2d *)
  0x4ea00a91; (* rev64  v17.4s, v20.4s *)
  0x4e955ab2; (* uzp2   v18.4s, v21.4s, v21.4s *)
  0x0ea12ab3; (* xtn    v19.2s, v21.2d *)
  0x4ea00ab4; (* rev64  v20.4s, v21.4s *)
  0x3cc20c56; (* ldr    q22, [x2, #32]! *)
  0x3dc00457; (* ldr    q23, [x2, #16] *)
  0x0ea12ac4; (* xtn    v4.2s, v22.2d *)
  0x2ebcc086; (* umull  v6.2d, v4.2s, v28.2s *)
  0x2ebec087; (* umull  v7.2d, v4.2s, v30.2s *)
  0x4e965ad0; (* uzp2   v16.4s, v22.4s, v22.4s *)
  0x4eb69e20; (* mul    v0.4s, v17.4s, v22.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ebec219; (* umull  v25.2d, v16.2s, v30.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ebc8202; (* umlal  v2.2d, v16.2s, v28.2s *)
  0x4f605418; (* shl    v24.2d, v0.2d, #32 *)
  0x6f6014f9; (* usra   v25.2d, v7.2d, #32 *)
  0x2ebc8098; (* umlal  v24.2d, v4.2s, v28.2s *)
  0x6f601459; (* usra   v25.2d, v2.2d, #32 *)
  0x0ea12ae4; (* xtn    v4.2s, v23.2d *)
  0x2eb3c086; (* umull  v6.2d, v4.2s, v19.2s *)
  0x2eb2c087; (* umull  v7.2d, v4.2s, v18.2s *)
  0x4e975af0; (* uzp2   v16.4s, v23.4s, v23.4s *)
  0x4eb79e80; (* mul    v0.4s, v20.4s, v23.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2eb2c21b; (* umull  v27.2d, v16.2s, v18.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2eb38202; (* umlal  v2.2d, v16.2s, v19.2s *)
  0x4f60541a; (* shl    v26.2d, v0.2d, #32 *)
  0x6f6014fb; (* usra   v27.2d, v7.2d, #32 *)
  0x2eb3809a; (* umlal  v26.2d, v4.2s, v19.2s *)
  0x6f60145b; (* usra   v27.2d, v2.2d, #32 *)
  0x4e083f30; (* mov    x16, v25.d[0] *)
  0x4e083f7a; (* mov    x26, v27.d[0] *)
  0x4e183f23; (* mov    x3, v25.d[1] *)
  0x4e183f71; (* mov    x17, v27.d[1] *)
  0x4e183f14; (* mov    x20, v24.d[1] *)
  0x4e083f55; (* mov    x21, v26.d[0] *)
  0x4e183f58; (* mov    x24, v26.d[1] *)
  0xab100296; (* adds   x22, x20, x16 *)
  0xba0302b7; (* adcs   x23, x21, x3 *)
  0xba1a0318; (* adcs   x24, x24, x26 *)
  0x9a1f0239; (* adc    x25, x17, xzr *)
  0x4e083f11; (* mov    x17, v24.d[0] *)
  0xa9c25434; (* ldp    x20, x21, [x1, #32]! *)
  0xab14018c; (* adds   x12, x12, x20 *)
  0xba1501ad; (* adcs   x13, x13, x21 *)
  0xa9415434; (* ldp    x20, x21, [x1, #16] *)
  0xba1401ce; (* adcs   x14, x14, x20 *)
  0xba1501ef; (* adcs   x15, x15, x21 *)
  0x9a1f03f0; (* adc    x16, xzr, xzr *)
  0xab1102d3; (* adds   x19, x22, x17 *)
  0xba1602f6; (* adcs   x22, x23, x22 *)
  0xba170317; (* adcs   x23, x24, x23 *)
  0xba180338; (* adcs   x24, x25, x24 *)
  0x9a1903f9; (* adc    x25, xzr, x25 *)
  0xab1102d4; (* adds   x20, x22, x17 *)
  0xba1302f5; (* adcs   x21, x23, x19 *)
  0xba160316; (* adcs   x22, x24, x22 *)
  0xba170337; (* adcs   x23, x25, x23 *)
  0xba1803f8; (* adcs   x24, xzr, x24 *)
  0x9a1903f9; (* adc    x25, xzr, x25 *)
  0xab0c0231; (* adds   x17, x17, x12 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xba0f02b5; (* adcs   x21, x21, x15 *)
  0xba1002d6; (* adcs   x22, x22, x16 *)
  0xba1f02f7; (* adcs   x23, x23, xzr *)
  0xba1f0318; (* adcs   x24, x24, xzr *)
  0x9a1f0339; (* adc    x25, x25, xzr *)
  0xa94733ef; (* ldp    x15, x12, [sp, #112] *)
  0xa9453bcd; (* ldp    x13, x14, [x30, #80] *)
  0xca0e018c; (* eor    x12, x12, x14 *)
  0x9b0d7dee; (* mul    x14, x15, x13 *)
  0x9bcd7ded; (* umulh  x13, x15, x13 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xca0c01ce; (* eor    x14, x14, x12 *)
  0xba0e02f7; (* adcs   x23, x23, x14 *)
  0xca0c01ad; (* eor    x13, x13, x12 *)
  0xba0d0318; (* adcs   x24, x24, x13 *)
  0x9a0c0339; (* adc    x25, x25, x12 *)
  0xa94233ef; (* ldp    x15, x12, [sp, #32] *)
  0xa9403bcd; (* ldp    x13, x14, [x30] *)
  0xca0e018c; (* eor    x12, x12, x14 *)
  0x9b0d7dee; (* mul    x14, x15, x13 *)
  0x9bcd7ded; (* umulh  x13, x15, x13 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xca0c01ce; (* eor    x14, x14, x12 *)
  0xba0e0273; (* adcs   x19, x19, x14 *)
  0xca0c01ad; (* eor    x13, x13, x12 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba0c02b5; (* adcs   x21, x21, x12 *)
  0xba0c02d6; (* adcs   x22, x22, x12 *)
  0xba0c02f7; (* adcs   x23, x23, x12 *)
  0xba0c0318; (* adcs   x24, x24, x12 *)
  0x9a0c0339; (* adc    x25, x25, x12 *)
  0xa9004c31; (* stp    x17, x19, [x1] *)
  0xa94633ef; (* ldp    x15, x12, [sp, #96] *)
  0xa9443bcd; (* ldp    x13, x14, [x30, #64] *)
  0xca0e018c; (* eor    x12, x12, x14 *)
  0x9b0d7dee; (* mul    x14, x15, x13 *)
  0x9bcd7ded; (* umulh  x13, x15, x13 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xca0c01ce; (* eor    x14, x14, x12 *)
  0xba0e02d6; (* adcs   x22, x22, x14 *)
  0xca0c01ad; (* eor    x13, x13, x12 *)
  0xba0d02f7; (* adcs   x23, x23, x13 *)
  0xba0c0318; (* adcs   x24, x24, x12 *)
  0x9a0c0339; (* adc    x25, x25, x12 *)
  0xa94333ef; (* ldp    x15, x12, [sp, #48] *)
  0xa9413bcd; (* ldp    x13, x14, [x30, #16] *)
  0xca0e018c; (* eor    x12, x12, x14 *)
  0x9b0d7dee; (* mul    x14, x15, x13 *)
  0x9bcd7ded; (* umulh  x13, x15, x13 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xca0c01ce; (* eor    x14, x14, x12 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xca0c01ad; (* eor    x13, x13, x12 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0xba0c02d6; (* adcs   x22, x22, x12 *)
  0xba0c02f7; (* adcs   x23, x23, x12 *)
  0xba0c0318; (* adcs   x24, x24, x12 *)
  0x9a0c0339; (* adc    x25, x25, x12 *)
  0xa94433ef; (* ldp    x15, x12, [sp, #64] *)
  0xa9423bcd; (* ldp    x13, x14, [x30, #32] *)
  0xca0e018c; (* eor    x12, x12, x14 *)
  0x9b0d7dee; (* mul    x14, x15, x13 *)
  0x9bcd7ded; (* umulh  x13, x15, x13 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xca0c01ce; (* eor    x14, x14, x12 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0xca0c01ad; (* eor    x13, x13, x12 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0xba0c02f7; (* adcs   x23, x23, x12 *)
  0xba0c0318; (* adcs   x24, x24, x12 *)
  0x9a0c0339; (* adc    x25, x25, x12 *)
  0xa94533ef; (* ldp    x15, x12, [sp, #80] *)
  0xa9433bcd; (* ldp    x13, x14, [x30, #48] *)
  0xca0e018c; (* eor    x12, x12, x14 *)
  0x9b0d7dee; (* mul    x14, x15, x13 *)
  0x9bcd7ded; (* umulh  x13, x15, x13 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xca0c01ce; (* eor    x14, x14, x12 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0xa9015434; (* stp    x20, x21, [x1, #16] *)
  0xca0c01ad; (* eor    x13, x13, x12 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0xba0c02ed; (* adcs   x13, x23, x12 *)
  0xba0c030e; (* adcs   x14, x24, x12 *)
  0x9a0c032f; (* adc    x15, x25, x12 *)
  0xaa1603ec; (* mov    x12, x22 *)
  0x910183de; (* add    x30, x30, #0x60 *)
  0xd100077b; (* sub    x27, x27, #0x1 *)
  0xb5ffed3b; (* cbnz   x27, 29c <bignum_emontredc_8n_neon_maddloop_neon> *)
  0xa9424c31; (* ldp    x17, x19, [x1, #32] *)
  0xa9435434; (* ldp    x20, x21, [x1, #48] *)
  0xa9417ffa; (* ldp    x26, xzr, [sp, #16] *)
  0xab1c039f; (* cmn    x28, x28 *)
  0xba0c0231; (* adcs   x17, x17, x12 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xba0f02b5; (* adcs   x21, x21, x15 *)
  0xda9f33fc; (* csetm  x28, cs  // cs = hs, nlast *)
  0xa9024c31; (* stp    x17, x19, [x1, #32] *)
  0xa9035434; (* stp    x20, x21, [x1, #48] *)
  0xcb000021; (* sub    x1, x1, x0 *)
  0xcb000042; (* sub    x2, x2, x0 *)
  0x91008021; (* add    x1, x1, #0x20 *)
  0xd100075a; (* sub    x26, x26, #0x1 *)
  0xa9017ffa; (* stp    x26, xzr, [sp, #16] *)
  0xf94007fe; (* ldr    x30, [sp, #8] *)
];;

let outerloop_step1_mc = define_mc_from_intlist "outerloop_step1_mc" outerloop_step1_ops;;

let OUTERLOOP_STEP1_EXEC = ARM_MK_EXEC_RULE outerloop_step1_mc;;

let outerloop_step1_labels = [
  ("maddloop_neon", (0x29c, new_definition `outerloop_step1_label_maddloop_neon = 0x29c`));
  ("inner_loop_postamble", (0x4fc, new_definition `outerloop_step1_label_inner_loop_postamble = 0x4fc`));
];;


(* intermediate state of the maddloop loop of step1 and step2. has a backedge too. *)
let maddloop_step2_x30_ops:int list = [
  0x3cc20c4e; (* ldr    q14, [x2, #32]! *)
  0x3dc00459; (* ldr    q25, [x2, #16] *)
  0x0ea129d5; (* xtn    v21.2s, v14.2d *)
  0x0ea12b3f; (* xtn    v31.2s, v25.2d *)
  0x4e995b38; (* uzp2   v24.4s, v25.4s, v25.4s *)
  0x2ebec2a5; (* umull  v5.2d, v21.2s, v30.2s *)
  0x2eb2c3f0; (* umull  v16.2d, v31.2s, v18.2s *)
  0x2ebcc2ad; (* umull  v13.2d, v21.2s, v28.2s *)
  0x4e8e59ca; (* uzp2   v10.4s, v14.4s, v14.4s *)
  0x2eb3c3e1; (* umull  v1.2d, v31.2s, v19.2s *)
  0x4eb99e86; (* mul    v6.4s, v20.4s, v25.4s *)
  0x2eb2c300; (* umull  v0.2d, v24.2s, v18.2s *)
  0x6f6015a5; (* usra   v5.2d, v13.2d, #32 *)
  0x2ebec142; (* umull  v2.2d, v10.2s, v30.2s *)
  0x6f601430; (* usra   v16.2d, v1.2d, #32 *)
  0x6ea028cd; (* uaddlp v13.2d, v6.4s *)
  0x4e3d1ca7; (* and    v7.16b, v5.16b, v29.16b *)
  0x6f6014a2; (* usra   v2.2d, v5.2d, #32 *)
  0x4e3d1e19; (* and    v25.16b, v16.16b, v29.16b *)
  0x2ebc8147; (* umlal  v7.2d, v10.2s, v28.2s *)
  0x6f601600; (* usra   v0.2d, v16.2d, #32 *)
  0x4f6055b0; (* shl    v16.2d, v13.2d, #32 *)
  0x2eb38319; (* umlal  v25.2d, v24.2s, v19.2s *)
  0x6f6014e2; (* usra   v2.2d, v7.2d, #32 *)
  0x2eb383f0; (* umlal  v16.2d, v31.2s, v19.2s *)
  0x4eae9e27; (* mul    v7.4s, v17.4s, v14.4s *)
  0x6f601720; (* usra   v0.2d, v25.2d, #32 *)
  0x6ea028ea; (* uaddlp v10.2d, v7.4s *)
  0x4e183c43; (* mov    x3, v2.d[1] *)
  0x4e083c1a; (* mov    x26, v0.d[0] *)
  0xa94353e9; (* ldp    x9, x20, [sp, #48] *)
  0x4f60554f; (* shl    v15.2d, v10.2d, #32 *)
  0x2ebc82af; (* umlal  v15.2d, v21.2s, v28.2s *)
  0x4e083e11; (* mov    x17, v16.d[0] *)
  0x4e083c50; (* mov    x16, v2.d[0] *)
  0xa94217e6; (* ldp    x6, x5, [sp, #32] *)
  0xa94167c7; (* ldp    x7, x25, [x30, #16] *)
  0x4e183df5; (* mov    x21, v15.d[1] *)
  0x4e183e17; (* mov    x23, v16.d[1] *)
  0xa9402bd8; (* ldp    x24, x10, [x30] *)
  0x9b077d36; (* mul    x22, x9, x7 *)
  0xca19028b; (* eor    x11, x20, x25 *)
  0xa9c27434; (* ldp    x20, x29, [x1, #32]! *)
  0x9bc77d28; (* umulh  x8, x9, x7 *)
  0xca0a00b3; (* eor    x19, x5, x10 *)
  0xab1002b9; (* adds   x25, x21, x16 *)
  0x4e183c10; (* mov    x16, v0.d[1] *)
  0xa9411c24; (* ldp    x4, x7, [x1, #16] *)
  0xba030235; (* adcs   x21, x17, x3 *)
  0xca0b02d6; (* eor    x22, x22, x11 *)
  0xba1a02f7; (* adcs   x23, x23, x26 *)
  0x9a1f0211; (* adc    x17, x16, xzr *)
  0xab140190; (* adds   x16, x12, x20 *)
  0x9b187cc5; (* mul    x5, x6, x24 *)
  0xba1d01a9; (* adcs   x9, x13, x29 *)
  0x4e083dfd; (* mov    x29, v15.d[0] *)
  0xba0401c4; (* adcs   x4, x14, x4 *)
  0xa94737ea; (* ldp    x10, x13, [sp, #112] *)
  0x9bd87cd4; (* umulh  x20, x6, x24 *)
  0xba0701f8; (* adcs   x24, x15, x7 *)
  0xa9451fcc; (* ldp    x12, x7, [x30, #80] *)
  0x9a1f03e6; (* adc    x6, xzr, xzr *)
  0xab1d032e; (* adds   x14, x25, x29 *)
  0xca0b010f; (* eor    x15, x8, x11 *)
  0xba1902b9; (* adcs   x25, x21, x25 *)
  0xba1502e8; (* adcs   x8, x23, x21 *)
  0xca0701a7; (* eor    x7, x13, x7 *)
  0xba170237; (* adcs   x23, x17, x23 *)
  0xca1300b5; (* eor    x21, x5, x19 *)
  0x9a1103ed; (* adc    x13, xzr, x17 *)
  0xab1d0331; (* adds   x17, x25, x29 *)
  0xba0e0105; (* adcs   x5, x8, x14 *)
  0xba1902f9; (* adcs   x25, x23, x25 *)
  0xba0801a8; (* adcs   x8, x13, x8 *)
  0xba1703f7; (* adcs   x23, xzr, x23 *)
  0x9a0d03ed; (* adc    x13, xzr, x13 *)
  0xab1003bd; (* adds   x29, x29, x16 *)
  0x9b0c7d50; (* mul    x16, x10, x12 *)
  0xba0901c9; (* adcs   x9, x14, x9 *)
  0xba040231; (* adcs   x17, x17, x4 *)
  0x9bcc7d4c; (* umulh  x12, x10, x12 *)
  0xba1800aa; (* adcs   x10, x5, x24 *)
  0xca070205; (* eor    x5, x16, x7 *)
  0xa9443bd0; (* ldp    x16, x14, [x30, #64] *)
  0xba060326; (* adcs   x6, x25, x6 *)
  0xca130298; (* eor    x24, x20, x19 *)
  0xba1f0104; (* adcs   x4, x8, xzr *)
  0xa94667f4; (* ldp    x20, x25, [sp, #96] *)
  0xba1f02f7; (* adcs   x23, x23, xzr *)
  0x9a1f01a8; (* adc    x8, x13, xzr *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xba050084; (* adcs   x4, x4, x5 *)
  0xca070185; (* eor    x5, x12, x7 *)
  0xba0502f7; (* adcs   x23, x23, x5 *)
  0x9b107e8c; (* mul    x12, x20, x16 *)
  0x9a070105; (* adc    x5, x8, x7 *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xba150135; (* adcs   x21, x9, x21 *)
  0xca0e0328; (* eor    x8, x25, x14 *)
  0xba18022d; (* adcs   x13, x17, x24 *)
  0xa900543d; (* stp    x29, x21, [x1] *)
  0x9bd07e94; (* umulh  x20, x20, x16 *)
  0xba130151; (* adcs   x17, x10, x19 *)
  0xa94463fd; (* ldp    x29, x24, [sp, #64] *)
  0xba1300d9; (* adcs   x25, x6, x19 *)
  0xa94257c6; (* ldp    x6, x21, [x30, #32] *)
  0xca08018a; (* eor    x10, x12, x8 *)
  0xba130089; (* adcs   x9, x4, x19 *)
  0xa94343c4; (* ldp    x4, x16, [x30, #48] *)
  0xba1302ec; (* adcs   x12, x23, x19 *)
  0x9a1300a5; (* adc    x5, x5, x19 *)
  0xb100051f; (* cmn    x8, #0x1 *)
  0xa9454fe7; (* ldp    x7, x19, [sp, #80] *)
  0xba0a032e; (* adcs   x14, x25, x10 *)
  0x9b067fb9; (* mul    x25, x29, x6 *)
  0xca080294; (* eor    x20, x20, x8 *)
  0xba140137; (* adcs   x23, x9, x20 *)
  0xca150318; (* eor    x24, x24, x21 *)
  0xba08018c; (* adcs   x12, x12, x8 *)
  0x9a0800aa; (* adc    x10, x5, x8 *)
  0xb100057f; (* cmn    x11, #0x1 *)
  0x9bc67fa5; (* umulh  x5, x29, x6 *)
  0xba1601a8; (* adcs   x8, x13, x22 *)
  0xca18032d; (* eor    x13, x25, x24 *)
  0xba0f023d; (* adcs   x29, x17, x15 *)
  0xba0b01d6; (* adcs   x22, x14, x11 *)
  0xba0b02f5; (* adcs   x21, x23, x11 *)
  0x9b047cf7; (* mul    x23, x7, x4 *)
  0xba0b018e; (* adcs   x14, x12, x11 *)
  0xca10026c; (* eor    x12, x19, x16 *)
  0x9a0b014f; (* adc    x15, x10, x11 *)
  0xb100071f; (* cmn    x24, #0x1 *)
  0xca1800b3; (* eor    x19, x5, x24 *)
  0xba0d03ab; (* adcs   x11, x29, x13 *)
  0x9bc47cfd; (* umulh  x29, x7, x4 *)
  0xba1302cd; (* adcs   x13, x22, x19 *)
  0xba1802b3; (* adcs   x19, x21, x24 *)
  0xca0c02f6; (* eor    x22, x23, x12 *)
  0xba1801ce; (* adcs   x14, x14, x24 *)
  0x9a1801ef; (* adc    x15, x15, x24 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xba16016b; (* adcs   x11, x11, x22 *)
  0xca0c03a4; (* eor    x4, x29, x12 *)
  0xba0401a4; (* adcs   x4, x13, x4 *)
  0xa9012c28; (* stp    x8, x11, [x1, #16] *)
  0xba0c026d; (* adcs   x13, x19, x12 *)
  0xba0c01ce; (* adcs   x14, x14, x12 *)
  0x9a0c01ef; (* adc    x15, x15, x12 *)
  0xaa0403ec; (* mov    x12, x4 *)
  0x910183de; (* add    x30, x30, #0x60 *)
  0xd100077b; (* sub    x27, x27, #0x1 *)
  0xb5ffed3b; (* cbnz   x27, 0 <bignum_emontredc_8n_neon_maddloop_neon> *)
];;

let maddloop_step2_x30_mc = define_mc_from_intlist "maddloop_step2_x30_mc" maddloop_step2_x30_ops;;

let MADDLOOP_STEP2_X30_EXEC = ARM_MK_EXEC_RULE maddloop_step2_x30_mc;;


(* The body of the main loop. Consists of three basic blocks
    'outerloop' + 'maddloop' + 'loop_postamble'. *)
let outerloop_step2_ops:int list = [
  0xf94003e3; (* ldr    x3, [sp] *)
  0xa9404c31; (* ldp    x17, x19, [x1] *)
  0xa9415434; (* ldp    x20, x21, [x1, #16] *)
  0xa9402448; (* ldp    x8, x9, [x2] *)
  0xa9412c4a; (* ldp    x10, x11, [x2, #16] *)
  0x3dc00455; (* ldr    q21, [x2, #16] *)
  0x9b037e24; (* mul    x4, x17, x3 *)
  0x4e080c80; (* dup    v0.2d, x4 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58080; (* umlal  v0.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083c0e; (* mov    x14, v0.d[0] *)
  0x4e183c0f; (* mov    x15, v0.d[1] *)
  0x9b087c8c; (* mul    x12, x4, x8 *)
  0xab0c0231; (* adds   x17, x17, x12 *)
  0x9bc87c8c; (* umulh  x12, x4, x8 *)
  0x9b097c8d; (* mul    x13, x4, x9 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0x9bc97c8d; (* umulh  x13, x4, x9 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xba0f02b5; (* adcs   x21, x21, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f6; (* adc    x22, xzr, xzr *)
  0xab0c0273; (* adds   x19, x19, x12 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0x9a0f02d6; (* adc    x22, x22, x15 *)
  0x9b037e65; (* mul    x5, x19, x3 *)
  0x4e080ca0; (* dup    v0.2d, x5 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58080; (* umlal  v0.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083c0e; (* mov    x14, v0.d[0] *)
  0x4e183c0f; (* mov    x15, v0.d[1] *)
  0x9b087cac; (* mul    x12, x5, x8 *)
  0xab0c0273; (* adds   x19, x19, x12 *)
  0x9bc87cac; (* umulh  x12, x5, x8 *)
  0x9b097cad; (* mul    x13, x5, x9 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0x9bc97cad; (* umulh  x13, x5, x9 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0xba0f02d6; (* adcs   x22, x22, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f7; (* adc    x23, xzr, xzr *)
  0xab0c0294; (* adds   x20, x20, x12 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0xba0e02d6; (* adcs   x22, x22, x14 *)
  0x9a0f02f7; (* adc    x23, x23, x15 *)
  0xa9001424; (* stp    x4, x5, [x1] *)
  0x9b037e86; (* mul    x6, x20, x3 *)
  0x4e080cc0; (* dup    v0.2d, x6 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605415; (* shl    v21.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58095; (* umlal  v21.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083eae; (* mov    x14, v21.d[0] *)
  0x4e183eaf; (* mov    x15, v21.d[1] *)
  0x9b087ccc; (* mul    x12, x6, x8 *)
  0xab0c0294; (* adds   x20, x20, x12 *)
  0x9bc87ccc; (* umulh  x12, x6, x8 *)
  0x9b097ccd; (* mul    x13, x6, x9 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0x9bc97ccd; (* umulh  x13, x6, x9 *)
  0xba0e02d6; (* adcs   x22, x22, x14 *)
  0xba0f02f7; (* adcs   x23, x23, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f8; (* adc    x24, xzr, xzr *)
  0xab0c02b5; (* adds   x21, x21, x12 *)
  0x9b037ea7; (* mul    x7, x21, x3 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0xba0e02f7; (* adcs   x23, x23, x14 *)
  0x9a0f0318; (* adc    x24, x24, x15 *)
  0xa9011c26; (* stp    x6, x7, [x1, #16] *)
  0x9b087cec; (* mul    x12, x7, x8 *)
  0x9b097ced; (* mul    x13, x7, x9 *)
  0x9b0a7cee; (* mul    x14, x7, x10 *)
  0x9b0b7cef; (* mul    x15, x7, x11 *)
  0xab0c02b5; (* adds   x21, x21, x12 *)
  0x9bc87cec; (* umulh  x12, x7, x8 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0x9bc97ced; (* umulh  x13, x7, x9 *)
  0xba0e02f7; (* adcs   x23, x23, x14 *)
  0x9bca7cee; (* umulh  x14, x7, x10 *)
  0xba0f0318; (* adcs   x24, x24, x15 *)
  0x9bcb7cef; (* umulh  x15, x7, x11 *)
  0x9a1f03f9; (* adc    x25, xzr, xzr *)
  0xab0c02cc; (* adds   x12, x22, x12 *)
  0xba0d02ed; (* adcs   x13, x23, x13 *)
  0xba0e030e; (* adcs   x14, x24, x14 *)
  0x9a0f032f; (* adc    x15, x25, x15 *)
  0xd345fc1b; (* lsr    x27, x0, #5 *)
  0x3dc00034; (* ldr    q20, [x1] *)
  0x3dc00435; (* ldr    q21, [x1, #16] *)
  0xeb050090; (* subs   x16, x4, x5 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9026bf0; (* stp    x16, x26, [sp, #32] *)
  0xeb060090; (* subs   x16, x4, x6 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9036bf0; (* stp    x16, x26, [sp, #48] *)
  0xeb070090; (* subs   x16, x4, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9046bf0; (* stp    x16, x26, [sp, #64] *)
  0xeb0600b0; (* subs   x16, x5, x6 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9056bf0; (* stp    x16, x26, [sp, #80] *)
  0xeb0700b0; (* subs   x16, x5, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9066bf0; (* stp    x16, x26, [sp, #96] *)
  0xeb0700d0; (* subs   x16, x6, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9076bf0; (* stp    x16, x26, [sp, #112] *)
  0x4e945a9e; (* uzp2   v30.4s, v20.4s, v20.4s *)
  0x0ea12a9c; (* xtn    v28.2s, v20.2d *)
  0x4ea00a91; (* rev64  v17.4s, v20.4s *)
  0x4e955ab2; (* uzp2   v18.4s, v21.4s, v21.4s *)
  0x0ea12ab3; (* xtn    v19.2s, v21.2d *)
  0x4ea00ab4; (* rev64  v20.4s, v21.4s *)
  0x3cc20c4e; (* ldr    q14, [x2, #32]! *)
  0x3dc00459; (* ldr    q25, [x2, #16] *)
  0x0ea129d5; (* xtn    v21.2s, v14.2d *)
  0x0ea12b3f; (* xtn    v31.2s, v25.2d *)
  0x4e995b38; (* uzp2   v24.4s, v25.4s, v25.4s *)
  0x2ebec2a5; (* umull  v5.2d, v21.2s, v30.2s *)
  0x2eb2c3f0; (* umull  v16.2d, v31.2s, v18.2s *)
  0x2ebcc2ad; (* umull  v13.2d, v21.2s, v28.2s *)
  0x4e8e59ca; (* uzp2   v10.4s, v14.4s, v14.4s *)
  0x2eb3c3e1; (* umull  v1.2d, v31.2s, v19.2s *)
  0x4eb99e86; (* mul    v6.4s, v20.4s, v25.4s *)
  0x2eb2c300; (* umull  v0.2d, v24.2s, v18.2s *)
  0x6f6015a5; (* usra   v5.2d, v13.2d, #32 *)
  0x2ebec142; (* umull  v2.2d, v10.2s, v30.2s *)
  0x6f601430; (* usra   v16.2d, v1.2d, #32 *)
  0x6ea028cd; (* uaddlp v13.2d, v6.4s *)
  0x4e3d1ca7; (* and    v7.16b, v5.16b, v29.16b *)
  0x6f6014a2; (* usra   v2.2d, v5.2d, #32 *)
  0x4e3d1e19; (* and    v25.16b, v16.16b, v29.16b *)
  0x2ebc8147; (* umlal  v7.2d, v10.2s, v28.2s *)
  0x6f601600; (* usra   v0.2d, v16.2d, #32 *)
  0x4f6055b0; (* shl    v16.2d, v13.2d, #32 *)
  0x2eb38319; (* umlal  v25.2d, v24.2s, v19.2s *)
  0x6f6014e2; (* usra   v2.2d, v7.2d, #32 *)
  0x2eb383f0; (* umlal  v16.2d, v31.2s, v19.2s *)
  0x4eae9e27; (* mul    v7.4s, v17.4s, v14.4s *)
  0x6f601720; (* usra   v0.2d, v25.2d, #32 *)
  0x6ea028ea; (* uaddlp v10.2d, v7.4s *)
  0x4e183c43; (* mov    x3, v2.d[1] *)
  0x4e083c1a; (* mov    x26, v0.d[0] *)
  0xa94353e9; (* ldp    x9, x20, [sp, #48] *)
  0x4f60554f; (* shl    v15.2d, v10.2d, #32 *)
  0x2ebc82af; (* umlal  v15.2d, v21.2s, v28.2s *)
  0x4e083e11; (* mov    x17, v16.d[0] *)
  0x4e083c50; (* mov    x16, v2.d[0] *)
  0xa94217e6; (* ldp    x6, x5, [sp, #32] *)
  0xa94167c7; (* ldp    x7, x25, [x30, #16] *)
  0x4e183df5; (* mov    x21, v15.d[1] *)
  0x4e183e17; (* mov    x23, v16.d[1] *)
  0xa8c62bd8; (* ldp    x24, x10, [x30], #96 *)
  0x9b077d36; (* mul    x22, x9, x7 *)
  0xca19028b; (* eor    x11, x20, x25 *)
  0xa9c27434; (* ldp    x20, x29, [x1, #32]! *)
  0x9bc77d28; (* umulh  x8, x9, x7 *)
  0xca0a00b3; (* eor    x19, x5, x10 *)
  0xab1002b9; (* adds   x25, x21, x16 *)
  0x4e183c10; (* mov    x16, v0.d[1] *)
  0xa9411c24; (* ldp    x4, x7, [x1, #16] *)
  0xba030235; (* adcs   x21, x17, x3 *)
  0xca0b02d6; (* eor    x22, x22, x11 *)
  0xba1a02f7; (* adcs   x23, x23, x26 *)
  0x9a1f0211; (* adc    x17, x16, xzr *)
  0xab140190; (* adds   x16, x12, x20 *)
  0x9b187cc5; (* mul    x5, x6, x24 *)
  0xba1d01a9; (* adcs   x9, x13, x29 *)
  0x4e083dfd; (* mov    x29, v15.d[0] *)
  0xba0401c4; (* adcs   x4, x14, x4 *)
  0xa94737ea; (* ldp    x10, x13, [sp, #112] *)
  0x9bd87cd4; (* umulh  x20, x6, x24 *)
  0xba0701f8; (* adcs   x24, x15, x7 *)
  0xa97f1fcc; (* ldp    x12, x7, [x30, #-16] *)
  0x9a1f03e6; (* adc    x6, xzr, xzr *)
  0xab1d032e; (* adds   x14, x25, x29 *)
  0xca0b010f; (* eor    x15, x8, x11 *)
  0xba1902b9; (* adcs   x25, x21, x25 *)
  0xba1502e8; (* adcs   x8, x23, x21 *)
  0xca0701a7; (* eor    x7, x13, x7 *)
  0xba170237; (* adcs   x23, x17, x23 *)
  0xca1300b5; (* eor    x21, x5, x19 *)
  0x9a1103ed; (* adc    x13, xzr, x17 *)
  0xab1d0331; (* adds   x17, x25, x29 *)
  0xba0e0105; (* adcs   x5, x8, x14 *)
  0xba1902f9; (* adcs   x25, x23, x25 *)
  0xba0801a8; (* adcs   x8, x13, x8 *)
  0xba1703f7; (* adcs   x23, xzr, x23 *)
  0x9a0d03ed; (* adc    x13, xzr, x13 *)
  0xab1003bd; (* adds   x29, x29, x16 *)
  0x9b0c7d50; (* mul    x16, x10, x12 *)
  0xba0901c9; (* adcs   x9, x14, x9 *)
  0xba040231; (* adcs   x17, x17, x4 *)
  0x9bcc7d4c; (* umulh  x12, x10, x12 *)
  0xba1800aa; (* adcs   x10, x5, x24 *)
  0xca070205; (* eor    x5, x16, x7 *)
  0xa97e3bd0; (* ldp    x16, x14, [x30, #-32] *)
  0xba060326; (* adcs   x6, x25, x6 *)
  0xca130298; (* eor    x24, x20, x19 *)
  0xba1f0104; (* adcs   x4, x8, xzr *)
  0xa94667f4; (* ldp    x20, x25, [sp, #96] *)
  0xba1f02f7; (* adcs   x23, x23, xzr *)
  0x9a1f01a8; (* adc    x8, x13, xzr *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xba050084; (* adcs   x4, x4, x5 *)
  0xca070185; (* eor    x5, x12, x7 *)
  0xba0502f7; (* adcs   x23, x23, x5 *)
  0x9b107e8c; (* mul    x12, x20, x16 *)
  0x9a070105; (* adc    x5, x8, x7 *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xba150135; (* adcs   x21, x9, x21 *)
  0xca0e0328; (* eor    x8, x25, x14 *)
  0xba18022d; (* adcs   x13, x17, x24 *)
  0xa900543d; (* stp    x29, x21, [x1] *)
  0x9bd07e94; (* umulh  x20, x20, x16 *)
  0xba130151; (* adcs   x17, x10, x19 *)
  0xa94463fd; (* ldp    x29, x24, [sp, #64] *)
  0xba1300d9; (* adcs   x25, x6, x19 *)
  0xa97c57c6; (* ldp    x6, x21, [x30, #-64] *)
  0xca08018a; (* eor    x10, x12, x8 *)
  0xba130089; (* adcs   x9, x4, x19 *)
  0xa97d43c4; (* ldp    x4, x16, [x30, #-48] *)
  0xba1302ec; (* adcs   x12, x23, x19 *)
  0x9a1300a5; (* adc    x5, x5, x19 *)
  0xb100051f; (* cmn    x8, #0x1 *)
  0xa9454fe7; (* ldp    x7, x19, [sp, #80] *)
  0xba0a032e; (* adcs   x14, x25, x10 *)
  0x9b067fb9; (* mul    x25, x29, x6 *)
  0xca080294; (* eor    x20, x20, x8 *)
  0xba140137; (* adcs   x23, x9, x20 *)
  0xca150318; (* eor    x24, x24, x21 *)
  0xba08018c; (* adcs   x12, x12, x8 *)
  0x9a0800aa; (* adc    x10, x5, x8 *)
  0xb100057f; (* cmn    x11, #0x1 *)
  0x9bc67fa5; (* umulh  x5, x29, x6 *)
  0xba1601a8; (* adcs   x8, x13, x22 *)
  0xca18032d; (* eor    x13, x25, x24 *)
  0xba0f023d; (* adcs   x29, x17, x15 *)
  0xba0b01d6; (* adcs   x22, x14, x11 *)
  0xba0b02f5; (* adcs   x21, x23, x11 *)
  0x9b047cf7; (* mul    x23, x7, x4 *)
  0xba0b018e; (* adcs   x14, x12, x11 *)
  0xca10026c; (* eor    x12, x19, x16 *)
  0x9a0b014f; (* adc    x15, x10, x11 *)
  0xb100071f; (* cmn    x24, #0x1 *)
  0xca1800b3; (* eor    x19, x5, x24 *)
  0xba0d03ab; (* adcs   x11, x29, x13 *)
  0x9bc47cfd; (* umulh  x29, x7, x4 *)
  0xba1302cd; (* adcs   x13, x22, x19 *)
  0xba1802b3; (* adcs   x19, x21, x24 *)
  0xca0c02f6; (* eor    x22, x23, x12 *)
  0xba1801ce; (* adcs   x14, x14, x24 *)
  0x9a1801ef; (* adc    x15, x15, x24 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xba16016b; (* adcs   x11, x11, x22 *)
  0xca0c03a4; (* eor    x4, x29, x12 *)
  0xba0401a4; (* adcs   x4, x13, x4 *)
  0xa9012c28; (* stp    x8, x11, [x1, #16] *)
  0xba0c026d; (* adcs   x13, x19, x12 *)
  0xba0c01ce; (* adcs   x14, x14, x12 *)
  0x9a0c01ef; (* adc    x15, x15, x12 *)
  0xaa0403ec; (* mov    x12, x4 *)
  0xd100077b; (* sub    x27, x27, #0x1 *)
  0xb5ffed5b; (* cbnz   x27, 29c <bignum_emontredc_8n_neon_maddloop_neon> *)
  0xa9424c31; (* ldp    x17, x19, [x1, #32] *)
  0xa9435434; (* ldp    x20, x21, [x1, #48] *)
  0xa9417ffa; (* ldp    x26, xzr, [sp, #16] *)
  0xab1c039f; (* cmn    x28, x28 *)
  0xba0c0231; (* adcs   x17, x17, x12 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xba0f02b5; (* adcs   x21, x21, x15 *)
  0xda9f33fc; (* csetm  x28, cs  // cs = hs, nlast *)
  0xa9024c31; (* stp    x17, x19, [x1, #32] *)
  0xa9035434; (* stp    x20, x21, [x1, #48] *)
  0xcb000021; (* sub    x1, x1, x0 *)
  0xcb000042; (* sub    x2, x2, x0 *)
  0x91008021; (* add    x1, x1, #0x20 *)
  0xd100075a; (* sub    x26, x26, #0x1 *)
  0xa9017ffa; (* stp    x26, xzr, [sp, #16] *)
  0xf94007fe; (* ldr    x30, [sp, #8] *)
];;

let outerloop_step2_mc = define_mc_from_intlist "outerloop_step2_mc" outerloop_step2_ops;;

let OUTERLOOP_STEP2_EXEC = ARM_MK_EXEC_RULE outerloop_step2_mc;;

let outerloop_step2_labels = [
  ("maddloop_neon", (0x29c, new_definition `outerloop_step2_label_maddloop_neon = 0x29c`));
  (* maddloop_rotated is a virtually existing label *)
  ("maddloop_rotated", (0x34c, new_definition `outerloop_step2_label_maddloop_rotated = 0x34c`));
  ("inner_loop_postamble", (0x4f8, new_definition `outerloop_step2_label_inner_loop_postamble = 0x4f8`));
];;


let outerloop_step3_ops = [
  0xf94003e3; (* ldr    x3, [sp] *)
  0xa9404c31; (* ldp    x17, x19, [x1] *)
  0xa9415434; (* ldp    x20, x21, [x1, #16] *)
  0xa9402448; (* ldp    x8, x9, [x2] *)
  0xa9412c4a; (* ldp    x10, x11, [x2, #16] *)
  0x3dc00455; (* ldr    q21, [x2, #16] *)
  0x9b037e24; (* mul    x4, x17, x3 *)
  0x4e080c80; (* dup    v0.2d, x4 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58080; (* umlal  v0.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083c0e; (* mov    x14, v0.d[0] *)
  0x4e183c0f; (* mov    x15, v0.d[1] *)
  0x9b087c8c; (* mul    x12, x4, x8 *)
  0xab0c0231; (* adds   x17, x17, x12 *)
  0x9bc87c8c; (* umulh  x12, x4, x8 *)
  0x9b097c8d; (* mul    x13, x4, x9 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0x9bc97c8d; (* umulh  x13, x4, x9 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xba0f02b5; (* adcs   x21, x21, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f6; (* adc    x22, xzr, xzr *)
  0xab0c0273; (* adds   x19, x19, x12 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0x9a0f02d6; (* adc    x22, x22, x15 *)
  0x9b037e65; (* mul    x5, x19, x3 *)
  0x4e080ca0; (* dup    v0.2d, x5 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605400; (* shl    v0.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58080; (* umlal  v0.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083c0e; (* mov    x14, v0.d[0] *)
  0x4e183c0f; (* mov    x15, v0.d[1] *)
  0x9b087cac; (* mul    x12, x5, x8 *)
  0xab0c0273; (* adds   x19, x19, x12 *)
  0x9bc87cac; (* umulh  x12, x5, x8 *)
  0x9b097cad; (* mul    x13, x5, x9 *)
  0xba0d0294; (* adcs   x20, x20, x13 *)
  0x9bc97cad; (* umulh  x13, x5, x9 *)
  0xba0e02b5; (* adcs   x21, x21, x14 *)
  0xba0f02d6; (* adcs   x22, x22, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f7; (* adc    x23, xzr, xzr *)
  0xab0c0294; (* adds   x20, x20, x12 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0xba0e02d6; (* adcs   x22, x22, x14 *)
  0x9a0f02f7; (* adc    x23, x23, x15 *)
  0xa9001424; (* stp    x4, x5, [x1] *)
  0x9b037e86; (* mul    x6, x20, x3 *)
  0x4e080cc0; (* dup    v0.2d, x6 *)
  0x4e955aa3; (* uzp2   v3.4s, v21.4s, v21.4s *)
  0x0ea12804; (* xtn    v4.2s, v0.2d *)
  0x0ea12aa5; (* xtn    v5.2s, v21.2d *)
  0x4ea00abc; (* rev64  v28.4s, v21.4s *)
  0x2ea5c086; (* umull  v6.2d, v4.2s, v5.2s *)
  0x2ea3c087; (* umull  v7.2d, v4.2s, v3.2s *)
  0x4e805810; (* uzp2   v16.4s, v0.4s, v0.4s *)
  0x4ea09f80; (* mul    v0.4s, v28.4s, v0.4s *)
  0x6f6014c7; (* usra   v7.2d, v6.2d, #32 *)
  0x2ea3c201; (* umull  v1.2d, v16.2s, v3.2s *)
  0x6ea02800; (* uaddlp v0.2d, v0.4s *)
  0x4e3d1ce2; (* and    v2.16b, v7.16b, v29.16b *)
  0x2ea58202; (* umlal  v2.2d, v16.2s, v5.2s *)
  0x4f605415; (* shl    v21.2d, v0.2d, #32 *)
  0x6f6014e1; (* usra   v1.2d, v7.2d, #32 *)
  0x2ea58095; (* umlal  v21.2d, v4.2s, v5.2s *)
  0x6f601441; (* usra   v1.2d, v2.2d, #32 *)
  0x4e083eae; (* mov    x14, v21.d[0] *)
  0x4e183eaf; (* mov    x15, v21.d[1] *)
  0x9b087ccc; (* mul    x12, x6, x8 *)
  0xab0c0294; (* adds   x20, x20, x12 *)
  0x9bc87ccc; (* umulh  x12, x6, x8 *)
  0x9b097ccd; (* mul    x13, x6, x9 *)
  0xba0d02b5; (* adcs   x21, x21, x13 *)
  0x9bc97ccd; (* umulh  x13, x6, x9 *)
  0xba0e02d6; (* adcs   x22, x22, x14 *)
  0xba0f02f7; (* adcs   x23, x23, x15 *)
  0x4e083c2e; (* mov    x14, v1.d[0] *)
  0x4e183c2f; (* mov    x15, v1.d[1] *)
  0x9a1f03f8; (* adc    x24, xzr, xzr *)
  0xab0c02b5; (* adds   x21, x21, x12 *)
  0x9b037ea7; (* mul    x7, x21, x3 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0xba0e02f7; (* adcs   x23, x23, x14 *)
  0x9a0f0318; (* adc    x24, x24, x15 *)
  0xa9011c26; (* stp    x6, x7, [x1, #16] *)
  0x9b087cec; (* mul    x12, x7, x8 *)
  0x9b097ced; (* mul    x13, x7, x9 *)
  0x9b0a7cee; (* mul    x14, x7, x10 *)
  0x9b0b7cef; (* mul    x15, x7, x11 *)
  0xab0c02b5; (* adds   x21, x21, x12 *)
  0x9bc87cec; (* umulh  x12, x7, x8 *)
  0xba0d02d6; (* adcs   x22, x22, x13 *)
  0x9bc97ced; (* umulh  x13, x7, x9 *)
  0xba0e02f7; (* adcs   x23, x23, x14 *)
  0x9bca7cee; (* umulh  x14, x7, x10 *)
  0xba0f0318; (* adcs   x24, x24, x15 *)
  0x9bcb7cef; (* umulh  x15, x7, x11 *)
  0x9a1f03f9; (* adc    x25, xzr, xzr *)
  0xab0c02cc; (* adds   x12, x22, x12 *)
  0xba0d02ed; (* adcs   x13, x23, x13 *)
  0xba0e030e; (* adcs   x14, x24, x14 *)
  0x9a0f032f; (* adc    x15, x25, x15 *)
  0xd345fc1b; (* lsr    x27, x0, #5 *)
  0xd100077b; (* sub    x27, x27, #0x1 *)
  0x3dc00034; (* ldr    q20, [x1] *)
  0x3dc00435; (* ldr    q21, [x1, #16] *)
  0xeb050090; (* subs   x16, x4, x5 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9026bf0; (* stp    x16, x26, [sp, #32] *)
  0xeb060090; (* subs   x16, x4, x6 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9036bf0; (* stp    x16, x26, [sp, #48] *)
  0xeb070090; (* subs   x16, x4, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9046bf0; (* stp    x16, x26, [sp, #64] *)
  0xeb0600b0; (* subs   x16, x5, x6 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9056bf0; (* stp    x16, x26, [sp, #80] *)
  0xeb0700b0; (* subs   x16, x5, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9066bf0; (* stp    x16, x26, [sp, #96] *)
  0xeb0700d0; (* subs   x16, x6, x7 *)
  0xda902610; (* cneg   x16, x16, cc  // cc = lo, ul, last *)
  0xda9f23fa; (* csetm  x26, cc  // cc = lo, ul, last *)
  0xa9076bf0; (* stp    x16, x26, [sp, #112] *)
  0x4e945a9e; (* uzp2   v30.4s, v20.4s, v20.4s *)
  0x0ea12a9c; (* xtn    v28.2s, v20.2d *)
  0x4ea00a91; (* rev64  v17.4s, v20.4s *)
  0x4e955ab2; (* uzp2   v18.4s, v21.4s, v21.4s *)
  0x0ea12ab3; (* xtn    v19.2s, v21.2d *)
  0x4ea00ab4; (* rev64  v20.4s, v21.4s *)
  0x3cc20c4e; (* ldr    q14, [x2, #32]! *)
  0x3dc00459; (* ldr    q25, [x2, #16] *)
  0x0ea129d5; (* xtn    v21.2s, v14.2d *)
  0x0ea12b3f; (* xtn    v31.2s, v25.2d *)
  0x4e995b38; (* uzp2   v24.4s, v25.4s, v25.4s *)
  0x2ebec2a5; (* umull  v5.2d, v21.2s, v30.2s *)
  0x2eb2c3f0; (* umull  v16.2d, v31.2s, v18.2s *)
  0x2ebcc2ad; (* umull  v13.2d, v21.2s, v28.2s *)
  0x4e8e59ca; (* uzp2   v10.4s, v14.4s, v14.4s *)
  0x2eb3c3e1; (* umull  v1.2d, v31.2s, v19.2s *)
  0x4eb99e86; (* mul    v6.4s, v20.4s, v25.4s *)
  0x2eb2c300; (* umull  v0.2d, v24.2s, v18.2s *)
  0x6f6015a5; (* usra   v5.2d, v13.2d, #32 *)
  0x2ebec142; (* umull  v2.2d, v10.2s, v30.2s *)
  0x6f601430; (* usra   v16.2d, v1.2d, #32 *)
  0x6ea028cd; (* uaddlp v13.2d, v6.4s *)
  0x4e3d1ca7; (* and    v7.16b, v5.16b, v29.16b *)
  0x6f6014a2; (* usra   v2.2d, v5.2d, #32 *)
  0x4e3d1e19; (* and    v25.16b, v16.16b, v29.16b *)
  0x2ebc8147; (* umlal  v7.2d, v10.2s, v28.2s *)
  0x6f601600; (* usra   v0.2d, v16.2d, #32 *)
  0x4f6055b0; (* shl    v16.2d, v13.2d, #32 *)
  0x2eb38319; (* umlal  v25.2d, v24.2s, v19.2s *)
  0x6f6014e2; (* usra   v2.2d, v7.2d, #32 *)
  0x2eb383f0; (* umlal  v16.2d, v31.2s, v19.2s *)
  0x4eae9e27; (* mul    v7.4s, v17.4s, v14.4s *)
  0x6f601720; (* usra   v0.2d, v25.2d, #32 *)
  0x6ea028ea; (* uaddlp v10.2d, v7.4s *)
  0x4e183c43; (* mov    x3, v2.d[1] *)
  0x4e083c1a; (* mov    x26, v0.d[0] *)
  0xa94353e9; (* ldp    x9, x20, [sp, #48] *)
  0x4f60554f; (* shl    v15.2d, v10.2d, #32 *)
  0x2ebc82af; (* umlal  v15.2d, v21.2s, v28.2s *)
  0x4e083e11; (* mov    x17, v16.d[0] *)
  0x4e083c50; (* mov    x16, v2.d[0] *)
  0xa94217e6; (* ldp    x6, x5, [sp, #32] *)
  0xa94167c7; (* ldp    x7, x25, [x30, #16] *)
  0x4e183df5; (* mov    x21, v15.d[1] *)
  0x4e183e17; (* mov    x23, v16.d[1] *)
  0xa8c62bd8; (* ldp    x24, x10, [x30], #96 *)
  0x9b077d36; (* mul    x22, x9, x7 *)
  0xca19028b; (* eor    x11, x20, x25 *)
  0xa9c27434; (* ldp    x20, x29, [x1, #32]! *)
  0x9bc77d28; (* umulh  x8, x9, x7 *)
  0xca0a00b3; (* eor    x19, x5, x10 *)
  0xab1002b9; (* adds   x25, x21, x16 *)
  0x4e183c10; (* mov    x16, v0.d[1] *)
  0xa9411c24; (* ldp    x4, x7, [x1, #16] *)
  0xba030235; (* adcs   x21, x17, x3 *)
  0xca0b02d6; (* eor    x22, x22, x11 *)
  0xba1a02f7; (* adcs   x23, x23, x26 *)
  0x9a1f0211; (* adc    x17, x16, xzr *)
  0xab140190; (* adds   x16, x12, x20 *)
  0x9b187cc5; (* mul    x5, x6, x24 *)
  0xba1d01a9; (* adcs   x9, x13, x29 *)
  0x4e083dfd; (* mov    x29, v15.d[0] *)
  0xba0401c4; (* adcs   x4, x14, x4 *)
  0xa94737ea; (* ldp    x10, x13, [sp, #112] *)
  0x9bd87cd4; (* umulh  x20, x6, x24 *)
  0xba0701f8; (* adcs   x24, x15, x7 *)
  0xa97f1fcc; (* ldp    x12, x7, [x30, #-16] *)
  0x9a1f03e6; (* adc    x6, xzr, xzr *)
  0xab1d032e; (* adds   x14, x25, x29 *)
  0xca0b010f; (* eor    x15, x8, x11 *)
  0xba1902b9; (* adcs   x25, x21, x25 *)
  0xba1502e8; (* adcs   x8, x23, x21 *)
  0xca0701a7; (* eor    x7, x13, x7 *)
  0xba170237; (* adcs   x23, x17, x23 *)
  0xca1300b5; (* eor    x21, x5, x19 *)
  0x9a1103ed; (* adc    x13, xzr, x17 *)
  0xab1d0331; (* adds   x17, x25, x29 *)
  0xba0e0105; (* adcs   x5, x8, x14 *)
  0xba1902f9; (* adcs   x25, x23, x25 *)
  0xba0801a8; (* adcs   x8, x13, x8 *)
  0xba1703f7; (* adcs   x23, xzr, x23 *)
  0x9a0d03ed; (* adc    x13, xzr, x13 *)
  0xab1003bd; (* adds   x29, x29, x16 *)
  0x9b0c7d50; (* mul    x16, x10, x12 *)
  0xba0901c9; (* adcs   x9, x14, x9 *)
  0xba040231; (* adcs   x17, x17, x4 *)
  0x9bcc7d4c; (* umulh  x12, x10, x12 *)
  0xba1800aa; (* adcs   x10, x5, x24 *)
  0xca070205; (* eor    x5, x16, x7 *)
  0xa97e3bd0; (* ldp    x16, x14, [x30, #-32] *)
  0xba060326; (* adcs   x6, x25, x6 *)
  0xca130298; (* eor    x24, x20, x19 *)
  0xba1f0104; (* adcs   x4, x8, xzr *)
  0xa94667f4; (* ldp    x20, x25, [sp, #96] *)
  0xba1f02f7; (* adcs   x23, x23, xzr *)
  0x9a1f01a8; (* adc    x8, x13, xzr *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xba050084; (* adcs   x4, x4, x5 *)
  0xca070185; (* eor    x5, x12, x7 *)
  0xba0502f7; (* adcs   x23, x23, x5 *)
  0x9b107e8c; (* mul    x12, x20, x16 *)
  0x9a070105; (* adc    x5, x8, x7 *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xba150135; (* adcs   x21, x9, x21 *)
  0xca0e0328; (* eor    x8, x25, x14 *)
  0xba18022d; (* adcs   x13, x17, x24 *)
  0xa900543d; (* stp    x29, x21, [x1] *)
  0x9bd07e94; (* umulh  x20, x20, x16 *)
  0xba130151; (* adcs   x17, x10, x19 *)
  0xa94463fd; (* ldp    x29, x24, [sp, #64] *)
  0xba1300d9; (* adcs   x25, x6, x19 *)
  0xa97c57c6; (* ldp    x6, x21, [x30, #-64] *)
  0xca08018a; (* eor    x10, x12, x8 *)
  0xba130089; (* adcs   x9, x4, x19 *)
  0xa97d43c4; (* ldp    x4, x16, [x30, #-48] *)
  0xba1302ec; (* adcs   x12, x23, x19 *)
  0x9a1300a5; (* adc    x5, x5, x19 *)
  0xb100051f; (* cmn    x8, #0x1 *)
  0xa9454fe7; (* ldp    x7, x19, [sp, #80] *)
  0xba0a032e; (* adcs   x14, x25, x10 *)
  0x9b067fb9; (* mul    x25, x29, x6 *)
  0xca080294; (* eor    x20, x20, x8 *)
  0xba140137; (* adcs   x23, x9, x20 *)
  0xca150318; (* eor    x24, x24, x21 *)
  0xba08018c; (* adcs   x12, x12, x8 *)
  0x9a0800aa; (* adc    x10, x5, x8 *)
  0xb100057f; (* cmn    x11, #0x1 *)
  0x9bc67fa5; (* umulh  x5, x29, x6 *)
  0xba1601a8; (* adcs   x8, x13, x22 *)
  0xca18032d; (* eor    x13, x25, x24 *)
  0xba0f023d; (* adcs   x29, x17, x15 *)
  0xba0b01d6; (* adcs   x22, x14, x11 *)
  0xba0b02f5; (* adcs   x21, x23, x11 *)
  0x9b047cf7; (* mul    x23, x7, x4 *)
  0xba0b018e; (* adcs   x14, x12, x11 *)
  0xca10026c; (* eor    x12, x19, x16 *)
  0x9a0b014f; (* adc    x15, x10, x11 *)
  0xb100071f; (* cmn    x24, #0x1 *)
  0xca1800b3; (* eor    x19, x5, x24 *)
  0xba0d03ab; (* adcs   x11, x29, x13 *)
  0x9bc47cfd; (* umulh  x29, x7, x4 *)
  0xba1302cd; (* adcs   x13, x22, x19 *)
  0xba1802b3; (* adcs   x19, x21, x24 *)
  0xca0c02f6; (* eor    x22, x23, x12 *)
  0xba1801ce; (* adcs   x14, x14, x24 *)
  0x9a1801ef; (* adc    x15, x15, x24 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xba16016b; (* adcs   x11, x11, x22 *)
  0xca0c03a4; (* eor    x4, x29, x12 *)
  0xba0401a4; (* adcs   x4, x13, x4 *)
  0xa9012c28; (* stp    x8, x11, [x1, #16] *)
  0xba0c026d; (* adcs   x13, x19, x12 *)
  0xba0c01ce; (* adcs   x14, x14, x12 *)
  0x9a0c01ef; (* adc    x15, x15, x12 *)
  0xaa0403ec; (* mov    x12, x4 *)
  0x3cc20c4e; (* ldr    q14, [x2, #32]! *)
  0x3dc00459; (* ldr    q25, [x2, #16] *)
  0x0ea129d5; (* xtn    v21.2s, v14.2d *)
  0x0ea12b3f; (* xtn    v31.2s, v25.2d *)
  0x4e995b38; (* uzp2   v24.4s, v25.4s, v25.4s *)
  0x2ebec2a5; (* umull  v5.2d, v21.2s, v30.2s *)
  0x2eb2c3f0; (* umull  v16.2d, v31.2s, v18.2s *)
  0x2ebcc2ad; (* umull  v13.2d, v21.2s, v28.2s *)
  0x4e8e59ca; (* uzp2   v10.4s, v14.4s, v14.4s *)
  0x2eb3c3e1; (* umull  v1.2d, v31.2s, v19.2s *)
  0x4eb99e86; (* mul    v6.4s, v20.4s, v25.4s *)
  0x2eb2c300; (* umull  v0.2d, v24.2s, v18.2s *)
  0x6f6015a5; (* usra   v5.2d, v13.2d, #32 *)
  0x2ebec142; (* umull  v2.2d, v10.2s, v30.2s *)
  0x6f601430; (* usra   v16.2d, v1.2d, #32 *)
  0x6ea028cd; (* uaddlp v13.2d, v6.4s *)
  0x4e3d1ca7; (* and    v7.16b, v5.16b, v29.16b *)
  0x6f6014a2; (* usra   v2.2d, v5.2d, #32 *)
  0x4e3d1e19; (* and    v25.16b, v16.16b, v29.16b *)
  0x2ebc8147; (* umlal  v7.2d, v10.2s, v28.2s *)
  0x6f601600; (* usra   v0.2d, v16.2d, #32 *)
  0x4f6055b0; (* shl    v16.2d, v13.2d, #32 *)
  0x2eb38319; (* umlal  v25.2d, v24.2s, v19.2s *)
  0x6f6014e2; (* usra   v2.2d, v7.2d, #32 *)
  0x2eb383f0; (* umlal  v16.2d, v31.2s, v19.2s *)
  0x4eae9e27; (* mul    v7.4s, v17.4s, v14.4s *)
  0x6f601720; (* usra   v0.2d, v25.2d, #32 *)
  0x6ea028ea; (* uaddlp v10.2d, v7.4s *)
  0x4e183c43; (* mov    x3, v2.d[1] *)
  0x4e083c1a; (* mov    x26, v0.d[0] *)
  0xa94353e9; (* ldp    x9, x20, [sp, #48] *)
  0x4f60554f; (* shl    v15.2d, v10.2d, #32 *)
  0x2ebc82af; (* umlal  v15.2d, v21.2s, v28.2s *)
  0x4e083e11; (* mov    x17, v16.d[0] *)
  0x4e083c50; (* mov    x16, v2.d[0] *)
  0xa94217e6; (* ldp    x6, x5, [sp, #32] *)
  0xa94167c7; (* ldp    x7, x25, [x30, #16] *)
  0x4e183df5; (* mov    x21, v15.d[1] *)
  0x4e183e17; (* mov    x23, v16.d[1] *)
  0xa8c62bd8; (* ldp    x24, x10, [x30], #96 *)
  0x9b077d36; (* mul    x22, x9, x7 *)
  0xca19028b; (* eor    x11, x20, x25 *)
  0xa9c27434; (* ldp    x20, x29, [x1, #32]! *)
  0x9bc77d28; (* umulh  x8, x9, x7 *)
  0xd100077b; (* sub    x27, x27, #0x1 *)
  0xb5ffed5b; (* cbnz   x27, 350 <bignum_emontredc_8n_neon_maddloop_neon> *)
  0xca0a00b3; (* eor    x19, x5, x10 *)
  0xab1002b9; (* adds   x25, x21, x16 *)
  0x4e183c10; (* mov    x16, v0.d[1] *)
  0xa9411c24; (* ldp    x4, x7, [x1, #16] *)
  0xba030235; (* adcs   x21, x17, x3 *)
  0xca0b02d6; (* eor    x22, x22, x11 *)
  0xba1a02f7; (* adcs   x23, x23, x26 *)
  0x9a1f0211; (* adc    x17, x16, xzr *)
  0xab140190; (* adds   x16, x12, x20 *)
  0x9b187cc5; (* mul    x5, x6, x24 *)
  0xba1d01a9; (* adcs   x9, x13, x29 *)
  0x4e083dfd; (* mov    x29, v15.d[0] *)
  0xba0401c4; (* adcs   x4, x14, x4 *)
  0xa94737ea; (* ldp    x10, x13, [sp, #112] *)
  0x9bd87cd4; (* umulh  x20, x6, x24 *)
  0xba0701f8; (* adcs   x24, x15, x7 *)
  0xa97f1fcc; (* ldp    x12, x7, [x30, #-16] *)
  0x9a1f03e6; (* adc    x6, xzr, xzr *)
  0xab1d032e; (* adds   x14, x25, x29 *)
  0xca0b010f; (* eor    x15, x8, x11 *)
  0xba1902b9; (* adcs   x25, x21, x25 *)
  0xba1502e8; (* adcs   x8, x23, x21 *)
  0xca0701a7; (* eor    x7, x13, x7 *)
  0xba170237; (* adcs   x23, x17, x23 *)
  0xca1300b5; (* eor    x21, x5, x19 *)
  0x9a1103ed; (* adc    x13, xzr, x17 *)
  0xab1d0331; (* adds   x17, x25, x29 *)
  0xba0e0105; (* adcs   x5, x8, x14 *)
  0xba1902f9; (* adcs   x25, x23, x25 *)
  0xba0801a8; (* adcs   x8, x13, x8 *)
  0xba1703f7; (* adcs   x23, xzr, x23 *)
  0x9a0d03ed; (* adc    x13, xzr, x13 *)
  0xab1003bd; (* adds   x29, x29, x16 *)
  0x9b0c7d50; (* mul    x16, x10, x12 *)
  0xba0901c9; (* adcs   x9, x14, x9 *)
  0xba040231; (* adcs   x17, x17, x4 *)
  0x9bcc7d4c; (* umulh  x12, x10, x12 *)
  0xba1800aa; (* adcs   x10, x5, x24 *)
  0xca070205; (* eor    x5, x16, x7 *)
  0xa97e3bd0; (* ldp    x16, x14, [x30, #-32] *)
  0xba060326; (* adcs   x6, x25, x6 *)
  0xca130298; (* eor    x24, x20, x19 *)
  0xba1f0104; (* adcs   x4, x8, xzr *)
  0xa94667f4; (* ldp    x20, x25, [sp, #96] *)
  0xba1f02f7; (* adcs   x23, x23, xzr *)
  0x9a1f01a8; (* adc    x8, x13, xzr *)
  0xb10004ff; (* cmn    x7, #0x1 *)
  0xba050084; (* adcs   x4, x4, x5 *)
  0xca070185; (* eor    x5, x12, x7 *)
  0xba0502f7; (* adcs   x23, x23, x5 *)
  0x9b107e8c; (* mul    x12, x20, x16 *)
  0x9a070105; (* adc    x5, x8, x7 *)
  0xb100067f; (* cmn    x19, #0x1 *)
  0xba150135; (* adcs   x21, x9, x21 *)
  0xca0e0328; (* eor    x8, x25, x14 *)
  0xba18022d; (* adcs   x13, x17, x24 *)
  0xa900543d; (* stp    x29, x21, [x1] *)
  0x9bd07e94; (* umulh  x20, x20, x16 *)
  0xba130151; (* adcs   x17, x10, x19 *)
  0xa94463fd; (* ldp    x29, x24, [sp, #64] *)
  0xba1300d9; (* adcs   x25, x6, x19 *)
  0xa97c57c6; (* ldp    x6, x21, [x30, #-64] *)
  0xca08018a; (* eor    x10, x12, x8 *)
  0xba130089; (* adcs   x9, x4, x19 *)
  0xa97d43c4; (* ldp    x4, x16, [x30, #-48] *)
  0xba1302ec; (* adcs   x12, x23, x19 *)
  0x9a1300a5; (* adc    x5, x5, x19 *)
  0xb100051f; (* cmn    x8, #0x1 *)
  0xa9454fe7; (* ldp    x7, x19, [sp, #80] *)
  0xba0a032e; (* adcs   x14, x25, x10 *)
  0x9b067fb9; (* mul    x25, x29, x6 *)
  0xca080294; (* eor    x20, x20, x8 *)
  0xba140137; (* adcs   x23, x9, x20 *)
  0xca150318; (* eor    x24, x24, x21 *)
  0xba08018c; (* adcs   x12, x12, x8 *)
  0x9a0800aa; (* adc    x10, x5, x8 *)
  0xb100057f; (* cmn    x11, #0x1 *)
  0x9bc67fa5; (* umulh  x5, x29, x6 *)
  0xba1601a8; (* adcs   x8, x13, x22 *)
  0xca18032d; (* eor    x13, x25, x24 *)
  0xba0f023d; (* adcs   x29, x17, x15 *)
  0xba0b01d6; (* adcs   x22, x14, x11 *)
  0xba0b02f5; (* adcs   x21, x23, x11 *)
  0x9b047cf7; (* mul    x23, x7, x4 *)
  0xba0b018e; (* adcs   x14, x12, x11 *)
  0xca10026c; (* eor    x12, x19, x16 *)
  0x9a0b014f; (* adc    x15, x10, x11 *)
  0xb100071f; (* cmn    x24, #0x1 *)
  0xca1800b3; (* eor    x19, x5, x24 *)
  0xba0d03ab; (* adcs   x11, x29, x13 *)
  0x9bc47cfd; (* umulh  x29, x7, x4 *)
  0xba1302cd; (* adcs   x13, x22, x19 *)
  0xba1802b3; (* adcs   x19, x21, x24 *)
  0xca0c02f6; (* eor    x22, x23, x12 *)
  0xba1801ce; (* adcs   x14, x14, x24 *)
  0x9a1801ef; (* adc    x15, x15, x24 *)
  0xb100059f; (* cmn    x12, #0x1 *)
  0xba16016b; (* adcs   x11, x11, x22 *)
  0xca0c03a4; (* eor    x4, x29, x12 *)
  0xba0401a4; (* adcs   x4, x13, x4 *)
  0xa9012c28; (* stp    x8, x11, [x1, #16] *)
  0xba0c026d; (* adcs   x13, x19, x12 *)
  0xba0c01ce; (* adcs   x14, x14, x12 *)
  0x9a0c01ef; (* adc    x15, x15, x12 *)
  0xaa0403ec; (* mov    x12, x4 *)
  0xa9424c31; (* ldp    x17, x19, [x1, #32] *)
  0xa9435434; (* ldp    x20, x21, [x1, #48] *)
  0xa9417ffa; (* ldp    x26, xzr, [sp, #16] *)
  0xab1c039f; (* cmn    x28, x28 *)
  0xba0c0231; (* adcs   x17, x17, x12 *)
  0xba0d0273; (* adcs   x19, x19, x13 *)
  0xba0e0294; (* adcs   x20, x20, x14 *)
  0xba0f02b5; (* adcs   x21, x21, x15 *)
  0xda9f33fc; (* csetm  x28, cs  // cs = hs, nlast *)
  0xa9024c31; (* stp    x17, x19, [x1, #32] *)
  0xa9035434; (* stp    x20, x21, [x1, #48] *)
  0xcb000021; (* sub    x1, x1, x0 *)
  0xcb000042; (* sub    x2, x2, x0 *)
  0x91008021; (* add    x1, x1, #0x20 *)
  0xd100075a; (* sub    x26, x26, #0x1 *)
  0xa9017ffa; (* stp    x26, xzr, [sp, #16] *)
  0xf94007fe; (* ldr    x30, [sp, #8] *)
];;


let outerloop_step3_mc = define_mc_from_intlist "outerloop_step3_mc" outerloop_step3_ops;;

let OUTERLOOP_STEP3_EXEC = ARM_MK_EXEC_RULE outerloop_step3_mc;;

let outerloop_step3_labels = [
  ("maddloop_prologue", (0x2a0, new_definition `outerloop_step3_label_maddloop_prologue = 0x2a0`));
  ("maddloop_neon", (0x350, new_definition `outerloop_step3_label_maddloop_neon = 0x350`));
  ("inner_loop_postamble", (0x5ac, new_definition `outerloop_step3_label_inner_loop_postamble = 0x5ac`));
  (* inner_loop_postamble_noepilogue is a virtually existing label *)
  ("inner_loop_postamble_noepilogue",
    (0x750, new_definition `outerloop_step3_label_inner_loop_postamble_noepilogue = 0x750`))
];;


(* All memory equivalences will look the same, except equivalence of
   bignum_emontredc_8n's outerloop and outerloop of step1 because
   bignum_emontredc_8n does not have m_precalc and step1 stores precalculated
   differences in sp. *)

let eq_mems =
  list_mk_gabs ([`z:int64`;`m:int64`;`sp:int64`;`m_precalc:int64`;`k:num`;
                `(s1,s1'):armstate#armstate`],
    `(exists a. bignum_from_memory (z,k+4) s1  = a /\
                bignum_from_memory (z,k+4) s1' = a) /\
     (exists a. bignum_from_memory (m,k) s1  = a /\
                bignum_from_memory (m,k) s1' = a) /\
     (exists a. bignum_from_memory (sp,1) s1 = a /\
                 bignum_from_memory (sp,1) s1' = a) /\
     (exists a. bignum_from_memory (word_add sp (word 32),12) s1 = a /\
                 bignum_from_memory (word_add sp (word 32),12) s1' = a) /\
     (exists a. bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1 = a /\
                bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1' = a)`);;

let replace_eq_regs eq_regs t =
  vsubst [eq_regs,mk_var("eq_regs", type_of eq_regs)] t;;

let replace_eq_mems_regs eq_regs t =
  vsubst [eq_mems,mk_var("eq_mems", type_of eq_mems);
          eq_regs,mk_var("eq_regs", type_of eq_regs)] t;;

(* Given two equivalence theorems equiv_th1 and equiv_th2 where
   - equiv_th1's output state equality uses definition equiv_th1_eqout
   - equiv_th2's input state equality uses definition equiv_th2_eqin
   This tries to enrich the precondition and postcondition of equiv_th1
   by adding equivalences between registers that appear in equiv_th2
   but not in equiv_th1.
   The returned theorem is equiv_th1 with such extension applied.
   In principle, the extended equiv_th1 and original equiv_th2 should
   be able to be sequentially composed by prove_equiv_seq_composition. *)

let extend_first_equiv_for_seq_composition equiv_th1 equiv_th2
    equiv_th1_eqout equiv_th2_eqin =
  let get_regs equiv_th equiv_eq_th is_pre =
    let unfolded_equiv_th = REWRITE_RULE[equiv_eq_th]equiv_th in
    let ensures2_const,args =
      let c = (concl unfolded_equiv_th) in
      let c = if is_forall c then snd (strip_forall c) else c in
      let c = if is_imp c then snd (dest_imp c) else c in
      strip_comb c in
    if name_of ensures2_const <> "ensures2" then failwith "" else
    let body = if is_pre then List.nth args 1 else List.nth args 2 in
    let ts = find_terms (fun t ->
      is_comb t && name_of (fst (dest_comb t)) = "mk_equiv_regs")
      body in
    let equiv_regs = List.concat_map (fun t -> let regs = snd (dest_comb t) in
      dest_list regs) ts in
    (* mk_equiv_regs2 can specify equivalent regs too. *)
    let ts' = find_terms (fun t ->
      is_comb t && let t = fst (dest_comb t) in
      is_comb t && name_of (fst (dest_comb t)) = "mk_equiv_regs2")
      body in
    let equiv_regs2 = List.concat_map (fun t ->
      let _,(ls1::ls2::[]) = strip_comb t in
      let regs1,regs2 = dest_list ls1,dest_list ls2 in
      let pairs = zip regs1 regs2 in
      map fst (filter (fun (t1,t2) -> t1 = t2) pairs)) ts' in

    (* some registers that are read. *)
    let ts2 = find_terms (fun t ->
      is_comb t && name_of (fst (dest_comb t)) = "read")
      body in
    let specified_regs = List.filter_map (fun t ->
      let r = snd (dest_comb t) in if is_const r then Some r else None)
      ts2 in
    (equiv_regs @ equiv_regs2,specified_regs) in

  let equiv_regs_out1,specified_regs_out1 =
      get_regs equiv_th1 equiv_th1_eqout false in
  let equiv_regs_in2,specified_regs_in2 =
      get_regs equiv_th2 equiv_th2_eqin true in

  let extra_regs = subtract (subtract equiv_regs_in2 equiv_regs_out1) specified_regs_out1 in
  let extra_regs_equiv = build_equiv_regs extra_regs in

  let the_goal =
    let s::s_final::s2::s_final2::[] = map (fun n -> mk_var (n,`:armstate`))
      ["s";  "s_final";"s2";"s_final2"] in
    let rel_maychange =
      let c = concl equiv_th1 in
      let e, args = strip_comb (snd (dest_imp (snd (strip_forall c)))) in
      List.nth args 3 in
    list_mk_forall([s;s_final;s2;s_final2],
      mk_imp (
        list_mk_comb (rel_maychange,[mk_pair(s,s2);mk_pair(s_final,s_final2)]),
        mk_eq(mk_comb(extra_regs_equiv,mk_pair(s,s2)),
              mk_comb(extra_regs_equiv,mk_pair(s_final,s_final2))))) in

  let helpful_thm = prove(the_goal,
    REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    INTRO_TAC "H1 H2" THEN
    MAP_EVERY (fun tm ->
      let l = list_mk_icomb "read" [tm;`s_final:armstate`] in
      let r = list_mk_icomb "read" [tm;`s:armstate`] in
      SUBGOAL_THEN (mk_eq (l,r)) ASSUME_TAC THENL [
        REMOVE_THEN "H1" MP_TAC THEN
        REWRITE_TAC[MAYCHANGE;SEQ_ID] THEN
        REWRITE_TAC[GSYM SEQ_ASSOC] THEN
        REWRITE_TAC[ASSIGNS_SEQ] THEN
        REWRITE_TAC[ASSIGNS_THM] THEN
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        CONV_TAC(LAND_CONV(DEPTH_CONV
        COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
        REFL_TAC;
        ALL_TAC
      ]) extra_regs THEN
    MAP_EVERY (fun tm ->
      let l = list_mk_icomb "read" [tm;`s_final2:armstate`] in
      let r = list_mk_icomb "read" [tm;`s2:armstate`] in
      SUBGOAL_THEN (mk_eq (l,r)) ASSUME_TAC THENL [
        REMOVE_THEN "H2" MP_TAC THEN
        REWRITE_TAC[MAYCHANGE;SEQ_ID] THEN
        REWRITE_TAC[GSYM SEQ_ASSOC] THEN
        REWRITE_TAC[ASSIGNS_SEQ] THEN
        REWRITE_TAC[ASSIGNS_THM] THEN
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        CONV_TAC(LAND_CONV(DEPTH_CONV
        COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
        REFL_TAC;
        ALL_TAC
      ]) extra_regs THEN
    ASM_REWRITE_TAC[mk_equiv_regs]) in


  let equiv_th1_ext =
    let thm_to_extend = equiv_th1 in
    let quants,body = strip_forall (concl thm_to_extend) in
    let body_l,body_r = dest_imp body in
    let ensures_const,(the_step::the_pre::the_post::other_args) =
      strip_comb body_r in
    let enhanced_pre =
      let a,b = dest_gabs the_pre in
      mk_gabs(a,mk_conj(
        mk_comb(the_pre,a),mk_comb(extra_regs_equiv,a))) in
    let enhanced_post =
      let a,b = dest_gabs the_post in
      mk_gabs(a,mk_conj(
        mk_comb(the_post,a),mk_comb(extra_regs_equiv,a))) in
    let new_ensures = list_mk_forall(quants,
      mk_imp(body_l,list_mk_comb(ensures_const,the_step::enhanced_pre::enhanced_post::other_args))) in

    REWRITE_RULE[] (prove(new_ensures,
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ENSURES2_CONJ_FRAME THEN
      CONJ_TAC THENL [
        MATCH_ACCEPT_TAC helpful_thm;

        REWRITE_TAC[LAMBDA_PAIR_THM] THEN
        ASM_MESON_TAC [thm_to_extend]
      ])) in

  equiv_th1_ext,extra_regs_equiv;;

(* ========================================================================= *)
(*                 Equivalence between Step 2 - Step 3                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Equivalence between the maddloop bodies, but after (k/4) - 2 iterations!  *)
(* maddloop_step2 will start in the middle of the loop body and stop there   *)
(* after the iterations. maddloop_step3 will start from the maddloop_neon    *)
(* label.                                                                    *)
(* ------------------------------------------------------------------------- *)

let step2_body_in_regs, step2_body_out_regs =
    get_input_output_regs (snd OUTERLOOP_STEP3_EXEC)
      [(fst (assoc "maddloop_neon" outerloop_step3_labels),
        fst (assoc "inner_loop_postamble" outerloop_step3_labels) - 4)];;

(* Build component equalities. *)
let step2_body_eq_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step2_body_eqin*)
  (subtract step2_body_in_regs [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

(* Build state equalities. *)
let step2_body_eqin = new_definition
  (replace_eq_mems_regs step2_body_eq_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step2_body_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X27 s1 = word (k DIV 4 - 1) /\ read X27 s1' = word (k DIV 4 - 2) /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word 32) /\ read X1 s1' = word_add z (word 32) /\
      read X2 s1 = word_add m (word 32) /\ read X2 s1' = word_add m (word 32) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word 96) /\
      read X30 s1' = word_add m_precalc (word 96) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let step2_body_eqout = new_definition
  (replace_eq_mems_regs step2_body_eq_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step2_body_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
     (read X27 s1 = word 1 /\
      read X27 s1' = word 0 /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * (k - 4))) /\
      read X1 s1' = word_add z (word (8 * (k - 4))) /\
      read X2 s1 = word_add m (word (8 * (k - 4))) /\
      read X2 s1' = word_add m (word (8 * (k - 4))) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      read X30 s1' = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let step2_body_maychanges = build_maychanges
    step2_body_out_regs `MAYCHANGE [
        memory :> bytes (z:int64,8 * (k + 4));
        memory :> bytes (sp:int64,128)]`;;

let equiv_goal1 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step2_mc; word pc2:int64,LENGTH outerloop_step3_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step2_body_eqin
    step2_body_eqout
    outerloop_step2_mc
    (fst (assoc "maddloop_rotated" outerloop_step2_labels))
    (fst (assoc "maddloop_rotated" outerloop_step2_labels))
    step2_body_maychanges
    outerloop_step3_mc
    (fst (assoc "maddloop_neon" outerloop_step3_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step3_labels))
    step2_body_maychanges
    `\(s:armstate). 151 * (k DIV 4 - 2)` `\(s:armstate). 151 * (k DIV 4 - 2)`;;


let MADDLOOP_STEP2_STEP3_EQUIV = prove(equiv_goal1,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP2_EXEC; fst OUTERLOOP_STEP3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k` ASSUME_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `3 <= k4` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN

  (* iterates 'k / 4 - 2' times, where k is the number of words in modulus *)
  ENSURES2_WHILE_PAUP_TAC `1` `k4 - 1:num`
    `pc+outerloop_step2_label_maddloop_rotated`
    `pc+outerloop_step2_label_maddloop_rotated`
    `pc2+outerloop_step3_label_maddloop_neon`
    `pc2+(outerloop_step3_label_inner_loop_postamble-4)`
    (replace_eq_mems_regs step2_body_eq_regs
    `\(i:num) s1 s1'.
      // loop counter
      read X27 s1 = word (k4 - i) /\
      read X27 s1' = word (k4 - (i + 1)) /\
      // pointers and constants
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * 4 * i)) /\
      read X1 s1' = word_add z (word (8 * 4 * i)) /\
      read X2 s1 = word_add m (word (8 * 4 * i)) /\
      read X2 s1' = word_add m (word (8 * 4 * i)) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * 12 * i)) /\
      read X30 s1' = word_add m_precalc (word (8 * 12 * i)) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // equalities
      eq_mems z m sp m_precalc (k:num) (s1,s1') /\
      eq_regs(s1,s1')`)
    `\(i:num) (s:armstate). T` `\(i:num) (s:armstate). T`
    `\(i:num). 151` (* include backedge *)
    `\(i:num). 150`
    (* pre steps *)`0` `0`
    (* post steps *)`0` `1`
    (* num backedges *)`0` `1`
  THEN SUBST1_TAC
    ((REWRITE_CONV (map (snd o snd) (outerloop_step2_labels @ outerloop_step3_labels))
      THENC NUM_REDUCE_CONV) `outerloop_step3_label_inner_loop_postamble-4`)
  THEN REWRITE_TAC (map (snd o snd) (outerloop_step2_labels @ outerloop_step3_labels))
  THEN REPEAT CONJ_TAC THENL [
    (* loop count which is k4-1 > 0. *)
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP DIVIDES_LE th)) THEN SIMPLE_ARITH_TAC;

    (* precond to loop entrance *)
    REWRITE_TAC[step2_body_eqin;MULT_0; WORD_ADD_0; SUB_0; ASSUME `k DIV 4 = k4`] THEN
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONJ_TAC THENL [
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
      REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* the loop body. lockstep simulation is needed. *)
    ALL_TAC;

    (* backedge. *)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    UNDISCH_THEN `k DIV 4 = k4` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE ([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES])) THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_RIGHT_TAC OUTERLOOP_STEP3_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `~(val (word (k4 - (i + 1)):int64) = 0)` MP_TAC THENL [
      IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    CONJ_TAC THENL [
      REPEAT (CONJ_TAC THENL
        [FIRST_X_ASSUM MATCH_ACCEPT_TAC ORELSE ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];
        ALL_TAC]) THEN
      REPEAT (CONJ_TAC THENL [
        REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC]) THEN
      REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* postcond! *)
    ASM_REWRITE_TAC[step2_body_eqout;SUB_REFL;MULT_0;mk_equiv_regs;
                    BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_RIGHT_TAC OUTERLOOP_STEP3_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    CONJ_TAC THENL [
      SUBGOAL_THEN `(val (word (k4 - (k4 - 1 + 1)):int64) = 0)`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [ SUBGOAL_THEN `k4 - (k4 - 1 + 1)=0` SUBST_ALL_TAC
        THENL [SIMPLE_ARITH_TAC;ALL_TAC]
        THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN
      REPLICATE_TAC 4 (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN

      SUBGOAL_THEN `k4 - (k4 - 1) = 1 /\ k4 - (k4 - 1 + 1) = 0 /\
                    8 * (k-4) = 8 * 4 * (k4-1)`
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* loop trip count, left prog *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC;

    (* loop trip count, right prog *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC
  ] THEN

  REPEAT STRIP_TAC THEN
  (* replace k DIV 4 with k4. *)
  FIND_ABBREV_THEN "k4" SUBST_ALL_TAC THEN
  FIND_ABBREV_THEN "k" (SUBST_ALL_TAC o GSYM) THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,i) s = ..
      2. bignum_from_memory (z+4*i,4) s = ..
      3. bignum_from_memory (z+4*(i+1),k+4-*(i+1)) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*i`;`4*(i+1)`]
      BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th ->
    MP_TAC (REWRITE_RULE[ARITH_RULE `4 * (i + 1) - 4 * i=4`] th)) THEN

  REWRITE_TAC([BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs]) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(i + 1) + 1 = i + 2` SUBST_ALL_TAC THENL [ARITH_TAC;ALL_TAC] THEN

  (* start *)
  ENSURES2_INIT_TAC "s0" "s0'" THEN

  RULE_ASSUM_TAC(CONV_RULE (DEPTH_CONV NUM_MULT_CONV)) THEN
  CONV_TAC (DEPTH_CONV NUM_MULT_CONV) THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* loop counter is larger than 0. *)
  SUBGOAL_THEN `1 <= (k4 - (i + 1))` (LABEL_TAC "HBOUND") THENL [
    UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;
    ALL_TAC
  ] THEN

  EQUIV_STEPS_TAC [("equal",0,105,0,105)] OUTERLOOP_STEP2_EXEC OUTERLOOP_STEP3_EXEC THEN
  (* backedge! *)
  ARM_N_STUTTER_LEFT_TAC OUTERLOOP_STEP2_EXEC [106;107] None THEN
  SUBGOAL_THEN `~(val (word_sub (word (k4 - i)) (word 1):int64) = 0)` MP_TAC THENL [
    REWRITE_TAC[VAL_EQ_0] THEN
    IMP_REWRITE_TAC[WORD_SUB2] THEN
    IMP_REWRITE_TAC[WORD_EQ_0;DIMINDEX_64] THEN
    REPEAT CONJ_TAC THENL [
      USE_THEN "HBOUND" MP_TAC THEN ARITH_TAC;
      UNDISCH_TAC `k4 < 2 EXP 59` THEN ARITH_TAC;
      USE_THEN "HBOUND" MP_TAC THEN ARITH_TAC
    ];

    DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN LABEL_TAC "HVALBOUND" th)
  ] THEN

  EQUIV_STEPS_TAC
    [("replace",108,109,106,107) (* use 'replace' because ldr's pointer writeback should not be abbreviated *);
    ("equal",109,147,107,145);
    ("replace",147,148,145,146);
    ("equal",148,150,146,148);
    ("replace",150,151,148,149);
    ("equal",151,152,149,150)] OUTERLOOP_STEP2_EXEC OUTERLOOP_STEP3_EXEC THEN
  ARM_N_STUTTER_RIGHT_TAC OUTERLOOP_STEP3_EXEC [151] "'" None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MESON[]`forall (a:A). exists x. a = x`] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; ARITH_RULE`8*4*z+32 = 8*4*(z+1)`;
                ARITH_RULE`8*12*z+96 = 8*12*(z+1)`] THEN
    REPEAT CONJ_TAC THENL [
      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      (* updates in zi': splitting now! *)
      REWRITE_TAC[ARITH_RULE`32=8*4`; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
              CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]
    ];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(* ------------------------------------------------------------------------- *)
(* Equivalence between the prologues only.                                   *)
(* ------------------------------------------------------------------------- *)

(* Building input state equiv. *)

let step2_prolog_in_regs, step2_prolog_out_regs =
  get_input_output_regs
    (snd OUTERLOOP_STEP3_EXEC)
    [(fst (assoc "maddloop_prologue" outerloop_step3_labels),
      fst (assoc "maddloop_neon" outerloop_step3_labels) - 4)];;

let step2_prolog_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear
     in step2_prolog_eqin*)
  (subtract step2_prolog_in_regs [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step2_prolog_eqin = new_definition
  (replace_eq_mems_regs step2_prolog_eqin_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step2_prolog_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (read X27 s1 = word (k DIV 4 - 1) /\ read X27 s1' = word (k DIV 4 - 2) /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = z /\ read X1 s1' = z /\
      read X2 s1 = m /\ read X2 s1' = m /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs (s1,s1'))`);;


(* Building output state equiv and maychange sets. *)

let step2_prolog_maychanges = build_maychanges
  step2_prolog_out_regs `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
        memory :> bytes (sp:int64,128)]`;;

let step2_prolog_eqout_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step2_prolog_eqout *)
  (subtract step2_prolog_out_regs [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step2_prolog_eqout = new_definition
  (replace_eq_mems_regs step2_prolog_eqout_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step2_prolog_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (read X27 s1 = word (k DIV 4 - 1) /\ read X27 s1' = word (k DIV 4 - 2) /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word 32) /\ read X1 s1' = word_add z (word 32) /\
      read X2 s1 = word_add m (word 32) /\ read X2 s1' = word_add m (word 32) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word 96) /\
      read X30 s1' = word_add m_precalc (word 96) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let equiv_goal2 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step2_mc; word pc2:int64,LENGTH outerloop_step3_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step2_prolog_eqin
    step2_prolog_eqout
    outerloop_step2_mc
    (fst (assoc "maddloop_neon" outerloop_step2_labels))
    (fst (assoc "maddloop_rotated" outerloop_step2_labels))
    step2_prolog_maychanges
    outerloop_step3_mc
    (fst (assoc "maddloop_prologue" outerloop_step3_labels))
    (fst (assoc "maddloop_neon" outerloop_step3_labels))
    step2_prolog_maychanges
    `\(s:armstate). 44` `\(s:armstate). 44`;;


let PROLOG_STEP2_STEP3_EQUIV = prove(equiv_goal2,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP2_EXEC; fst OUTERLOOP_STEP3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (** Initialize **)
  EQUIV_INITIATE_TAC step2_prolog_eqin THEN
  RULE_ASSUM_TAC(REWRITE_RULE ([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES])) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* prepare memory loads *)
  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k`
      (fun th -> SUBST_ALL_TAC (GSYM th) THEN LABEL_TAC "DO_NOT_CLEAR" th)
      THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* start *)
  EQUIV_STEPS_TAC [
      ("replace",0,1,0,1);("equal",1,39,1,39);("replace",39,40,39,40);
      ("replace",40,44,40,44)]
    OUTERLOOP_STEP2_EXEC OUTERLOOP_STEP3_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC([BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs;step2_prolog_eqout]) THEN
    FIND_ABBREV_THEN "k" (SUBST_ALL_TAC o GSYM) THEN
    ASM_REWRITE_TAC[ARITH_RULE`(4 * x) DIV 4 = x`; MESON[]`!(x:A). exists y. x = y`] THEN
    NO_TAC;

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;



let PROLOG_STEP2_STEP3_EQUIV_EXT,extra_regs_equiv =
  extend_first_equiv_for_seq_composition
    PROLOG_STEP2_STEP3_EQUIV MADDLOOP_STEP2_STEP3_EQUIV
    step2_prolog_eqout step2_body_eqin;;

let STEP2_PROLOG_EQOUT_IMPLIES_BODY_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs_equiv,`extra_regs_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        step2_prolog_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs_equiv (s1,s1') ==>
        step2_body_eqin (s1,s1') z m m_precalc sp k outerloop_counter`),
    REWRITE_TAC([step2_prolog_eqout;step2_body_eqin;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let PROLOG_MADDLOOP_STEP2_STEP3_EQUIV =
  prove_equiv_seq_composition
    PROLOG_STEP2_STEP3_EQUIV_EXT
    MADDLOOP_STEP2_STEP3_EQUIV
    STEP2_PROLOG_EQOUT_IMPLIES_BODY_EQIN;;


(* ------------------------------------------------------------------------- *)
(* Equivalence between the epilogues only.                                   *)
(* ------------------------------------------------------------------------- *)

(* input states *)

let step2_epilog_in_regs, step2_epilog_out_regs = get_input_output_regs
    (snd OUTERLOOP_STEP3_EXEC)
    [(fst (assoc "inner_loop_postamble" outerloop_step3_labels),
      fst (assoc "inner_loop_postamble_noepilogue" outerloop_step3_labels) - 4)];;

let step2_epilog_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step2_epilog_eqin *)
  (subtract step2_epilog_in_regs [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step2_epilog_eqin = new_definition
  (replace_eq_mems_regs step2_epilog_eqin_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step2_epilog_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (read X27 s1 = word 1 /\ read X27 s1' = word 0 /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * (k - 4))) /\
      read X1 s1' = word_add z (word (8 * (k - 4))) /\
      read X2 s1 = word_add m (word (8 * (k - 4))) /\
      read X2 s1' = word_add m (word (8 * (k - 4))) /\
      read SP s1 = sp /\
      read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
      read X30 s1' = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // and others
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs (s1,s1'))`);;


(* output states and maychange *)

let step2_epilog_maychanges_left = build_maychanges
  step2_epilog_out_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4))] ,, MAYCHANGE [X27]`;;

let step2_epilog_maychanges_right = build_maychanges
  step2_epilog_out_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4))]`;;

let step2_epilog_eqout_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step2_epilog_eqin *)
  (subtract step2_epilog_out_regs [`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step2_epilog_eqout = new_definition
  (replace_eq_mems_regs step2_epilog_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
  (step2_epilog_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word (8 * (k - 4))) /\
    read X1 s1' = word_add z (word (8 * (k - 4))) /\
    read X2 s1 = word_add m (word (8 * (k - 4))) /\
    read X2 s1' = word_add m (word (8 * (k - 4))) /\
    read SP s1 = sp /\
    read SP s1' = sp /\
    read X30 s1 = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
    read X30 s1' = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // Equalities
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs(s1,s1'))`);;

let equiv_goal3 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step2_mc; word pc2:int64,LENGTH outerloop_step3_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step2_epilog_eqin
    step2_epilog_eqout
    outerloop_step2_mc
    (fst (assoc "maddloop_rotated" outerloop_step2_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step2_labels))
    step2_epilog_maychanges_left
    outerloop_step3_mc
    (fst (assoc "inner_loop_postamble" outerloop_step3_labels))
    (fst (assoc "inner_loop_postamble_noepilogue" outerloop_step3_labels))
    step2_epilog_maychanges_right
    `\(s:armstate). 107` `\(s:armstate). 105`;;



let EPILOG_STEP2_STEP3_EQUIV = prove(equiv_goal3,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP2_EXEC; fst OUTERLOOP_STEP3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* prepare memory loads *)
  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,k-4) s = ..
      2. bignum_from_memory (z+4*(k-4),4) s = ..
      3. bignum_From_memory (z+4*k,4) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*k4-4`;`4*k4`] BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4*k4-(4*k4-4) = 4 /\ (4*k4+4)-(4*k4)=4` MP_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN (fun th ->
    DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit" (REWRITE_RULE[th]th2))) THEN

  (** Initialize **)
  REWRITE_TAC[step2_epilog_eqin;step2_epilog_eqout;
              mk_equiv_regs;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  EQUIV_STEPS_TAC [
      ("equal",0,105,0,105);
      ("delete",105,107,105,105) (* exit the branch of the maddloop (step2) *)]
    OUTERLOOP_STEP2_EXEC OUTERLOOP_STEP3_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
    (* only one goal here.. memory :> bytes z. *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(* Sequential composition of step2_outerloop_(prolog+maddloop) and
   step2_outerloop_epilog. *)
let STEP2_BODY_EQOUT_IMPLIES_EPILOGUE_EQIN =
  prove(`forall s1 s1' z m m_precalc sp k outerloop_counter.
    step2_body_eqout (s1,s1') z m m_precalc sp k outerloop_counter ==>
    step2_epilog_eqin (s1,s1') z m m_precalc sp k outerloop_counter`,
    REWRITE_TAC([step2_body_eqout;step2_epilog_eqin;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]);;

let PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_FULL_EQUIV =
  prove_equiv_seq_composition
    PROLOG_MADDLOOP_STEP2_STEP3_EQUIV
    EPILOG_STEP2_STEP3_EQUIV
    STEP2_BODY_EQOUT_IMPLIES_EPILOGUE_EQIN;;


(* ------------------------------------------------------------------------- *)
(* Equivalence between the outerloop blocks.                                 *)
(* ------------------------------------------------------------------------- *)

(* input states *)

let step2_outerloop_in_regs, step2_outerloop_out_regs = get_input_output_regs
    (snd OUTERLOOP_STEP3_EXEC)
    [(0x0, fst (assoc "maddloop_prologue" outerloop_step3_labels) - 4)];;

let step2_outerloop_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step2_outerloop_eqin *)
  (subtract step2_outerloop_in_regs [`X0`;`X1`;`X2`;`SP`]);;

let step2_outerloop_eqin = new_definition
  (replace_eq_mems_regs step2_outerloop_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step2_outerloop_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = z /\ read X1 s1' = z /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // others
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;


(* output states and maychange
   Q: step2_outerloop_out_regs is underapproxiation of 'updated
      registers' because it only includes updated regs that are
      never read again. Why does this work? *)

let step2_outerloop_maychanges = build_maychanges
  step2_outerloop_out_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step2_outerloop_eqout_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step2_epilog_eqout *)
  (subtract step2_outerloop_out_regs [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step2_outerloop_eqout = new_definition
  (replace_eq_mems_regs step2_outerloop_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
  (step2_outerloop_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X27 s1 = word (k DIV 4 - 1) /\ read X27 s1' = word (k DIV 4 - 2) /\
    read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = z /\ read X1 s1' = z /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // others
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let equiv_goal4 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k+4)))
     [word pc:int64,LENGTH outerloop_step2_mc; word pc2:int64,LENGTH outerloop_step3_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc:int64,LENGTH outerloop_step2_mc; word pc2:int64,LENGTH outerloop_step3_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step2_outerloop_eqin
    step2_outerloop_eqout
    outerloop_step2_mc
    0x0
    (fst (assoc "maddloop_neon" outerloop_step2_labels))
    step2_outerloop_maychanges
    outerloop_step3_mc
    0x0
    (fst (assoc "maddloop_prologue" outerloop_step3_labels))
    step2_outerloop_maychanges
    `\(s:armstate). 167` `\(s:armstate). 168`;;


let OUTERLOOP_STEP2_STEP3_EQUIV = prove(equiv_goal4,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP2_EXEC; fst OUTERLOOP_STEP3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k) s = bignum_from_memory (z,k) s2' into two parts:
      1. bignum_from_memory (z,4) s = ..
      2. bignum_from_memory (z+4,k) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4`] BIGNUM_FROM_MEMORY_EQ_SPLIT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit" (REWRITE_RULE[ARITH_RULE`8*4=32`]th2))
  THEN

  (** Initialize **)
  REWRITE_TAC[step2_outerloop_eqin;step2_outerloop_eqout;mk_equiv_regs;
              mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  EQUIV_STEPS_TAC [
      ("equal",0,134,0,134);
      ("replace",134,135,134,135) (* x27 is x0 << 5 *);
      ("insert",135,135,135,136) (* decrement counter (x27) *);
      ("equal",135,167,136,168)]
    OUTERLOOP_STEP2_EXEC OUTERLOOP_STEP3_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    (* updates of loop counter (x27) *)
    CONJ_TAC THENL [
      REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT]
      THEN CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC;SIMPLE_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT;WORD_SUB2] THEN
      REPEAT CONJ_TAC THENL [
        AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC];
      ALL_TAC] THEN
    (* only two goals here for memory equality.. let's expand memory :> bytes. *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (NUM_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(* Sequential composition of
    OUTERLOOP_STEP2_STEP3_EQUIV and
    PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_FULL_EQUIV. *)

let OUTERLOOP_STEP2_STEP3_EQUIV_EXT,extra_regs2_equiv =
  extend_first_equiv_for_seq_composition
    OUTERLOOP_STEP2_STEP3_EQUIV
    PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_FULL_EQUIV
    step2_outerloop_eqout
    step2_prolog_eqin;;

let STEP2_OUTERLOOP_EQOUT_IMPLIES_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs2_equiv,`extra_regs2_equiv:armstate#armstate->bool`;
             extra_regs_equiv,`extra_regs_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        step2_outerloop_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs2_equiv (s1,s1') ==>
        step2_prolog_eqin (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs_equiv (s1,s1')`),
    REWRITE_TAC([step2_prolog_eqin;step2_outerloop_eqout;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let OUTERLOOP_PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_STEP2_STEP3_EQUIV_EXT
    PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_FULL_EQUIV
    STEP2_OUTERLOOP_EQOUT_IMPLIES_EQIN;;


(* ------------------------------------------------------------------------- *)
(* Equivalence between the inner_loop_postamble blocks.                      *)
(* ------------------------------------------------------------------------- *)

(* input states *)

let step2_inner_loop_postamble_in_regs, step2_inner_loop_postamble_out_regs =
  get_input_output_regs
    (snd OUTERLOOP_STEP3_EXEC)
    [(fst (assoc "inner_loop_postamble_noepilogue" outerloop_step3_labels),
      Array.length (snd OUTERLOOP_STEP3_EXEC) - 4)];;

let step2_inner_loop_postamble_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in
     step2_inner_loop_postamble_eqin *)
  (subtract step2_inner_loop_postamble_in_regs [`X0`;`X1`;`X2`;`SP`]);;

let step2_inner_loop_postamble_eqin = new_definition
  (replace_eq_mems_regs step2_inner_loop_postamble_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step2_inner_loop_postamble_eqin
      :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word (8 * (k - 4))) /\
    read X1 s1' = word_add z (word (8 * (k - 4))) /\
    read X2 s1 = word_add m (word (8 * (k - 4))) /\
    read X2 s1' = word_add m (word (8 * (k - 4))) /\
    read SP s1 = sp /\
    read SP s1' = sp /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // Equalities
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs(s1,s1'))`);;


(* output states and maychange *)

let step2_inner_loop_postamble_maychanges = build_maychanges
  step2_inner_loop_postamble_out_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step2_inner_loop_postamble_eqout_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in
     step2_inner_loop_postamble_eqout *)
  (subtract step2_inner_loop_postamble_out_regs [`X0`;`X1`;`X2`;`SP`;`X30`;`X26`]);;

let step2_inner_loop_postamble_eqout = new_definition
  (replace_eq_mems_regs step2_inner_loop_postamble_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step2_inner_loop_postamble_eqout
      :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word 32) /\
    read X1 s1' = word_add z (word 32) /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 =
        word_sub (word outerloop_counter) (word 1) /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' =
        word_sub (word outerloop_counter) (word 1) /\
    read X26 s1 = word_sub (word outerloop_counter) (word 1) /\
    read X26 s1' = word_sub (word outerloop_counter) (word 1) /\
    // Equalities
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let equiv_goal5 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step2_mc; word pc2:int64,LENGTH outerloop_step3_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc:int64,LENGTH outerloop_step2_mc; word pc2:int64,LENGTH outerloop_step3_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step2_inner_loop_postamble_eqin
    step2_inner_loop_postamble_eqout
    outerloop_step2_mc
    (fst (assoc "inner_loop_postamble" outerloop_step2_labels))
    (Array.length (snd (OUTERLOOP_STEP2_EXEC)))
    step2_inner_loop_postamble_maychanges
    outerloop_step3_mc
    (fst (assoc "inner_loop_postamble_noepilogue" outerloop_step3_labels))
    (Array.length (snd (OUTERLOOP_STEP3_EXEC)))
    step2_inner_loop_postamble_maychanges
    `\(s:armstate). 17` `\(s:armstate). 17`;;

let INNER_LOOP_POSTAMBLE_STEP2_STEP3_EQUIV = prove(equiv_goal5,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP2_EXEC; fst OUTERLOOP_STEP3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* prepare memory loads *)
  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k) s = bignum_from_memory (z,k) s2' into two parts:
      1. bignum_from_memory (z,k) s = ..
      2. bignum_from_memory (z+4*k,4) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*(k4+1)`;`4*k4`] BIGNUM_FROM_MEMORY_EQ_SPLIT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4*(k4+1)-4*k4 = 4` MP_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN (fun th ->
    DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit"
      (REWRITE_RULE[th;ARITH_RULE`4*(x+1)=4*x+4`]th2))) THEN

  (** Initialize **)
  REWRITE_TAC[step2_inner_loop_postamble_eqin;step2_inner_loop_postamble_eqout;
              mk_equiv_regs;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  EQUIV_STEPS_TAC [
      ("equal",0,2,0,2);
      ("replace",2,3,2,3); (* load outerloop_counter *)
      ("equal",3,11,3,11);
      ("replace",11,16,11,16); (* update x1 and x2, decrement outerloop_counter,
                                  store it *)
      ("equal",16,17,16,17)]
    OUTERLOOP_STEP2_EXEC OUTERLOOP_STEP3_EXEC THEN

  (* deal with '8 * (4 * k4 - 4) + 32, 8 * (4 * k4 - 4) + 40, ..' first *)
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 32 = 8 * 4 * k4` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 40 = 8 * 4 * k4 + 8` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 48 = 8 * 4 * k4 + 16` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 56 = 8 * 4 * k4 + 24` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[ARITH_RULE`(4 * x) DIV 4 = x`; MESON[] `!(x:A). exists y. x = y`] THEN
    REWRITE_TAC[WORD_RULE`word_add (word_sub (word_add k a) a) b = word_add k b`;
                WORD_RULE`word_sub(word_add k a) a = k`] THEN
    (* only one goal here.. memory :> bytes (z + 8 * 4 * k4). *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(* Sequential composition of all basic blocks. *)

let OUTERLOOP_PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_EQUIV_EXT,extra_regs3_equiv =
  extend_first_equiv_for_seq_composition
    OUTERLOOP_PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_EQUIV
    INNER_LOOP_POSTAMBLE_STEP2_STEP3_EQUIV
    step2_epilog_eqout
    step2_inner_loop_postamble_eqin;;

let STEP2_EPILOG_EQOUT_IMPLIES_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs3_equiv,`extra_regs3_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        step2_epilog_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs3_equiv (s1,s1') ==>
        step2_inner_loop_postamble_eqin (s1,s1') z m m_precalc sp k outerloop_counter`),
    REWRITE_TAC([step2_inner_loop_postamble_eqin;step2_epilog_eqout;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let OUTERLOOP_FULL_STEP2_STEP3_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_PROLOG_MADDLOOP_EPILOG_STEP2_STEP3_EQUIV_EXT
    INNER_LOOP_POSTAMBLE_STEP2_STEP3_EQUIV
    STEP2_EPILOG_EQOUT_IMPLIES_EQIN;;


(* ========================================================================= *)
(*                 Equivalence between Step 3 - Step 4                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Equivalence between the maddloop bodies after (k/4) - 2 iterations.       *)
(* ------------------------------------------------------------------------- *)

(* Build state equalities. Use step2_body_eq_regs. *)
let step3_maddloop_eqin = new_definition
  (replace_eq_mems_regs step2_body_eq_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step3_maddloop_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X27 s1 = word (k DIV 4 - 2) /\ read X27 s1' = word (k DIV 4 - 2) /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word 32) /\ read X1 s1' = word_add z (word 32) /\
      read X2 s1 = word_add m (word 32) /\ read X2 s1' = word_add m (word 32) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word 96) /\
      read X30 s1' = word_add m_precalc (word 96) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let step3_maddloop_eqout = new_definition
  (replace_eq_mems_regs step2_body_eq_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step3_maddloop_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
     (read X27 s1 = word 0 /\
      read X27 s1' = word 0 /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * (k - 4))) /\
      read X1 s1' = word_add z (word (8 * (k - 4))) /\
      read X2 s1 = word_add m (word (8 * (k - 4))) /\
      read X2 s1' = word_add m (word (8 * (k - 4))) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      read X30 s1' = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let equiv_goal1 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step3_mc; word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step3_maddloop_eqin
    step3_maddloop_eqout
    outerloop_step3_mc
    (fst (assoc "maddloop_neon" outerloop_step3_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step3_labels))
    step2_body_maychanges
    bignum_emontredc_8n_cdiff_mc
    (fst (assoc "maddloop_neon" bignum_emontredc_8n_cdiff_labels))
    (fst (assoc "inner_loop_postamble" bignum_emontredc_8n_cdiff_labels))
    step2_body_maychanges
    `\(s:armstate). 151 * (k DIV 4 - 2)` `\(s:armstate). 151 * (k DIV 4 - 2)`;;


let inst_map = [
  106;107;1;2;3;4;5;6;7;8;9;10;108;109;11;110;12;13;14;111;15;16;17;112;18;19;113;114;20;21;115;22;116;23;24;25;26;27;117;118;28;119;29;120;30;121;31;122;32;33;34;123;35;124;36;125;37;38;126;39;40;41;127;42;43;44;128;45;129;130;46;47;131;48;49;50;51;52;53;54;55;132;56;57;58;133;59;134;60;61;62;63;64;135;65;66;67;68;69;70;71;72;73;136;74;75;76;77;78;137;79;80;81;138;82;139;83;84;85;86;140;87;88;89;90;91;92;141;142;93;143;94;95;144;96;97;145;98;146;99;100;101;102;147;148;103;104;105;149;
  150;
];;

let regs_no_abbrev_left =
  let pcbeg = fst (assoc "maddloop_neon" outerloop_step3_labels) and
      pcend = fst (assoc "inner_loop_postamble" outerloop_step3_labels) - 8
          (* minus 8 because the last instruction is cond br *) in
  let addr_regs = collect_mem_address_regs (snd OUTERLOOP_STEP3_EXEC)
      [pcbeg,pcend] in
  let addr_regs = (pcend,`X27`)::addr_regs in (* loop counter *)
  let res = tl (backward_taint_analysis (snd OUTERLOOP_STEP3_EXEC)
    [pcbeg,pcend] (map (fun (x,y) -> x,[y]) addr_regs)) in
  List.map (fun pcdiv4 ->
      try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;

let regs_no_abbrev_right =
  let pcbeg = fst (assoc "maddloop_neon" bignum_emontredc_8n_cdiff_labels) and
      pcend = fst (assoc "inner_loop_postamble" bignum_emontredc_8n_cdiff_labels) - 8
      (* minus 8 because the last instruction is cond br *)in
  let addr_regs = collect_mem_address_regs (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
      [pcbeg,pcend] in
  let addr_regs = (pcend,`X27`)::addr_regs in (* loop counter *)
  let res = tl (backward_taint_analysis (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
    [pcbeg,pcend] (map (fun (x,y) -> x,[y]) addr_regs)) in
  List.map (fun pcdiv4 ->
      try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;


(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let MADDLOOP_STEP3_STEP4_EQUIV = prove(equiv_goal1,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP3_EXEC; fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k` ASSUME_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `3 <= k4` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN

  (* iterates 'k / 4 - 2' times, where k is the number of words in modulus *)
  ENSURES2_WHILE_PAUP_TAC `1` `k4 - 1:num`
    `pc+outerloop_step3_label_maddloop_neon`
    `pc+(outerloop_step3_label_inner_loop_postamble-4)`
    `pc2+slothy_maddloop_neon`
    `pc2+(slothy_inner_loop_postamble-4)`
    (replace_eq_mems_regs step2_body_eq_regs
    `\(i:num) s1 s1'.
      // loop counter
      read X27 s1 = word (k4 - (i + 1)) /\
      read X27 s1' = word (k4 - (i + 1)) /\
      // pointers and constants
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * 4 * i)) /\
      read X1 s1' = word_add z (word (8 * 4 * i)) /\
      read X2 s1 = word_add m (word (8 * 4 * i)) /\
      read X2 s1' = word_add m (word (8 * 4 * i)) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * 12 * i)) /\
      read X30 s1' = word_add m_precalc (word (8 * 12 * i)) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // equalities
      eq_mems z m sp m_precalc (k:num) (s1,s1') /\
      eq_regs(s1,s1')`)
    `\(i:num) (s:armstate). T` `\(i:num) (s:armstate). T`
    `\(i:num). 150` (* include backedge *)
    `\(i:num). 150`
    (* pre steps *)`0` `0`
    (* post steps *)`1` `1`
    (* num backedges *)`1` `1`
  THEN MAP_EVERY (fun t -> SUBST1_TAC
    ((REWRITE_CONV (map (snd o snd) (outerloop_step3_labels @
        bignum_emontredc_8n_cdiff_labels))
      THENC NUM_REDUCE_CONV) t))
    [`outerloop_step3_label_inner_loop_postamble-4`;
     `slothy_inner_loop_postamble-4`]
  THEN REWRITE_TAC (map (snd o snd)
    (outerloop_step3_labels @ bignum_emontredc_8n_cdiff_labels))
  THEN REPEAT CONJ_TAC THENL [
    (* loop count which is k4-1 > 0. *)
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP DIVIDES_LE th)) THEN SIMPLE_ARITH_TAC;

    (* precond to loop entrance *)
    REWRITE_TAC[step3_maddloop_eqin;MULT_0; WORD_ADD_0; SUB_0; ASSUME `k DIV 4 = k4`] THEN
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONJ_TAC THENL [
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
      REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* the loop body. lockstep simulation is needed. *)
    ALL_TAC;

    (* backedge. *)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    UNDISCH_THEN `k DIV 4 = k4` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE ([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES])) THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC OUTERLOOP_STEP3_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `~(val (word (k4 - (i + 1)):int64) = 0)` MP_TAC THENL [
      IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    CONJ_TAC THENL [
      REPEAT (CONJ_TAC THENL
        [FIRST_X_ASSUM MATCH_ACCEPT_TAC ORELSE ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];
        ALL_TAC]) THEN
      REPEAT (CONJ_TAC THENL [
        REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC]) THEN
      REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* postcond! *)
    ASM_REWRITE_TAC[step3_maddloop_eqout;SUB_REFL;MULT_0;mk_equiv_regs;
                    BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC OUTERLOOP_STEP3_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    CONJ_TAC THENL [
      SUBGOAL_THEN `(val (word (k4 - (k4 - 1 + 1)):int64) = 0)`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [ SUBGOAL_THEN `k4 - (k4 - 1 + 1)=0` SUBST_ALL_TAC
        THENL [SIMPLE_ARITH_TAC;ALL_TAC]
        THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN
      REPLICATE_TAC 4 (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN

      SUBGOAL_THEN `k4 - (k4 - 1) = 1 /\ k4 - (k4 - 1 + 1) = 0 /\
                    8 * (k-4) = 8 * 4 * (k4-1)`
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* loop trip count, left prog *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC;
  ] THEN

  REPEAT STRIP_TAC THEN
  (* replace k DIV 4 with k4. *)
  FIND_ABBREV_THEN "k4" SUBST_ALL_TAC THEN
  FIND_ABBREV_THEN "k" (SUBST_ALL_TAC o GSYM) THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,i) s = ..
      2. bignum_from_memory (z+4*i,4) s = ..
      3. bignum_from_memory (z+4*(i+1),k+4-*(i+1)) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*i`;`4*(i+1)`]
      BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th ->
    MP_TAC (REWRITE_RULE[ARITH_RULE `4 * (i + 1) - 4 * i=4`] th)) THEN

  REWRITE_TAC([BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs]) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(i + 1) + 1 = i + 2` SUBST_ALL_TAC THENL [ARITH_TAC;ALL_TAC] THEN

  (* start *)
  ENSURES2_INIT_TAC "s0" "s0'" THEN

  RULE_ASSUM_TAC(CONV_RULE (DEPTH_CONV NUM_MULT_CONV)) THEN
  CONV_TAC (DEPTH_CONV NUM_MULT_CONV) THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* loop counter is larger than 0. *)
  SUBGOAL_THEN `1 <= (k4 - (i + 1))` (LABEL_TAC "HBOUND") THENL [
    UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;
    ALL_TAC
  ] THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC OUTERLOOP_STEP3_EXEC
    (1--(List.length inst_map)) state_to_abbrevs (Some regs_no_abbrev_left) THEN

(* let e tac = refine(by(tac));; *)
  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs (Some regs_no_abbrev_right) THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MESON[]`forall (a:A). exists x. a = x`] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; ARITH_RULE`8*4*z+32 = 8*4*(z+1)`;
                ARITH_RULE`8*12*z+96 = 8*12*(z+1)`] THEN
    REPEAT CONJ_TAC THENL [
      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      (* updates in zi': splitting now! *)
      REWRITE_TAC[ARITH_RULE`32=8*4`; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
              CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]
    ];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence between the outerloop blocks.                                 *)
(* ------------------------------------------------------------------------- *)

let inst_map = [
  2;1;135;136;3;4;6;7;9;8;11;12;28;85;82;16;47;45;33;10;29;13;14;19;30;22;15;24;31;17;18;26;32;20;27;48;34;21;23;35;38;39;40;43;25;44;79;64;37;137;36;52;41;46;42;139;165;140;141;55;67;142;49;163;58;51;66;60;50;62;65;63;5;68;69;53;205;70;169;164;71;170;54;74;75;84;80;56;76;177;171;59;57;81;174;176;106;182;172;89;61;83;88;104;87;72;86;92;73;101;91;181;77;95;78;143;90;145;144;151;97;152;146;103;186;194;153;102;185;105;154;199;96;93;188;99;100;94;107;209;196;108;192;111;112;98;114;113;200;197;201;109;120;117;110;138;115;206;118;116;155;157;156;159;158;166;119;168;167;175;161;178;160;127;122;179;124;204;203;126;162;183;121;173;184;180;123;187;190;128;191;130;147;189;210;125;193;148;211;149;195;129;207;150;131;132;198;212;133;202;134;208
];;

let step3_outerloop_in_regs_right, step3_outerloop_out_regs_right =
  get_input_output_regs
    (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
    [(fst (assoc "outerloop" bignum_emontredc_8n_cdiff_labels),
      fst (assoc "maddloop_neon" bignum_emontredc_8n_cdiff_labels) - 4)];;

let step3_outerloop_in_regs_left, step3_outerloop_out_regs_left =
  get_input_output_regs
    (snd OUTERLOOP_STEP3_EXEC)
    [(0,fst (assoc "maddloop_neon" outerloop_step3_labels) - 4)];;

(* Note: step3_outerloop_out_regs_left will not be used later,
  and step3_outerloop_out_regs_right will be shrunk to exclude
  registers that are not really outputs. *)
assert
  (sort (fun x y -> compare x y < 0) step3_outerloop_in_regs_right =
   sort (fun x y -> compare x y < 0) step3_outerloop_in_regs_left);;

let step3_outerloop_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step3_outerloop_eqin *)
  (subtract step3_outerloop_in_regs_left [`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step3_outerloop_eqin = new_definition
  (replace_eq_mems_regs step3_outerloop_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step3_outerloop_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = z /\ read X1 s1' = z /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // others
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let step3_outerloop_maychanges_left = build_maychanges
  step3_outerloop_out_regs_left
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step3_outerloop_maychanges_right = build_maychanges
  step3_outerloop_out_regs_right
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

(* Map renamed registers. *)
let step3_outerloop_out_regs_left,step3_outerloop_out_regs_right =
  let m = map_output_regs
    (snd OUTERLOOP_STEP3_EXEC) 0
    (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
    (fst (assoc "outerloop" bignum_emontredc_8n_cdiff_labels))
    (Array.of_list inst_map)
    step3_outerloop_out_regs_right in
  let lr = zip m step3_outerloop_out_regs_right in
  let lr = List.filter_map (fun x,y ->
    if x = None then None else Some (snd (Option.get x),y)) lr in
  unzip lr;;

let step3_outerloop_eqout_regs = build_equiv_regs2
  (subtract step3_outerloop_out_regs_left [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`])
  (subtract step3_outerloop_out_regs_right [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step3_outerloop_eqout = new_definition
  (replace_eq_mems_regs step3_outerloop_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
  (step3_outerloop_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X27 s1 = word (k DIV 4 - 2) /\ read X27 s1' = word (k DIV 4 - 2) /\
    read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word 32) /\ read X1 s1' = word_add z (word 32) /\
    read X2 s1 = word_add m (word 32) /\ read X2 s1' = word_add m (word 32) /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = word_add m_precalc (word 96) /\
    read X30 s1' = word_add m_precalc (word 96) /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // others
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let equiv_goal2 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k+4)))
     [word pc:int64,LENGTH outerloop_step3_mc; word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc:int64,LENGTH outerloop_step3_mc; word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step3_outerloop_eqin
    step3_outerloop_eqout
    outerloop_step3_mc
    0x0
    (fst (assoc "maddloop_neon" outerloop_step3_labels))
    step3_outerloop_maychanges_left
    bignum_emontredc_8n_cdiff_mc
    (fst (assoc "outerloop" bignum_emontredc_8n_cdiff_labels))
    (fst (assoc "maddloop_neon" bignum_emontredc_8n_cdiff_labels))
    step3_outerloop_maychanges_right
    `\(s:armstate). 212` `\(s:armstate). 212`;;

(* Some registers should not be abbreviated because they will be
   used as memory addresses. *)
let regs_no_abbrev_left =
  let pcbeg = 0 and
      pcend = fst (assoc "maddloop_neon" outerloop_step3_labels) - 4 in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd OUTERLOOP_STEP3_EXEC) [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition *)
  let addr_regs = (pcend,[`X27`;`X0`;`X1`;`X2`;`SP`;`X30`])::addr_regs in
  let res = tl (backward_taint_analysis (snd OUTERLOOP_STEP3_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;

let regs_no_abbrev_right =
  let pcbeg = fst (assoc "outerloop" bignum_emontredc_8n_cdiff_labels) and
      pcend = fst (assoc "maddloop_neon" bignum_emontredc_8n_cdiff_labels) - 4
      in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
      [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition *)
  let addr_regs = map (fun (pc,regs) ->
      (pc,if pc = pcend then [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`] @ regs else regs))
      addr_regs in
  let res = tl (backward_taint_analysis (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;


(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;


let OUTERLOOP_STEP3_STEP4_EQUIV = prove(equiv_goal2,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP3_EXEC; fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k) s = bignum_from_memory (z,k) s2' into two parts:
      1. bignum_from_memory (z,4) s = ..
      2. bignum_from_memory (z+4,k) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4`] BIGNUM_FROM_MEMORY_EQ_SPLIT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit" (REWRITE_RULE[ARITH_RULE`8*4=32`]th2))
  THEN

  (** Initialize **)
  REWRITE_TAC[step3_outerloop_eqin;step3_outerloop_eqout;mk_equiv_regs;
              mk_equiv_regs2;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC OUTERLOOP_STEP3_EXEC
    (1--(List.length inst_map)) state_to_abbrevs (Some regs_no_abbrev_left) THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs (Some regs_no_abbrev_right) THEN


  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    (* updates of loop counter (x27) *)
    CONJ_TAC THENL [
      REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT;WORD_SUB2]
      THEN CONJ_TAC THENL [
        CONJ_TAC THENL [
          AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
          SIMPLE_ARITH_TAC
        ]; SIMPLE_ARITH_TAC
      ];
      ALL_TAC] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT;WORD_SUB2] THEN
      REPEAT CONJ_TAC THENL [
        AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC];
      ALL_TAC] THEN
    (* only two goals here for memory equality.. let's expand memory :> bytes. *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (NUM_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

let OUTERLOOP_STEP3_STEP4_EQUIV_EXT,extra_regs_equiv =
  extend_first_equiv_for_seq_composition
    OUTERLOOP_STEP3_STEP4_EQUIV
    MADDLOOP_STEP3_STEP4_EQUIV
    step3_outerloop_eqout
    step3_maddloop_eqin;;

let STEP3_OUTERLOOP_EQOUT_IMPLIES_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs_equiv,`extra_regs_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        step3_outerloop_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs_equiv (s1,s1') ==>
        step3_maddloop_eqin (s1,s1') z m m_precalc sp k outerloop_counter`),
    REWRITE_TAC([step3_outerloop_eqout;step3_maddloop_eqin;mk_equiv_regs;mk_equiv_regs2]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let OUTERLOOP_MADDLOOP_STEP3_STEP4_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_STEP3_STEP4_EQUIV_EXT
    MADDLOOP_STEP3_STEP4_EQUIV
    STEP3_OUTERLOOP_EQOUT_IMPLIES_EQIN;;

(* ------------------------------------------------------------------------- *)
(* Equivalence between the inner_loop_postamble blocks.                      *)
(* ------------------------------------------------------------------------- *)

let inst_map = [
  15;14;2;3;1;5;4;7;20;8;9;11;12;13;42;16;17;10;18;19;21;6;22;23;24;26;27;25;28;108;118;29;30;31;32;33;34;35;36;38;37;40;41;44;43;45;46;47;39;48;49;51;55;50;52;53;58;60;54;56;62;63;59;57;61;65;64;66;78;69;67;68;72;70;73;74;84;75;76;77;79;81;71;89;82;83;85;87;88;80;90;91;92;106;93;86;95;94;96;97;99;98;101;100;102;107;105;103;104;109;110;111;122;112;115;113;114;116;120;117;121;119
];;

let step3_inner_loop_postamble_in_regs_left,
    step3_inner_loop_postamble_out_regs_left =
  get_input_output_regs
    (snd OUTERLOOP_STEP3_EXEC)
    [(fst (assoc "inner_loop_postamble" outerloop_step3_labels),
      Array.length (snd OUTERLOOP_STEP3_EXEC) - 4)];;

let step3_inner_loop_postamble_in_regs_right,
    step3_inner_loop_postamble_out_regs_right =
  get_input_output_regs
    (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
    [(fst (assoc "inner_loop_postamble" bignum_emontredc_8n_cdiff_labels),
     (fst (assoc "outerloop_end" bignum_emontredc_8n_cdiff_labels) - 4))];;

assert
  (sort (fun x y -> compare x y < 0) step3_inner_loop_postamble_in_regs_right =
   sort (fun x y -> compare x y < 0) step3_inner_loop_postamble_in_regs_left);;

let step3_inner_loop_postamble_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear later *)
  (subtract step3_inner_loop_postamble_in_regs_left [`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step3_inner_loop_postamble_eqin = new_definition
  (replace_eq_mems_regs step3_inner_loop_postamble_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step3_inner_loop_postamble_eqin
      :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word (8 * (k - 4))) /\
    read X1 s1' = word_add z (word (8 * (k - 4))) /\
    read X2 s1 = word_add m (word (8 * (k - 4))) /\
    read X2 s1' = word_add m (word (8 * (k - 4))) /\
    read SP s1 = sp /\
    read SP s1' = sp /\
    read X30 s1 = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
    read X30 s1' = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // Equalities
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs(s1,s1'))`);;


(* output states and maychange *)

let step3_inner_loop_postamble_maychanges_left = build_maychanges
  step3_inner_loop_postamble_out_regs_left
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step3_inner_loop_postamble_maychanges_right = build_maychanges
  step3_inner_loop_postamble_out_regs_right
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

(* Map renamed registers. *)
let step3_inner_loop_postamble_out_regs_left,
    step3_inner_loop_postamble_out_regs_right =
  let m = map_output_regs
    (snd OUTERLOOP_STEP3_EXEC)
    (fst (assoc "inner_loop_postamble" outerloop_step3_labels))
    (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
    (fst (assoc "inner_loop_postamble" bignum_emontredc_8n_cdiff_labels))
    (Array.of_list inst_map)
    step3_inner_loop_postamble_out_regs_right in
  let lr = zip m step3_inner_loop_postamble_out_regs_right in
  let lr = List.filter_map (fun x,y ->
    if x = None then None else Some (snd (Option.get x),y)) lr in
  unzip lr;;

let step3_inner_loop_postamble_eqout_regs = build_equiv_regs2
  (subtract step3_inner_loop_postamble_out_regs_left [`X0`;`X1`;`X2`;`SP`;`X30`;`X26`])
  (subtract step3_inner_loop_postamble_out_regs_right [`X0`;`X1`;`X2`;`SP`;`X30`;`X26`]);;

let step3_inner_loop_postamble_eqout = new_definition
  (replace_eq_mems_regs step3_inner_loop_postamble_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step3_inner_loop_postamble_eqout
      :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word 32) /\
    read X1 s1' = word_add z (word 32) /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 =
        word_sub (word outerloop_counter) (word 1) /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' =
        word_sub (word outerloop_counter) (word 1) /\
    read X26 s1 = word_sub (word outerloop_counter) (word 1) /\
    read X26 s1' = word_sub (word outerloop_counter) (word 1) /\
    // Equalities
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let equiv_goal3 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step3_mc; word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc:int64,LENGTH outerloop_step3_mc; word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step3_inner_loop_postamble_eqin
    step3_inner_loop_postamble_eqout
    outerloop_step3_mc
    (fst (assoc "inner_loop_postamble" outerloop_step3_labels))
    (Array.length (snd (OUTERLOOP_STEP3_EXEC)))
    step3_inner_loop_postamble_maychanges_left
    bignum_emontredc_8n_cdiff_mc
    (fst (assoc "inner_loop_postamble" bignum_emontredc_8n_cdiff_labels))
    (fst (assoc "outerloop_end" bignum_emontredc_8n_cdiff_labels))
    step3_inner_loop_postamble_maychanges_right
    `\(s:armstate). 122` `\(s:armstate). 122`;;

(* Some registers should not be abbreviated because they will be
   used as memory addresses. *)
let regs_no_abbrev_left =
  let pcbeg = (fst (assoc "inner_loop_postamble" outerloop_step3_labels)) and
      pcend = (Array.length (snd (OUTERLOOP_STEP3_EXEC))) - 4 in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd OUTERLOOP_STEP3_EXEC) [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition
     X26 is the outer loop counter *)
  let addr_regs = update_key_list pcend [`X0`;`X1`;`X2`;`SP`;`X30`;`X26`] addr_regs in
  let res = tl (backward_taint_analysis (snd OUTERLOOP_STEP3_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;

let regs_no_abbrev_right =
  let pcbeg = fst (assoc "inner_loop_postamble" bignum_emontredc_8n_cdiff_labels) and
      pcend = fst (assoc "outerloop_end" bignum_emontredc_8n_cdiff_labels) - 4
      in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
      [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition *)
  let addr_regs = update_key_list pcend [`X0`;`X1`;`X2`;`SP`;`X30`;`X26`] addr_regs in
  let res = tl (backward_taint_analysis (snd BIGNUM_EMONTREDC_8N_CDIFF_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;


(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let INNER_LOOP_POSTAMBLE_STEP3_STEP4_EQUIV = prove(equiv_goal3,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP3_EXEC; fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* prepare memory loads *)
  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,k-4) s = ..
      2. bignum_from_memory (z+4*(k-4),4) s = ..
      3. bignum_From_memory (z+4*k,4) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*k4-4`;`4*k4`] BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4*k4-(4*k4-4) = 4 /\ (4*k4+4)-(4*k4)=4` MP_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN (fun th ->
    DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit" (REWRITE_RULE[th]th2))) THEN

  (** Initialize **)
  REWRITE_TAC[step3_inner_loop_postamble_eqin;step3_inner_loop_postamble_eqout;
              mk_equiv_regs;mk_equiv_regs2;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC OUTERLOOP_STEP3_EXEC
    (1--(List.length inst_map)) state_to_abbrevs (Some regs_no_abbrev_left) THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs (Some regs_no_abbrev_right)
    THEN

  (* deal with '8 * (4 * k4 - 4) + 32, 8 * (4 * k4 - 4) + 40, ..' first *)
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 32 = 8 * 4 * k4` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 40 = 8 * 4 * k4 + 8` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 48 = 8 * 4 * k4 + 16` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 56 = 8 * 4 * k4 + 24` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[ARITH_RULE`(4 * x) DIV 4 = x`] THEN
    REWRITE_TAC[WORD_RULE`word_add (word_sub (word_add k a) a) b = word_add k b`;
                WORD_RULE`word_sub(word_add k a) a = k`] THEN
    (* only one goal here..
      memory :> bytes (z + 8 * (4 * k4 - 4)), and
      memory :> bytes (z + 8 * 4 * k4). *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

let OUTERLOOP_MADDLOOP_STEP3_STEP4_EQUIV_EXT,extra_regs_equiv2 =
  extend_first_equiv_for_seq_composition
    OUTERLOOP_MADDLOOP_STEP3_STEP4_EQUIV
    INNER_LOOP_POSTAMBLE_STEP3_STEP4_EQUIV
    step3_maddloop_eqout step3_inner_loop_postamble_eqin;;

let STEP3_OUTERLOOP_MADDLOOP_EQOUT_IMPLIES_BODY_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs_equiv2,`extra_regs_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        step3_maddloop_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs_equiv (s1,s1') ==>
        step3_inner_loop_postamble_eqin (s1,s1') z m m_precalc sp k outerloop_counter`),
    REWRITE_TAC([step3_maddloop_eqout;step3_inner_loop_postamble_eqin;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let OUTERLOOP_FULL_STEP3_STEP4_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_MADDLOOP_STEP3_STEP4_EQUIV_EXT
    INNER_LOOP_POSTAMBLE_STEP3_STEP4_EQUIV
    STEP3_OUTERLOOP_MADDLOOP_EQOUT_IMPLIES_BODY_EQIN;;



(* ========================================================================= *)
(*                 Equivalence between Step 1 - Step 2                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Equivalence between the maddloop bodies after (k/4) - 1 iterations.       *)
(* First, let's prove maddloop_step2_x30 = maddloop_step2.                   *)
(* ------------------------------------------------------------------------- *)

let step2_maddloop_x30_in_regs, step2_maddloop_x30_out_regs =
    get_input_output_regs (snd MADDLOOP_STEP2_X30_EXEC)
      [0, Array.length (snd MADDLOOP_STEP2_X30_EXEC) - 4];;

let step2_maddloop_x30_eq_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step2_body_eqin*)
  (subtract step2_maddloop_x30_in_regs [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

(* Build state equalities. *)
let step2_maddloop_x30_eqin = new_definition
  (replace_eq_mems_regs step2_maddloop_x30_eq_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step2_maddloop_x30_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X27 s1 = word (k DIV 4 - 1) /\ read X27 s1' = word (k DIV 4 - 1) /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = z /\ read X1 s1' = z /\
      read X2 s1 = m /\ read X2 s1' = m /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let step2_maddloop_x30_eqout = new_definition
  (replace_eq_mems_regs step2_maddloop_x30_eq_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step2_maddloop_x30_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
     (read X27 s1 = word 0 /\
      read X27 s1' = word 0 /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * (k - 4))) /\
      read X1 s1' = word_add z (word (8 * (k - 4))) /\
      read X2 s1 = word_add m (word (8 * (k - 4))) /\
      read X2 s1' = word_add m (word (8 * (k - 4))) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      read X30 s1' = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let step2_maddloop_x30_maychanges = build_maychanges
    step2_maddloop_x30_out_regs `MAYCHANGE [
        memory :> bytes (z:int64,8 * (k + 4));
        memory :> bytes (sp:int64,128)]`;;

let equiv_goal1 = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH maddloop_step2_x30_mc; word pc2:int64,LENGTH outerloop_step2_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step2_maddloop_x30_eqin
    step2_maddloop_x30_eqout
    maddloop_step2_x30_mc
    0
    (Array.length (snd MADDLOOP_STEP2_X30_EXEC))
    step2_maddloop_x30_maychanges
    outerloop_step2_mc
    (fst (assoc "maddloop_neon" outerloop_step2_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step2_labels))
    step2_maddloop_x30_maychanges
    `\(s:armstate). 152 * (k DIV 4 - 1)` `\(s:armstate). 151 * (k DIV 4 - 1)`;;

let actions = [
  ("replace", 0, 1, 0, 1); (* address update *)
  ("equal", 1, 39, 1, 39);
  ("replace", 39, 40, 39, 40);
  ("equal", 40, 42, 40, 42);
  ("replace", 42, 43, 42, 43); (*address update *)
];;
let actions2 = [
  ("equal", 43, 60, 43, 60);
  ("replace", 60, 61, 60, 61);
  ("equal", 61, 83, 61, 83);
  ("replace", 83, 84, 83, 84);
  ("equal", 84, 105, 84, 105);
  ("replace", 105, 106, 105, 106);
  ("equal", 106, 108, 106, 108);
  ("replace", 108, 109, 108, 109);
  ("equal", 109, 149, 109, 149);
  ("delete", 149, 150, 149, 149);
  ("replace", 150, 151, 149, 150); (* counter update *)
];;


let MADDLOOP_STEP2_X30_STEP2_EQUIV = prove(equiv_goal1,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst MADDLOOP_STEP2_X30_EXEC; fst OUTERLOOP_STEP2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k` ASSUME_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `3 <= k4` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN

  (* iterates 'k / 4 - 1' times, where k is the number of words in modulus *)
  ENSURES2_WHILE_PAUP_TAC `0` `k4 - 1`
    `pc:num`
    `pc+(LENGTH maddloop_step2_x30_mc-4)`
    `pc2+outerloop_step2_label_maddloop_neon`
    `pc2+(outerloop_step2_label_inner_loop_postamble-4)`
    (replace_eq_mems_regs step2_maddloop_x30_eq_regs
    `\(i:num) s1 s1'.
      // loop counter
      read X27 s1 = word (k4 - (i + 1)) /\
      read X27 s1' = word (k4 - (i + 1)) /\
      // pointers and constants
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * 4 * i)) /\
      read X1 s1' = word_add z (word (8 * 4 * i)) /\
      read X2 s1 = word_add m (word (8 * 4 * i)) /\
      read X2 s1' = word_add m (word (8 * 4 * i)) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * 12 * i)) /\
      read X30 s1' = word_add m_precalc (word (8 * 12 * i)) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // equalities
      eq_mems z m sp m_precalc (k:num) (s1,s1') /\
      eq_regs(s1,s1')`)
    `\(i:num) (s:armstate). T` `\(i:num) (s:armstate). T`
    `\(i:num). 151`
    `\(i:num). 150`
    (* pre steps *)`0` `0`
    (* post steps *)`1` `1`
    (* num backedges *)`1` `1`
  THEN MAP_EVERY (fun t -> SUBST1_TAC
    ((REWRITE_CONV (fst MADDLOOP_STEP2_X30_EXEC::(map (snd o snd) (outerloop_step2_labels)))
      THENC NUM_REDUCE_CONV) t))
    [`outerloop_step2_label_inner_loop_postamble-4`;
     `LENGTH maddloop_step2_x30_mc-4`]
  THEN REWRITE_TAC (map (snd o snd) (outerloop_step2_labels @ outerloop_step3_labels))
  THEN REPEAT CONJ_TAC THENL [
    (* loop count which is k4-1 > 0. *)
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP DIVIDES_LE th)) THEN SIMPLE_ARITH_TAC;

    (* precond to loop entrance *)
    REWRITE_TAC[step2_maddloop_x30_eqin;MULT_0; WORD_ADD_0; SUB_0; ASSUME `k DIV 4 = k4`] THEN
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONJ_TAC THENL [
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
      REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* the loop body. lockstep simulation is needed. *)
    ALL_TAC;

    (* backedge. *)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    UNDISCH_THEN `k DIV 4 = k4` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE ([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES])) THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC MADDLOOP_STEP2_X30_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC OUTERLOOP_STEP2_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `~(val (word (k4 - (i+1)):int64) = 0)` MP_TAC THENL [
      IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    CONJ_TAC THENL [
      REPEAT (CONJ_TAC THENL
        [FIRST_X_ASSUM MATCH_ACCEPT_TAC ORELSE ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];
        ALL_TAC]) THEN
      REPEAT (CONJ_TAC THENL [
        REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC]) THEN
      REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* postcond! *)
    ASM_REWRITE_TAC[step2_maddloop_x30_eqout;SUB_REFL;MULT_0;
                    mk_equiv_regs;
                    BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC MADDLOOP_STEP2_X30_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC OUTERLOOP_STEP2_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    CONJ_TAC THENL [
      SUBGOAL_THEN `(val (word (k4 - (k4 - 1 + 1)):int64) = 0)`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [ SUBGOAL_THEN `k4 - (k4 - 1 + 1)=0` SUBST_ALL_TAC
        THENL [SIMPLE_ARITH_TAC;ALL_TAC]
        THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN
      REPLICATE_TAC 4 (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN

      SUBGOAL_THEN `8 * (k-4) = 8 * 4 * (k4-1)` SUBST_ALL_TAC THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      SUBGOAL_THEN `k4 - (k4 - 1 + 1) = 0` SUBST_ALL_TAC THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* loop trip count, left prog *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC;

    (* loop trip count, right prog *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC
  ] THEN

  REPEAT STRIP_TAC THEN
  (* replace k DIV 4 with k4. *)
  FIND_ABBREV_THEN "k4" SUBST_ALL_TAC THEN
  FIND_ABBREV_THEN "k" (SUBST_ALL_TAC o GSYM) THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,i) s = ..
      2. bignum_from_memory (z+4*(i+1),4) s = ..
      3. bignum_from_memory (z+4*(i+2),k-4*(i+2)) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*(i+1)`;`4*(i+2)`]
      BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th ->
    MP_TAC (REWRITE_RULE[ARITH_RULE `4*(i+2) - 4*(i+1)=4`] th)) THEN

  REWRITE_TAC([BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs]) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(i + 1) + 1 = i + 2` SUBST_ALL_TAC THENL [ARITH_TAC;ALL_TAC] THEN

  (* start *)
  ENSURES2_INIT_TAC "s0" "s0'" THEN

  RULE_ASSUM_TAC(CONV_RULE (DEPTH_CONV NUM_MULT_CONV)) THEN
  CONV_TAC (DEPTH_CONV NUM_MULT_CONV) THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* loop counter is larger than 0. *)
  SUBGOAL_THEN `1 <= (k4 - (i + 1))` (LABEL_TAC "HBOUND") THENL [
    UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;
    ALL_TAC
  ] THEN

  EQUIV_STEPS_TAC actions MADDLOOP_STEP2_X30_EXEC OUTERLOOP_STEP2_EXEC THEN
  (* simplify the address of X1 *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add z (word (8 * 4 * i))) (word 32):int64 =
     word_add z (word (8 * 4 * i + 32))`]) THEN
  EQUIV_STEPS_TAC actions2 MADDLOOP_STEP2_X30_EXEC OUTERLOOP_STEP2_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MESON[]`forall (a:A). exists x. a = x`] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; ARITH_RULE`8*4*z+32 = 8*4*(z+1)`;
                ARITH_RULE`8*12*z+96 = 8*12*(z+1)`] THEN
    REPEAT CONJ_TAC THENL [
      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      (* updates in zi': splitting now! *)
      REWRITE_TAC[ARITH_RULE`32=8*4`; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
              CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;LEFT_ADD_DISTRIB] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]
    ];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(* ------------------------------------------------------------------------- *)
(* Now we prove maddloop_step1 = maddloop_step2_x30, and horizontally compose*)
(* this with maddloop_step2_x30 = maddloop_step2.                            *)
(* ------------------------------------------------------------------------- *)

let inst_map = [
1;2;3;17;20;5;19;4;6;18;21;23;8;9;22;24;11;14;25;12;28;27;26;16;29;7;30;10;33;32;108;13;15;36;31;80;109;35;37;81;111;110;43;112;82;38;
34;46;39;114;40;41;44;83;45;42;47;69;84;48;70;49;50;116;51;52;71;53;86;54;55;56;57;58;59;60;61;72;62;63;73;64;75;97;65;88;66;96;67;68;
74;76;77;78;99;79;85;87;98;89;95;100;90;122;91;123;102;92;136;93;94;101;135;103;125;104;105;124;106;107;113;126;115;128;117;118;119;138;120;137;121;127;130;129;139;131;132;141;133;134;140;142;144;145;143;146;147;148;149;150;151
];;

let step1_maddloop_in_regs_right, step1_maddloop_out_regs_right =
  get_input_output_regs
    (snd MADDLOOP_STEP2_X30_EXEC)
    [0,Array.length (snd MADDLOOP_STEP2_X30_EXEC) - 4];;

let step1_maddloop_in_regs_left, step1_maddloop_out_regs_left =
  get_input_output_regs
    (snd OUTERLOOP_STEP1_EXEC)
    [(fst (assoc "maddloop_neon" outerloop_step1_labels),
      fst (assoc "inner_loop_postamble" outerloop_step1_labels) - 4)];;

(* Note: step1_maddloop_out_regs_left will not be used later,
  and step1_maddloop_out_regs_right will be shrunk to exclude
  registers that are not really outputs. *)
assert
  (sort (fun x y -> compare x y < 0) step1_maddloop_in_regs_right =
   sort (fun x y -> compare x y < 0) step1_maddloop_in_regs_left);;

let step1_maddloop_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in precond *)
  (subtract step1_maddloop_in_regs_right [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

(* Build state equalities. *)
let step1_maddloop_eqin = new_definition
  (replace_eq_mems_regs step1_maddloop_eqin_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step1_maddloop_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X27 s1 = word (k DIV 4 - 1) /\ read X27 s1' = word (k DIV 4 - 1) /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = z /\ read X1 s1' = z /\
      read X2 s1 = m /\ read X2 s1' = m /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let step1_maddloop_maychanges_left = build_maychanges
  step1_maddloop_out_regs_left
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step1_maddloop_maychanges_right = build_maychanges
  step1_maddloop_out_regs_right
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step1_maddloop_eqout = new_definition
  (replace_eq_mems_regs step1_maddloop_eqin_regs
    `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (step1_maddloop_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
     (read X27 s1 = word 0 /\
      read X27 s1' = word 0 /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * (k - 4))) /\
      read X1 s1' = word_add z (word (8 * (k - 4))) /\
      read X2 s1 = word_add m (word (8 * (k - 4))) /\
      read X2 s1' = word_add m (word (8 * (k - 4))) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      read X30 s1' = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // Equalities
      eq_mems z m sp m_precalc k (s1,s1') /\
      eq_regs(s1,s1'))`);;

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step1_mc; word pc2:int64,LENGTH maddloop_step2_x30_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step1_maddloop_eqin
    step1_maddloop_eqout
    outerloop_step1_mc
    (fst (assoc "maddloop_neon" outerloop_step1_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step1_labels))
    step1_maddloop_maychanges_left
    maddloop_step2_x30_mc
    0
    (Array.length (snd MADDLOOP_STEP2_X30_EXEC))
    step1_maddloop_maychanges_right
    `\(s:armstate). 152 * (k DIV 4 - 1)` `\(s:armstate). 152 * (k DIV 4 - 1)`;;

(* Some registers should not be abbreviated because they will be
   used as memory addresses. *)
let regs_no_abbrev_left =
  let pcbeg = fst (assoc "maddloop_neon" outerloop_step1_labels) and
      pcend = fst (assoc "inner_loop_postamble" outerloop_step1_labels) - 8
      in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd OUTERLOOP_STEP1_EXEC) [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition *)
  let addr_regs = update_key_list pcend
      [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`] addr_regs in
  let res = tl (backward_taint_analysis (snd OUTERLOOP_STEP1_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;

let regs_no_abbrev_right =
  let pcbeg = 0 and
      pcend = Array.length (snd MADDLOOP_STEP2_X30_EXEC) - 8
      in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd MADDLOOP_STEP2_X30_EXEC)
      [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition *)
  let addr_regs = update_key_list pcend
      [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`] addr_regs in
  let res = tl (backward_taint_analysis (snd MADDLOOP_STEP2_X30_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;


(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

(* Yeah, this is ugly.. this is to simplify address that X1 register
   stores. *)
extra_word_CONV := (GEN_REWRITE_CONV I [WORD_RULE
    `word_add (word_add z (word (8 * 4 * i))) (word 32):int64 =
     word_add z (word (8 * 4 * i + 32))`])::!extra_word_CONV;;

let MADDLOOP_STEP1_STEP2_X30_EQUIV = prove(equiv_goal,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP1_EXEC; fst MADDLOOP_STEP2_X30_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k` ASSUME_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `3 <= k4` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN

  (* iterates 'k / 4 - 1' times, where k is the number of words in modulus *)
  ENSURES2_WHILE_PAUP_TAC `0` `k4 - 1`
    `pc+outerloop_step1_label_maddloop_neon`
    `pc+(outerloop_step1_label_inner_loop_postamble-4)`
    `pc2:num`
    `pc2+(LENGTH maddloop_step2_x30_mc-4)`
    (replace_eq_mems_regs step1_maddloop_eqin_regs
    `\(i:num) s1 s1'.
      // loop counter
      read X27 s1 = word (k4 - (i + 1)) /\
      read X27 s1' = word (k4 - (i + 1)) /\
      // pointers and constants
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * 4 * i)) /\
      read X1 s1' = word_add z (word (8 * 4 * i)) /\
      read X2 s1 = word_add m (word (8 * 4 * i)) /\
      read X2 s1' = word_add m (word (8 * 4 * i)) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * 12 * i)) /\
      read X30 s1' = word_add m_precalc (word (8 * 12 * i)) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
      // equalities
      eq_mems z m sp m_precalc (k:num) (s1,s1') /\
      eq_regs(s1,s1')`)
    `\(i:num) (s:armstate). T` `\(i:num) (s:armstate). T`
    `\(i:num). 151`
    `\(i:num). 151`
    (* pre steps *)`0` `0`
    (* post steps *)`1` `1`
    (* num backedges *)`1` `1`
  THEN MAP_EVERY (fun t -> SUBST1_TAC
    ((REWRITE_CONV (fst MADDLOOP_STEP2_X30_EXEC::(map (snd o snd) (outerloop_step1_labels)))
      THENC NUM_REDUCE_CONV) t))
    [`outerloop_step1_label_inner_loop_postamble-4`;
     `LENGTH maddloop_step2_x30_mc-4`]
  THEN REWRITE_TAC (map (snd o snd) (outerloop_step1_labels @ outerloop_step1_labels))
  THEN REPEAT CONJ_TAC THENL [
    (* loop count which is k4-1 > 0. *)
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP DIVIDES_LE th)) THEN SIMPLE_ARITH_TAC;

    (* precond to loop entrance *)
    REWRITE_TAC[step1_maddloop_eqin;MULT_0; WORD_ADD_0; SUB_0; ASSUME `k DIV 4 = k4`] THEN
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONJ_TAC THENL [
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
      REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* the loop body. lockstep simulation is needed. *)
    ALL_TAC;

    (* backedge. *)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    UNDISCH_THEN `k DIV 4 = k4` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE ([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES])) THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC OUTERLOOP_STEP1_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC MADDLOOP_STEP2_X30_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `~(val (word (k4 - (i+1)):int64) = 0)` MP_TAC THENL [
      IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    CONJ_TAC THENL [
      REPEAT (CONJ_TAC THENL
        [FIRST_X_ASSUM MATCH_ACCEPT_TAC ORELSE ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];
        ALL_TAC]) THEN
      REPEAT (CONJ_TAC THENL [
        REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC]) THEN
      REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* postcond! *)
    ASM_REWRITE_TAC[step1_maddloop_eqout;SUB_REFL;MULT_0;
                    mk_equiv_regs;
                    BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC OUTERLOOP_STEP1_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC MADDLOOP_STEP2_X30_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    CONJ_TAC THENL [
      SUBGOAL_THEN `(val (word (k4 - (k4 - 1 + 1)):int64) = 0)`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [ SUBGOAL_THEN `k4 - (k4 - 1 + 1)=0` SUBST_ALL_TAC
        THENL [SIMPLE_ARITH_TAC;ALL_TAC]
        THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN
      REPLICATE_TAC 4 (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN

      SUBGOAL_THEN `8 * (k-4) = 8 * 4 * (k4-1)` SUBST_ALL_TAC THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      SUBGOAL_THEN `k4 - (k4 - 1 + 1) = 0` SUBST_ALL_TAC THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* loop trip count *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC;
  ] THEN

  REPEAT STRIP_TAC THEN
  (* replace k DIV 4 with k4. *)
  FIND_ABBREV_THEN "k4" SUBST_ALL_TAC THEN
  FIND_ABBREV_THEN "k" (SUBST_ALL_TAC o GSYM) THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,i) s = ..
      2. bignum_from_memory (z+4*(i+1),4) s = ..
      3. bignum_from_memory (z+4*(i+2),k-4*(i+2)) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*(i+1)`;`4*(i+2)`]
      BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th ->
    MP_TAC (REWRITE_RULE[ARITH_RULE `4*(i+2) - 4*(i+1)=4`] th)) THEN

  REWRITE_TAC([BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs]) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(i + 1) + 1 = i + 2` SUBST_ALL_TAC THENL [ARITH_TAC;ALL_TAC] THEN

  (* start *)
  ENSURES2_INIT_TAC "s0" "s0'" THEN

  RULE_ASSUM_TAC(CONV_RULE (DEPTH_CONV NUM_MULT_CONV)) THEN
  CONV_TAC (DEPTH_CONV NUM_MULT_CONV) THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* loop counter is larger than 0. *)
  SUBGOAL_THEN `1 <= (k4 - (i + 1))` (LABEL_TAC "HBOUND") THENL [
    UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;
    ALL_TAC
  ] THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC OUTERLOOP_STEP1_EXEC
    (1--length inst_map) state_to_abbrevs (Some regs_no_abbrev_left) THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC MADDLOOP_STEP2_X30_EXEC
    (1--length inst_map) inst_map state_to_abbrevs
    (Some regs_no_abbrev_right) THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MESON[]`forall (a:A). exists x. a = x`] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; ARITH_RULE`8*4*z+32 = 8*4*(z+1)`;
                ARITH_RULE`8*12*z+96 = 8*12*(z+1)`] THEN
    REPEAT CONJ_TAC THENL [
      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      (* updates in zi': splitting now! *)
      REWRITE_TAC[ARITH_RULE`32=8*4`; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
              CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;LEFT_ADD_DISTRIB] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]
    ];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV_backup;;

(* Now horizontally compose MADDLOOP_STEP1_STEP2_X30_EQUIV and
   MADDLOOP_STEP2_X30_STEP2_EQUIV *)

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step1_mc; word pc2:int64,LENGTH outerloop_step2_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61 /\
     // Extra!
     k < 2 EXP 32`
    step1_maddloop_eqin
    step1_maddloop_eqout
    outerloop_step1_mc
    (fst (assoc "maddloop_neon" outerloop_step1_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step1_labels))
    step1_maddloop_maychanges_left
    outerloop_step2_mc
    (fst (assoc "maddloop_neon" outerloop_step2_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step2_labels))
    step2_maddloop_x30_maychanges
    `\(s:armstate). 152 * (k DIV 4 - 1)` `\(s:armstate). 151 * (k DIV 4 - 1)`;;

let eqout_TRANS = prove(
  `!s s2 s'
    z m m_precalc sp k outerloop_counter.
        step1_maddloop_eqout (s,s') z m m_precalc sp k outerloop_counter /\
        step2_maddloop_x30_eqout (s',s2) z m m_precalc sp k outerloop_counter
    ==> step1_maddloop_eqout (s,s2) z m m_precalc sp k outerloop_counter`,
  REWRITE_TAC[step1_maddloop_eqout;step2_maddloop_x30_eqout;mk_equiv_regs]
  THEN REPEAT STRIP_TAC THEN (TRY (ASM_REWRITE_TAC[] THEN NO_TAC)) THEN
  ASM_MESON_TAC[]);;

let MADDLOOP_STEP1_STEP2_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * (k + 4)))
        [word pc:int64, LENGTH outerloop_step1_mc;
         word pc3:int64, LENGTH maddloop_step2_x30_mc] /\
      ALL (nonoverlapping (z,8 * (k + 4)))
        [word pc3:int64, LENGTH maddloop_step2_x30_mc;
         word pc2:int64, LENGTH outerloop_step2_mc] /\
      ALL (nonoverlapping
        (word pc3:int64, LENGTH maddloop_step2_x30_mc))
        [m,8 * k; m_precalc,8 * 12 * (k DIV 4 - 1); sp,128] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM (fun th ->
      if can (find_term (fun t -> name_of t = "nonoverlapping")) (concl th)
      then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst MADDLOOP_STEP2_X30_EXEC;
       fst OUTERLOOP_STEP2_EXEC;
       fst OUTERLOOP_STEP1_EXEC;GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN (* resolve nonoverlapping between z and pc/pc2 *)

    SUBGOAL_THEN `?pc3.
        nonoverlapping_modulo (2 EXP 64) (val (z:int64),8 * (2 EXP 32 + 4)) (pc3,608) /\
        nonoverlapping_modulo (2 EXP 64) (val (z:int64),8 * (2 EXP 32 + 4)) (pc3,608) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,608) (val (m:int64),8 * 2 EXP 32) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,608)
        (val (m_precalc:int64),8 * 12 * ((2 EXP 32) DIV 4 - 1)) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,608) (val (sp:int64),128) /\
        4 divides val (word pc3:int64)` MP_TAC THENL [
      MAP_EVERY (fun t -> SUBST_ALL_TAC (NUM_COMPUTE_CONV t)) [`2 EXP 32`] THEN
      REPEAT (FIRST_X_ASSUM (K ALL_TAC)) THEN
      FIND_HOLE_TAC;

      ALL_TAC
    ] THEN
    STRIP_TAC THEN EXISTS_TAC `pc3:num` THEN
    ASM_REWRITE_TAC[] THEN
    (* Now we have 4 goals that can be subsumed by the larger nonoverlapping assumptions *)
    REPEAT STRIP_TAC THENL [
      NONOVERLAPPING_TAC;
      NONOVERLAPPING_TAC;
      NONOVERLAPPING_TAC;
      NONOVERLAPPING_TAC
    ];

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (MADDLOOP_STEP1_STEP2_X30_EQUIV, MADDLOOP_STEP2_X30_STEP2_EQUIV)
    (step1_maddloop_eqin,step2_maddloop_x30_eqin,step1_maddloop_eqin)
    eqout_TRANS
    (OUTERLOOP_STEP1_EXEC,MADDLOOP_STEP2_X30_EXEC,OUTERLOOP_STEP2_EXEC));;

(* ------------------------------------------------------------------------- *)
(* Equivalence between the outerloop blocks (identical).                     *)
(* ------------------------------------------------------------------------- *)

let inst_map = (1--167);;

let step1_outerloop_in_regs, step1_outerloop_out_regs =
  get_input_output_regs
    (snd OUTERLOOP_STEP2_EXEC)
    [(0,fst (assoc "maddloop_neon" outerloop_step2_labels) - 4)];;

let step1_outerloop_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear in step3_outerloop_eqin *)
  (subtract step1_outerloop_in_regs [`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step1_outerloop_eqin = new_definition
  (replace_eq_mems_regs step1_outerloop_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step1_outerloop_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = z /\ read X1 s1' = z /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // others
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let step1_outerloop_maychanges = build_maychanges
  step1_outerloop_out_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step1_outerloop_eqout_regs = build_equiv_regs
  (subtract step1_outerloop_out_regs [`X27`;`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step1_outerloop_eqout = new_definition
  (replace_eq_mems_regs step1_outerloop_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
  (step1_outerloop_eqout:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (// Actual values of pointers and constants
    read X27 s1 = word (k DIV 4 - 1) /\ read X27 s1' = word (k DIV 4 - 1) /\
    read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = z /\ read X1 s1' = z /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // others
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k+4)))
     [word pc:int64,LENGTH outerloop_step1_mc; word pc2:int64,LENGTH outerloop_step2_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc:int64,LENGTH outerloop_step1_mc; word pc2:int64,LENGTH outerloop_step2_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step1_outerloop_eqin
    step1_outerloop_eqout
    outerloop_step1_mc
    0x0
    (fst (assoc "maddloop_neon" outerloop_step1_labels))
    step1_outerloop_maychanges
    outerloop_step2_mc
    0x0
    (fst (assoc "maddloop_neon" outerloop_step2_labels))
    step1_outerloop_maychanges
    `\(s:armstate). 167` `\(s:armstate). 167`;;

(* Some registers should not be abbreviated because they will be
   used as memory addresses. *)
let regs_no_abbrev =
  let pcbeg = 0 and
      pcend = fst (assoc "maddloop_neon" outerloop_step1_labels) - 4 in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd OUTERLOOP_STEP1_EXEC) [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition *)
  let addr_regs = (pcend,[`X27`;`X0`;`X1`;`X2`;`SP`;`X30`])::addr_regs in
  let res = tl (backward_taint_analysis (snd OUTERLOOP_STEP1_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;


(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;


let OUTERLOOP_STEP1_STEP2_EQUIV = prove(equiv_goal,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP1_EXEC; fst OUTERLOOP_STEP2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k) s = bignum_from_memory (z,k) s2' into two parts:
      1. bignum_from_memory (z,4) s = ..
      2. bignum_from_memory (z+4,k) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4`] BIGNUM_FROM_MEMORY_EQ_SPLIT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit" (REWRITE_RULE[ARITH_RULE`8*4=32`]th2))
  THEN

  (** Initialize **)
  REWRITE_TAC[step1_outerloop_eqin;step1_outerloop_eqout;mk_equiv_regs;
              mk_equiv_regs2;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC OUTERLOOP_STEP1_EXEC
    (1--(List.length inst_map)) state_to_abbrevs (Some regs_no_abbrev) THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC OUTERLOOP_STEP2_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs (Some regs_no_abbrev) THEN


  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    (* updates of loop counter (x27) *)
    CONJ_TAC THENL [
      REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT;WORD_SUB2]
      THEN CONJ_TAC THENL [
        AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC
      ];
      ALL_TAC] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT;WORD_SUB2] THEN
      REPEAT CONJ_TAC THENL [
        AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC];
      ALL_TAC] THEN
    (* only two goals here for memory equality.. let's expand memory :> bytes. *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (NUM_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

let OUTERLOOP_STEP1_STEP2_EQUIV_EXT,extra_regs_equiv =
  extend_first_equiv_for_seq_composition
    OUTERLOOP_STEP1_STEP2_EQUIV
    MADDLOOP_STEP1_STEP2_EQUIV
    step1_outerloop_eqout
    step1_maddloop_eqin;;

let STEP1_OUTERLOOP_EQOUT_IMPLIES_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs_equiv,`extra_regs_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        step1_outerloop_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs_equiv (s1,s1') ==>
        step1_maddloop_eqin (s1,s1') z m m_precalc sp k outerloop_counter`),
    REWRITE_TAC([step1_outerloop_eqout;step1_maddloop_eqin;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let OUTERLOOP_MADDLOOP_STEP1_STEP2_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_STEP1_STEP2_EQUIV_EXT
    MADDLOOP_STEP1_STEP2_EQUIV
    STEP1_OUTERLOOP_EQOUT_IMPLIES_EQIN;;


(* ------------------------------------------------------------------------- *)
(* Equivalence between the inner_loop_postamble blocks (identical).          *)
(* ------------------------------------------------------------------------- *)

let inst_map = (1--
  ((Array.length (snd OUTERLOOP_STEP1_EXEC) - fst (assoc "inner_loop_postamble" outerloop_step1_labels)) / 4));;

let step1_inner_loop_postamble_in_regs,
    step1_inner_loop_postamble_out_regs =
  get_input_output_regs
    (snd OUTERLOOP_STEP1_EXEC)
    [(fst (assoc "inner_loop_postamble" outerloop_step1_labels),
      Array.length (snd OUTERLOOP_STEP1_EXEC) - 4)];;

let step1_inner_loop_postamble_eqin_regs = build_equiv_regs
  (* exclude pointers and loop counter because they will explicitly appear later *)
  (subtract step1_inner_loop_postamble_in_regs [`X0`;`X1`;`X2`;`SP`;`X30`]);;

let step1_inner_loop_postamble_eqin = new_definition
  (replace_eq_mems_regs step1_inner_loop_postamble_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step1_inner_loop_postamble_eqin
      :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word (8 * (k - 4))) /\
    read X1 s1' = word_add z (word (8 * (k - 4))) /\
    read X2 s1 = word_add m (word (8 * (k - 4))) /\
    read X2 s1' = word_add m (word (8 * (k - 4))) /\
    read SP s1 = sp /\
    read SP s1' = sp /\
    read X30 s1 = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
    read X30 s1' = word_add m_precalc (word (8 * 12 * (k DIV 4 - 1))) /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 = word outerloop_counter /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\
    // Equalities
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs(s1,s1'))`);;


(* output states and maychange *)

let step1_inner_loop_postamble_maychanges = build_maychanges
  step1_inner_loop_postamble_out_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let step1_inner_loop_postamble_eqout_regs = build_equiv_regs
  (subtract step1_inner_loop_postamble_out_regs [`X0`;`X1`;`X2`;`SP`;`X30`;`X26`]);;

let step1_inner_loop_postamble_eqout = new_definition
  (replace_eq_mems_regs step1_inner_loop_postamble_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (step1_inner_loop_postamble_eqout
      :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word 32) /\
    read X1 s1' = word_add z (word 32) /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = m_precalc /\ read X30 s1' = m_precalc /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1 = m_precalc /\
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read (memory :> bytes64 (word_add sp (word 16))) s1 =
        word_sub (word outerloop_counter) (word 1) /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' =
        word_sub (word outerloop_counter) (word 1) /\
    read X26 s1 = word_sub (word outerloop_counter) (word 1) /\
    read X26 s1' = word_sub (word outerloop_counter) (word 1) /\
    // Equalities
    eq_mems z m sp m_precalc k (s1,s1') /\
    eq_regs (s1,s1'))`);;

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH outerloop_step1_mc; word pc2:int64,LENGTH outerloop_step2_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc:int64,LENGTH outerloop_step1_mc; word pc2:int64,LENGTH outerloop_step2_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    step1_inner_loop_postamble_eqin
    step1_inner_loop_postamble_eqout
    outerloop_step1_mc
    (fst (assoc "inner_loop_postamble" outerloop_step1_labels))
    (Array.length (snd (OUTERLOOP_STEP1_EXEC)))
    step1_inner_loop_postamble_maychanges
    outerloop_step2_mc
    (fst (assoc "inner_loop_postamble" outerloop_step2_labels))
    (Array.length (snd (OUTERLOOP_STEP2_EXEC)))
    step1_inner_loop_postamble_maychanges
    `\(s:armstate). 17` `\(s:armstate). 17`;;

(* Some registers should not be abbreviated because they will be
   used as memory addresses. *)
let regs_no_abbrev =
  let pcbeg = (fst (assoc "inner_loop_postamble" outerloop_step1_labels)) and
      pcend = (Array.length (snd (OUTERLOOP_STEP1_EXEC))) - 4 in
  let addr_regs = map (fun (x,y) -> x,[y])
      (collect_mem_address_regs (snd OUTERLOOP_STEP1_EXEC) [pcbeg,pcend]) in
  (* add regs whose exact expressions must be preserved for proving postcondition
     X26 is the outer loop counter *)
  let addr_regs = update_key_list pcend [`X0`;`X1`;`X2`;`SP`;`X30`;`X26`] addr_regs in
  let res = tl (backward_taint_analysis (snd OUTERLOOP_STEP1_EXEC)
    [pcbeg,pcend] addr_regs) in
  List.map (fun pcdiv4 -> try assoc (pcdiv4 * 4) res with _ -> [])
    ((pcbeg / 4) -- (pcend / 4));;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let INNER_LOOP_POSTAMBLE_STEP1_STEP2_EQUIV = prove(equiv_goal,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP1_EXEC; fst OUTERLOOP_STEP2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* prepare memory loads *)
  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,k-4) s = ..
      2. bignum_from_memory (z+4*(k-4),4) s = ..
      3. bignum_From_memory (z+4*k,4) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*k4-4`;`4*k4`] BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4*k4-(4*k4-4) = 4 /\ (4*k4+4)-(4*k4)=4` MP_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN (fun th ->
    DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit" (REWRITE_RULE[th]th2))) THEN

  (** Initialize **)
  REWRITE_TAC[step1_inner_loop_postamble_eqin;step1_inner_loop_postamble_eqout;
              mk_equiv_regs;mk_equiv_regs2;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC OUTERLOOP_STEP1_EXEC
    (1--(List.length inst_map)) state_to_abbrevs (Some regs_no_abbrev) THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC OUTERLOOP_STEP2_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs (Some regs_no_abbrev)
    THEN

  (* deal with '8 * (4 * k4 - 4) + 32, 8 * (4 * k4 - 4) + 40, ..' first *)
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 32 = 8 * 4 * k4` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 40 = 8 * 4 * k4 + 8` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 48 = 8 * 4 * k4 + 16` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 56 = 8 * 4 * k4 + 24` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[ARITH_RULE`(4 * x) DIV 4 = x`] THEN
    REWRITE_TAC[WORD_RULE`word_add (word_sub (word_add k a) a) b = word_add k b`;
                WORD_RULE`word_sub(word_add k a) a = k`] THEN
    (* only one goal here..
      memory :> bytes (z + 8 * (4 * k4 - 4)), and
      memory :> bytes (z + 8 * 4 * k4). *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

let OUTERLOOP_MADDLOOP_STEP1_STEP2_EQUIV_EXT,extra_regs_equiv =
  extend_first_equiv_for_seq_composition
    OUTERLOOP_MADDLOOP_STEP1_STEP2_EQUIV
    INNER_LOOP_POSTAMBLE_STEP1_STEP2_EQUIV
    step1_maddloop_eqout step1_inner_loop_postamble_eqin;;

let STEP1_OUTERLOOP_MADDLOOP_EQOUT_IMPLIES_BODY_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs_equiv,`extra_regs_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        step1_maddloop_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs_equiv (s1,s1') ==>
        step1_inner_loop_postamble_eqin (s1,s1') z m m_precalc sp k outerloop_counter`),
    REWRITE_TAC([step1_maddloop_eqout;step1_inner_loop_postamble_eqin;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let OUTERLOOP_FULL_STEP1_STEP2_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_MADDLOOP_STEP1_STEP2_EQUIV_EXT
    INNER_LOOP_POSTAMBLE_STEP1_STEP2_EQUIV
    STEP1_OUTERLOOP_MADDLOOP_EQOUT_IMPLIES_BODY_EQIN;;


(* ========================================================================= *)
(*       Equivalence between the original bignum_emontredc_8n - Step 1       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Equivalence between the maddloop bodies after (k/4) - 1 iterations.       *)
(* ------------------------------------------------------------------------- *)

let original_maddloop_in_left_regs, original_maddloop_out_left_regs =
    get_input_output_regs (snd BIGNUM_EMONTREDC_8N_EXEC)
      [(fst (assoc "maddloop" bignum_emontredc_8n_labels),
        (fst (assoc "madddone" bignum_emontredc_8n_labels) - 4))];;

let original_maddloop_in_right_regs, original_maddloop_out_right_regs =
    get_input_output_regs (snd OUTERLOOP_STEP1_EXEC)
      [(fst (assoc "maddloop_neon" outerloop_step1_labels),
        (fst (assoc "inner_loop_postamble" outerloop_step1_labels) - 4))];;

assert (subtract original_maddloop_in_left_regs [`X4`;`X5`;`X6`;`X7`] =
        subtract original_maddloop_in_right_regs
          [`Q17`;`Q18`;`Q19`;`Q20`;`Q28`;`Q30`;`Q29`; (* and two pointers *)`SP`;`X30`]);;

let original_maddloop_eq_regs = build_equiv_regs
  (subtract original_maddloop_in_left_regs ([`X4`;`X5`;`X6`;`X7`] @ [`X1`;`X2`;`X27`]));;

(*
 * ---- LEFT -----
 * x4 = word (bigdigit zn (4*i)):int64     // i is the outer loop counter; rebased to 0 in the spec/proof
 * x5 = word (bigdigit zn (4*i+1)):int64
 * x6 = word (bigdigit zn (4*i+2)):int64
 * x7 = word (bigdigit zn (4*i+3)):int64
 *
 * ---- RIGHT ----
 * (temporary) v20: [z[4*i],  z[4*i+1]]
 * (temporary) v21: [z[4*i+2],z[4*i+3]]

 * v29: word_join (word 0xffffffff:int64) (word 0xffffffff:int64):int128

 * vpre00 .req v30 =
  let v20 = word_join (word (bigdigit zn (4*i+1)):int64)
                      (word (bigdigit zn (4*i)):int64):int128 in
    word_join (usimd2 (\x. word_subword x (32,32): (32)word) v20)
              (usimd2 (\x. word_subword x (32,32): (32)word) v20):int128

 * vpre01 .req v28 =
  let v20 = word_join (word (bigdigit zn (4*i+1)):int64)
                      (word (bigdigit zn (4*i)):int64):int128 in
    word_zx (usimd2 (\x. word_subword x (0,32): (32)word) v20):int128

 * vpre02 .req v17 =
  let v20 = word_join (word (bigdigit zn (4*i+1)):int64)
                      (word (bigdigit zn (4*i)):int64):int128 in
    usimd2 (\x. word_join
            (word_subword x (0,32):(32)word) (word_subword x (32,32):(32)word)
            : (64)word) v20

 * vpre10 .req v18 =
  let v21 = word_join (word (bigdigit zn (4*i+3)):int64)
                      (word (bigdigit zn (4*i+2)):int64):int128 in
    word_join (usimd2 (\x. word_subword x (32,32): (32)word) v21)
              (usimd2 (\x. word_subword x (32,32): (32)word) v21):int128

 * vpre11 .req v19 =
  let v21 = word_join (word (bigdigit zn (4*i+3)):int64)
                      (word (bigdigit zn (4*i+2)):int64):int128 in
    word_zx (usimd2 (\x. word_subword x (0,32): (32)word) v21):int128

 * vpre12 .req v20 =
  let v21 = word_join (word (bigdigit zn (4*i+3)):int64)
                      (word (bigdigit zn (4*i+2)):int64):int128 in
    usimd2 (\x. word_join
            (word_subword x (0,32):(32)word) (word_subword x (32,32):(32)word)
            : (64)word) v21
 * bignum_from_memory (word_add sp (word 32),12) s = z_precalc zn
 * bignum_from_memory (m_precalc, 12*(k DIV 4 - 1)) s = m_precalc mn (k DIV 4 - 1)
 *)

let original_maddloop_eqin = new_definition
  (replace_eq_regs original_maddloop_eq_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (original_maddloop_eqin:(armstate#armstate)->int64->int64->int64->int64->
                            num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X27 s1 = word (8 * (k - 4)) /\ read X27 s1' = word (k DIV 4 - 1) /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = z /\ read X1 s1' = z /\
      read X2 s1 = m /\ read X2 s1' = m /\

      // Outer loop counter
      read X26 s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\

      // Stack pointer (original version does not use stack)
      read SP s1' = sp /\

      // Numbers
      (exists zn'.
        bignum_from_memory (word_add z (word 32),k) s1 = zn' /\
        bignum_from_memory (word_add z (word 32),k) s1' = zn') /\
      (exists mn.
        bignum_from_memory (m,k) s1 = mn /\
        bignum_from_memory (m,k) s1' = mn /\
        bignum_from_memory (m_precalc, 12*(k DIV 4 - 1)) s1' = get_m_precalc mn (k DIV 4 - 1)) /\
      (exists w.
        read X3 s1 = w /\
        read (memory :> bytes64 sp) s1' = w) /\

      // m_precalc exists only in the STEP1 program!
      read X30 s1' = m_precalc /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\

      read Q29 s1' = word_join (word 0xffffffff:int64) (word 0xffffffff:int64):int128 /\

      (exists zn.
        bignum_from_memory (z,4) s1 = zn /\
        bignum_from_memory (z,4) s1' = zn /\

        bignum_from_memory (word_add sp (word 32),12) s1' = get_z_precalc zn /\

        // X4~X7 which are inputs of the original maddloop
        read X4 s1 = word (bigdigit zn 0) /\
        read X5 s1 = word (bigdigit zn 1) /\
        read X6 s1 = word (bigdigit zn 2) /\
        read X7 s1 = word (bigdigit zn 3) /\

        // Q17,Q18,Q19,Q20,Q28,Q30,Q29 that are inputs in STEP1 only
        read Q30 s1' = (let v20 = word_join (word (bigdigit zn 1):int64)
                        (word (bigdigit zn 0):int64):int128 in
          word_join (usimd2 (\x. word_subword x (32,32): (32)word) v20)
                    (usimd2 (\x. word_subword x (32,32): (32)word) v20):int128) /\

        read Q28 s1' = (let v20 = word_join (word (bigdigit zn 1):int64)
                        (word (bigdigit zn 0):int64):int128 in
          word_zx (usimd2 (\x. word_subword x (0,32): (32)word) v20):int128) /\

        read Q17 s1' = (let v20 = word_join (word (bigdigit zn 1):int64)
                        (word (bigdigit zn 0):int64):int128 in
          usimd2 (\x. word_join
                  (word_subword x (0,32):(32)word) (word_subword x (32,32):(32)word)
                  : (64)word) v20) /\

        read Q18 s1' = (let v21 = word_join (word (bigdigit zn 3):int64)
                        (word (bigdigit zn 2):int64):int128 in
          word_join (usimd2 (\x. word_subword x (32,32): (32)word) v21)
                    (usimd2 (\x. word_subword x (32,32): (32)word) v21):int128) /\

        read Q19 s1' = (let v21 = word_join (word (bigdigit zn 3):int64)
                        (word (bigdigit zn 2):int64):int128 in
          word_zx (usimd2 (\x. word_subword x (0,32): (32)word) v21):int128) /\

        read Q20 s1' = (let v21 = word_join (word (bigdigit zn 3):int64)
                        (word (bigdigit zn 2):int64):int128 in
          usimd2 (\x. word_join
                  (word_subword x (0,32):(32)word) (word_subword x (32,32):(32)word)
                  : (64)word) v21)) /\

      // Register equalities
      eq_regs(s1,s1'))`);;

let original_maddloop_eqout = new_definition
  (replace_eq_regs original_maddloop_eq_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (original_maddloop_eqout:(armstate#armstate)->int64->int64->int64->int64->
                            num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X27 s1 = word 0 /\
      read X27 s1' = word 0 /\
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * (k - 4))) /\
      read X1 s1' = word_add z (word (8 * (k - 4))) /\
      read X2 s1 = word_add m (word (8 * (k - 4))) /\
      read X2 s1' = word_add m (word (8 * (k - 4))) /\
      read SP s1' = sp /\

      // Outer loop counter
      read X26 s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\

      // Stack pointer (original version does not use stack)
      read SP s1' = sp /\

      // Numbers
      (exists zn.
        bignum_from_memory (z,4) s1 = zn /\
        bignum_from_memory (z,4) s1' = zn) /\
      (exists zn'.
        bignum_from_memory (word_add z (word 32),k) s1 = zn' /\
        bignum_from_memory (word_add z (word 32),k) s1' = zn') /\
      (exists mn.
        bignum_from_memory (m,k) s1 = mn /\
        bignum_from_memory (m,k) s1' = mn /\
        bignum_from_memory (m_precalc, 12*(k DIV 4 - 1)) s1' = get_m_precalc mn (k DIV 4 - 1)) /\
      (exists w.
        read X3 s1 = w /\
        read (memory :> bytes64 sp) s1' = w) /\

      // m_precalc exists only in the STEP1 program!
      read X30 s1' = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\

      read Q29 s1' = word_join (word 0xffffffff:int64) (word 0xffffffff:int64):int128 /\

      // Register equalities
      eq_regs(s1,s1'))`);;

let original_maddloop_maychanges_left = build_maychanges
    original_maddloop_out_left_regs `MAYCHANGE [
        memory :> bytes (z:int64,8 * (k + 4))]`;;

let original_maddloop_maychanges_right = build_maychanges
    original_maddloop_out_right_regs `MAYCHANGE [
        memory :> bytes (z:int64,8 * (k + 4))]`;;

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH bignum_emontredc_8n_mc;
      word pc2:int64,LENGTH outerloop_step1_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    original_maddloop_eqin
    original_maddloop_eqout
    bignum_emontredc_8n_mc
    (fst (assoc "maddloop" bignum_emontredc_8n_labels))
    (fst (assoc "madddone" bignum_emontredc_8n_labels))
    original_maddloop_maychanges_left
    outerloop_step1_mc
    (fst (assoc "maddloop_neon" outerloop_step1_labels))
    (fst (assoc "inner_loop_postamble" outerloop_step1_labels))
    original_maddloop_maychanges_right
    `\(s:armstate). 143 * (k DIV 4 - 1)` `\(s:armstate). 152 * (k DIV 4 - 1)`;;

let actions = [
  ("replace", 0, 17, 0, 43);
  ("equal", 17, 42, 43, 68);
  ("replace", 42, 47, 68, 71);
  ("equal", 47, 49, 71, 73);
  ("delete", 49, 50, 73, 73);
  ("equal", 50, 56, 73, 79);
  ("replace", 56, 61, 79, 82);
  ("equal", 61, 63, 82, 84);
  ("delete", 63, 64, 84, 84);
  ("equal", 64, 74, 84, 94);
  ("replace", 74, 79, 94, 98);
  ("equal", 79, 81, 98, 100);
  ("delete", 81, 82, 100, 100);
  ("equal", 82, 89, 100, 107);
  ("replace", 89, 94, 107, 110);
  ("equal", 94, 96, 110, 112);
  ("delete", 96, 97, 112, 112);
  ("equal", 97, 106, 112, 121);
  ("replace", 106, 111, 121, 124);
  ("equal", 111, 113, 124, 126);
  ("delete", 113, 114, 126, 126);
  ("equal", 114, 122, 126, 134);
  ("replace", 122, 127, 134, 137);
  ("equal", 127, 129, 137, 139);
  ("delete", 129, 130, 139, 139);
  ("equal", 130, 133, 139, 142);
  ("insert", 133, 133, 142, 143);
  ("equal", 133, 139, 143, 149);
  ("replace", 139, 141, 149, 150);
  ("replace", 141, 142, 150, 151);
];;

let actions = break_equal_loads actions
    (snd BIGNUM_EMONTREDC_8N_EXEC)
    (fst (assoc "maddloop" bignum_emontredc_8n_labels))
    (snd OUTERLOOP_STEP1_EXEC)
    (fst (assoc "maddloop_neon" outerloop_step1_labels));;

let _org_extra_word_CONV = !extra_word_CONV;;

let ITE_WORD_NOT_XOR =
  let th = prove(`!c (w:int64). (if c then w else (word_not w)) =
      word_xor w (if c then word 0 else word_UINT_MAX)`,
    REWRITE_TAC[word_UINT_MAX;DIMINDEX_64] THEN BITBLAST_TAC) in
  (CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[word_UINT_MAX;DIMINDEX_64]) th;;

extra_word_CONV :=
  [GEN_REWRITE_CONV I ([
    WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
    WORD_RULE
    (* Yeah, this is ugly.. this is to simplify address that X1 register
      stores. *)
    `word_add (word_add z (word (8 * 4 * i))) (word 32):int64 =
     word_add z (word (8 * 4 * i + 32))`;
    WORD_RULE `val (word (bigdigit mn (4 * i + x)):int64) * val (word (bigdigit zn 0):int64) =
           val (word (bigdigit zn 0):int64) * val (word (bigdigit mn (4 * i + x)):int64)`;
    WORD_RULE `val (word (bigdigit mn (4 * i + x)):int64) * val (word (bigdigit zn 1):int64) =
              val (word (bigdigit zn 1):int64) * val (word (bigdigit mn (4 * i + x)):int64)`;
    WORD_RULE `val (word (bigdigit mn (4 * i + x)):int64) * val (word (bigdigit zn 2):int64) =
              val (word (bigdigit zn 2):int64) * val (word (bigdigit mn (4 * i + x)):int64)`;
    WORD_RULE `val (word (bigdigit mn (4 * i + x)):int64) * val (word (bigdigit zn 3):int64) =
              val (word (bigdigit zn 3):int64) * val (word (bigdigit mn (4 * i + x)):int64)`;
    ARITH_RULE `(4 * i + 4) + 1 = 4 * i + 5`;
    ARITH_RULE `(4 * i + 4) + 2 = 4 * i + 6`;
    ARITH_RULE `(4 * i + 4) + 3 = 4 * i + 7`;
    ITE_WORD_NOT_XOR;
    WORD_VAL;
    ]
    @ bigdigit_get_z_precalc_thms
    (* bigdigit_get_m_precalc_thms will be added just before symbolic simulation. *)
    )]
  @ (!extra_word_CONV);;


let MADDLOOP_ORIGINAL_STEP1_EQUIV = prove(equiv_goal,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_EMONTREDC_8N_EXEC; fst OUTERLOOP_STEP1_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k` ASSUME_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `3 <= k4` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN

  (* iterates 'k / 4 - 1' times, where k is the number of words in modulus *)
  (let the_invariant = rhs (snd (strip_forall (concl original_maddloop_eqin))) in
  let loop_invariant =
    list_mk_abs ([`i:num`;`s1:armstate`;`s1':armstate`],
      (subst [`read X27 s1 = word (8 * (k - 4 * (i + 1)))`,`read X27 s1 = word (8 * (k - 4))`;
              `read X27 s1' = word (k4 - (i + 1))`,`read X27 s1' = word (k DIV 4 - 1)`;
              `read X1 s1 = word_add z (word (8 * 4 * i))`,`read X1 s1 = z`;
              `read X1 s1' = word_add z (word (8 * 4 * i))`,`read X1 s1' = z`;
              `read X2 s1 = word_add m (word (8 * 4 * i))`,`read X2 s1 = m`;
              `read X2 s1' = word_add m (word (8 * 4 * i))`,`read X2 s1' = m`;
              `read X30 s1' = word_add m_precalc (word (8 * 12 * i))`,`read X30 s1' = m_precalc`;
              ] the_invariant)) in

  ENSURES2_WHILE_PAUP_TAC `0` `k4 - 1`
    `pc+bignum_emontredc_8n_label_maddloop`
    `pc+(bignum_emontredc_8n_label_madddone-4)`
    `pc2+outerloop_step1_label_maddloop_neon`
    `pc2+(outerloop_step1_label_inner_loop_postamble-4)`
    (replace_eq_mems_regs original_maddloop_eq_regs loop_invariant)
    `\(i:num) (s:armstate). read ZF s <=> i = k4 - 1`
    `\(i:num) (s:armstate). T`
    `\(i:num). 142`
    `\(i:num). 151`
    (* pre steps *)`0` `0`
    (* post steps *)`1` `1`
    (* num backedges *)`1` `1`)
  THEN MAP_EVERY (fun t -> SUBST1_TAC
    ((REWRITE_CONV (map (snd o snd) (bignum_emontredc_8n_labels @ outerloop_step1_labels))
      THENC NUM_REDUCE_CONV) t))
    [`bignum_emontredc_8n_label_madddone-4`;
     `outerloop_step1_label_inner_loop_postamble-4`]
  THEN REWRITE_TAC (map (snd o snd) (bignum_emontredc_8n_labels @ outerloop_step1_labels))
  THEN REPEAT CONJ_TAC THENL [
    (* loop count which is k4-1 > 0. *)
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP DIVIDES_LE th)) THEN SIMPLE_ARITH_TAC;

    (* precond to loop entrance *)
    REWRITE_TAC[original_maddloop_eqin;MULT_0; WORD_ADD_0; SUB_0; ASSUME `k DIV 4 = k4`] THEN
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONJ_TAC THENL [
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
      REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* the loop body. lockstep simulation is needed. *)
    ALL_TAC;

    (* backedge. *)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    UNDISCH_THEN `k DIV 4 = k4` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE ([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES])) THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC BIGNUM_EMONTREDC_8N_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC OUTERLOOP_STEP1_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `~(val (word (k4 - (i+1)):int64) = 0) /\ ~(i = k4 - 1)` MP_TAC THENL [
      IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    CONJ_TAC THENL [
      REPEAT (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
      REPEAT (CONJ_TAC THENL [
        REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC]) THEN
      REWRITE_TAC([mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* postcond! *)
    ASM_REWRITE_TAC[original_maddloop_eqout;SUB_REFL;MULT_0;
                    mk_equiv_regs;
                    BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    ARM_N_STUTTER_LEFT_TAC BIGNUM_EMONTREDC_8N_EXEC [1] None THEN
    ARM_N_STUTTER_RIGHT_TAC OUTERLOOP_STEP1_EXEC [1] "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    CONJ_TAC THENL [
      SUBGOAL_THEN `(val (word (k4 - (k4 - 1 + 1)):int64) = 0)`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [ SUBGOAL_THEN `k4 - (k4 - 1 + 1)=0` SUBST_ALL_TAC
        THENL [SIMPLE_ARITH_TAC;ALL_TAC]
        THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN
      REPLICATE_TAC 4 (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN

      SUBGOAL_THEN `8 * (k-4) = 8 * 4 * (k4-1)` SUBST_ALL_TAC THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      SUBGOAL_THEN `k4 - (k4 - 1 + 1) = 0 /\ 8 * (k - 4 * (k4 - 1 + 1)) = 0`
        (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
      (* counter *)
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* loop trip count *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC;

    (* loop trip count *)
    REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
    SIMPLE_ARITH_TAC
  ] THEN

  REPEAT STRIP_TAC THEN
  (* replace k DIV 4 with k4. *)
  FIND_ABBREV_THEN "k4" SUBST_ALL_TAC THEN
  FIND_ABBREV_THEN "k" (SUBST_ALL_TAC o GSYM) THEN

  (* split 'bignum_from_memory (z+32,k) s = bignum_from_memory (z+32,k) s2' into three parts:
      1. bignum_from_memory (z+32,(i-4)) s = ..
      2. bignum_from_memory (z+32+4*i,4) s = ..
      3. bignum_from_memory (z+32+4*(i+1),k-4*(i+1)) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`word_add z (word 32):int64`;`4*k4`;`4*i`;`4*(i+1)`]
      BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th ->
    MP_TAC (REWRITE_RULE[ARITH_RULE `4*(i+1) - 4*i=4`;WORD_ADD_ASSOC_CONSTS] th)) THEN

  REWRITE_TAC([BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs]) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(i + 1) + 1 = i + 2` SUBST_ALL_TAC THENL [ARITH_TAC;ALL_TAC] THEN

  (* start *)
  ENSURES2_INIT_TAC "s0" "s0'" THEN

  RULE_ASSUM_TAC(CONV_RULE (DEPTH_CONV NUM_MULT_CONV)) THEN
  (* simplify assumptions on Q regs *)
  RULE_ASSUM_TAC(REWRITE_RULE[LET_DEF;LET_END_DEF;usimd2;DIMINDEX_64;WORD_BITMANIP_SIMP_LEMMAS]) THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  (* loop counter is larger than 0. *)
  SUBGOAL_THEN `1 <= (k4 - (i + 1))` (LABEL_TAC "HBOUND") THENL [
    UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;
    ALL_TAC
  ] THEN

  SUBGOAL_THEN `(i+1) <= (k4 - 1)` MP_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  DISCH_THEN (fun le_th ->
    MAP_EVERY (fun th -> ASSUME_TAC (MATCH_MP th le_th)) bigdigit_get_m_precalc_thms) THEN

  EQUIV_STEPS_TAC actions BIGNUM_EMONTREDC_8N_EXEC OUTERLOOP_STEP1_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MESON[]`forall (a:A). exists x. a = x`] THEN
  CONJ_TAC THENL [
    (* The X registers *)
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS; ARITH_RULE`8*4*z+32 = 8*4*(z+1)`;
                ARITH_RULE`8*12*z+96 = 8*12*(z+1)`] THEN
    (* The memory reads *)
    ASM_REWRITE_TAC[ARITH_RULE`8*4 = 32`;ARITH_RULE`8*12=96`] THEN
    (* The Q registers *)
    REPEAT CONJ_TAC THENL [
      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      IMP_REWRITE_TAC[WORD_SUB2] THEN
      REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
      ARITH_TAC;

      (* updates in zi': splitting now! *)
      REWRITE_TAC[ARITH_RULE`32=8*4`; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
              CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;LEFT_ADD_DISTRIB;
                  ARITH_RULE`32+8*4*i=8*4*i+32`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];

      (* mn. *)
      MESON_TAC[];

      (* The zn. *)
      EXISTS_TAC `zn:num` THEN
      REWRITE_TAC[LET_DEF;LET_END_DEF;usimd2;WORD_BITMANIP_SIMP_LEMMAS;DIMINDEX_64;DIMINDEX_32];

      (* Counter thingy *)
      REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC
    ];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV_backup;;

(* ------------------------------------------------------------------------- *)
(* Equivalence between the outerloop blocks.                                 *)
(* ------------------------------------------------------------------------- *)

let original_outerloop_in_left_regs, original_outerloop_out_left_regs =
    get_input_output_regs (snd BIGNUM_EMONTREDC_8N_EXEC)
      [(fst (assoc "outerloop" bignum_emontredc_8n_labels),
        (fst (assoc "maddloop" bignum_emontredc_8n_labels) - 4))];;

let original_outerloop_in_right_regs, original_outerloop_out_right_regs =
    get_input_output_regs (snd OUTERLOOP_STEP1_EXEC)
      [0, (fst (assoc "maddloop_neon" outerloop_step1_labels) - 4)];;

assert (set_eq (subtract original_outerloop_in_right_regs [`Q29`;`SP`])
               (subtract original_outerloop_in_left_regs [`X3`]));;

let original_outerloop_eqin_regs = build_equiv_regs
  (subtract original_outerloop_in_left_regs [`X3`;`X0`;`X1`;`X2`]);;


(*
 * ---- LEFT -----
 * read X3 s = w
 *
 * ---- RIGHT ----
 * v29: word_join (word 0xffffffff:int64) (word 0xffffffff:int64):int128
 * read (memory :> bytes64 sp) s = w

 * bignum_from_memory (word_add sp (word 32),12) s = z_precalc zn
 * bignum_from_memory (m_precalc, 12*(k DIV 4 - 1)) s = m_precalc mn (k DIV 4 - 1)
 *)

let original_outerloop_eqin = new_definition
  (replace_eq_regs original_outerloop_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (original_outerloop_eqin:(armstate#armstate)->int64->int64->int64->int64->
                             num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = z /\ read X1 s1' = z /\
      read X2 s1 = m /\ read X2 s1' = m /\

      // Outer loop counter
      read X26 s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\

      // Stack pointer (original version does not use stack)
      read SP s1' = sp /\

      // Numbers
      (exists zn'.
        bignum_from_memory (z,k+4) s1 = zn' /\
        bignum_from_memory (z,k+4) s1' = zn') /\
      (exists mn.
        bignum_from_memory (m,k) s1 = mn /\
        bignum_from_memory (m,k) s1' = mn /\
        bignum_from_memory (m_precalc, 12*(k DIV 4 - 1)) s1' = get_m_precalc mn (k DIV 4 - 1)) /\
      (exists w.
        read X3 s1 = w /\
        read (memory :> bytes64 sp) s1' = w) /\

      read Q29 s1' = word_join (word 0xffffffff:int64) (word 0xffffffff:int64):int128 /\

      // m_precalc exists only in the STEP1 program!
      read X30 s1' = m_precalc /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\

      // Register equalities
      eq_regs(s1,s1'))`);;


let original_outerloop_maychanges_left = build_maychanges
    original_outerloop_out_left_regs `MAYCHANGE [
        memory :> bytes (z:int64,8 * (k + 4))]`;;

let original_outerloop_maychanges_right = build_maychanges
    original_outerloop_out_right_regs `MAYCHANGE [
        memory :> bytes (z:int64,8 * (k + 4));
        memory :> bytes (sp:int64,128)]`;;

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH bignum_emontredc_8n_mc;
      word pc2:int64,LENGTH outerloop_step1_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc2:int64,LENGTH outerloop_step1_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    original_outerloop_eqin
    original_maddloop_eqin
    bignum_emontredc_8n_mc
    (fst (assoc "outerloop" bignum_emontredc_8n_labels))
    (fst (assoc "maddloop" bignum_emontredc_8n_labels))
    original_outerloop_maychanges_left
    outerloop_step1_mc
    0
    (fst (assoc "maddloop_neon" outerloop_step1_labels))
    original_outerloop_maychanges_right
    `\(s:armstate). 79` `\(s:armstate). 167`;;

let actions = [
  ("insert", 0, 0, 0, 1);
  ("equal", 0, 4, 1, 5);
  ("insert", 4, 4, 5, 6);
  ("equal", 4, 5, 6, 7);
  ("insert", 5, 5, 7, 27);
  ("equal", 5, 6, 27, 28);
  ("delete", 6, 9, 28, 28);
  ("equal", 9, 11, 28, 30);
  ("insert", 11, 11, 30, 31);
  ("equal", 11, 14, 31, 34);
  ("delete", 14, 15, 34, 34);
  ("equal", 15, 16, 34, 35);
  ("replace", 16, 17, 35, 37);
  ("equal", 17, 23, 37, 43);
  ("insert", 23, 23, 43, 63);
  ("equal", 23, 24, 63, 64);
  ("delete", 24, 27, 64, 64);
  ("equal", 27, 29, 64, 66);
  ("insert", 29, 29, 66, 67);
  ("equal", 29, 32, 67, 70);
  ("delete", 32, 33, 70, 70);
  ("equal", 33, 34, 70, 71);
  ("replace", 34, 35, 71, 73);
  ("equal", 35, 40, 73, 78);
  ("insert", 40, 40, 78, 79);
  ("equal", 40, 41, 79, 80);
  ("insert", 41, 41, 80, 100);
  ("equal", 41, 42, 100, 101);
  ("delete", 42, 45, 101, 101);
  ("equal", 45, 47, 101, 103);
  ("insert", 47, 47, 103, 104);
  ("equal", 47, 50, 104, 107);
  ("delete", 50, 51, 107, 107);
  ("equal", 51, 52, 107, 108);
  ("replace", 52, 53, 108, 110);
  ("equal", 53, 55, 110, 112);
  ("insert", 55, 55, 112, 113);
  ("equal", 55, 58, 113, 116);
  ("replace", 58, 59, 116, 117);
  ("equal", 59, 76, 117, 134);
  ("replace", 76, 79, 134, 167);
  ("equal", 79, 79, 167, 167);
];;

let actions = break_equal_loads actions
    (snd BIGNUM_EMONTREDC_8N_EXEC)
    (fst (assoc "outerloop" bignum_emontredc_8n_labels))
    (snd OUTERLOOP_STEP1_EXEC) 0;;

let _org_extra_word_CONV = !extra_word_CONV;;


extra_word_CONV :=
  [GEN_REWRITE_CONV I ([
    WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;]
    )]
  @ (!extra_word_CONV);;

let OUTERLOOP_ORIGINAL_STEP1_EQUIV = prove(equiv_goal,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP1_EXEC; fst BIGNUM_EMONTREDC_8N_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k) s = bignum_from_memory (z,k) s2' into two parts:
      1. bignum_from_memory (z,4) s = ..
      2. bignum_from_memory (z+4,k) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4`] BIGNUM_FROM_MEMORY_EQ_SPLIT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit"
    (REWRITE_RULE[ARITH_RULE`8*4=32`;ARITH_RULE`(4*k4+4)-4=4*k4`]th2))
  THEN

  (** Initialize **)
  REWRITE_TAC[original_outerloop_eqin;original_maddloop_eqin;mk_equiv_regs;
              mk_equiv_regs2;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  EQUIV_STEPS_TAC actions BIGNUM_EMONTREDC_8N_EXEC OUTERLOOP_STEP1_EXEC THEN

  (* here. we will need taint analysis again. *)
  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    (* updates of loop counter (x27) *)
    CONJ_TAC THENL [
      REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT;WORD_SUB2]
      THEN CONJ_TAC THENL [
        AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC
      ];
      ALL_TAC] THEN

    (* mn *)
    CONJ_TAC THENL [ MESON_TAC[]; ALL_TAC ] THEN

    (* zn *)
    EXISTS_TAC `bignum_from_memory (z,4) s79` THEN
    CONJ_TAC THENL [
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC
    ] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND;WORD_ADD_ASSOC_CONSTS] THEN
            CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC
    ] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;get_z_precalc;precalc_diffs_rev;bignum_of_wordlist] THEN
      REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_LT_CONV) THEN
      ASM_REWRITE_TAC[ARITH_RULE`8*0=0`;ARITH_RULE`8*1=8`;ARITH_RULE`8*2=16`;ARITH_RULE`8*3=24`;WORD_ADD_0] THEN
      (* rhs *)
      REPEAT_N 16 (ONCE_REWRITE_TAC [BIGNUM_FROM_MEMORY_EXPAND]) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      CONV_TAC ((LAND_CONV o REDEPTH_CONV) (NUM_EQ_CONV ORELSEC NUM_SUB_CONV)) THEN
      REWRITE_TAC [COND_CLAUSES] THEN
      CONV_TAC (REDEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_VAL] THEN REWRITE_TAC[LEFT_ADD_DISTRIB;MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_0] THEN NO_TAC;
      ALL_TAC
    ] THEN

    ASM_REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY;
      ARITH_RULE`8*0=0`;ARITH_RULE`8*1=8`;ARITH_RULE`8*2=16`;ARITH_RULE`8*3=24`;WORD_ADD_0] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_LT_CONV) THEN REWRITE_TAC[WORD_VAL] THEN
    (* The Q registers *)
    REWRITE_TAC[LET_DEF;LET_END_DEF;usimd2;DIMINDEX_64;WORD_BITMANIP_SIMP_LEMMAS] THEN
    NO_TAC;

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV_backup;;

let OUTERLOOP_MADDLOOP_ORIGINAL_STEP1_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_ORIGINAL_STEP1_EQUIV
    MADDLOOP_ORIGINAL_STEP1_EQUIV
    (TAUT `true`);;


(* ------------------------------------------------------------------------- *)
(* Equivalence between the last blocks (madddone - inner_loop_postamble).    *)
(* ------------------------------------------------------------------------- *)

let original_inner_loop_postamble_in_left_regs,
    original_inner_loop_postamble_out_left_regs =
    get_input_output_regs (snd BIGNUM_EMONTREDC_8N_EXEC)
      [(fst (assoc "madddone" bignum_emontredc_8n_labels),
        (fst (assoc "outerloop_end" bignum_emontredc_8n_labels) - 4))];;

let original_inner_loop_postamble_in_right_regs,
    original_inner_loop_postamble_out_right_regs =
    get_input_output_regs (snd OUTERLOOP_STEP1_EXEC)
      [fst (assoc "inner_loop_postamble" outerloop_step1_labels),
       Array.length (snd OUTERLOOP_STEP1_EXEC) - 4];;

assert (set_eq (subtract original_inner_loop_postamble_in_left_regs
                         [`X0`;`X1`;`X2`;`X26`])
               (subtract original_inner_loop_postamble_in_right_regs
                         [`X0`;`X1`;`X2`;`SP`;`X30`;`Q29`]));;

let original_inner_loop_postamble_eqin_regs = build_equiv_regs
  (subtract original_inner_loop_postamble_in_left_regs
            [`X0`;`X1`;`X2`;`X26`]);;

let original_inner_loop_postamble_eqin = new_definition
  (replace_eq_regs original_inner_loop_postamble_eqin_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    (original_inner_loop_postamble_eqin
        :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
          (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (// Actual values of pointers and constants
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * (k - 4))) /\
      read X1 s1' = word_add z (word (8 * (k - 4))) /\
      read X2 s1 = word_add m (word (8 * (k - 4))) /\
      read X2 s1' = word_add m (word (8 * (k - 4))) /\
      read SP s1' = sp /\

      // Outer loop counter
      read X26 s1 = word outerloop_counter /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word outerloop_counter /\

      // Stack pointer (original version does not use stack)
      read SP s1' = sp /\

      // Numbers
      (exists zn.
        bignum_from_memory (z,4) s1 = zn /\
        bignum_from_memory (z,4) s1' = zn) /\
      (exists zn'.
        bignum_from_memory (word_add z (word 32),k) s1 = zn' /\
        bignum_from_memory (word_add z (word 32),k) s1' = zn') /\
      (exists mn.
        bignum_from_memory (m,k) s1 = mn /\
        bignum_from_memory (m,k) s1' = mn /\
        bignum_from_memory (m_precalc, 12*(k DIV 4 - 1)) s1' = get_m_precalc mn (k DIV 4 - 1)) /\
      (exists w.
        read X3 s1 = w /\
        read (memory :> bytes64 sp) s1' = w) /\

      // m_precalc exists only in the STEP1 program!
      read X30 s1' = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\

      read Q29 s1' = word_join (word 0xffffffff:int64) (word 0xffffffff:int64):int128 /\

      // Register equalities
      eq_regs(s1,s1'))`);;

assert (original_inner_loop_postamble_out_left_regs =
        (subtract original_inner_loop_postamble_out_right_regs [`X30`]));;

let original_inner_loop_postamble_eqout_regs = build_equiv_regs
  (subtract original_inner_loop_postamble_out_left_regs
            [`X0`;`X1`;`X2`;`X26`]);;

let original_inner_loop_postamble_eqout = new_definition
  (replace_eq_regs original_inner_loop_postamble_eqout_regs
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
   (original_inner_loop_postamble_eqout
      :(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k outerloop_counter <=>
   (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
    read X1 s1 = word_add z (word 32) /\
    read X1 s1' = word_add z (word 32) /\
    read X2 s1 = m /\ read X2 s1' = m /\
    read SP s1' = sp /\
    // Preserved value of m_precalc
    read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
    // Outer loop counter
    read X26 s1 = word_sub (word outerloop_counter) (word 1) /\
    read X26 s1' = word_sub (word outerloop_counter) (word 1) /\
    read (memory :> bytes64 (word_add sp (word 16))) s1' =
        word_sub (word outerloop_counter) (word 1) /\

    read X30 s1' = m_precalc /\

    (exists zn.
      bignum_from_memory (z, k+4) s1 = zn /\
      bignum_from_memory (z, k+4) s1' = zn) /\
    (exists mn.
      bignum_from_memory (m,k) s1 = mn /\
      bignum_from_memory (m,k) s1' = mn /\
      bignum_from_memory (m_precalc,12 * (k DIV 4 - 1)) s1' =
      get_m_precalc mn (k DIV 4 - 1)) /\
    (exists w. read X3 s1 = w /\ read (memory :> bytes64 sp) s1' = w) /\
    read Q29 s1' = word_join (word 4294967295:int64) (word 4294967295:int64) /\

    eq_regs(s1,s1'))`);;

let original_inner_loop_postamble_maychanges_left = build_maychanges
  original_inner_loop_postamble_out_left_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4))]`;;

let original_inner_loop_postamble_maychanges_right = build_maychanges
  original_inner_loop_postamble_out_right_regs
  `MAYCHANGE [memory :> bytes (z:int64,8 * (k + 4));
              memory :> bytes (sp:int64,128)]`;;

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH bignum_emontredc_8n_mc;
      word pc2:int64,LENGTH outerloop_step1_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc2:int64,LENGTH outerloop_step1_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61`
    original_inner_loop_postamble_eqin
    original_inner_loop_postamble_eqout
    bignum_emontredc_8n_mc
    (fst (assoc "madddone" bignum_emontredc_8n_labels))
    (fst (assoc "outerloop_end" bignum_emontredc_8n_labels))
    original_inner_loop_postamble_maychanges_left
    outerloop_step1_mc
    (fst (assoc "inner_loop_postamble" outerloop_step1_labels))
    (Array.length (snd OUTERLOOP_STEP1_EXEC))
    original_inner_loop_postamble_maychanges_right
    `\(s:armstate). 14` `\(s:armstate). 17`;;

let INNER_LOOP_POSTAMBLE_ORIGINAL_STEP1_EQUIV = prove(equiv_goal,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst OUTERLOOP_STEP1_EXEC; fst BIGNUM_EMONTREDC_8N_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* prepare memory loads *)
  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `3 <= k4 /\ k4 < 2 EXP 59` MP_TAC THENL [ASM_ARITH_TAC;STRIP_TAC]
  THEN
  SUBGOAL_THEN `k = 4 * k4` (LABEL_TAC "HK_DO_NOT_CLEAR") THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* split 'bignum_from_memory (z,k+4) s = bignum_from_memory (z,k+4) s2' into three parts:
      1. bignum_from_memory (z,k-4) s = ..
      2. bignum_from_memory (z+4*(k-4),4) s = ..
      3. bignum_From_memory (z+4*k,4) s = .. *)
  MP_TAC (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4*k4-4`;`4*k4`] BIGNUM_FROM_MEMORY_EQ_SPLIT3)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4*k4-(4*k4-4) = 4 /\ (4*k4+4)-(4*k4)=4` MP_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN (fun th ->
    DISCH_THEN (fun th2 -> LABEL_TAC "Hmemsplit" (REWRITE_RULE[th]th2))) THEN
  (* split 'bignum_from_memory (z+32,k) s = bignum_from_memory (z+32,k) s2' into three parts:
      1. bignum_from_memory (z+32,k-4) s = ..
      3. bignum_From_memory (z+4*k,4) s = .. *)
  MP_TAC (GSYM (REWRITE_RULE
    [TAUT `(forall (x:A). b ==> P x) <=> (b ==> forall x. P x)`]
    (SPECL [`z:int64`;`4*k4+4`;`4`] BIGNUM_FROM_MEMORY_EQ_SPLIT))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4*k4-(4*k4-4) = 4 /\ (4*k4+4)-4=4*k4 /\ 8 * 4 = 32` MP_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN (fun th ->
    DISCH_THEN (fun th2 -> LABEL_TAC "Hmemmerge" (REWRITE_RULE[th]th2))) THEN

  (** Initialize **)
  REWRITE_TAC[original_inner_loop_postamble_eqin;
              original_inner_loop_postamble_eqout;
              mk_equiv_regs;mk_equiv_regs2;mk_equiv_bool_regs] THEN
  REMOVE_THEN "HK_DO_NOT_CLEAR" (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "HK_DO_NOT_CLEAR" th) THEN
  REWRITE_TAC[MESON[] `((exists (x:A). P x) /\ (exists (y:A). Q y) /\ R) <=>
             (((exists (x:A). P x) /\ (exists (y:A). Q y)) /\ R)`] THEN
  USE_THEN "Hmemmerge" (fun th -> REWRITE_TAC [th]) THEN
  USE_THEN "Hmemsplit" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE`(4 * x) DIV 4 = x`;
              WORD_ADD_ASSOC_CONSTS] THEN
  SUBGOAL_THEN `32 + 8 * (4 * k4 - 4) = 8*4*k4` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  DESTRUCT_EXISTS_ASSUMS_TAC THEN

  EQUIV_STEPS_TAC [("replace",0,14,0,17)]
    BIGNUM_EMONTREDC_8N_EXEC OUTERLOOP_STEP1_EXEC THEN

  (* deal with '8 * (4 * k4 - 4) + 32, 8 * (4 * k4 - 4) + 40, ..' first *)
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 32 = 8 * 4 * k4` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 40 = 8 * 4 * k4 + 8` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 48 = 8 * 4 * k4 + 16` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `8 * (4 * k4 - 4) + 56 = 8 * 4 * k4 + 24` SUBST_ALL_TAC THENL
  [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[MESON[] `!(x:A). exists y. x = y`] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    REWRITE_TAC[WORD_RULE`word_add (word_sub (word_add k a) a) b = word_add k b`;
                WORD_RULE`word_sub(word_add k a) a = k`] THEN
    (* now memory invariants *)
    CONJ_TAC THENL [
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
              CHANGED_TAC (CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];

      ALL_TAC
    ] THEN
    MESON_TAC[];

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

let OUTERLOOP_MADDLOOP_ORIGINAL_STEP1_EQUIV_EXT,extra_regs_equiv =
  extend_first_equiv_for_seq_composition
    OUTERLOOP_MADDLOOP_ORIGINAL_STEP1_EQUIV INNER_LOOP_POSTAMBLE_ORIGINAL_STEP1_EQUIV
    original_maddloop_eqout original_inner_loop_postamble_eqin;;

let EQOUT_IMPLIES_BODY_EQIN =
  REWRITE_RULE[] (prove(
    (vsubst [extra_regs_equiv,`extra_regs_equiv:armstate#armstate->bool`]
      `forall s1 s1' z m m_precalc sp k outerloop_counter.
        original_maddloop_eqout (s1,s1') z m m_precalc sp k outerloop_counter /\
        extra_regs_equiv (s1,s1') ==>
        original_inner_loop_postamble_eqin (s1,s1') z m m_precalc sp k outerloop_counter`),
    REWRITE_TAC([original_maddloop_eqout;original_inner_loop_postamble_eqin;mk_equiv_regs]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
    THEN MESON_TAC[]));;

let OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV =
  prove_equiv_seq_composition
    OUTERLOOP_MADDLOOP_ORIGINAL_STEP1_EQUIV_EXT
    INNER_LOOP_POSTAMBLE_ORIGINAL_STEP1_EQUIV
    EQOUT_IMPLIES_BODY_EQIN;;


(* ========================================================================= *)
(*           Horizontal composition of equivalences of outer loops:          *)
(* - OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV                                     *)
(* - OUTERLOOP_FULL_STEP1_STEP2_EQUIV                                        *)
(* - OUTERLOOP_FULL_STEP2_STEP3_EQUIV                                        *)
(* - OUTERLOOP_FULL_STEP3_STEP4_EQUIV                                        *)
(* ========================================================================= *)

(* Canonicalize OUTERLOOP_FULL_STEP1_STEP2_EQUIV and add Q29 *)
let add_Q29_to_precond equiv_th equiv_th_eqout =
  let dummy_equiv_with_Q29 =
    prove(`ensures2 arm (\(s,s2). mk_equiv_regs [Q29] (s,s2))
      (\(s,s2). T) (\(s,s2) (s',s2'). T) (\s. 0) (\s. 0)`,
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[LAMBDA_PAIR]) in
  fst (extend_first_equiv_for_seq_composition
    equiv_th
    dummy_equiv_with_Q29
    equiv_th_eqout
    (new_definition `_a_dummy_def = 10`));;

let OUTERLOOP_FULL_STEP1_STEP2_EQUIV_EXT0 =
  add_Q29_to_precond OUTERLOOP_FULL_STEP1_STEP2_EQUIV
    step1_inner_loop_postamble_eqout;;

let OUTERLOOP_FULL_STEP1_STEP2_EQUIV_EXT1 =
  REWRITE_RULE[
      MESON[mk_equiv_regs]`mk_equiv_regs [] (s,s2) = true`;
      GSYM CONJ_ASSOC;
      TAUT `P /\ Q /\ P <=> P /\ Q`]
    OUTERLOOP_FULL_STEP1_STEP2_EQUIV_EXT0;;

let step1_outerloop_eqin_ext = new_definition(
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    step1_outerloop_eqin_ext (s1,s1') z m m_precalc sp k
                  outerloop_counter <=>
    step1_outerloop_eqin (s1,s1') z m m_precalc sp k
                  outerloop_counter /\
                  mk_equiv_regs [Q29] (s1,s1') /\
                  mk_equiv_regs [X28] (s1,s1')`);;

let OUTERLOOP_FULL_STEP1_STEP2_EQUIV_EXT =
  REWRITE_RULE[GSYM step1_outerloop_eqin_ext]
    OUTERLOOP_FULL_STEP1_STEP2_EQUIV_EXT1;;

let step1_outerloop_eqin_ext = REWRITE_RULE[step1_outerloop_eqin]
  step1_outerloop_eqin_ext;;

(* Canonicalize OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV *)
let OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV0 =
  REWRITE_RULE[
      MESON[mk_equiv_regs]`mk_equiv_regs [] (s,s2) = true`;
      GSYM CONJ_ASSOC]
    OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV;;

let original_outerloop_eqin_ext = new_definition(
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    original_outerloop_eqin_ext (s1,s1') z m m_precalc sp k
                  outerloop_counter <=>
    original_outerloop_eqin (s1,s1') z m m_precalc sp k
                  outerloop_counter /\
                  mk_equiv_regs [X28] (s1,s1')`);;

let OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV_EXT =
  REWRITE_RULE[GSYM original_outerloop_eqin_ext]
    OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV0;;

let original_outerloop_eqin_ext = REWRITE_RULE
    [original_outerloop_eqin] original_outerloop_eqin_ext;;


(* Input and output state equivalences for the full lemma *)
(* Use the input of OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV *)
let outerloop_eqin = REWRITE_RULE [original_outerloop_eqin_ext]
  (new_definition (`
    forall s1 s1' z m m_precalc sp k outerloop_counter.
      outerloop_eqin (s1,s1') z m m_precalc sp k outerloop_counter <=>
      (original_outerloop_eqin_ext (s1,s1') z m m_precalc sp k outerloop_counter)`));;

(* Use the output of OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV but erase mk_equiv_regs
   because the equivalences won't be preserved *)
let outerloop_eqout =
  new_definition `
    forall s1 s1' z m m_precalc sp k outerloop_counter.
      outerloop_eqout (s1,s1') z m m_precalc sp k outerloop_counter <=>
    (read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word 32) /\
      read X1 s1' = word_add z (word 32) /\
      read X2 s1 = m /\ read X2 s1' = m /\
      read SP s1' = sp /\
      // Preserved value of m_precalc
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      // Outer loop counter
      read X26 s1 = word_sub (word outerloop_counter) (word 1) /\
      read X26 s1' = word_sub (word outerloop_counter) (word 1) /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' =
          word_sub (word outerloop_counter) (word 1) /\

      read X30 s1' = m_precalc /\

      (exists zn.
        bignum_from_memory (z, k+4) s1 = zn /\
        bignum_from_memory (z, k+4) s1' = zn) /\
      (exists mn.
        bignum_from_memory (m,k) s1 = mn /\
        bignum_from_memory (m,k) s1' = mn /\
        bignum_from_memory (m_precalc,12 * (k DIV 4 - 1)) s1' =
        get_m_precalc mn (k DIV 4 - 1)) /\
      (exists w. read X3 s1 = w /\ read (memory :> bytes64 sp) s1' = w) /\
      read Q29 s1' = word_join (word 4294967295:int64) (word 4294967295:int64) /\
      mk_equiv_regs [X28] (s1,s1'))`;;

let get_maychange equiv_th (get_left:bool): term =
  let c = concl equiv_th in
  let ensures2_const, args =
      strip_comb (snd (dest_imp (snd (strip_forall c)))) in
  let maychange_lambda = List.nth args 3 in
  let body = snd (strip_gabs maychange_lambda) in
  let a,b = dest_conj body in
  let maychange_s1_s2 = if get_left then a else b in
  fst (dest_comb (fst (dest_comb maychange_s1_s2)));;

let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH bignum_emontredc_8n_mc;
      word pc2:int64,LENGTH outerloop_step2_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc2:int64,LENGTH outerloop_step2_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61 /\
     // Extra!
     k < 2 EXP 32`
    outerloop_eqin
    outerloop_eqout
    bignum_emontredc_8n_mc
    (fst (assoc "outerloop" bignum_emontredc_8n_labels))
    (fst (assoc "outerloop_end" bignum_emontredc_8n_labels))
    (get_maychange OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV true)
    outerloop_step2_mc
    0
    (Array.length (snd OUTERLOOP_STEP2_EXEC))
    (get_maychange OUTERLOOP_FULL_STEP1_STEP2_EQUIV false)
    `\(s:armstate). (79 + 143 * (k DIV 4 - 1)) + 14`
    `\(s:armstate). (167 + 151 * (k DIV 4 - 1)) + 17`;;

let eqout_TRANS = prove(
  `forall s s2 s'
    z m m_precalc sp k outerloop_counter.
        original_inner_loop_postamble_eqout (s,s')
          z m m_precalc sp k outerloop_counter /\
        step1_inner_loop_postamble_eqout (s',s2)
          z m m_precalc sp k outerloop_counter /\
        mk_equiv_regs [Q29] (s',s2)
    ==> outerloop_eqout (s,s2) z m m_precalc sp k outerloop_counter`,
  REWRITE_TAC[original_inner_loop_postamble_eqout;
              step1_inner_loop_postamble_eqout;
              outerloop_eqout;mk_equiv_regs]
  THEN REPEAT STRIP_TAC THEN (TRY (ASM_REWRITE_TAC[] THEN NO_TAC)) THEN ASM_MESON_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL]);;

let OUTERLOOP_FULL_ORIGINAL_STEP2_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * (k + 4)))
        [word pc:int64, LENGTH bignum_emontredc_8n_mc;
         word pc3:int64, LENGTH outerloop_step1_mc;
         word pc2:int64, LENGTH outerloop_step2_mc] /\
      ALL (nonoverlapping (sp,128))
        [word pc3:int64, LENGTH outerloop_step1_mc;
         word pc2:int64, LENGTH outerloop_step2_mc] /\
      ALL (nonoverlapping
        (word pc3:int64, LENGTH outerloop_step1_mc))
        [m,8 * k; m_precalc,8 * 12 * (k DIV 4 - 1)] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    REPEAT (FIRST_X_ASSUM (fun th ->
      if can (find_term (fun t -> name_of t = "nonoverlapping")) (concl th)
      then MP_TAC th else NO_TAC)) THEN
    REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_EMONTREDC_8N_EXEC;
       fst OUTERLOOP_STEP2_EXEC;
       fst OUTERLOOP_STEP1_EXEC;GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN (* resolve nonoverlapping between z and pc/pc2 *)

    SUBGOAL_THEN `?pc3.
        nonoverlapping_modulo (2 EXP 64) (val (z:int64),8 * (2 EXP 32 + 4)) (pc3,1344) /\
        nonoverlapping_modulo (2 EXP 64) (val (sp:int64),128) (pc3,1344) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,1344) (val (m:int64),8 * 2 EXP 32) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,1344)
        (val (m_precalc:int64),8 * 12 * (2 EXP 32 DIV 4 - 1)) /\
        4 divides val (word pc3:int64)` MP_TAC THENL [
      MAP_EVERY (fun t -> SUBST_ALL_TAC (NUM_COMPUTE_CONV t)) [`2 EXP 32`] THEN
      REPEAT (FIRST_X_ASSUM (K ALL_TAC)) THEN
      FIND_HOLE_TAC;

      ALL_TAC
    ] THEN
    STRIP_TAC THEN EXISTS_TAC `pc3:num` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_GEN_TAC
    (OUTERLOOP_FULL_ORIGINAL_STEP1_EQUIV_EXT, OUTERLOOP_FULL_STEP1_STEP2_EQUIV_EXT)
    (original_outerloop_eqin_ext,step1_outerloop_eqin_ext,
     outerloop_eqin)
    eqout_TRANS
    (BIGNUM_EMONTREDC_8N_EXEC,OUTERLOOP_STEP1_EXEC,OUTERLOOP_STEP2_EXEC));;


(* Now + STEP2-STEP3. *)

let OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT0 =
  add_Q29_to_precond OUTERLOOP_FULL_STEP2_STEP3_EQUIV
    step2_inner_loop_postamble_eqout;;

let OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT1 =
  REWRITE_RULE[
      MESON[mk_equiv_regs]`mk_equiv_regs [] (s,s2) = true`;
      GSYM CONJ_ASSOC;
      TAUT `P /\ Q /\ P <=> P /\ Q`]
    OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT0;;

let step2_outerloop_eqin_ext = new_definition(
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    step2_outerloop_eqin_ext (s1,s1') z m m_precalc sp k
                  outerloop_counter <=>
    step2_outerloop_eqin (s1,s1') z m m_precalc sp k
                  outerloop_counter /\
                  mk_equiv_regs [Q29] (s1,s1') /\
                  mk_equiv_regs [X28] (s1,s1')`);;

let OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT2 =
  REWRITE_RULE[GSYM step2_outerloop_eqin_ext]
    OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT1;;

(* Different MAYCHANGE items order. *)
let maychange_eq_thm =
  prove(mk_eq(
      get_maychange OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT2 true,
      get_maychange OUTERLOOP_FULL_ORIGINAL_STEP2_EQUIV false),

    REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    EQ_TAC THENL [
      STRIP_TAC THEN MONOTONE_MAYCHANGE_TAC;
      STRIP_TAC THEN MONOTONE_MAYCHANGE_TAC;
    ]);;

let OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT =
  let c = concl OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT2 in
  let xs,body = strip_forall c in
  let th = prove(list_mk_forall (xs,
    subst[`(167 + 151 * (k DIV 4 - 1)) + 17`,
              `(167 + (44 + 151 * (k DIV 4 - 2)) + 107) + 17`] body),
    REPEAT STRIP_TAC THEN
    IMP_REWRITE_TAC[ARITH_RULE
      `16 <= k ==> (167 + 151 * (k DIV 4 - 1)) + 17 =
                   (167 + (44 + 151 * (k DIV 4 - 2)) + 107) + 17`] THEN
    ASM_MESON_TAC[OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT2]) in
  REWRITE_RULE[maychange_eq_thm] th;;

let step2_outerloop_eqin_ext = REWRITE_RULE[step2_outerloop_eqin]
  step2_outerloop_eqin_ext;;


let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH bignum_emontredc_8n_mc;
      word pc2:int64,LENGTH outerloop_step3_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc2:int64,LENGTH outerloop_step3_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61 /\
     // Extra!
     k < 2 EXP 32`
    outerloop_eqin
    outerloop_eqout
    bignum_emontredc_8n_mc
    (fst (assoc "outerloop" bignum_emontredc_8n_labels))
    (fst (assoc "outerloop_end" bignum_emontredc_8n_labels))
    (get_maychange OUTERLOOP_FULL_ORIGINAL_STEP2_EQUIV true)
    outerloop_step3_mc
    0
    (Array.length (snd OUTERLOOP_STEP3_EXEC))
    (get_maychange OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT false)
    `\(s:armstate). (79 + 143 * (k DIV 4 - 1)) + 14`
    `\(s:armstate). (168 + (44 + 151 * (k DIV 4 - 2)) + 105) + 17`;;

let eqout_TRANS = prove(
  `forall s s2 s'
    z m m_precalc sp k outerloop_counter.
        outerloop_eqout (s,s')
          z m m_precalc sp k outerloop_counter /\
        step2_inner_loop_postamble_eqout (s',s2)
          z m m_precalc sp k outerloop_counter /\
        mk_equiv_regs [Q29] (s',s2)
    ==> outerloop_eqout (s,s2) z m m_precalc sp k outerloop_counter`,
  REWRITE_TAC[original_inner_loop_postamble_eqout;
              step2_inner_loop_postamble_eqout;
              outerloop_eqout;mk_equiv_regs]
  THEN REPEAT STRIP_TAC THEN (TRY (ASM_REWRITE_TAC[] THEN NO_TAC)) THEN ASM_MESON_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL]);;

let OUTERLOOP_FULL_ORIGINAL_STEP3_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * (k + 4)))
        [word pc:int64, LENGTH bignum_emontredc_8n_mc;
         word pc3:int64, LENGTH outerloop_step2_mc;
         word pc2:int64, LENGTH outerloop_step3_mc] /\
      ALL (nonoverlapping (sp,128))
        [word pc3:int64, LENGTH outerloop_step2_mc;
         word pc2:int64, LENGTH outerloop_step3_mc] /\
      ALL (nonoverlapping
        (word pc3:int64, LENGTH outerloop_step2_mc))
        [m,8 * k; m_precalc,8 * 12 * (k DIV 4 - 1)] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    REPEAT (FIRST_X_ASSUM (fun th ->
      if can (find_term (fun t -> name_of t = "nonoverlapping")) (concl th)
      then MP_TAC th else NO_TAC)) THEN
    REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_EMONTREDC_8N_EXEC;
       fst OUTERLOOP_STEP2_EXEC;
       fst OUTERLOOP_STEP1_EXEC;GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN (* resolve nonoverlapping between z and pc/pc2 *)

    SUBGOAL_THEN `?pc3.
        nonoverlapping_modulo (2 EXP 64) (val (z:int64),8 * (2 EXP 32 + 4)) (pc3,1340) /\
        nonoverlapping_modulo (2 EXP 64) (val (sp:int64),128) (pc3,1340) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,1340) (val (m:int64),8 * 2 EXP 32) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,1340)
        (val (m_precalc:int64),8 * 12 * (2 EXP 32 DIV 4 - 1)) /\
        4 divides val (word pc3:int64)` MP_TAC THENL [
      MAP_EVERY (fun t -> SUBST_ALL_TAC (NUM_COMPUTE_CONV t)) [`2 EXP 32`] THEN
      REPEAT (FIRST_X_ASSUM (K ALL_TAC)) THEN
      FIND_HOLE_TAC;

      ALL_TAC
    ] THEN
    STRIP_TAC THEN EXISTS_TAC `pc3:num` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_GEN_TAC
    (OUTERLOOP_FULL_ORIGINAL_STEP2_EQUIV, OUTERLOOP_FULL_STEP2_STEP3_EQUIV_EXT)
    (outerloop_eqin,step2_outerloop_eqin_ext,
     outerloop_eqin)
    eqout_TRANS
    (BIGNUM_EMONTREDC_8N_EXEC,OUTERLOOP_STEP2_EXEC,OUTERLOOP_STEP3_EXEC));;


(* Next horizontal composition *)

let OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT0 =
  add_Q29_to_precond OUTERLOOP_FULL_STEP3_STEP4_EQUIV
    step3_inner_loop_postamble_eqout;;

let OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT1 =
  REWRITE_RULE[
      MESON[mk_equiv_regs]`mk_equiv_regs [] (s,s2) = true`;
      GSYM CONJ_ASSOC;
      TAUT `P /\ Q /\ P <=> P /\ Q`]
    OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT0;;

let step3_outerloop_eqin_ext = new_definition(
  `forall s1 s1' z m m_precalc sp k outerloop_counter.
    step3_outerloop_eqin_ext (s1,s1') z m m_precalc sp k
                  outerloop_counter <=>
    step3_outerloop_eqin (s1,s1') z m m_precalc sp k
                  outerloop_counter /\
                  mk_equiv_regs [Q29] (s1,s1') /\
                  mk_equiv_regs [X28] (s1,s1')`);;

let OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT2 =
  REWRITE_RULE[GSYM step3_outerloop_eqin_ext]
    OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT1;;

let maychange_eq_thm (* X2; X1; X29; X30; X28 = .. *)=
  prove(mk_eq(
      get_maychange OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT2 true,
      get_maychange OUTERLOOP_FULL_ORIGINAL_STEP3_EQUIV false),

    REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    EQ_TAC THENL [
      STRIP_TAC THEN MONOTONE_MAYCHANGE_TAC;
      STRIP_TAC THEN MONOTONE_MAYCHANGE_TAC;
    ]);;

let steps_eq_thm =
  ARITH_RULE`(212 + 151 * (k DIV 4 - 2)) + 122 =
            (168 + (44 + 151 * (k DIV 4 - 2)) + 105) + 17`;;

let OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT =
  REWRITE_RULE[maychange_eq_thm;steps_eq_thm]
  OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT2;;

let step3_outerloop_eqin_ext = REWRITE_RULE[step3_outerloop_eqin]
  step3_outerloop_eqin_ext;;


let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * (k + 4)))
     [word pc:int64,LENGTH bignum_emontredc_8n_mc;
      word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61 /\
     // Extra!
     k < 2 EXP 32`
    outerloop_eqin
    outerloop_eqout
    bignum_emontredc_8n_mc
    (fst (assoc "outerloop" bignum_emontredc_8n_labels))
    (fst (assoc "outerloop_end" bignum_emontredc_8n_labels))
    (get_maychange OUTERLOOP_FULL_ORIGINAL_STEP3_EQUIV true)
    bignum_emontredc_8n_cdiff_mc
    (fst (assoc "outerloop" bignum_emontredc_8n_cdiff_labels))
    (fst (assoc "outerloop_end" bignum_emontredc_8n_cdiff_labels))
    (get_maychange OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT false)
    `\(s:armstate). (79 + 143 * (k DIV 4 - 1)) + 14`
    `\(s:armstate). (168 + (44 + 151 * (k DIV 4 - 2)) + 105) + 17`;;

let eqout_TRANS = prove(
  `forall s s2 s'
    z m m_precalc sp k outerloop_counter.
        outerloop_eqout (s,s')
          z m m_precalc sp k outerloop_counter /\
        step3_inner_loop_postamble_eqout (s',s2)
          z m m_precalc sp k outerloop_counter /\
        mk_equiv_regs [Q29] (s',s2)
    ==> outerloop_eqout (s,s2) z m m_precalc sp k outerloop_counter`,
  REWRITE_TAC[original_inner_loop_postamble_eqout;
              step3_inner_loop_postamble_eqout;
              outerloop_eqout;mk_equiv_regs;mk_equiv_regs2]
  THEN REPEAT STRIP_TAC THEN (TRY (ASM_REWRITE_TAC[] THEN NO_TAC)) THEN ASM_MESON_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL]);;

let OUTERLOOP_FULL_EQUIV = prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z,8 * (k + 4)))
        [word pc:int64, LENGTH bignum_emontredc_8n_mc;
         word pc3:int64, LENGTH outerloop_step3_mc;
         word pc2:int64, LENGTH bignum_emontredc_8n_cdiff_mc] /\
      ALL (nonoverlapping (sp,128))
        [word pc3:int64, LENGTH outerloop_step3_mc;
         word pc2:int64, LENGTH bignum_emontredc_8n_cdiff_mc] /\
      ALL (nonoverlapping
        (word pc3:int64, LENGTH outerloop_step3_mc))
        [m,8 * k; m_precalc,8 * 12 * (k DIV 4 - 1)] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    REPEAT (FIRST_X_ASSUM (fun th ->
      if can (find_term (fun t -> name_of t = "nonoverlapping")) (concl th)
      then MP_TAC th else NO_TAC)) THEN
    REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_EMONTREDC_8N_EXEC;
       fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC;
       fst OUTERLOOP_STEP3_EXEC;GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN (* resolve nonoverlapping between z and pc/pc2 *)

    SUBGOAL_THEN `?pc3.
        nonoverlapping_modulo (2 EXP 64) (val (z:int64),8 * (2 EXP 32 + 4)) (pc3,1940) /\
        nonoverlapping_modulo (2 EXP 64) (val (sp:int64),128) (pc3,1940) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,1940) (val (m:int64),8 * 2 EXP 32) /\
        nonoverlapping_modulo (2 EXP 64) (pc3,1940)
        (val (m_precalc:int64),8 * 12 * (2 EXP 32 DIV 4 - 1)) /\
        4 divides val (word pc3:int64)` MP_TAC THENL [
      MAP_EVERY (fun t -> SUBST_ALL_TAC (NUM_COMPUTE_CONV t)) [`2 EXP 32`] THEN
      REPEAT (FIRST_X_ASSUM (K ALL_TAC)) THEN
      FIND_HOLE_TAC;

      ALL_TAC
    ] THEN
    STRIP_TAC THEN EXISTS_TAC `pc3:num` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_GEN_TAC
    (OUTERLOOP_FULL_ORIGINAL_STEP3_EQUIV, OUTERLOOP_FULL_STEP3_STEP4_EQUIV_EXT)
    (outerloop_eqin,step3_outerloop_eqin_ext,
     outerloop_eqin)
    eqout_TRANS
    (BIGNUM_EMONTREDC_8N_EXEC,OUTERLOOP_STEP3_EXEC,BIGNUM_EMONTREDC_8N_CDIFF_EXEC));;


(* ========================================================================= *)
(*         Equivalence of the outer loop including its actual backedges      *)
(* ========================================================================= *)

(* Extend OUTERLOOP_FULL_EQUIV by instantiating z as z+4i. *)
let OUTERLOOP_FULL_EQUIV_EXT =
  let equiv_th1 = SPECL
      [`pc:num`;`pc2:num`;`word_add z (word (8 * 4 * i)):int64`;`m:int64`;
       `m_precalc:int64`;`sp:int64`;`k:num`;
       `k4 - i`]
      OUTERLOOP_FULL_EQUIV in

  let equiv_comps = [
    `memory :> bytes (z, 8*4*i)`;
    `memory :> bytes (word_add z (word (8 * (4 * i + k + 4))),
              8 * (2 * k - (4 * i + k + 4)))`] and
    extra_precond = `
      4 * (i+1) <= k /\
      k < 2 EXP 32 /\
      16 <= k /\
      nonoverlapping (z:int64, 8*2*k) (sp:int64,128)` in
  let extra_equiv = `\(s,s2).
      (exists n.
        read (memory :> bytes (z, 8*4*i)) s = n /\
        read (memory :> bytes (z, 8*4*i)) s2 = n) /\
      (exists n.
        read (memory :> bytes (word_add z (word (8 * (4 * i + k + 4))),
            8 * (2 * k - (4 * i + k + 4)))) s = n /\
        read (memory :> bytes (word_add z (word (8 * (4 * i + k + 4))),
            8 * (2 * k - (4 * i + k + 4)))) s2 = n)` in
  let the_goal =
    let s::s_final::s2::s_final2::[] = map (fun n -> mk_var (n,`:armstate`))
      ["s";"s_final";"s2";"s_final2"] in
    let rel_maychange =
      let c = concl equiv_th1 in
      let e, args = strip_comb (snd (dest_imp (c))) in
      List.nth args 3 in
    list_mk_forall([s;s_final;s2;s_final2],
      mk_imp (
        list_mk_conj
          [list_mk_comb (rel_maychange,[mk_pair(s,s2);mk_pair(s_final,s_final2)]);
           extra_precond] (* range conditions *)
        ,
        mk_eq(mk_comb(extra_equiv,mk_pair(s,s2)),
              mk_comb(extra_equiv,mk_pair(s_final,s_final2))))) in

  let helpful_thm = prove(the_goal,
    REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT GEN_TAC THEN
    INTRO_TAC "(H1 H2) (HPRE1 HPRE2 HPRE3 HPRE4)" THEN
    MAP_EVERY (fun tm ->
      let l = list_mk_icomb "read" [tm;`s_final:armstate`] in
      let r = list_mk_icomb "read" [tm;`s:armstate`] in
      SUBGOAL_THEN (mk_eq (l,r)) ASSUME_TAC THENL [
        REMOVE_THEN "H1" MP_TAC THEN
        REWRITE_TAC[MAYCHANGE;SEQ_ID] THEN
        REWRITE_TAC[GSYM SEQ_ASSOC] THEN
        REWRITE_TAC[ASSIGNS_SEQ] THEN
        REWRITE_TAC[ASSIGNS_THM] THEN
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        READ_OVER_WRITE_ORTHOGONAL_TAC;
        ALL_TAC
      ]) equiv_comps THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(4 * i + k + 4) + 2 * k - (4 * i + k + 4) <= 2 * k` ASSUME_TAC
    THENL [
      IMP_REWRITE_TAC[ADD_SUB_SWAP2] THEN
      REWRITE_TAC[SUB_REFL; SUB_0; LE_REFL;GE] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    MAP_EVERY (fun tm ->
      let l = list_mk_icomb "read" [tm;`s_final2:armstate`] in
      let r = list_mk_icomb "read" [tm;`s2:armstate`] in
      SUBGOAL_THEN (mk_eq (l,r)) ASSUME_TAC THENL [
        REMOVE_THEN "H2" MP_TAC THEN
        REWRITE_TAC[MAYCHANGE;SEQ_ID] THEN
        REWRITE_TAC[GSYM SEQ_ASSOC] THEN
        REWRITE_TAC[ASSIGNS_SEQ] THEN
        REWRITE_TAC[ASSIGNS_THM] THEN
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        READ_OVER_WRITE_ORTHOGONAL_TAC;
        ALL_TAC
      ]) equiv_comps THEN
    ASM_REWRITE_TAC[]) in

  let equiv_th_ext =
    let thm_to_extend = equiv_th1 in
    let quants,body = strip_forall (concl thm_to_extend) in
    let body_l,body_r = dest_imp body in

    let the_precond = (* specific to this full equiv! *)
      list_mk_conj[body_l;`4 * (i+1) <= k`;
        `nonoverlapping (z:int64,8*2*k) (sp:int64,128)`] in

    let ensures_const,(the_step::the_pre::the_post::other_args) =
      strip_comb body_r in
    let enhanced_pre =
      let a,b = dest_gabs the_pre in
      mk_gabs(a,mk_conj(
        mk_comb(the_pre,a),mk_comb(extra_equiv,a))) in
    let enhanced_post =
      let a,b = dest_gabs the_post in
      mk_gabs(a,mk_conj(
        mk_comb(the_post,a),mk_comb(extra_equiv,a))) in
    let new_ensures = list_mk_forall(quants,
      mk_imp(the_precond,list_mk_comb(ensures_const,the_step::enhanced_pre::enhanced_post::other_args))) in

    REWRITE_RULE[] (prove(new_ensures,
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ENSURES2_CONJ_FRAME THEN
      CONJ_TAC THENL [
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC helpful_thm THEN
        ASM_MESON_TAC[];

        REWRITE_TAC[LAMBDA_PAIR_THM] THEN
        ASM_MESON_TAC [thm_to_extend]
      ])) in
  equiv_th_ext;;


let mainloop_eqin =
  new_definition (`
    forall s1 s1' z m m_precalc sp k.
      mainloop_eqin (s1,s1') z m m_precalc sp k <=>
       (read X0 s1 = word (k DIV 4) /\
        read X0 s1' = word (k DIV 4) /\
        read X1 s1 = z /\
        read X1 s1' = z /\
        read X2 s1 = m /\
        read X2 s1' = m /\
        read X12 s1 = word (k DIV 4 - 1) /\
        read X12 s1' = word (k DIV 4 - 1) /\
        read X26 s1 = word (k DIV 4) /\
        read X26 s1' = word (k DIV 4) /\
        read SP s1' = sp /\
        (exists zn'.
            bignum_from_memory (z,2 * k) s1 = zn' /\
            bignum_from_memory (z,2 * k) s1' = zn') /\
        (exists mn.
            bignum_from_memory (m,k) s1 = mn /\
            bignum_from_memory (m,k) s1' = mn /\
            bignum_from_memory (m_precalc,12 * (k DIV 4 - 1)) s1' =
              get_m_precalc mn (k DIV 4 - 1)) /\
        read X30 s1' = m_precalc /\
        mk_equiv_regs [X3; X28] (s1,s1'))`);;

let mainloop_eqout =
  new_definition (`
    forall s1 s1' z m sp k.
      mainloop_eqout (s1,s1') z m sp k <=>
       (read SP s1' = sp /\
        (exists zn'.
             bignum_from_memory (z,2 * k) s1 = zn' /\
             bignum_from_memory (z,2 * k) s1' = zn') /\
        (exists mn.
             bignum_from_memory (m,k) s1 = mn /\
             bignum_from_memory (m,k) s1' = mn) /\
        mk_equiv_regs [X0;X28] (s1,s1'))`);;


let equiv_goal = mk_equiv_statement
    `ALL (nonoverlapping (z,8 * 2 * k))
     [word pc:int64,LENGTH bignum_emontredc_8n_mc;
      word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     ALL (nonoverlapping (sp,128))
     [word pc2:int64,LENGTH bignum_emontredc_8n_cdiff_mc;
      m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 16 <= k /\ k < 2 EXP 61 /\
     // Extra!
     k < 2 EXP 32`
    mainloop_eqin
    mainloop_eqout
    bignum_emontredc_8n_mc
    (fst (assoc "main" bignum_emontredc_8n_labels))
    (fst (assoc "main_end" bignum_emontredc_8n_labels))
    (`MAYCHANGE
      [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16;
      X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [memory :> bytes (z,8 * 2 * k)] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]`)
    bignum_emontredc_8n_cdiff_mc
    (fst (assoc "precomp_loop_end" bignum_emontredc_8n_cdiff_labels))
    (fst (assoc "main_end" bignum_emontredc_8n_cdiff_labels))
    (`MAYCHANGE
      [Q29; Q2; Q12; Q27; Q17; Q30; Q28; Q21; Q31; Q23; Q24; Q3; Q16; Q26; Q11; Q5; Q8;
        Q4; Q15; Q9; Q18; Q20; Q19; Q14; Q25; Q1; Q7; Q10; Q13; Q0; Q6] ,,
      MAYCHANGE
      [X0; X27; X2; X22; X3; X21; X5; X6; X16; X25; X4; X9; X11; X7; X1; X29; X20;
        X19; X23; X12; X13; X26; X8; X14; X17; X15; X30; X10; X24; PC; X28] ,,
      MAYCHANGE [memory :> bytes (sp,128)] ,,
      MAYCHANGE [memory :> bytes (z,8 * 2 * k)] ,,
      MAYCHANGE [VF; CF; ZF; NF] ,, MAYCHANGE [events]`)
    `\(s:armstate). 2 + (k DIV 4) * ((79 + 143 * (k DIV 4 - 1)) + 14) + (k DIV 4 - 1) + 2`
    `\(s:armstate). 5 + (k DIV 4) * ((168 + (44 + 151 * (k DIV 4 - 2)) + 105) + 17) + (k DIV 4 - 1) + 2`;;

let MAINLOOP_EQUIV = prove(equiv_goal,

  REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES;SOME_FLAGS;
      fst BIGNUM_EMONTREDC_8N_EXEC;
      fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC; mainloop_eqin; mainloop_eqout;
      mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k` ASSUME_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `3 <= k4` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN

  ENSURES2_WHILE_PAUP_TAC `0` `k4:num`
    `pc+bignum_emontredc_8n_label_outerloop`
    `pc+bignum_emontredc_8n_label_outerloop_end`
    `pc2+slothy_outerloop`
    `pc2+slothy_outerloop_end`
    (`\(i:num) s1 s1'.
      // loop counter
      read X26 s1 = word (k4 - i) /\
      read (memory :> bytes64 (word_add sp (word 16))) s1' = word (k4 - i) /\
      // pointers and constants
      read X0 s1 = word (8 * (k - 4)) /\ read X0 s1' = word (8 * (k - 4)) /\
      read X1 s1 = word_add z (word (8 * 4 * i)) /\
      read X1 s1' = word_add z (word (8 * 4 * i)) /\
      read X2 s1 = m /\
      read X2 s1' = m /\
      read SP s1' = sp /\
      read X30 s1' = m_precalc /\
      (exists zn'.
          bignum_from_memory (z,2 * k) s1 = zn' /\
          bignum_from_memory (z,2 * k) s1' = zn') /\
      (exists mn.
          bignum_from_memory (m,k) s1 = mn /\
          bignum_from_memory (m,k) s1' = mn /\
          bignum_from_memory (m_precalc,12 * (k DIV 4 - 1)) s1' =
            get_m_precalc mn (k DIV 4 - 1)) /\
      (exists w. read X3 s1 = w /\ read (memory :> bytes64 sp) s1' = w) /\
      read Q29 s1' = (word_join (word 4294967295:int64) (word 4294967295:int64):int128) /\
      read (memory :> bytes64 (word_add sp (word 8))) s1' = m_precalc /\
      mk_equiv_regs [X28] (s1,s1')`)
    `\(i:num) (s:armstate). T`
    `\(i:num) (s:armstate). read X26 s = word (k4 - i)`
    `\(i:num). (79 + 143 * (k DIV 4 - 1)) + 14`
    `\(i:num). (168 + (44 + 151 * (k DIV 4 - 2)) + 105) + 17`
    (* pre steps *)`2` `5`
    (* post steps *)`2` `2`
    (* num backedges *)`1` `1` THEN
  REWRITE_TAC(map (snd o snd)
    (bignum_emontredc_8n_labels @ bignum_emontredc_8n_cdiff_labels)) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs] THEN
  REPEAT CONJ_TAC THENL [
    SIMPLE_ARITH_TAC;

    (* to loop entry *)
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    EQUIV_STEPS_TAC ["replace",0,2,0,5] BIGNUM_EMONTREDC_8N_EXEC
        BIGNUM_EMONTREDC_8N_CDIFF_EXEC THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_0; MULT_0; WORD_ADD_0] THEN
    CONJ_TAC THENL [
      CONJ_TAC THENL [
        (* (k4 - 1) << 5 = 8 * (k - 4) *)
        REWRITE_TAC[word_shl] THEN IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
        SUBGOAL_THEN `k4 - 1 < 2 EXP 64` (fun th -> REWRITE_TAC[th]) THENL [
          SIMPLE_ARITH_TAC; ALL_TAC
        ] THEN
        AP_TERM_TAC THEN EXPAND_TAC "k" THEN ARITH_TAC;

        ALL_TAC
      ] THEN

      CONJ_TAC THENL [
        (* (k4 - 1) << 5 = 8 * (k - 4) *)
        REWRITE_TAC[word_shl] THEN IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
        SUBGOAL_THEN `k4 - 1 < 2 EXP 64` (fun th -> REWRITE_TAC[th]) THENL [
          SIMPLE_ARITH_TAC; ALL_TAC
        ] THEN
        AP_TERM_TAC THEN EXPAND_TAC "k" THEN ARITH_TAC;

        ALL_TAC
      ] THEN

      CONV_TAC WORD_REDUCE_CONV THEN MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* loop body *)
    REPEAT STRIP_TAC THEN
    MP_TAC (OUTERLOOP_FULL_EQUIV_EXT (*SPECL
      [`pc:num`;`pc2:num`;`word_add z (word (8 * 4 * i)):int64`;`m:int64`;
       `m_precalc:int64`;`sp:int64`;`k:num`;
       `k4 - i`]
      OUTERLOOP_FULL_EQUIV)*)) THEN
    ANTS_TAC THENL [
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES;ALL;fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC;
          fst BIGNUM_EMONTREDC_8N_EXEC] THEN
      REPEAT CONJ_TAC THENL [
        NONOVERLAPPING_TAC;
        NONOVERLAPPING_TAC;
        NONOVERLAPPING_TAC;
        NONOVERLAPPING_TAC;
        NONOVERLAPPING_TAC;
        SIMPLE_ARITH_TAC
      ];

      ALL_TAC
    ] THEN
    MATCH_MP_TAC ENSURES2_WEAKEN2 THEN
    REPEAT CONJ_TAC THENL [
      (* precond implication *)
      REWRITE_TAC[outerloop_eqin;mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[MESON[]`forall x. exists (k:A). x = k`] THEN
      (* separated memory here *)
      SUBGOAL_THEN `exists zn'.
          read (memory :> bytes (z,8 * 2 * k)) s = zn' /\
          read (memory :> bytes (z,8 * 2 * k)) s' = zn'` MP_TAC THENL [
        ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      IMP_REWRITE_TAC[SPECL [`z:int64`;`2*k`;`4*i`;`4*i+(k+4)`]
        BIGNUM_FROM_MEMORY_EQ_SPLIT3] THEN
      REWRITE_TAC[ADD_SUB2] THEN
      DISCH_THEN (fun th -> IMP_REWRITE_TAC[th]) THEN
      REWRITE_TAC[MESON[]`exists (k:A). x = k`] THEN
      SIMPLE_ARITH_TAC;

      (* postcond implication *)
      REWRITE_TAC[outerloop_eqout;mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[MESON[]`forall x. exists (k:A). x = k`] THEN
      SUBGOAL_THEN `word_sub (word (k4 - i)) (word 1:int64) = word (k4 - (i + 1))`
        (fun th -> REWRITE_TAC[th]) THENL [
        IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
        [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ];
        ALL_TAC
      ] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      (* one last goal: read memory (z, 8*2*k) is the same *)
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      IMP_REWRITE_TAC[SPECL [`z:int64`;`2*k`;`4*i`;`4*i+(k+4)`]
        BIGNUM_FROM_MEMORY_EQ_SPLIT3] THEN
      REWRITE_TAC[ADD_SUB2] THEN
      EXISTS_TAC `i:num` THEN
      CONJ_TAC THENL [ ALL_TAC; SIMPLE_ARITH_TAC ] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;MESON[]`exists (k:A). x = k`];

      (* maychange subsume *)
      (* copied rom ENSURES2_FRAME_SUBSUMED_TAC *)
      REWRITE_TAC[subsumed;FORALL_PAIR_THM;SEQ_PAIR_SPLIT;ETA_AX;SOME_FLAGS] THEN
      REPEAT STRIP_TAC THEN
      (* two subgoals from here *)
      (fun (asl,g) ->
          let st,st' = rand(rator g), rand g in
          (FIRST_X_ASSUM (fun th ->
            if rand(concl th) = st' then
              MP_TAC th THEN MAP_EVERY SPEC_TAC [(st',st');(st,st)]
            else NO_TAC)) (asl,g)) THEN
      REWRITE_TAC[GSYM subsumed; ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC;
    ];


    (** backedge **)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    EQUIV_STEPS_TAC ["replace",0,1,0,1] BIGNUM_EMONTREDC_8N_EXEC
          BIGNUM_EMONTREDC_8N_CDIFF_EXEC THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_0; MULT_0; WORD_ADD_0] THEN
    SUBGOAL_THEN `~(val (word (k4 - i):int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL [
      IMP_REWRITE_TAC[VAL_WORD_EQ_ZERO] THEN
      SIMPLE_ARITH_TAC; ALL_TAC
    ] THEN
    REWRITE_TAC[MESON[]`exists (k:A). x = k`] THEN
    CONJ_TAC THENL [
      EXPAND_TAC "k4" THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (** to postcond **)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN
    EQUIV_STEPS_TAC ["replace",0,2,0,2] BIGNUM_EMONTREDC_8N_EXEC
          BIGNUM_EMONTREDC_8N_CDIFF_EXEC THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MESON[]`exists (k:A). x = k`] THEN
    MONOTONE_MAYCHANGE_CONJ_TAC;

    (* num steps *)
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NSUM_CONST_NUMSEG;SUB_0;MULT_CLAUSES] THEN
    IMP_REWRITE_TAC[SUB_ADD] THEN SIMPLE_ARITH_TAC;

    (* num steps 2*)
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NSUM_CONST_NUMSEG;SUB_0;MULT_CLAUSES] THEN
    IMP_REWRITE_TAC[SUB_ADD] THEN SIMPLE_ARITH_TAC
  ]);;


(* ========================================================================= *)
(*       Derive the correctness of the optimized loop using equiv and        *)
(*                              original spec                                *)
(* ========================================================================= *)

(* BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N + MAINLOOP_EQUIV *)

(* BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N with
  - number of steps rewritten
  - k4 not used *)
let BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N_NSTEP_REWRITTEN =
  prove(`forall k z m w a mn pc.
       w < 2 EXP 64 /\
       ~(k = 0) /\
       ~(k = 4) /\ 8 divides k /\
       nonoverlapping_modulo (2 EXP 64) (val z,8 * 2 * k) (pc,1020) /\
       nonoverlapping_modulo (2 EXP 64) (val z,8 * 2 * k) (val m,8 * k) /\
       a < 2 EXP (64 * 2 * k) /\
       mn < 2 EXP (64 * k)
       ==> ensures_n arm
           (\s.
                aligned_bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
                read PC s = word (pc + 36) /\
                read X12 s = word (k DIV 4 - 1) /\
                read X26 s = word (k DIV 4) /\
                read X1 s = z /\
                read X2 s = m /\
                read X3 s = word w /\
                bignum_from_memory (z,2 * k) s = a /\
                bignum_from_memory (m,k) s = mn)
           (\s.
                aligned_bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
                read PC s = word (pc + 996) /\
                ((mn * w + 1 == 0) (mod (2 EXP 64))
                 ==> mn * bignum_from_memory (z,k) s + a =
                     2 EXP (64 * k) *
                     (2 EXP (64 * k) * val (read X0 s) +
                      bignum_from_memory (word_add z (word (8 * k)),k) s)))
           (MAYCHANGE
            [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
             X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
            MAYCHANGE [memory :> bytes (z,8 * 2 * k)] ,,
            MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])
           (\s. 2 + k DIV 4 * ((79 + 143 * (k DIV 4 - 1)) + 14) +
                k DIV 4 - 1 + 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `2 + k4 * ((79 + 143 * (k4 - 1)) + 14) +
                k4 - 1 + 2 = 4 + k4 * (93 + (k4 - 1) * 143) + k4 - 1`
  SUBST1_TAC THENL [
    REWRITE_TAC[GSYM (ASSUME `4 * k4 = k`)] THEN
    REWRITE_TAC[ARITH_RULE`(4 * x) DIV 4 = x`] THEN
    SIMPLE_ARITH_TAC;

    ALL_TAC
  ] THEN

  MATCH_MP_TAC BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (ASSUME `8 divides k`) THEN
  REWRITE_TAC[ARITH_RULE`8 = 4*2`; GSYM DIVIDES_DIVIDES_DIV_EQ] THEN
  DISCH_THEN (fun th -> MP_TAC (CONJUNCT1 th)) THEN
  REWRITE_TAC[DIVIDES_DIV_MULT] THEN
  ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC);;


let BIGNUM_EMONTREDC_8N_CDIFF_MAINLOOP_CORRECT = prove(
  `forall k (z:int64) (m:int64) w a mn (sp:int64) pc2.
      // Assumptions of BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N
      w < 2 EXP 64 /\
      ~(k = 0) /\
      ~(k = 4) /\
      a < 2 EXP (64 * 2 * k) /\
      mn < 2 EXP (64 * k) /\

      // Assumptions of MAINLOOP_EQUIV
      ALL (nonoverlapping (z,8 * 2 * k))
      [word pc2,LENGTH bignum_emontredc_8n_cdiff_mc; sp,128; m,8 * k;
      m_precalc,8 * 12 * (k DIV 4 - 1)] /\
      ALL (nonoverlapping (sp,128))
      [word pc2,LENGTH bignum_emontredc_8n_cdiff_mc; m,8 * k;
      m_precalc,8 * 12 * (k DIV 4 - 1)] /\
      aligned 16 sp /\
      8 divides k /\
      16 <= k /\
      k < 2 EXP 61 /\
      k < 2 EXP 32
      ==> ensures arm
           (\s.
                aligned_bytes_loaded s (word pc2) bignum_emontredc_8n_cdiff_mc /\
                read PC s = word (pc2 + slothy_precomp_loop_end) /\
                read X0 s = word (k DIV 4) /\
                read X12 s = word (k DIV 4 - 1) /\
                read X26 s = word (k DIV 4) /\
                read X1 s = z /\
                read X2 s = m /\
                read X3 s = word w /\
                read SP s = sp /\
                read X30 s = m_precalc /\
                bignum_from_memory (z,2 * k) s = a /\
                bignum_from_memory (m,k) s = mn /\
                read (memory :> bytes (m_precalc,8 * 12 * (k DIV 4 - 1))) s =
                  get_m_precalc mn (k DIV 4 - 1))
           (\s.
                aligned_bytes_loaded s (word pc2) bignum_emontredc_8n_cdiff_mc /\
                read PC s = word (pc2 + slothy_main_end) /\
                ((mn * w + 1 == 0) (mod (2 EXP 64))
                 ==> mn * bignum_from_memory (z,k) s + a =
                     2 EXP (64 * k) *
                     (2 EXP (64 * k) * val (read X0 s) +
                      bignum_from_memory (word_add z (word (8 * k)),k) s)))
           (MAYCHANGE
                 [Q29; Q2; Q12; Q27; Q17; Q30; Q28; Q21; Q31; Q23; Q24; Q3;
                  Q16; Q26; Q11; Q5; Q8; Q4; Q15; Q9; Q18; Q20; Q19; Q14;
                  Q25; Q1; Q7; Q10; Q13; Q0; Q6] ,,
                 MAYCHANGE
                 [X0; X27; X2; X22; X3; X21; X5; X6; X16; X25; X4; X9; X11;
                  X7; X1; X29; X20; X19; X23; X12; X13; X26; X8; X14; X17;
                  X15; X30; X10; X24; PC; X28] ,,
                 MAYCHANGE [memory :> bytes (sp,128)] ,,
                 MAYCHANGE [memory :> bytes (z,8 * 2 * k)] ,,
                 MAYCHANGE [VF; CF; ZF; NF] ,, MAYCHANGE [events])`,

  REWRITE_TAC(map (snd o snd) bignum_emontredc_8n_cdiff_labels) THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  (* Prepare pc for the original program.  *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc:int64, 1020) (z:int64,8 * 2 * k) /\
      nonoverlapping (word pc:int64, 1020) (m:int64,8 * k) /\
      4 divides val (word pc:int64)` MP_TAC THENL [

    SUBGOAL_THEN `?pc.
      nonoverlapping (word pc:int64, 1020) (z:int64,8 * 2 * 2 EXP 32) /\
      nonoverlapping (word pc:int64, 1020) (m:int64,8 * 2 EXP 32) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
      MAP_EVERY (fun t -> SUBST_ALL_TAC (NUM_COMPUTE_CONV t)) [`2 EXP 32`] THEN
      REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
      FIND_HOLE_TAC;

      ALL_TAC
    ] THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
    STRIP_TAC THEN EXISTS_TAC `pc:num` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;

    ALL_TAC
  ] THEN

  STRIP_TAC THEN

  VCGEN_EQUIV_TAC
      MAINLOOP_EQUIV
      BIGNUM_EMONTREDC_8N_MAINLOOP_ENSURES_N_NSTEP_REWRITTEN
      [fst BIGNUM_EMONTREDC_8N_EXEC;fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN

  RULE_ASSUM_TAC (REWRITE_RULE[
      ALL; NONOVERLAPPING_CLAUSES; fst BIGNUM_EMONTREDC_8N_EXEC; fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT CONJ_TAC THENL [
    (* precond *)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[mainloop_eqin;C_ARGUMENTS;mk_equiv_regs] THEN
    EXISTS_TAC `write (memory :> bytelist
        (word pc,LENGTH bignum_emontredc_8n_mc))
        bignum_emontredc_8n_mc (write PC (word (pc + 36)) s2)` THEN
    (* Expand variables appearing in the equiv relation *)
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_EMONTREDC_8N_EXEC) THENL
    [ REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      HINT_EXISTS_REFL_TAC THEN CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_EMONTREDC_8N_EXEC);

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      HINT_EXISTS_REFL_TAC THEN
        CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_EMONTREDC_8N_EXEC) THEN
      ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_EMONTREDC_8N_EXEC;

      HINT_EXISTS_REFL_TAC THEN CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_EMONTREDC_8N_EXEC);

      HINT_EXISTS_REFL_TAC THEN CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC BIGNUM_EMONTREDC_8N_EXEC);
    ];

    (* postcond *)
    REWRITE_TAC[mainloop_eqout;BIGNUM_FROM_MEMORY_BYTES;mk_equiv_regs] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
        `read (memory :> bytes (z,8*k)) s2 = read (memory :> bytes (z,8*k)) s1 /\
         read (memory :> bytes (word_add z (word (8 * k)),8 * k)) s2 =
         read (memory :> bytes (word_add z (word (8 * k)),8 * k)) s1`
        (fun th -> REWRITE_TAC[th]) THENL [
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      SUBGOAL_THEN `k = MIN (2*k) k`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL [ARITH_TAC;ALL_TAC] THEN
      REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
      SUBGOAL_THEN `forall (x:int64). (x,k) = (x,(2 * k) - k)`
          (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL [
        REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC;ALL_TAC] THEN
      REWRITE_TAC[GSYM HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN NO_TAC;

      ALL_TAC
    ] THEN
    ASM_MESON_TAC[];

    (* Frame *)
    MESON_TAC[]
  ]);;


(* ========================================================================= *)
(*       Now let's prove the functional correctness of the subroutine!       *)
(* ========================================================================= *)


let BIGNUM_EMONTREDC_8N_CDIFF_CORE_CORRECT = prove(
  `forall z m_precalc m (k:num) (w:num) zn mn pc sp.
      ALL (nonoverlapping (z,8 * 2 * k))
         [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; sp,128; m,8 * k;
          m_precalc,8 * 12 * (k DIV 4 - 1)] /\
      ALL (nonoverlapping (sp,128))
         [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; m,8 * k;
          m_precalc,8 * 12 * (k DIV 4 - 1)] /\
      ALL (nonoverlapping (m_precalc,8 * 12 * (k DIV 4 - 1)))
         [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; m,8 * k] /\
      aligned 16 sp /\
      8 divides k /\
      16 <= k /\
      k < 2 EXP 32 /\
      w < 2 EXP 64 /\
      zn < 2 EXP (64 * 2 * k) /\
      mn < 2 EXP (64 * k) /\
      ~(k = 0) /\
      ~(k = 4)
      ==> ensures arm
          (\s.
                aligned_bytes_loaded s (word pc) bignum_emontredc_8n_cdiff_mc /\
                read PC s = word (pc + slothy_main) /\
                read SP s = sp /\
                read X0 s = word (k DIV 4) /\
                read X1 s = z /\
                read X2 s = m /\
                read X3 s = word w /\
                read X4 s = m_precalc /\
                read X26 s = word (k DIV 4) /\
                read X12 s = word (k DIV 4 - 1) /\
                read (memory :> bytes (z,8 * 2 * k)) s = zn /\
                read (memory :> bytes (m,8 * k)) s = mn)
          (\s.
                aligned_bytes_loaded s (word pc) bignum_emontredc_8n_cdiff_mc /\
                read PC s = word (pc + slothy_main_end) /\
                ((mn * w + 1 == 0) (mod (2 EXP 64))
                 ==> mn * bignum_from_memory (z,k) s + zn =
                     2 EXP (64 * k) *
                     (2 EXP (64 * k) * val (read X0 s) +
                      bignum_from_memory (word_add z (word (8 * k)),k) s)))
          (MAYCHANGE
            [Q29; Q2; Q12; Q27; Q17; Q30; Q28; Q21; Q31; Q23; Q24; Q3; Q16;
             Q26; Q11; Q5; Q8; Q4; Q15; Q9; Q18; Q20; Q19; Q14; Q25; Q1; Q7;
             Q10; Q13; Q0; Q6] ,,
          MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                    X12; X13; X14; X15; X16; X17; X19; X20;
                    X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
          MAYCHANGE [memory :> bytes(z,8 * 2 * k)] ,,
          MAYCHANGE [memory :> bytes(sp,128)] ,,
          MAYCHANGE [memory :> bytes(m_precalc,8 * 12 * (k DIV 4 - 1))] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REWRITE_TAC[NONOVERLAPPING_CLAUSES;ALL;SOME_FLAGS;
      fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
  REWRITE_TAC(map (snd o snd) bignum_emontredc_8n_cdiff_labels) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k < 2 EXP 64` ASSUME_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 208`
      `(\s. read SP s = sp /\
            read X0 s = word (k DIV 4) /\
            read X1 s = z /\
            read X2 s = m /\
            read X3 s = word w /\
            read X30 s = m_precalc /\
            read X26 s = word (k DIV 4) /\
            read X12 s = word (k DIV 4 - 1) /\
            read (memory :> bytes (z,8 * 2 * k)) s = zn /\
            read (memory :> bytes (m,8 * k)) s = mn /\
            read (memory :> bytes (m_precalc,8 * 12 * (k DIV 4 - 1))) s =
                get_m_precalc mn (k DIV 4 - 1))` THEN
  CONJ_TAC THENL [
    MP_TAC (SPECL [`z:int64`;`m_precalc:int64`;`m:int64`;`word k:int64`;`k DIV 4`;
        `word w:int64`;`zn:num`;`mn:num`;`pc:num`;`word_add sp (word 128):int64`]
        (REWRITE_RULE(map (snd o snd) bignum_emontredc_8n_cdiff_labels)
          BIGNUM_EMONTREDC_8N_CDIFF_PRECALCLOOP)) THEN
    REWRITE_TAC[fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
    ANTS_TAC THENL [
      REWRITE_TAC[VAL_WORD;DIMINDEX_64;ALL;NONOVERLAPPING_CLAUSES] THEN
      SUBGOAL_THEN `k MOD 2 EXP 64 = k` SUBST_ALL_TAC THENL [
        IMP_REWRITE_TAC[MOD_LT]; ALL_TAC
      ] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
        NONOVERLAPPING_TAC;
        NONOVERLAPPING_TAC;
        UNDISCH_TAC `8 divides k` THEN
        REWRITE_TAC[ARITH_RULE`8=4*2`; GSYM DIVIDES_DIVIDES_DIV_EQ] THEN
        REWRITE_TAC[DIVIDES_DIV_MULT] THEN MESON_TAC[MULT_SYM];
        UNDISCH_TAC `8 divides k` THEN
        REWRITE_TAC[ARITH_RULE`8=4*2`; GSYM DIVIDES_DIVIDES_DIV_EQ] THEN
        REWRITE_TAC[DIVIDES_DIV_MULT] THEN SIMPLE_ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    REPEAT CONJ_TAC THENL [
      (* pre cond *)
      REWRITE_TAC[WORD_VAL;WORD_RULE`word_sub (word_add x y) y:int64 = x`] THEN
      IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT];

      (* frame *)
      REWRITE_TAC[SOME_FLAGS] THEN
      IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
      SUBSUMED_MAYCHANGE_TAC;

      (* postcond *)
      REWRITE_TAC[SOME_FLAGS;WORD_RULE`word_sub (word_add x y) y:int64 = x`] THEN
      IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC (ASSUME `aligned_bytes_loaded s (word pc) bignum_emontredc_8n_cdiff_mc`) THEN
      REWRITE_TAC[aligned_bytes_loaded;bytes_loaded;
        fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
      FIRST_X_ASSUM (fun th -> STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC th) THEN
      (* okay, now MAYCHANGE at antedecendant.. *)
      (* a standard procedure *)
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN ASM_REWRITE_TAC[]
    ];

    MP_TAC (SPECL [`k:num`;`z:int64`;`m:int64`;`w:num`;`zn:num`;`mn:num`;
        `sp:int64`;`pc:num`]
      (REWRITE_RULE(map (snd o snd) bignum_emontredc_8n_cdiff_labels)
        BIGNUM_EMONTREDC_8N_CDIFF_MAINLOOP_CORRECT)) THEN
    REWRITE_TAC[fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
    ANTS_TAC THENL [
      ASM_REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES] THEN SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    REPEAT CONJ_TAC THENL [
      (* pre cond *)
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN NO_TAC;

      (* frame *)
      SUBSUMED_MAYCHANGE_TAC;

      (* postcond *)
      REWRITE_TAC[] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      NO_TAC
    ]
  ]);;


let BIGNUM_EMONTREDC_8N_CDIFF_CORRECT = time prove
 (`forall k z m m_precalc w a n pc sp.
      ALL (nonoverlapping (z,8 * 2 * val k))
         [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; sp,128; m,8 * val k;
          m_precalc,8 * 12 * (val k DIV 4 - 1)] /\
      ALL (nonoverlapping (sp,128))
         [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; m,8 * val k;
          m_precalc,8 * 12 * (val k DIV 4 - 1)] /\
      ALL (nonoverlapping (m_precalc,8 * 12 * (val k DIV 4 - 1)))
         [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; m,8 * val k] /\
      aligned 16 sp /\
      8 divides val k /\ val k < 2 EXP 32 /\ 16 <= val k
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_cdiff_mc /\
                read PC s = word(pc + 0x34) /\
                read SP s = sp /\
                C_ARGUMENTS [k; z; m; w; m_precalc] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read PC s = word(pc + 0x880) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
           (MAYCHANGE
              [Q29; Q2; Q12; Q27; Q17; Q30; Q28; Q21; Q31; Q23; Q24; Q3; Q16;
              Q26; Q11; Q5; Q8; Q4; Q15; Q9; Q18; Q20; Q19; Q14; Q25; Q1; Q7;
              Q10; Q13; Q0; Q6] ,,
            MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                      X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
            MAYCHANGE [memory :> bytes(z,8 * 2 * val k)] ,,
            MAYCHANGE [memory :> bytes(sp,128)] ,,
            MAYCHANGE [memory :> bytes(m_precalc,8 * 12 * (val k DIV 4 - 1))] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`; `m_precalc:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`; `sp:int64`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  ABBREV_TAC `k4 = k DIV 4` THEN

  (*** Degenerate k/4 = 0 case ***)

  ASM_CASES_TAC `k4 = 0` THENL
   [UNDISCH_THEN `k4 = 0` SUBST_ALL_TAC THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC (1--4) THEN
    UNDISCH_TAC `8 divides k` THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`] THEN
    ASM_REWRITE_TAC[DIVIDES_DIV_MULT; MULT_CLAUSES; ARITH_RULE `0 < 1`;
                    DIV_0; ARITH_RULE `k DIV 8 = k DIV 4 DIV 2`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN
  ASM_CASES_TAC `k4 = 1` THENL
  [ FIRST_X_ASSUM (fun th -> ASSUME_TAC (MATCH_MP DIVIDES_LE th)) THEN
    ASM_ARITH_TAC; ALL_TAC ] THEN

  (*** Restate things in terms of k' = k * k DIV 4 for naturalness ***)

  ABBREV_TAC `k' = 4 * k4` THEN
  ABBREV_TAC `a' = lowdigits a (2 * k')` THEN
  ABBREV_TAC `n' = lowdigits n k'` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x44`
   `\s. read SP s = sp /\
        read X0 s = word (k DIV 4) /\
        read X1 s = z /\
        read X2 s = m /\
        read X3 s = word w /\
        read X4 s = m_precalc /\
        read X26 s = word (k DIV 4) /\
        read X12 s = word (k DIV 4 - 1) /\
        bignum_from_memory (z,2 * k') s = a' /\
        bignum_from_memory (m,k') s = n'` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC (1--4) THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[WORD_RULE `word_sub x z = word_sub y z <=> x = y`] THEN
    ASM_REWRITE_TAC[word_ushr; NUM_REDUCE_CONV `2 EXP 2`] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "n'"; "a"; "n"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN
    CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x880`
   `\s. ((n' * w + 1 == 0) (mod (2 EXP 64))
         ==> n' * bignum_from_memory (z,k') s + a' =
           2 EXP (64 * k') *
           (2 EXP (64 * k') * val(read X0 s) +
            bignum_from_memory (word_add z (word (8 * k')),k') s))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_CDIFF_EXEC [] THEN REWRITE_TAC[IMP_CONJ] THEN
    UNDISCH_TAC `8 divides k` THEN
    DISCH_THEN(MP_TAC o SPEC `4` o MATCH_MP (NUMBER_RULE
     `y divides a ==> !x:num. x divides y ==> x divides a`)) THEN
    ANTS_TAC THENL [CONV_TAC DIVIDES_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIVIDES_DIV_MULT] THEN
    ASM_CASES_TAC `k':num = k` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `k':num = k` SUBST_ALL_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`lowdigits a (2 * k) = a'`; `lowdigits n k = n'`] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN NO_TAC] THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN

  SUBGOAL_THEN `k':num = k` SUBST_ALL_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[ARITH_RULE`8=4*2`;GSYM DIVIDES_DIVIDES_DIV_EQ] THEN
    REWRITE_TAC[DIVIDES_DIV_MULT] THEN SIMPLE_ARITH_TAC;
    ALL_TAC
  ] THEN
  EXPAND_TAC "k4" THEN
  MATCH_MP_TAC (REWRITE_RULE
    ([BIGNUM_FROM_MEMORY_BYTES;SOME_FLAGS] @
      (map (snd o snd) bignum_emontredc_8n_cdiff_labels))
    BIGNUM_EMONTREDC_8N_CDIFF_CORE_CORRECT) THEN
  ASM_REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_EMONTREDC_8N_CDIFF_EXEC] THEN
  REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THENL [
    EXPAND_TAC "a'" THEN IMP_REWRITE_TAC[LOWDIGITS_BOUND];
    EXPAND_TAC "n'" THEN IMP_REWRITE_TAC[LOWDIGITS_BOUND];
  ]);;

let BIGNUM_EMONTREDC_8N_CDIFF_SUBROUTINE_CORRECT = time prove
 (`forall k z m m_precalc w a n pc sp returnaddress.
        ALL (nonoverlapping (z,8 * 2 * val k))
         [word pc,LENGTH bignum_emontredc_8n_cdiff_mc;
          word_sub sp (word 288),288; m,8 * val k;
          m_precalc,8 * 12 * (val k DIV 4 - 1)] /\
        ALL (nonoverlapping (word_sub sp (word 288),288))
          [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; m,8 * val k;
            m_precalc,8 * 12 * (val k DIV 4 - 1)] /\
        ALL (nonoverlapping (m_precalc,8 * 12 * (val k DIV 4 - 1)))
          [word pc,LENGTH bignum_emontredc_8n_cdiff_mc; m,8 * val k] /\
        aligned 16 sp /\
        8 divides val k /\ val k < 2 EXP 32 /\ 16 <= val k
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_cdiff_mc /\
                  read PC s = word pc /\
                  read SP s = sp /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; m; w; m_precalc] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
             MAYCHANGE [memory :> bytes(z,8 * 2 * val k)] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 288),288)] ,,
              MAYCHANGE [memory :> bytes(m_precalc,8 * 12 * (val k DIV 4 - 1))])`,
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(13,13)
    BIGNUM_EMONTREDC_8N_CDIFF_EXEC
    BIGNUM_EMONTREDC_8N_CDIFF_CORRECT
   `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
     D8; D9; D10; D11; D12; D13; D14; D15]` 288);;
