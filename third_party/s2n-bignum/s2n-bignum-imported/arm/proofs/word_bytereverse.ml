(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reversing the order of the bytes in a single 64-bit word.                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/word_bytereverse.o";;
 ****)

let word_bytereverse_mc = define_assert_from_elf "word_bytereverse_mc" "arm/generic/word_bytereverse.o"
[
  0xb2103fe1;       (* arm_MOV X1 (rvalue (word 18446462603027742720)) *)
  0xb2003fe2;       (* arm_MOV X2 (rvalue (word 281470681808895)) *)
  0x8a000021;       (* arm_AND X1 X1 X0 *)
  0x8a000042;       (* arm_AND X2 X2 X0 *)
  0x93c18021;       (* arm_ROR X1 X1 (rvalue (word 32)) *)
  0xaa020020;       (* arm_ORR X0 X1 X2 *)
  0xb2089fe1;       (* arm_MOV X1 (rvalue (word 18374966859414961920)) *)
  0xb2009fe2;       (* arm_MOV X2 (rvalue (word 71777214294589695)) *)
  0x8a000021;       (* arm_AND X1 X1 X0 *)
  0x8a000042;       (* arm_AND X2 X2 X0 *)
  0x93c16021;       (* arm_ROR X1 X1 (rvalue (word 24)) *)
  0x93c22042;       (* arm_ROR X2 X2 (rvalue (word 8)) *)
  0xaa020020;       (* arm_ORR X0 X1 X2 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let WORD_BYTEREVERSE_EXEC = ARM_MK_EXEC_RULE word_bytereverse_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_BYTEREVERSE_CORRECT = prove
 (`!a pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_bytereverse_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = word(pc + 0x34) /\
               !i. i < 8
                   ==> word_subword (C_RETURN s) (8 * i,8) :byte =
                       word_subword a (8 * (7 - i),8))
          (MAYCHANGE [PC; X0; X1; X2] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ARM_SIM_TAC WORD_BYTEREVERSE_EXEC (1--13) THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_SUBWORD; BIT_WORD_JOIN] THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let WORD_BYTEREVERSE_SUBROUTINE_CORRECT = prove
 (`!a pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_bytereverse_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = returnaddress /\
               !i. i < 8
                   ==> word_subword (C_RETURN s) (8 * i,8) :byte =
                       word_subword a (8 * (7 - i),8))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC WORD_BYTEREVERSE_EXEC WORD_BYTEREVERSE_CORRECT);;
