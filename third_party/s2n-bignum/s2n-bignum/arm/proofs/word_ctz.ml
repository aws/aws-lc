(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting trailing zeros in a well-defined way for a single word.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/word_ctz.o";;
 ****)

let word_ctz_mc = define_assert_from_elf "word_ctz_mc" "arm/generic/word_ctz.o"
[
  0xaa2003e1;       (* arm_ORN X1 XZR X0 *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0x8a010000;       (* arm_AND X0 X0 X1 *)
  0xdac01001;       (* arm_CLZ X1 X0 *)
  0xd2800800;       (* arm_MOV X0 (rvalue (word 64)) *)
  0xcb010000;       (* arm_SUB X0 X0 X1 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let WORD_CTZ_EXEC = ARM_MK_EXEC_RULE word_ctz_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_CTZ_CORRECT = prove
 (`!a pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_ctz_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = word(pc + 0x18) /\
               C_RETURN s = word(word_ctz a))
          (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ARM_SIM_TAC WORD_CTZ_EXEC (1--6) THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  SIMP_TAC[WORD_CTZ_EMULATION; WORD_SUB; WORD_CLZ_LE_DIMINDEX] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC WORD_REDUCE_CONV);;

let WORD_CTZ_SUBROUTINE_CORRECT = prove
 (`!a pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_ctz_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word(word_ctz a))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC WORD_CTZ_EXEC WORD_CTZ_CORRECT);;
