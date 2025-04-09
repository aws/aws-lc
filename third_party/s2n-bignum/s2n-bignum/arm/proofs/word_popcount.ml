(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting set bits in a single machine word (population count).            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/word_popcount.o";;
 ****)

let word_popcount_mc = define_assert_from_elf "word_popcount_mc" "arm/generic/word_popcount.o"
[
  0x9201f001;       (* arm_AND X1 X0 (rvalue (word 12297829382473034410)) *)
  0xcb410400;       (* arm_SUB X0 X0 (Shiftedreg X1 LSR 1) *)
  0x9202e401;       (* arm_AND X1 X0 (rvalue (word 14757395258967641292)) *)
  0x9200e400;       (* arm_AND X0 X0 (rvalue (word 3689348814741910323)) *)
  0x8b410800;       (* arm_ADD X0 X0 (Shiftedreg X1 LSR 2) *)
  0x8b401000;       (* arm_ADD X0 X0 (Shiftedreg X0 LSR 4) *)
  0x9200cc00;       (* arm_AND X0 X0 (rvalue (word 1085102592571150095)) *)
  0xb200c3e1;       (* arm_MOV X1 (rvalue (word 72340172838076673)) *)
  0x9b017c00;       (* arm_MUL X0 X0 X1 *)
  0xd378fc00;       (* arm_LSR X0 X0 56 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let WORD_POPCOUNT_EXEC = ARM_MK_EXEC_RULE word_popcount_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_POPCOUNT_CORRECT = prove
 (`!a pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_popcount_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = word(pc + 0x28) /\
               C_RETURN s = word(word_popcount a))
          (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ARM_SIM_TAC WORD_POPCOUNT_EXEC (1--10) THEN
  REWRITE_TAC[WORD_RULE `word(0 + val a * b) = word_mul a (word b)`] THEN
  CONV_TAC BITBLAST_RULE);;

let WORD_POPCOUNT_SUBROUTINE_CORRECT = prove
 (`!a pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_popcount_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word(word_popcount a))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC WORD_POPCOUNT_EXEC WORD_POPCOUNT_CORRECT);;
