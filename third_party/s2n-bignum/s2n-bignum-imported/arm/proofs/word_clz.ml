(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting leading zeros in a well-defined way for a single word.           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/word_clz.o";;
 ****)

let word_clz_mc = define_assert_from_elf "word_clz_mc" "arm/generic/word_clz.o"
[
  0xdac01000;       (* arm_CLZ X0 X0 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let WORD_CLZ_EXEC = ARM_MK_EXEC_RULE word_clz_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_CLZ_CORRECT = prove
 (`!a pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_clz_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = word(pc + 0x4) /\
               C_RETURN s = word(word_clz a))
          (MAYCHANGE [PC; X0] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ARM_SIM_TAC WORD_CLZ_EXEC [1]);;

let WORD_CLZ_SUBROUTINE_CORRECT = prove
 (`!a pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_clz_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word(word_clz a))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC WORD_CLZ_EXEC WORD_CLZ_CORRECT);;
