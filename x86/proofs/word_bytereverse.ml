(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reversing the order of the bytes in a single 64-bit word.                 *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/generic/word_bytereverse.o";;
 ****)

let word_bytereverse_mc = define_assert_from_elf "word_bytereverse_mc" "x86/generic/word_bytereverse.o"
[
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x0f; 0xc8;        (* BSWAP (% rax) *)
  0xc3                     (* RET *)
];;

let WORD_BYTEREVERSE_EXEC = X86_MK_CORE_EXEC_RULE word_bytereverse_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_BYTEREVERSE_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_bytereverse_mc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = word(pc + 0x6) /\
               !i. i < 8
                   ==> word_subword (C_RETURN s) (8 * i,8) :byte =
                       word_subword a (8 * (7 - i),8))
          (MAYCHANGE [RIP; RAX])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_BYTEREVERSE_EXEC (1--2) THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN REFL_TAC);;

let WORD_BYTEREVERSE_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_bytereverse_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 8
                   ==> word_subword (C_RETURN s) (8 * i,8) :byte =
                       word_subword a (8 * (7 - i),8))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_bytereverse_mc WORD_BYTEREVERSE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_word_bytereverse_mc = define_from_elf
   "windows_word_bytereverse_mc" "x86/generic/word_bytereverse.obj";;

let WINDOWS_WORD_BYTEREVERSE_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,0xe)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) windows_word_bytereverse_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   !i. i < 8
                       ==> word_subword (WINDOWS_C_RETURN s) (8 * i,8) :byte =
                           word_subword a (8 * (7 - i),8))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    windows_word_bytereverse_mc word_bytereverse_mc WORD_BYTEREVERSE_CORRECT);;
