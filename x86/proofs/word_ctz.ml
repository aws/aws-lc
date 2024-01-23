(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting trailing zeros in a well-defined way for a single word.          *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/generic/word_ctz.o";;
 ****)

let word_ctz_mc = define_assert_from_elf "word_ctz_mc" "x86/generic/word_ctz.o"
[
  0x48; 0x0f; 0xbc; 0xc7;  (* BSF (% rax) (% rdi) *)
  0xba; 0x40; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 64)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x48; 0x0f; 0x44; 0xc2;  (* CMOVE (% rax) (% rdx) *)
  0xc3                     (* RET *)
];;

let WORD_CTZ_EXEC = X86_MK_CORE_EXEC_RULE word_ctz_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_CTZ_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_ctz_mc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = word(pc + 0x10) /\
               C_RETURN s = word(word_ctz a))
          (MAYCHANGE [RIP; RAX; RDX] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_CTZ_EXEC (1--4) THEN
  REWRITE_TAC[VAL_EQ_0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[DIMINDEX_64; WORD_CTZ_0]);;

let WORD_CTZ_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_ctz_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word(word_ctz a))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_ctz_mc WORD_CTZ_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_word_ctz_mc = define_from_elf
   "windows_word_ctz_mc" "x86/generic/word_ctz.obj";;

let WINDOWS_WORD_CTZ_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,0x18)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) windows_word_ctz_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word(word_ctz a))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_word_ctz_mc word_ctz_mc
    WORD_CTZ_CORRECT);;
