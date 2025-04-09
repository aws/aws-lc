(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting set bits in a single machine word (population count).            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/word_popcount.o";;
 ****)

let word_popcount_mc = define_assert_from_elf "word_popcount_mc" "x86/generic/word_popcount.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0xba; 0x55; 0x55; 0x55; 0x55; 0x55; 0x55; 0x55; 0x55;
                           (* MOV (% rdx) (Imm64 (word 6148914691236517205)) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0xd1; 0xe8;        (* SHR (% rax) (Imm8 (word 1)) *)
  0x48; 0x21; 0xd0;        (* AND (% rax) (% rdx) *)
  0x48; 0x29; 0xc7;        (* SUB (% rdi) (% rax) *)
  0x48; 0xb8; 0x33; 0x33; 0x33; 0x33; 0x33; 0x33; 0x33; 0x33;
                           (* MOV (% rax) (Imm64 (word 3689348814741910323)) *)
  0x48; 0x89; 0xfa;        (* MOV (% rdx) (% rdi) *)
  0x48; 0x21; 0xc7;        (* AND (% rdi) (% rax) *)
  0x48; 0xc1; 0xea; 0x02;  (* SHR (% rdx) (Imm8 (word 2)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x48; 0x01; 0xfa;        (* ADD (% rdx) (% rdi) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x04;  (* SHR (% rax) (Imm8 (word 4)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0xba; 0x0f; 0x0f; 0x0f; 0x0f; 0x0f; 0x0f; 0x0f; 0x0f;
                           (* MOV (% rdx) (Imm64 (word 1085102592571150095)) *)
  0x48; 0x21; 0xd0;        (* AND (% rax) (% rdx) *)
  0x48; 0xba; 0x01; 0x01; 0x01; 0x01; 0x01; 0x01; 0x01; 0x01;
                           (* MOV (% rdx) (Imm64 (word 72340172838076673)) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x38;  (* SHR (% rax) (Imm8 (word 56)) *)
  0xc3                     (* RET *)
];;

let word_popcount_tmc = define_trimmed "word_popcount_tmc" word_popcount_mc;;

let WORD_POPCOUNT_EXEC = X86_MK_CORE_EXEC_RULE word_popcount_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_POPCOUNT_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_popcount_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = word(pc + 0x59) /\
               C_RETURN s = word(word_popcount a))
          (MAYCHANGE [RIP; RAX; RDX; RDI] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_POPCOUNT_EXEC (1--19) THEN
  CONV_TAC BITBLAST_RULE);;

let WORD_POPCOUNT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_popcount_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word(word_popcount a))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_popcount_tmc WORD_POPCOUNT_CORRECT);;

let WORD_POPCOUNT_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_popcount_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word(word_popcount a))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_POPCOUNT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let word_popcount_windows_mc = define_from_elf
   "word_popcount_windows_mc" "x86/generic/word_popcount.obj";;

let word_popcount_windows_tmc = define_trimmed "word_popcount_windows_tmc" word_popcount_windows_mc;;

let WORD_POPCOUNT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_popcount_windows_tmc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_popcount_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word(word_popcount a))
              (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC word_popcount_windows_tmc word_popcount_tmc
    WORD_POPCOUNT_CORRECT);;

let WORD_POPCOUNT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_popcount_windows_mc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_popcount_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word(word_popcount a))
              (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_POPCOUNT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

