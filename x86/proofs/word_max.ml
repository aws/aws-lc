(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Finding maximum of two 64-bit words.                                      *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/generic/word_max.o";;
 ****)

let word_max_mc = define_assert_from_elf "word_max_mc" "x86/generic/word_max.o"
[
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x39; 0xf7;        (* CMP (% rdi) (% rsi) *)
  0x48; 0x0f; 0x42; 0xc6;  (* CMOVB (% rax) (% rsi) *)
  0xc3                     (* RET *)
];;

let WORD_MAX_EXEC = X86_MK_CORE_EXEC_RULE word_max_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_MAX_CORRECT = prove
 (`!a b pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_max_mc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a; b] s)
          (\s. read RIP s = word(pc + 0xa) /\
               C_RETURN s = word_umax a b)
          (MAYCHANGE [RIP; RAX] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `b:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_MAX_EXEC (1--3) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMAX] THEN ASM_ARITH_TAC);;

let WORD_MAX_SUBROUTINE_CORRECT = prove
 (`!a b pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_max_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; b] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word_umax a b)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_max_mc WORD_MAX_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_word_max_mc = define_from_elf
   "windows_word_max_mc" "x86/generic/word_max.obj";;

let WINDOWS_WORD_MAX_SUBROUTINE_CORRECT = prove
 (`!a b pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,0x15)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) windows_word_max_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a; b] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word_umax a b)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_word_max_mc word_max_mc
    WORD_MAX_CORRECT);;
