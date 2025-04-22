(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting leading zeros in a well-defined way for a single word.           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/word_clz.o";;
 ****)

let word_clz_mc = define_assert_from_elf "word_clz_mc" "x86/generic/word_clz.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x0f; 0xbd; 0xc7;  (* BSR (% rax) (% rdi) *)
  0x48; 0x83; 0xf0; 0x3f;  (* XOR (% rax) (Imm8 (word 63)) *)
  0xba; 0x40; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 64)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x48; 0x0f; 0x44; 0xc2;  (* CMOVE (% rax) (% rdx) *)
  0xc3                     (* RET *)
];;

let word_clz_tmc = define_trimmed "word_clz_tmc" word_clz_mc;;

let WORD_CLZ_EXEC = X86_MK_CORE_EXEC_RULE word_clz_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_CLZ_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_clz_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = word(pc + 0x14) /\
               C_RETURN s = word(word_clz a))
          (MAYCHANGE [RIP; RAX; RDX] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_CLZ_EXEC (1--5) THEN
  REWRITE_TAC[VAL_EQ_0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[DIMINDEX_64; WORD_CLZ_0] THEN
  MP_TAC(ISPEC `a:int64` WORD_CLZ_LT_DIMINDEX) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  SPEC_TAC(`word_clz(a:int64)`,`n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let WORD_CLZ_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_clz_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word(word_clz a))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_clz_tmc WORD_CLZ_CORRECT);;

let WORD_CLZ_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_clz_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word(word_clz a))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_CLZ_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let word_clz_windows_mc = define_from_elf
   "word_clz_windows_mc" "x86/generic/word_clz.obj";;

let word_clz_windows_tmc = define_trimmed "word_clz_windows_tmc" word_clz_windows_mc;;

let WORD_CLZ_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_clz_windows_tmc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_clz_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word(word_clz a))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC word_clz_windows_tmc word_clz_tmc
    WORD_CLZ_CORRECT);;

let WORD_CLZ_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_clz_windows_mc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_clz_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word(word_clz a))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_CLZ_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

