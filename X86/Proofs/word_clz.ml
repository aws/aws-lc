(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Counting leading zeros in a well-defined way for a single word.           *)
(* ========================================================================= *)

(**** print_literal_from_elf "X86/generic/word_clz.o";;
 ****)

let word_clz_mc = define_assert_from_elf "word_clz_mc" "X86/generic/word_clz.o"
[
  0x48; 0x0f; 0xbd; 0xc7;  (* BSR (% rax) (% rdi) *)
  0x48; 0x83; 0xf0; 0x3f;  (* XOR (% rax) (Imm8 (word 63)) *)
  0xba; 0x40; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 64)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x48; 0x0f; 0x44; 0xc2;  (* CMOVE (% rax) (% rdx) *)
  0xc3                     (* RET *)
];;

let WORD_CLZ_EXEC = X86_MK_EXEC_RULE word_clz_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_CLZ_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) word_clz_mc /\
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
          (MAYCHANGE [RIP; RSP; RAX; RDX] ,,
           MAYCHANGE SOME_FLAGS)`,
  X86_ADD_RETURN_NOSTACK_TAC WORD_CLZ_EXEC WORD_CLZ_CORRECT);;
