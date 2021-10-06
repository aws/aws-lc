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
(* Finding minimum of two 64-bit words.                                      *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/generic/word_min.o";;
 ****)

let word_min_mc = define_assert_from_elf "word_min_mc" "x86/generic/word_min.o"
[
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x39; 0xf7;        (* CMP (% rdi) (% rsi) *)
  0x48; 0x0f; 0x43; 0xc6;  (* CMOVAE (% rax) (% rsi) *)
  0xc3                     (* RET *)
];;

let WORD_MIN_EXEC = X86_MK_EXEC_RULE word_min_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_MIN_CORRECT = prove
 (`!a b pc.
        ensures x86
          (\s. bytes_loaded s (word pc) word_min_mc /\
               read RIP s = word pc /\
               C_ARGUMENTS [a; b] s)
          (\s. read RIP s = word(pc + 0xa) /\
               C_RETURN s = word_umin a b)
          (MAYCHANGE [RIP; RAX] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `b:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_MIN_EXEC (1--3) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMIN] THEN ASM_ARITH_TAC);;

let WORD_MIN_SUBROUTINE_CORRECT = prove
 (`!a b pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_min_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; b] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word_umin a b)
          (MAYCHANGE [RIP; RSP; RAX] ,,
           MAYCHANGE SOME_FLAGS)`,
  X86_ADD_RETURN_NOSTACK_TAC WORD_MIN_EXEC WORD_MIN_CORRECT);;
