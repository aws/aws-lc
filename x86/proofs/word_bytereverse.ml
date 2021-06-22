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

let WORD_BYTEREVERSE_EXEC = X86_MK_EXEC_RULE word_bytereverse_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_BYTEREVERSE_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) word_bytereverse_mc /\
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
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_OF_BITS; IN; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

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
          (MAYCHANGE [RIP; RSP; RAX])`,
  X86_ADD_RETURN_NOSTACK_TAC WORD_BYTEREVERSE_EXEC WORD_BYTEREVERSE_CORRECT);;
