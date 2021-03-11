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
(* Deduce if a bignum is odd or even.                                        *)
(* ========================================================================= *)

(**** print_literal_from_elf "X86/bignum_even.o";;
 ****)

let bignum_even_mc = define_assert_from_elf "bignum_even_mc" "X86/bignum_even.o"
[
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x48; 0x0f; 0x45; 0x06;  (* CMOVNE (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x83; 0xe0; 0x01;  (* AND (% rax) (Imm8 (word 1)) *)
  0x48; 0x83; 0xf0; 0x01;  (* XOR (% rax) (Imm8 (word 1)) *)
  0xc3                     (* RET *)
];;

let BIGNUM_EVEN_EXEC = X86_MK_EXEC_RULE bignum_even_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EVEN_CORRECT = prove
 (`!k a x pc.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_even_mc /\
               read RIP s = word pc /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s. read RIP s = word(pc + 0x12) /\
               C_RETURN s = if EVEN x then word 1 else word 0)
          (MAYCHANGE [RIP; RAX] ,, MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a1:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[ENSURES_TRIVIAL; EVEN] THEN
    X86_SIM_TAC BIGNUM_EVEN_EXEC (1--5);
    ENSURES_INIT_TAC "s0" THEN EXPAND_TAC "x" THEN
    ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
    ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; EVEN_EXP; ARITH_EVEN; ARITH_EQ] THEN
    ABBREV_TAC `d = read (memory :> bytes64 a1) s0` THEN
    X86_STEPS_TAC BIGNUM_EVEN_EXEC (1--5) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_AND_1; BIT_LSB; GSYM NOT_ODD; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV]);;

let BIGNUM_EVEN_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_even_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = if EVEN x then word 1 else word 0)
          (MAYCHANGE [RIP; RSP; RAX] ,, MAYCHANGE SOME_FLAGS)`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_EVEN_EXEC BIGNUM_EVEN_CORRECT);;
