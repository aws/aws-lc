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
(* Multiplexing (selection, if-then-else) for 6-digit (384-bit) bignums.     *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/p384/bignum_mux_6.o";;
 ****)

let bignum_mux_6_mc =
  define_assert_from_elf "bignum_mux_6_mc" "x86/p384/bignum_mux_6.o"
[
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x48; 0x8b; 0x02;        (* MOV (% rax) (Memop Quadword (%% (rdx,0))) *)
  0x4c; 0x8b; 0x01;        (* MOV (% r8) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x0f; 0x44; 0xc0;  (* CMOVE (% rax) (% r8) *)
  0x48; 0x89; 0x06;        (* MOV (Memop Quadword (%% (rsi,0))) (% rax) *)
  0x48; 0x8b; 0x42; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rdx,8))) *)
  0x4c; 0x8b; 0x41; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x0f; 0x44; 0xc0;  (* CMOVE (% rax) (% r8) *)
  0x48; 0x89; 0x46; 0x08;  (* MOV (Memop Quadword (%% (rsi,8))) (% rax) *)
  0x48; 0x8b; 0x42; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rdx,16))) *)
  0x4c; 0x8b; 0x41; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x0f; 0x44; 0xc0;  (* CMOVE (% rax) (% r8) *)
  0x48; 0x89; 0x46; 0x10;  (* MOV (Memop Quadword (%% (rsi,16))) (% rax) *)
  0x48; 0x8b; 0x42; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rdx,24))) *)
  0x4c; 0x8b; 0x41; 0x18;  (* MOV (% r8) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x0f; 0x44; 0xc0;  (* CMOVE (% rax) (% r8) *)
  0x48; 0x89; 0x46; 0x18;  (* MOV (Memop Quadword (%% (rsi,24))) (% rax) *)
  0x48; 0x8b; 0x42; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rdx,32))) *)
  0x4c; 0x8b; 0x41; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rcx,32))) *)
  0x49; 0x0f; 0x44; 0xc0;  (* CMOVE (% rax) (% r8) *)
  0x48; 0x89; 0x46; 0x20;  (* MOV (Memop Quadword (%% (rsi,32))) (% rax) *)
  0x48; 0x8b; 0x42; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rdx,40))) *)
  0x4c; 0x8b; 0x41; 0x28;  (* MOV (% r8) (Memop Quadword (%% (rcx,40))) *)
  0x49; 0x0f; 0x44; 0xc0;  (* CMOVE (% rax) (% r8) *)
  0x48; 0x89; 0x46; 0x28;  (* MOV (Memop Quadword (%% (rsi,40))) (% rax) *)
  0xc3                     (* RET *)
];;

let BIGNUM_MUX_6_EXEC = X86_MK_EXEC_RULE bignum_mux_6_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX_6_CORRECT = prove
 (`!p z x y m n pc.
     nonoverlapping (word pc,0x61) (z,8 * 6) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6)) /\
     (y = z \/ nonoverlapping (y,8 * 6) (z,8 * 6))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_6_mc /\
                read RIP s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,6) s = m /\
                bignum_from_memory (y,6) s = n)
           (\s. read RIP s = word (pc + 0x60) /\
                bignum_from_memory (z,6) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [RIP; RAX; R8] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`p:int64`; `z:int64`; `x:int64`; `y:int64`;
    `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 6)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 6)) s0` THEN
  X86_STEPS_TAC BIGNUM_MUX_6_EXEC (1--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COND_SWAP; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_MUX_6_SUBROUTINE_CORRECT = prove
 (`!p z x y m n pc stackpointer returnaddress.
     nonoverlapping (word pc,0x61) (z,8 * 6) /\
     nonoverlapping (stackpointer,8) (z,8 * 6) /\
     (x = z \/ nonoverlapping (x,8 * 6) (z,8 * 6)) /\
     (y = z \/ nonoverlapping (y,8 * 6) (z,8 * 6))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_6_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,6) s = m /\
                bignum_from_memory (y,6) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,6) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [RIP; RSP; RAX; R8] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_MUX_6_EXEC BIGNUM_MUX_6_CORRECT);;
