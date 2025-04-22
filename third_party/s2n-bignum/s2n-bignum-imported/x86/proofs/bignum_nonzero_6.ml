(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Deduce if a 384-bit bignum is nonzero.                                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_nonzero_6.o";;
 ****)

let bignum_nonzero_6_mc =
  define_assert_from_elf "bignum_nonzero_6_mc" "x86/p384/bignum_nonzero_6.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x57; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x0b; 0x47; 0x10;  (* OR (% rax) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x0b; 0x57; 0x18;  (* OR (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x48; 0x0b; 0x47; 0x20;  (* OR (% rax) (Memop Quadword (%% (rdi,32))) *)
  0x48; 0x0b; 0x57; 0x28;  (* OR (% rdx) (Memop Quadword (%% (rdi,40))) *)
  0x48; 0x09; 0xd0;        (* OR (% rax) (% rdx) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x0f; 0x45; 0xc2;  (* CMOVNE (% rax) (% rdx) *)
  0xc3                     (* RET *)
];;

let bignum_nonzero_6_tmc = define_trimmed "bignum_nonzero_6_tmc" bignum_nonzero_6_mc;;

let BIGNUM_NONZERO_6_EXEC = X86_MK_CORE_EXEC_RULE bignum_nonzero_6_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_NONZERO_6_CORRECT = prove
 (`!x n pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST bignum_nonzero_6_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [x] s /\
               bignum_from_memory(x,6) s = n)
          (\s. read RIP s = word(pc + 0x23) /\
               C_RETURN s = if ~(n = 0) then word 1 else word 0)
          (MAYCHANGE [RIP; RAX; RDX] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN
  X86_STEPS_TAC BIGNUM_NONZERO_6_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[ADD_EQ_0; VAL_EQ_0; WORD_OR_EQ_0] THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ; VAL_EQ_0] THEN
  REWRITE_TAC[CONJ_ACI; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_OR_0]);;

let BIGNUM_NONZERO_6_NOIBT_SUBROUTINE_CORRECT = prove
 (`!x n pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_nonzero_6_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [x] s /\
               bignum_from_memory(x,6) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = if ~(n = 0) then word 1 else word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_nonzero_6_tmc BIGNUM_NONZERO_6_CORRECT);;

let BIGNUM_NONZERO_6_SUBROUTINE_CORRECT = prove
 (`!x n pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_nonzero_6_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [x] s /\
               bignum_from_memory(x,6) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = if ~(n = 0) then word 1 else word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NONZERO_6_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_nonzero_6_windows_mc = define_from_elf
   "bignum_nonzero_6_windows_mc" "x86/p384/bignum_nonzero_6.obj";;

let bignum_nonzero_6_windows_tmc = define_trimmed "bignum_nonzero_6_windows_tmc" bignum_nonzero_6_windows_mc;;

let BIGNUM_NONZERO_6_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_nonzero_6_windows_tmc); (x,8 * 6)]
        ==> ensures x86
              (\s. bytes_loaded s (word pc) bignum_nonzero_6_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [x] s /\
                   bignum_from_memory(x,6) s = n)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = if ~(n = 0) then word 1 else word 0)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_nonzero_6_windows_tmc bignum_nonzero_6_tmc
    BIGNUM_NONZERO_6_CORRECT);;

let BIGNUM_NONZERO_6_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_nonzero_6_windows_mc); (x,8 * 6)]
        ==> ensures x86
              (\s. bytes_loaded s (word pc) bignum_nonzero_6_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [x] s /\
                   bignum_from_memory(x,6) s = n)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = if ~(n = 0) then word 1 else word 0)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NONZERO_6_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

