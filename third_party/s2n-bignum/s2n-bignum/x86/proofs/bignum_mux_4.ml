(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplexing (selection, if-then-else) for 4-digit (256-bit) bignums.     *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p256/bignum_mux_4.o";;
 ****)

let bignum_mux_4_mc =
  define_assert_from_elf "bignum_mux_4_mc" "x86/p256/bignum_mux_4.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
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
  0xc3                     (* RET *)
];;

let bignum_mux_4_tmc = define_trimmed "bignum_mux_4_tmc" bignum_mux_4_mc;;

let BIGNUM_MUX_4_EXEC = X86_MK_CORE_EXEC_RULE bignum_mux_4_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX_4_CORRECT = prove
 (`!p z x y m n pc.
     nonoverlapping (word pc,0x41) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mux_4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read RIP s = word (pc + 0x40) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [RIP; RAX; R8] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`p:int64`; `z:int64`; `x:int64`; `y:int64`;
    `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN
  X86_STEPS_TAC BIGNUM_MUX_4_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COND_SWAP; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_MUX_4_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z x y m n pc stackpointer returnaddress.
     nonoverlapping (word pc,LENGTH bignum_mux_4_tmc) (z,8 * 4) /\
     nonoverlapping (stackpointer,8) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mux_4_tmc BIGNUM_MUX_4_CORRECT);;

let BIGNUM_MUX_4_SUBROUTINE_CORRECT = prove
 (`!p z x y m n pc stackpointer returnaddress.
     nonoverlapping (word pc,LENGTH bignum_mux_4_mc) (z,8 * 4) /\
     nonoverlapping (stackpointer,8) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUX_4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mux_4_windows_mc = define_from_elf
   "bignum_mux_4_windows_mc" "x86/p256/bignum_mux_4.obj";;

let bignum_mux_4_windows_tmc = define_trimmed "bignum_mux_4_windows_tmc" bignum_mux_4_windows_mc;;

let BIGNUM_MUX_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z x y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mux_4_windows_tmc); (x,8 * 4); (y,8 * 4)] /\
     nonoverlapping (word pc,LENGTH bignum_mux_4_windows_tmc) (z,8 * 4) /\
     nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_4_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_mux_4_windows_tmc bignum_mux_4_tmc
    BIGNUM_MUX_4_CORRECT);;

let BIGNUM_MUX_4_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z x y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mux_4_windows_mc); (x,8 * 4); (y,8 * 4)] /\
     nonoverlapping (word pc,LENGTH bignum_mux_4_windows_mc) (z,8 * 4) /\
     nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_4_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUX_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

