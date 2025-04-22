(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Translation to little-endian byte sequence, 9 digits -> 66 bytes.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_tolebytes_p521.o";;
 ****)

let bignum_tolebytes_p521_mc =
  define_assert_from_elf "bignum_tolebytes_p521_mc" "x86/p521/bignum_tolebytes_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rax) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rax) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x89; 0x47; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rax) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x89; 0x47; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rax) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x89; 0x47; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rax) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x66; 0x89; 0x47; 0x40;  (* MOV (Memop Word (%% (rdi,64))) (% ax) *)
  0xc3                     (* RET *)
];;

let bignum_tolebytes_p521_tmc = define_trimmed "bignum_tolebytes_p521_tmc" bignum_tolebytes_p521_mc;;

let BIGNUM_TOLEBYTES_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_tolebytes_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TOLEBYTES_P521_CORRECT = prove
 (`!z x n pc.
      nonoverlapping (word pc,0x47) (z,66) /\
      (x = z \/ nonoverlapping (x,8 * 9) (z,66))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_tolebytes_p521_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,9) s = n)
           (\s. read RIP s = word (pc + 0x46) /\
                read (memory :> bytelist(z,66)) s = bytelist_of_num 66 n)
           (MAYCHANGE [RIP; RAX] ,,
            MAYCHANGE [memory :> bytes(z,66)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "d_" `bignum_from_memory(x,9) s0` THEN
  X86_STEPS_TAC BIGNUM_TOLEBYTES_P521_EXEC (1--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 EXP 66 = 2 EXP (8 * 66)`] THEN
    REWRITE_TAC[READ_BYTES_BOUND; READ_COMPONENT_COMPOSE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes (z,66)) s18 =
    read (memory :> bytes (z,64)) s18 +
    2 EXP (8 * 64) * read (memory :> bytes (word_add z (word 64),2)) s18`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_COMBINE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
    REWRITE_TAC[SYM(NUM_MULT_CONV `8 * 8`)]] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[ARITH_RULE `256 EXP 66 = 2 EXP 512 * 2 EXP 16`] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(x:num == y) (mod d) ==> (a + e * x == a + e * y) (mod (e * d))`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int16->num`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytes16] THEN
  REWRITE_TAC[asword; read; through; VAL_WORD; GSYM CONG] THEN
  REWRITE_TAC[DIMINDEX_16; NUM_EXP_CONV `2 EXP 16`] THEN
  REWRITE_TAC[CONG_RMOD; BIGNUM_OF_WORDLIST_SING] THEN REWRITE_TAC[CONG_SYM]);;

let BIGNUM_TOLEBYTES_P521_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,66) /\
      nonoverlapping (word pc,LENGTH bignum_tolebytes_p521_tmc) (z,66) /\
      (x = z \/ nonoverlapping (x,8 * 9) (z,66))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_tolebytes_p521_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,66)) s = bytelist_of_num 66 n)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,66)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_tolebytes_p521_tmc
    BIGNUM_TOLEBYTES_P521_CORRECT);;

let BIGNUM_TOLEBYTES_P521_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,66) /\
      nonoverlapping (word pc,LENGTH bignum_tolebytes_p521_mc) (z,66) /\
      (x = z \/ nonoverlapping (x,8 * 9) (z,66))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_tolebytes_p521_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,66)) s = bytelist_of_num 66 n)
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,66)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOLEBYTES_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_tolebytes_p521_windows_mc = define_from_elf
   "bignum_tolebytes_p521_windows_mc" "x86/p521/bignum_tolebytes_p521.obj";;

let bignum_tolebytes_p521_windows_tmc = define_trimmed "bignum_tolebytes_p521_windows_tmc" bignum_tolebytes_p521_windows_mc;;

let BIGNUM_TOLEBYTES_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_tolebytes_p521_windows_tmc); (x,8 * 9)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,66) /\
      nonoverlapping (word pc,LENGTH bignum_tolebytes_p521_windows_tmc) (z,66) /\
      (x = z \/ nonoverlapping (x,8 * 9) (z,66))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_tolebytes_p521_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,66)) s = bytelist_of_num 66 n)
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,66);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_tolebytes_p521_windows_tmc bignum_tolebytes_p521_tmc
    BIGNUM_TOLEBYTES_P521_CORRECT);;

let BIGNUM_TOLEBYTES_P521_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_tolebytes_p521_windows_mc); (x,8 * 9)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,66) /\
      nonoverlapping (word pc,LENGTH bignum_tolebytes_p521_windows_mc) (z,66) /\
      (x = z \/ nonoverlapping (x,8 * 9) (z,66))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_tolebytes_p521_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,66)) s = bytelist_of_num 66 n)
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,66);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOLEBYTES_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

