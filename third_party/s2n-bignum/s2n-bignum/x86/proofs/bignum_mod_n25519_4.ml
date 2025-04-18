(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_25519, the basepoint order for curve25519.             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/curve25519/bignum_mod_n25519_4.o";;
 ****)

let bignum_mod_n25519_4_mc =
  define_assert_from_elf "bignum_mod_n25519_4_mc" "x86/curve25519/bignum_mod_n25519_4.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x4e; 0x18;  (* MOV (% rcx) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x89; 0xcb;        (* MOV (% r11) (% rcx) *)
  0x48; 0xc1; 0xe9; 0x3c;  (* SHR (% rcx) (Imm8 (word 60)) *)
  0x49; 0xc1; 0xe3; 0x04;  (* SHL (% r11) (Imm8 (word 4)) *)
  0x49; 0xc1; 0xeb; 0x04;  (* SHR (% r11) (Imm8 (word 4)) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xb8; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rax) (Imm64 (word 1503914060200516822)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x29; 0xc8;        (* SUB (% r8) (% r9) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4d; 0x19; 0xd1;        (* SBB (% r9) (% r10) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xb8; 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58;
                           (* MOV (% rax) (Imm64 (word 6346243789798364141)) *)
  0x48; 0x21; 0xc8;        (* AND (% rax) (% rcx) *)
  0x48; 0xba; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14;
                           (* MOV (% rdx) (Imm64 (word 1503914060200516822)) *)
  0x48; 0x21; 0xca;        (* AND (% rdx) (% rcx) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x10;
                           (* MOV (% rcx) (Imm64 (word 1152921504606846976)) *)
  0x48; 0x21; 0xc1;        (* AND (% rcx) (% rax) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_mod_n25519_4_tmc = define_trimmed "bignum_mod_n25519_4_tmc" bignum_mod_n25519_4_mc;;

let BIGNUM_MOD_N25519_4_EXEC = X86_MK_CORE_EXEC_RULE bignum_mod_n25519_4_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_25519 = new_definition `n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989`;;

let BIGNUM_MOD_N25519_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x99) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mod_n25519_4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = word (pc + 0x98) /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `m:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  X86_ACCSTEPS_TAC BIGNUM_MOD_N25519_4_EXEC
   [7;11;12;13; 15;17;19;20; 28;30;32;34] (1--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s35" THEN

  (*** Quotient and associated mangling ***)

  ABBREV_TAC `q:int64 = word_ushr m_3 60` THEN
  SUBGOAL_THEN
   `&(val(word_ushr (word_shl (m_3:int64) 4) 4)):real =
    &(val m_3) - &2 pow 60 * &(val(q:int64))`
  SUBST_ALL_TAC THENL [EXPAND_TAC "q" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN

  (*** Main reasoning including quotient estimate correctness ***)

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  EXISTS_TAC `256` THEN
  EXISTS_TAC
   `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
         &n_25519:real` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `m < val(q:int64) * n_25519 <=> carry_s20`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      EXPAND_TAC "m" THEN
      REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      BOOL_CASES_TAC `carry_s20:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    SUBGOAL_THEN `val(q:int64) = m DIV 2 EXP 252` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "q"] THEN
      CONV_TAC(RAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[VAL_WORD_USHR];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
    UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[n_25519; bitval] THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let BIGNUM_MOD_N25519_4_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_n25519_4_tmc) (z,8 * 4) /\
      nonoverlapping (stackpointer,8) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n25519_4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mod_n25519_4_tmc BIGNUM_MOD_N25519_4_CORRECT);;

let BIGNUM_MOD_N25519_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_n25519_4_mc) (z,8 * 4) /\
      nonoverlapping (stackpointer,8) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n25519_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_N25519_4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_n25519_4_windows_mc = define_from_elf
   "bignum_mod_n25519_4_windows_mc" "x86/curve25519/bignum_mod_n25519_4.obj";;

let bignum_mod_n25519_4_windows_tmc = define_trimmed "bignum_mod_n25519_4_windows_tmc" bignum_mod_n25519_4_windows_mc;;

let BIGNUM_MOD_N25519_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_n25519_4_windows_tmc); (x,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_n25519_4_windows_tmc) (z,8 * 4) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n25519_4_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_mod_n25519_4_windows_tmc
    bignum_mod_n25519_4_tmc BIGNUM_MOD_N25519_4_CORRECT);;

let BIGNUM_MOD_N25519_4_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_n25519_4_windows_mc); (x,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_n25519_4_windows_mc) (z,8 * 4) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n25519_4_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_N25519_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

