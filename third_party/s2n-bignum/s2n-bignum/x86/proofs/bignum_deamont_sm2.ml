(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_sm2.             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/sm2/bignum_deamont_sm2.o";;
 ****)

let bignum_deamont_sm2_mc =
  define_assert_from_elf "bignum_deamont_sm2_mc" "x86/sm2/bignum_deamont_sm2.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xce;        (* MOV (% rsi) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xf0;        (* SBB (% r8) (% rsi) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xce;        (* MOV (% rsi) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xf1;        (* SBB (% r9) (% rsi) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xce;        (* MOV (% rsi) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xf2;        (* SBB (% r10) (% rsi) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xce;        (* MOV (% rsi) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xf3;        (* SBB (% r11) (% rsi) *)
  0x49; 0x83; 0xe8; 0xff;  (* SUB (% r8) (Imm8 (word 255)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584320)) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x49; 0x83; 0xda; 0xff;  (* SBB (% r10) (Imm8 (word 255)) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584319)) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x21; 0xc8;        (* AND (% rax) (% rcx) *)
  0x48; 0x21; 0xca;        (* AND (% rdx) (% rcx) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_deamont_sm2_tmc = define_trimmed "bignum_deamont_sm2_tmc" bignum_deamont_sm2_mc;;

let BIGNUM_DEAMONT_SM2_EXEC = X86_MK_CORE_EXEC_RULE bignum_deamont_sm2_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let BIGNUM_DEAMONT_SM2_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0xf2) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_deamont_sm2_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0xf1) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2)
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_DEAMONT_SM2_EXEC (1--52) (1--52) THEN

  (*** Show that the pre-reduced dd satisfies the key congruence ***)

  ABBREV_TAC `dd = bignum_of_wordlist[sum_s49;sum_s50;sum_s51;sum_s52]` THEN
  SUBGOAL_THEN `(inverse_mod p_sm2 (2 EXP 256) * a == dd) (mod p_sm2)`
  MP_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `!e. (e * d == a) (mod p) /\ (e * i == 1) (mod p)
           ==> (i * a == d) (mod p)`) THEN
    EXISTS_TAC `2 EXP 256` THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN CONJ_TAC
    THENL [ALL_TAC; REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["dd"; "a"] THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[CONG] THEN
    DISCH_THEN SUBST1_TAC] THEN

  X86_ACCSTEPS_TAC BIGNUM_DEAMONT_SM2_EXEC
   [53;55;56;58;62;64;66;68] (53--69) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  SUBGOAL_THEN `carry_s58 <=> dd < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s69" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN `dd MOD p_sm2 = if p_sm2 <= dd then dd - p_sm2 else dd`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN MATCH_MP_TAC MOD_CASES THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[p_sm2; bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[GSYM REAL_OF_NUM_SUB]] THEN
  REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN ABBREV_TAC `q <=> dd < p_sm2` THEN
  EXPAND_TAC "dd" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DEAMONT_SM2_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_deamont_sm2_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_sm2_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC
    bignum_deamont_sm2_tmc BIGNUM_DEAMONT_SM2_CORRECT);;

let BIGNUM_DEAMONT_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_deamont_sm2_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_sm2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_SM2_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_deamont_sm2_windows_mc = define_from_elf
   "bignum_deamont_sm2_windows_mc" "x86/sm2/bignum_deamont_sm2.obj";;

let bignum_deamont_sm2_windows_tmc = define_trimmed "bignum_deamont_sm2_windows_tmc" bignum_deamont_sm2_windows_mc;;

let BIGNUM_DEAMONT_SM2_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 16),24) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_deamont_sm2_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_sm2_windows_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_sm2_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_deamont_sm2_windows_tmc bignum_deamont_sm2_tmc
    BIGNUM_DEAMONT_SM2_CORRECT);;

let BIGNUM_DEAMONT_SM2_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 16),24) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_deamont_sm2_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_sm2_windows_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_sm2_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_sm2 (2 EXP 256) * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_SM2_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

