(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Halving modulo p_256k1, the field characteristic for secp256k1.           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_half_p256k1.o";;
 ****)

let bignum_half_p256k1_mc =
  define_assert_from_elf "bignum_half_p256k1_mc" "x86/secp256k1/bignum_half_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x0e;        (* MOV (% rcx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xb8; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294968273)) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0xc7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Imm32 (word 1)) *)
  0x49; 0x21; 0xc9;        (* AND (% r9) (% rcx) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x0f; 0x44; 0xc1;  (* CMOVE (% rax) (% r9) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x0f; 0xac; 0xd1; 0x01;
                           (* SHRD (% rcx) (% rdx) (Imm8 (word 1)) *)
  0x48; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (rdi,0))) (% rcx) *)
  0x4c; 0x0f; 0xac; 0xc2; 0x01;
                           (* SHRD (% rdx) (% r8) (Imm8 (word 1)) *)
  0x48; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rdx) *)
  0x4d; 0x0f; 0xac; 0xc8; 0x01;
                           (* SHRD (% r8) (% r9) (Imm8 (word 1)) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x0f; 0xac; 0xc1; 0x01;
                           (* SHRD (% r9) (% rax) (Imm8 (word 1)) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0xc3                     (* RET *)
];;

let bignum_half_p256k1_tmc = define_trimmed "bignum_half_p256k1_tmc" bignum_half_p256k1_mc;;

let BIGNUM_HALF_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_half_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_HALF_P256K1_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x5e) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_half_p256k1_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x5d) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 2 * n) MOD p_256k1))
            (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  X86_STEPS_TAC BIGNUM_HALF_P256K1_EXEC (1--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_1_BITVAL]) THEN
  SUBGOAL_THEN `bit 0 (n_0:int64) <=> ODD n` SUBST_ALL_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[BIT_LSB; ODD_ADD; ODD_MULT; ODD_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL; BITVAL_EQ_0; COND_SWAP]) THEN
    RULE_ASSUM_TAC(SIMP_RULE[BITVAL_CLAUSES])] THEN

  X86_ACCSTEPS_TAC BIGNUM_HALF_P256K1_EXEC (9--13) (9--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(inverse_mod p_256k1 2 * n) MOD p_256k1 =
    (if ODD n then n + p_256k1 else n) DIV 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `n < p_256k1` THEN ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_DIV_COPRIME THEN
    REWRITE_TAC[COPRIME_2; DIVIDES_2; GSYM NOT_ODD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[p_256k1; ODD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
    REWRITE_TAC[COND_ID; NUMBER_RULE
     `(n + p:num == m) (mod p) <=> (n == m) (mod p)`] THEN
    MATCH_MP_TAC(NUMBER_RULE
       `(x * y == 1) (mod n) ==> (a == x * y * a) (mod n)`) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_2] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * 4)` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[CONG_SYM]] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC
   `(bignum_of_wordlist [sum_s9; sum_s10; sum_s11; sum_s12; sum_s13])
    DIV 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[ARITH_RULE `2 * 2 EXP (64 * 4) = 2 EXP 257`] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    MATCH_MP_TAC(NUMBER_RULE
     `!d. n * d + b = a ==> (a == b) (mod n)`) THEN
    EXISTS_TAC `val(sum_s13:int64) DIV 2` THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[MATCH_MP VAL_WORD_SUBWORD_JOIN_64 (ARITH_RULE `1 <= 64`)] THEN
    ARITH_TAC]);;

let BIGNUM_HALF_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_half_p256k1_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_half_p256k1_tmc
      BIGNUM_HALF_P256K1_CORRECT);;

let BIGNUM_HALF_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_half_p256k1_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_HALF_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_half_p256k1_windows_mc = define_from_elf
   "bignum_half_p256k1_windows_mc" "x86/secp256k1/bignum_half_p256k1.obj";;

let bignum_half_p256k1_windows_tmc = define_trimmed "bignum_half_p256k1_windows_tmc" bignum_half_p256k1_windows_mc;;

let BIGNUM_HALF_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_half_p256k1_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_half_p256k1_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_half_p256k1_windows_tmc
    bignum_half_p256k1_tmc BIGNUM_HALF_P256K1_CORRECT);;

let BIGNUM_HALF_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_half_p256k1_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_half_p256k1_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_HALF_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

