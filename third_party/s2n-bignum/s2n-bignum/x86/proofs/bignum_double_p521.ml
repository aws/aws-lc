(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Doubling modulo p_521, the field characteristic for the NIST P-521 curve. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_double_p521.o";;
 ****)

let bignum_double_p521_mc =
  define_assert_from_elf "bignum_double_p521_mc" "x86/p521/bignum_double_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x4e; 0x40;  (* MOV (% rcx) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x0f; 0xba; 0xe1; 0x08;
                           (* BT (% rcx) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rax) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rax) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x47; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rax) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x47; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rax) *)
  0x48; 0x8b; 0x46; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0x48; 0x89; 0x47; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rax) *)
  0x48; 0x11; 0xc9;        (* ADC (% rcx) (% rcx) *)
  0x48; 0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rcx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x4f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rcx) *)
  0xc3                     (* RET *)
];;

let bignum_double_p521_tmc = define_trimmed "bignum_double_p521_tmc" bignum_double_p521_mc;;

let BIGNUM_DOUBLE_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_double_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_DOUBLE_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x6e) (z,8 * 9) /\
        (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_double_p521_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = word (pc + 0x6d) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (2 * n) MOD p_521))
            (MAYCHANGE [RIP; RAX; RCX] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_DOUBLE_P521_EXEC
   [4;7;10;13;16;19;22;25;27] (1--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** Confirm the initial bit selection as the right condition ***)

  SUBGOAL_THEN `bit 8 (n_8:int64) <=> p_521 <= 2 * n`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[BIT_VAL_MOD] THEN
    SUBGOAL_THEN `val(n_8:int64) = n DIV 2 EXP 512`
    SUBST1_TAC THENL
     [EXPAND_TAC "n" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[];
      MATCH_MP_TAC(MESON[MOD_LT]
       `y < n /\ (x <= y <=> q) ==> (x <= y MOD n <=> q)`) THEN
      UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Hence show that we get the right result in 521 bits ***)

  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if p_521 <= 2 * n then &(2 * n) - &p_521 else &(2 * n):real`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MULT_2; MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `bb <=> p_521 <= 2 * n` THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DOUBLE_P521_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_double_p521_tmc) (z,8 * 9) /\
        nonoverlapping (stackpointer,8) (z,8 * 9) /\
        (x = z \/ nonoverlapping (x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p521_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (2 * n) MOD p_521))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC
    bignum_double_p521_tmc BIGNUM_DOUBLE_P521_CORRECT);;

let BIGNUM_DOUBLE_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_double_p521_mc) (z,8 * 9) /\
        nonoverlapping (stackpointer,8) (z,8 * 9) /\
        (x = z \/ nonoverlapping (x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (2 * n) MOD p_521))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DOUBLE_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_double_p521_windows_mc = define_from_elf
   "bignum_double_p521_windows_mc" "x86/p521/bignum_double_p521.obj";;

let bignum_double_p521_windows_tmc = define_trimmed "bignum_double_p521_windows_tmc" bignum_double_p521_windows_mc;;

let BIGNUM_DOUBLE_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_double_p521_windows_tmc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_double_p521_windows_tmc) (z,8 * 9) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
        (x = z \/ nonoverlapping (x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p521_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (2 * n) MOD p_521))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_double_p521_windows_tmc bignum_double_p521_tmc
    BIGNUM_DOUBLE_P521_CORRECT);;

let BIGNUM_DOUBLE_P521_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_double_p521_windows_mc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_double_p521_windows_mc) (z,8 * 9) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
        (x = z \/ nonoverlapping (x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p521_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (2 * n) MOD p_521))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DOUBLE_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

