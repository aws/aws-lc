(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_521, the field characteristic of the NIST curve P-521. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_mod_p521_9.o";;
 ****)

let bignum_mod_p521_9_mc =
  define_assert_from_elf "bignum_mod_p521_9_mc" "x86/p521/bignum_mod_p521_9.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x48; 0x8b; 0x46; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rsi,64))) *)
  0xba; 0xff; 0x01; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 511)) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x48; 0xc1; 0xe8; 0x09;  (* SHR (% rax) (Imm8 (word 9)) *)
  0xf9;                    (* STCF *)
  0x48; 0x13; 0x06;        (* ADC (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x5e; 0x30;  (* MOV (% rbx) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x83; 0xd3; 0x00;  (* ADC (% rbx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x76; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xfa; 0x00; 0x02; 0x00; 0x00;
                           (* CMP (% rdx) (Imm32 (word 512)) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r11) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x5f; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rbx) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0x89; 0x77; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rsi) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe2; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rdx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x57; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rdx) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_mod_p521_9_tmc = define_trimmed "bignum_mod_p521_9_tmc" bignum_mod_p521_9_mc;;

let BIGNUM_MOD_P521_9_EXEC = X86_MK_CORE_EXEC_RULE bignum_mod_p521_9_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_MOD_P521_9_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0xa8) (z,8 * 9)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mod_p521_9_tmc) /\
                read RIP s = word (pc + 0x1) /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = word (pc + 0xa6) /\
                bignum_from_memory (z,9) s = n MOD p_521)
          (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11; RBX] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  (*** Breaking the problem down to (H + L) MOD p_521 ***)

  SUBGOAL_THEN `n MOD p_521 = (n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `n = 2 EXP 521 * n DIV 2 EXP 521 + n MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `n DIV 2 EXP 521 < 2 EXP 55 /\ n MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; ARITH_RULE
     `n DIV 2 EXP 521 < 2 EXP 55 <=> n < 2 EXP (64 * 9)`] THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
    `l = bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7;
                            word_and (word 511) n_8]` THEN
  ABBREV_TAC `h:int64 = word_ushr n_8 9` THEN

  SUBGOAL_THEN
   `n DIV 2 EXP 521 = val(h:int64) /\ n MOD 2 EXP 521 = l`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["n"; "h"; "l"] THEN CONJ_TAC THENL
     [CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD];
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
      SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD;
               ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
               MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; ADD_CLAUSES] THEN
      ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ADD_CLAUSES] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Initial non-overflowing addition s = H + L + 1 ***)

  X86_ACCSTEPS_TAC BIGNUM_MOD_P521_9_EXEC
   [6;8;10;12;14;16;18;20;21] (1--22) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s6;sum_s8;sum_s10;sum_s12;sum_s14;sum_s16;sum_s18;sum_s20;sum_s21] =
    val(h:int64) + l + 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      MAP_EVERY UNDISCH_TAC [`l < 2 EXP 521`; `val(h:int64) < 2 EXP 55`] THEN
      ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    EXPAND_TAC "l" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The net comparison s >= 2^521 <=> H + L >= p_521 ***)

  SUBGOAL_THEN `val(sum_s21:int64) < 512 <=> val(h:int64) + l < p_521`
  SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(val(h:int64) + l + 1) DIV 2 EXP 512 < 2 EXP 9` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The final optional subtraction of 1 and masking ***)

  X86_ACCSTEPS_TAC BIGNUM_MOD_P521_9_EXEC
   [23;25;27;29;31;33;35;37;39] (23--41) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if val(h:int64) + l < p_521
     then &(val(h:int64) + l + 1) - &1
     else &(val(h:int64) + l + 1) - &2 pow 521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`l < 2 EXP 521`; `val(h:int64) < 2 EXP 55`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `bb <=> val(h:int64) + l < p_521` THEN
  UNDISCH_THEN
   `bignum_of_wordlist
     [sum_s6;sum_s8;sum_s10;sum_s12;sum_s14;sum_s16;sum_s18;sum_s20;sum_s21] =
    val(h:int64) + l + 1`
   (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_P521_9_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 8),16) (z,8 * 9) /\
      ALL (nonoverlapping (word_sub stackpointer (word 8),8))
          [(word pc,LENGTH bignum_mod_p521_9_tmc); (x,8 * 9)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p521_9_tmc) (z,8 * 9)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p521_9_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD p_521)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 8),8)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_mod_p521_9_tmc BIGNUM_MOD_P521_9_CORRECT
   `[RBX]` 8);;

let BIGNUM_MOD_P521_9_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 8),16) (z,8 * 9) /\
      ALL (nonoverlapping (word_sub stackpointer (word 8),8))
          [(word pc,LENGTH bignum_mod_p521_9_mc); (x,8 * 9)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p521_9_mc) (z,8 * 9)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p521_9_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD p_521)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 8),8)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_P521_9_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_p521_9_windows_mc = define_from_elf
   "bignum_mod_p521_9_windows_mc" "x86/p521/bignum_mod_p521_9.obj";;

let bignum_mod_p521_9_windows_tmc = define_trimmed "bignum_mod_p521_9_windows_tmc" bignum_mod_p521_9_windows_mc;;

let BIGNUM_MOD_P521_9_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 24),32) (z,8 * 9) /\
      ALL (nonoverlapping (word_sub stackpointer (word 24),24))
          [(word pc,LENGTH bignum_mod_p521_9_windows_tmc); (x,8 * 9)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p521_9_windows_tmc) (z,8 * 9)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p521_9_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD p_521)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 24),24)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_mod_p521_9_windows_tmc bignum_mod_p521_9_tmc
    BIGNUM_MOD_P521_9_CORRECT `[RBX]` 8);;

let BIGNUM_MOD_P521_9_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 24),32) (z,8 * 9) /\
      ALL (nonoverlapping (word_sub stackpointer (word 24),24))
          [(word pc,LENGTH bignum_mod_p521_9_windows_mc); (x,8 * 9)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p521_9_windows_mc) (z,8 * 9)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p521_9_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD p_521)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_P521_9_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

