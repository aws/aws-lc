(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_521, the order of the NIST curve P-521                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_mod_n521_9.o";;
 ****)

let bignum_mod_n521_9_mc =
  define_assert_from_elf "bignum_mod_n521_9_mc" "x86/p521/bignum_mod_n521_9.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x56; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xc7; 0xc0; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294966784)) *)
  0x48; 0x09; 0xd0;        (* OR (% rax) (% rdx) *)
  0x48; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rax) *)
  0x48; 0xc1; 0xea; 0x09;  (* SHR (% rdx) (Imm8 (word 9)) *)
  0x48; 0x83; 0xc2; 0x01;  (* ADD (% rdx) (Imm8 (word 1)) *)
  0x49; 0xb9; 0xf7; 0x9b; 0xc7; 0x6e; 0xe1; 0x48; 0x90; 0x44;
                           (* MOV (% r9) (Imm64 (word 4940528924288850935)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% rax) (% rdx,% r9) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x06;
                           (* ADCX (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x49; 0xba; 0x51; 0xb8; 0x63; 0x76; 0x47; 0x36; 0x4a; 0xc4;
                           (* MOV (% r10) (Imm64 (word 14144177260267288657)) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xc2;
                           (* MULX4 (% r8,% rax) (% rdx,% r10) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x46; 0x08;
                           (* ADCX (% rax) (Memop Quadword (%% (rsi,8))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% rax) (% rcx) *)
  0x48; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rax) *)
  0x49; 0xbb; 0x2f; 0x5a; 0xf6; 0x08; 0xb7; 0xfe; 0x33; 0x80;
                           (* MOV (% r11) (Imm64 (word 9238007322749852207)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcb;
                           (* MULX4 (% rcx,% rax) (% rdx,% r11) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x46; 0x10;
                           (* ADCX (% rax) (Memop Quadword (%% (rsi,16))) *)
  0xf3; 0x49; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADOX (% rax) (% r8) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0xb8; 0x94; 0x69; 0xd0; 0x40; 0x7c; 0x78; 0x79; 0xae;
                           (* MOV (% rax) (Imm64 (word 12572212309840128404)) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xc0;
                           (* MULX4 (% r8,% rax) (% rdx,% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x46; 0x18;
                           (* ADCX (% rax) (Memop Quadword (%% (rsi,24))) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% rax) (% rcx) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0xb8; 0x05; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 5)) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% rax) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0x46; 0x20;
                           (* ADCX (% rax) (Memop Quadword (%% (rsi,32))) *)
  0xf3; 0x49; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADOX (% rax) (% r8) *)
  0x48; 0x89; 0x47; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rax) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% rcx) (% rcx) *)
  0x48; 0x13; 0x4e; 0x28;  (* ADC (% rcx) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x89; 0x4f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rcx) *)
  0x48; 0x8b; 0x4e; 0x30;  (* MOV (% rcx) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x48; 0x89; 0x4f; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rcx) *)
  0x48; 0x8b; 0x4e; 0x38;  (* MOV (% rcx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0x48; 0x89; 0x4f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rcx) *)
  0x48; 0x8b; 0x4f; 0x40;  (* MOV (% rcx) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0x11; 0xc1;        (* ADC (% rcx) (% rax) *)
  0xf5;                    (* CMC *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x49; 0x21; 0xd1;        (* AND (% r9) (% rdx) *)
  0x49; 0x21; 0xd2;        (* AND (% r10) (% rdx) *)
  0x49; 0x21; 0xd3;        (* AND (% r11) (% rdx) *)
  0x49; 0xb8; 0x94; 0x69; 0xd0; 0x40; 0x7c; 0x78; 0x79; 0xae;
                           (* MOV (% r8) (Imm64 (word 12572212309840128404)) *)
  0x49; 0x21; 0xd0;        (* AND (% r8) (% rdx) *)
  0x83; 0xe2; 0x05;        (* AND (% edx) (Imm8 (word 5)) *)
  0x4c; 0x29; 0x0f;        (* SUB (Memop Quadword (%% (rdi,0))) (% r9) *)
  0x4c; 0x19; 0x57; 0x08;  (* SBB (Memop Quadword (%% (rdi,8))) (% r10) *)
  0x4c; 0x19; 0x5f; 0x10;  (* SBB (Memop Quadword (%% (rdi,16))) (% r11) *)
  0x4c; 0x19; 0x47; 0x18;  (* SBB (Memop Quadword (%% (rdi,24))) (% r8) *)
  0x48; 0x19; 0x57; 0x20;  (* SBB (Memop Quadword (%% (rdi,32))) (% rdx) *)
  0x48; 0x19; 0x47; 0x28;  (* SBB (Memop Quadword (%% (rdi,40))) (% rax) *)
  0x48; 0x19; 0x47; 0x30;  (* SBB (Memop Quadword (%% (rdi,48))) (% rax) *)
  0x48; 0x19; 0x47; 0x38;  (* SBB (Memop Quadword (%% (rdi,56))) (% rax) *)
  0x19; 0xc1;              (* SBB (% ecx) (% eax) *)
  0x81; 0xe1; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% ecx) (Imm32 (word 511)) *)
  0x48; 0x89; 0x4f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rcx) *)
  0xc3                     (* RET *)
];;

let bignum_mod_n521_9_tmc = define_trimmed "bignum_mod_n521_9_tmc" bignum_mod_n521_9_mc;;

let BIGNUM_MOD_N521_9_EXEC = X86_MK_CORE_EXEC_RULE bignum_mod_n521_9_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_521 = new_definition `n_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449`;;

let BIGNUM_MOD_N521_9_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x124) (z,8 * 9) /\
      (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mod_n521_9_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = word (pc + 0x123) /\
                bignum_from_memory (z,9) s = n MOD n_521)
          (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `9` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  (*** Initial quotient approximation ***)

  X86_STEPS_TAC BIGNUM_MOD_N521_9_EXEC (1--6) THEN
  SUBGOAL_THEN `n DIV 2 EXP 521 = val(n_8:int64) DIV 2 EXP 9` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q:int64 = word_add (word_ushr n_8 9) (word 1)` THEN
  SUBGOAL_THEN `val(n_8:int64) DIV 2 EXP 9 + 1 = val(q:int64)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR] THEN
    ASM_REWRITE_TAC[VAL_WORD_1; DIMINDEX_64] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPEC `n_8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(q:int64) <= 2 EXP 55` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MP_TAC(SPEC `n_8:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Observe that the last add clears the CF and OF flags as required ***)

  SUBGOAL_THEN
   `(2 EXP 64 <= val (word_ushr n_8 9) + 1 <=> F) /\
    (~(ival (word_ushr (n_8:int64) 9) + &1 = ival(q:int64)) <=> F)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_USHR; word_ushr] THEN
    REWRITE_TAC[GSYM WORD_ADD; IVAL_VAL; MSB_VAL] THEN
    REWRITE_TAC[DIMINDEX_64; NUM_REDUCE_CONV `64 - 1`; GSYM NOT_LT] THEN
    MP_TAC(SPEC `n_8:int64` VAL_BOUND_64) THEN
    SIMP_TAC[BITVAL_CLAUSES; INT_MUL_RZERO; INT_SUB_RZERO; VAL_WORD_LT;
     ARITH_RULE
     `n < 2 EXP 64
      ==> n DIV 2 EXP 9 + 1 < 2 EXP 64 /\ n DIV 2 EXP 9 + 1 < 2 EXP 63 /\
          n DIV 2 EXP 9 < 2 EXP 63`] THEN
    SIMP_TAC[INT_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64; MOD_LT; ARITH_RULE
      `n < 2 EXP 64
       ==> n DIV 2 EXP 9 + 1 < 2 EXP 64 /\ n DIV 2 EXP 9 < 2 EXP 64`];
    ALL_TAC] THEN

  (*** Main multiply-add block, observing that the last high product = 0 ***)

  X86_ACCSTEPS_TAC BIGNUM_MOD_N521_9_EXEC (7--42) (7--42) THEN
  SUBGOAL_THEN `&(val(mulhi_s27:int64)):real = &0`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
  THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 64 * c + s:real = q
      ==> &0 <= s /\ (~(c = &0) ==> &1 <= c) /\ q < &2 pow 64
          ==> c = &0`)) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; LE_1] THEN
    UNDISCH_TAC `val(q:int64) <= 2 EXP 55` THEN ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 64 * &0 + x:real = y ==> x = y`))] THEN
  SUBGOAL_THEN
   `&2 pow 576 * &(bitval carry_s42) +
    &(bignum_of_wordlist
       [sum_s9; sum_s14; sum_s19; sum_s24;
        sum_s29; sum_s33; sum_s36; sum_s39; sum_s42]):real =
    &2 pow 576 + (&n - &(val(q:int64)) * &n_521)`
  ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    SUBGOAL_THEN
     `&(val(word_or (word 18446744073709551104) n_8:int64)):real =
      (&2 pow 64 - &2 pow 9) + &(val n_8 MOD 2 EXP 9)`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
       `word_or b a = word_or b (word_and a (word_not b))`] THEN
      SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
       `word_and x (word_and y (word_not x)) = word 0`] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; EQ_ADD_LCANCEL] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD];
      ALL_TAC] THEN
    EXPAND_TAC "n" THEN SUBST1_TAC(SYM(ASSUME
     `val(n_8:int64) DIV 2 EXP 9 + 1 = val(q:int64)`)) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD;
                n_521] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction; rvalue hack to handle the 32-bit operations ****)

  X86_ACCSTEPS_TAC BIGNUM_MOD_N521_9_EXEC (51--58) (43--61) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `read (rvalue
     (word_sub sum_s42 (word_add mulhi_s27 (word (bitval carry_s58))):int64))
     (s61:x86state) =
    word_sub sum_s42 (word_add mulhi_s27 (word (bitval carry_s58)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_RVALUE]; ALL_TAC] THEN
  ACCUMULATE_ARITH_TAC "s61" THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE LAND_CONV [READ_RVALUE]) THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word(bitval carry_s58) = (word_zx:int64->int32) (word(bitval carry_s58))`
  SUBST_ALL_TAC THENL
   [SIMP_TAC[WORD_ZX_WORD_SIMPLE; DIMINDEX_32; DIMINDEX_64; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH;
           GSYM WORD_ZX_SUB; GSYM WORD_ZX_ADD; WORD_ZX_AND] THEN
  ASM_REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `511 MOD 2 EXP 32 = 2 EXP 9 - 1`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  EXISTS_TAC `521` THEN
  EXISTS_TAC
   `if n < val(q:int64) * n_521
    then (&n - &(val q) * &n_521) + &n_521
    else &n - &(val q) * &n_521:real` THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[n_521] THEN ARITH_TAC;
    REWRITE_TAC[n_521] THEN ARITH_TAC;
    ALL_TAC;
    UNDISCH_THEN `val(n_8:int64) DIV 2 EXP 9 + 1 = val(q:int64)`
     (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `n DIV 2 EXP 521 = val(n_8:int64) DIV 2 EXP 9`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH
     `x - (q + &1) * n + n = x - q * n`] THEN
    SUBGOAL_THEN `n DIV 2 EXP 521 * n_521 <= n` MP_TAC THENL
     [REWRITE_TAC[n_521] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_TAC `n < 2 EXP (64 * 9)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ; MOD_UNIQUE] THEN
    (CONJ_TAC THENL
      [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[n_521] THEN ARITH_TAC;
       ASM_SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB] THEN
       REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE])] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `e:real = &2 pow 576 + x ==> x = e - &2 pow 576`)) THEN
  SUBGOAL_THEN `n < val(q:int64) * n_521 <=> ~carry_s42` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `576` THEN
    ASM_REWRITE_TAC[REAL_BITVAL_NOT; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    BOUNDER_TAC[];
    ASM_REWRITE_TAC[COND_SWAP; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD_ZX_GEN] THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES; n_521] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC]);;

let BIGNUM_MOD_N521_9_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_n521_9_tmc) (z,8 * 9) /\
      nonoverlapping (stackpointer,8) (z,8 * 9) /\
      (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n521_9_tmc /\
                read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD n_521)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC
    bignum_mod_n521_9_tmc BIGNUM_MOD_N521_9_CORRECT);;

let BIGNUM_MOD_N521_9_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_n521_9_mc) (z,8 * 9) /\
      nonoverlapping (stackpointer,8) (z,8 * 9) /\
      (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n521_9_mc /\
                read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD n_521)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_N521_9_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_n521_9_windows_mc = define_from_elf
   "bignum_mod_n521_9_windows_mc" "x86/p521/bignum_mod_n521_9.obj";;

let bignum_mod_n521_9_windows_tmc = define_trimmed "bignum_mod_n521_9_windows_tmc" bignum_mod_n521_9_windows_mc;;

let BIGNUM_MOD_N521_9_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_n521_9_windows_tmc); (x,8 * 9)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_n521_9_windows_tmc) (z,8 * 9) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
      (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n521_9_windows_tmc /\
                read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD n_521)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_mod_n521_9_windows_tmc bignum_mod_n521_9_tmc
    BIGNUM_MOD_N521_9_CORRECT);;

let BIGNUM_MOD_N521_9_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_n521_9_windows_mc); (x,8 * 9)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_n521_9_windows_mc) (z,8 * 9) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
      (x = z \/ nonoverlapping(x,8 * 9) (z,8 * 9))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n521_9_windows_mc /\
                read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,9) s = n MOD n_521)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_N521_9_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

