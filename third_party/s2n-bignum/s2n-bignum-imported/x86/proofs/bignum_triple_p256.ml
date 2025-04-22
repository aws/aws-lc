(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_256, the field characteristic for the NIST P-256 curve. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p256/bignum_triple_p256.o";;
 ****)

let bignum_triple_p256_mc = define_assert_from_elf "bignum_triple_p256_mc" "x86/p256/bignum_triple_p256.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xca;
                           (* ADOX (% r9) (% rdx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% r11) (% rdx) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% rdx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967296)) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% rax) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% rax) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x48; 0x19; 0xca;        (* SBB (% rdx) (% rcx) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xd0;        (* AND (% rax) (% rdx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_triple_p256_tmc = define_trimmed "bignum_triple_p256_tmc" bignum_triple_p256_mc;;

let BIGNUM_TRIPLE_P256_EXEC = X86_MK_CORE_EXEC_RULE bignum_triple_p256_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let p256genshortredlemma = prove
 (`!n. n < 3 * 2 EXP 256
       ==> let q = (n DIV 2 EXP 256) + 1 in
           q <= 3 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let BIGNUM_TRIPLE_P256_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0xc0) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_triple_p256_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0xbf) /\
                  bignum_from_memory (z,4) s = (3 * n) MOD p_256)
          (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** Input load and initial multiplication by 3 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P256_EXEC (1--20) (1--20) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s5; sum_s9; sum_s13; sum_s17; sum_s20] =
    2 EXP 256 + 3 * n`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = (3 * n) DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s20:int64 = word(h + 1)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ARITH_RULE
     `(3 * n) DIV 2 EXP 256 + 1 = (2 EXP 256 + 3 * n) DIV 2 EXP 256`] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `3 * n` p256genshortredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of 3 * n - (h + 1) * p_256 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P256_EXEC
    [21;24;25;26;27;30;31;32] (21--32) THEN
  MP_TAC(SPECL
   [`sum_s32:int64`;
    `&(bignum_of_wordlist[sum_s21; sum_s26; sum_s27; sum_s30]):real`;
    `256`; `3 * n`; `(h + 1) * p_256`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_256 <= 3 * n + p_256`;
        `3 * n < (h + 1) * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `&(3 * n):real =
      &(bignum_of_wordlist [sum_s5; sum_s9; sum_s13; sum_s17; word (h + 1)]) -
      &2 pow 256`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN

    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(fun th ->
      (MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      (MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) th THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P256_EXEC [37;39;41;43] (33--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> 3 * n < (h + 1) * p_256` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &(3 * n) - y + z ==> &(3 * n) = x + y - z`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TRIPLE_P256_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_triple_p256_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * n) MOD p_256)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_triple_p256_tmc
      BIGNUM_TRIPLE_P256_CORRECT);;

let BIGNUM_TRIPLE_P256_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_triple_p256_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * n) MOD p_256)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P256_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_triple_p256_windows_mc = define_from_elf
   "bignum_triple_p256_windows_mc" "x86/p256/bignum_triple_p256.obj";;

let bignum_triple_p256_windows_tmc = define_trimmed "bignum_triple_p256_windows_tmc" bignum_triple_p256_windows_mc;;

let BIGNUM_TRIPLE_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_triple_p256_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p256_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * n) MOD p_256)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_triple_p256_windows_tmc bignum_triple_p256_tmc
    BIGNUM_TRIPLE_P256_CORRECT);;

let BIGNUM_TRIPLE_P256_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_triple_p256_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p256_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * n) MOD p_256)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

