(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Doubling modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_double_p256k1.o";;
 ****)

let bignum_double_p256k1_mc =
  define_assert_from_elf "bignum_double_p256k1_mc" "x86/secp256k1/bignum_double_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4c; 0x8b; 0x56; 0x18;  (* MOV (% r10) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x89; 0xd2;        (* MOV (% rdx) (% r10) *)
  0x4c; 0x8b; 0x4e; 0x10;  (* MOV (% r9) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xc1; 0xea; 0x3f;  (* SHR (% rdx) (Imm8 (word 63)) *)
  0x4d; 0x0f; 0xa4; 0xca; 0x01;
                           (* SHLD (% r10) (% r9) (Imm8 (word 1)) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x4c; 0x8b; 0x46; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rsi,8))) *)
  0x4d; 0x0f; 0xa4; 0xc1; 0x01;
                           (* SHLD (% r9) (% r8) (Imm8 (word 1)) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x48; 0x8b; 0x0e;        (* MOV (% rcx) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x0f; 0xa4; 0xc8; 0x01;
                           (* SHLD (% r8) (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x21; 0xc0;        (* AND (% rax) (% r8) *)
  0x48; 0xd1; 0xe1;        (* SHL (% rcx) (Imm8 (word 1)) *)
  0x48; 0xbe; 0x2e; 0xfc; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rsi) (Imm64 (word 18446744069414583342)) *)
  0x48; 0x39; 0xce;        (* CMP (% rsi) (% rcx) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0xf7; 0xd6;        (* NOT (% rsi) *)
  0x48; 0x0f; 0x44; 0xf2;  (* CMOVE (% rsi) (% rdx) *)
  0x48; 0x01; 0xf1;        (* ADD (% rcx) (% rsi) *)
  0x48; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (rdi,0))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r8) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r10) *)
  0xc3                     (* RET *)
];;

let bignum_double_p256k1_tmc = define_trimmed "bignum_double_p256k1_tmc" bignum_double_p256k1_mc;;

let BIGNUM_DOUBLE_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_double_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_DOUBLE_P256K1_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x6c) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_double_p256k1_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x6b) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_256k1))
            (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; R8; R9; R10] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  X86_STEPS_TAC BIGNUM_DOUBLE_P256K1_EXEC (1--13) THEN
  ABBREV_TAC `topbit <=> bit 63 (m_3:int64)` THEN
  SUBGOAL_THEN `word_ushr (m_3:int64) 63 = word(bitval topbit)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_BITVAL] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    EXPAND_TAC "topbit" THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC
   `l = bignum_of_wordlist
     [word_shl m_0 1;
      word_subword ((word_join:int64->int64->int128) m_1 m_0) (63,64);
      word_subword ((word_join:int64->int64->int128) m_2 m_1) (63,64);
      word_subword ((word_join:int64->int64->int128) m_3 m_2) (63,64)]` THEN
  SUBGOAL_THEN `2 EXP 256 * bitval topbit + l = 2 * n` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "n"; "topbit"] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC BIGNUM_DOUBLE_P256K1_EXEC (15--16) (14--19) THEN
  RULE_ASSUM_TAC(SIMP_RULE[ADD_CLAUSES; VAL_EQ_0]) THEN
  SUBGOAL_THEN
   `word_add (word (bitval topbit)) (word (bitval carry_s16)) =
    (word 0:int64) <=>
    2 * n < p_256k1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ_0] THEN
    REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    ASM_CASES_TAC `topbit:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS `2 EXP 256 <= l + 4294968273` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[p_256k1] THEN ARITH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 128 <=
      bignum_of_wordlist[word_shl m_0 1;
       word_and
        (word_and
           (word_subword ((word_join:int64->int64->int128) m_3 m_2) (63,64))
           (word_subword ((word_join:int64->int64->int128) m_2 m_1) (63,64)))
         (word_subword ((word_join:int64->int64->int128) m_1 m_0) (63,64))] +
      4294968273` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "l" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP 64 /\ (a < 2 EXP 64 - 1 <=> h < 2 EXP 192 - 1) /\
      (~(h < 2 EXP 192 - 1)
       ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
            2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273))
      ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
           2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273)`) THEN
    SIMP_TAC[VAL_BOUND_64; BIGNUM_OF_WORDLIST_LT_MAX; LENGTH;
             ARITH_MULT; ARITH_ADD; ARITH_SUC; EX; DE_MORGAN_THM;
             WORD_BITWISE_RULE
              `word_and a b = word_not(word 0) <=>
               a = word_not(word 0) /\ b = word_not(word 0)`] THEN
    REWRITE_TAC[DISJ_ACI] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  X86_ACCSTEPS_TAC BIGNUM_DOUBLE_P256K1_EXEC [20;22;24;26] (20--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s27" THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 4`;
    `if 2 * n < p_256k1 then &(2 * n) else &(2 * n) - &p_256k1:real`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MULT_2; MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256k1] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `q <=> 2 * n < p_256k1` THEN
  UNDISCH_THEN `2 EXP 256 * bitval topbit + l = 2 * n`
   (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "l" THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DOUBLE_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_double_p256k1_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC
    bignum_double_p256k1_tmc BIGNUM_DOUBLE_P256K1_CORRECT);;

let BIGNUM_DOUBLE_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_double_p256k1_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DOUBLE_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_double_p256k1_windows_mc = define_from_elf
   "bignum_double_p256k1_windows_mc" "x86/secp256k1/bignum_double_p256k1.obj";;

let bignum_double_p256k1_windows_tmc = define_trimmed "bignum_double_p256k1_windows_tmc" bignum_double_p256k1_windows_mc;;

let BIGNUM_DOUBLE_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_double_p256k1_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_double_p256k1_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_double_p256k1_windows_tmc bignum_double_p256k1_tmc
    BIGNUM_DOUBLE_P256K1_CORRECT);;

let BIGNUM_DOUBLE_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_double_p256k1_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_double_p256k1_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_double_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> bignum_from_memory (z,4) s = (2 * n) MOD p_256k1))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,4);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DOUBLE_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

