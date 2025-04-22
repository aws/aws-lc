(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_25519 of a single word and a bignum < p_25519.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/curve25519/bignum_cmul_p25519_alt.o";;
 ****)

let bignum_cmul_p25519_alt_mc = define_assert_from_elf "bignum_cmul_p25519_alt_mc" "x86/curve25519/bignum_cmul_p25519_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x41; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rcx,8))) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x41; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rcx,16))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x41; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x11; 0xf2;        (* ADC (% rdx) (% rsi) *)
  0x4c; 0x0f; 0xa4; 0xda; 0x01;
                           (* SHLD (% rdx) (% r11) (Imm8 (word 1)) *)
  0xb9; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 19)) *)
  0x48; 0x8d; 0x42; 0x01;  (* LEA (% rax) (%% (rdx,1)) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x11; 0xf2;        (* ADC (% r10) (% rsi) *)
  0x49; 0x11; 0xf3;        (* ADC (% r11) (% rsi) *)
  0x48; 0x0f; 0x42; 0xce;  (* CMOVB (% rcx) (% rsi) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xf1;        (* SBB (% r9) (% rsi) *)
  0x49; 0x19; 0xf2;        (* SBB (% r10) (% rsi) *)
  0x49; 0x19; 0xf3;        (* SBB (% r11) (% rsi) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_cmul_p25519_alt_tmc = define_trimmed "bignum_cmul_p25519_alt_tmc" bignum_cmul_p25519_alt_mc;;

let BIGNUM_CMUL_P25519_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmul_p25519_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let BIGNUM_CMUL_P25519_ALT_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0x86) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmul_p25519_alt_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0x85) /\
                  (a < p_25519
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_25519))
          (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_25519 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_25519` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_CMUL_P25519_ALT_EXEC (1--39)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `val(c:int64) * a` p25519redlemma) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    MP_TAC(ISPEC `c:int64` VAL_BOUND) THEN UNDISCH_TAC `a < p_25519` THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Intermediate result from initial multiply ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P25519_ALT_EXEC (1--20) (1--20) THEN
  ABBREV_TAC
  `ca = bignum_of_wordlist [mullo_s3; sum_s9; sum_s13; sum_s19; sum_s20]`THEN
  SUBGOAL_THEN `val(c:int64) * a = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check((fun l -> not(l = [])) o
        intersect [`a:num`; `x:int64`; `c:int64`] o frees o concl))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC BIGNUM_CMUL_P25519_ALT_EXEC (21--24) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [mullo_s3; sum_s9; sum_s13; word_or sum_s19 (word 9223372036854775808)]` THEN
  SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [mullo_s3; sum_s9; sum_s13] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s20 sum_s19) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 < 2 EXP 64` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q:int64 = word_add hw (word 1)` THEN
  SUBGOAL_THEN `&(val(q:int64)):real = &(val(hw:int64)) + &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P25519_ALT_EXEC
   [25;26;27;28;29;31;32;33;34] (25--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(hw:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(hw:int64) + 1) * p_25519 <=> ~carry_s29`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s29:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_CMUL_P25519_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_p25519_alt_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p25519_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_25519
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_25519))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_cmul_p25519_alt_tmc
    BIGNUM_CMUL_P25519_ALT_CORRECT);;

let BIGNUM_CMUL_P25519_ALT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_p25519_alt_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p25519_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_25519
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_25519))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P25519_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmul_p25519_alt_windows_mc = define_from_elf
   "bignum_cmul_p25519_alt_windows_mc" "x86/curve25519/bignum_cmul_p25519_alt.obj";;

let bignum_cmul_p25519_alt_windows_tmc = define_trimmed "bignum_cmul_p25519_alt_windows_tmc" bignum_cmul_p25519_alt_windows_mc;;

let BIGNUM_CMUL_P25519_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_p25519_alt_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_p25519_alt_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p25519_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_25519
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_25519))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_cmul_p25519_alt_windows_tmc
    bignum_cmul_p25519_alt_tmc BIGNUM_CMUL_P25519_ALT_CORRECT);;

let BIGNUM_CMUL_P25519_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_p25519_alt_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_p25519_alt_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p25519_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_25519
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_25519))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P25519_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

