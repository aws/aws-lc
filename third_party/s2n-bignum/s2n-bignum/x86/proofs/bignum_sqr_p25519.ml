(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squaring modulo p_25519, the field characteristic for curve25519.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/curve25519/bignum_sqr_p25519.o";;
 ****)

let bignum_sqr_p25519_mc = define_assert_from_elf "bignum_sqr_p25519_mc" "x86/curve25519/bignum_sqr_p25519.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x76; 0x18;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADCX (% r13) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0x49; 0x11; 0xde;        (* ADC (% r14) (% rbx) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% r10) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADOX (% r12) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0xc4; 0xc2; 0xeb; 0xf6; 0xcf;
                           (* MULX4 (% rcx,% rdx) (% rdx,% r15) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADCX (% r15) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfb;
                           (* ADOX (% r15) (% rbx) *)
  0x4c; 0x01; 0xda;        (* ADD (% rdx) (% r11) *)
  0x48; 0x11; 0xd9;        (* ADC (% rcx) (% rbx) *)
  0x48; 0x0f; 0xa4; 0xd1; 0x01;
                           (* SHLD (% rcx) (% rdx) (Imm8 (word 1)) *)
  0x48; 0x8d; 0x59; 0x01;  (* LEA (% rbx) (%% (rcx,1)) *)
  0x48; 0x6b; 0xdb; 0x13;  (* IMUL3 (% rbx) (% rbx,Imm8 (word 19)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcc;
                           (* MULX4 (% rcx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcd;
                           (* MULX4 (% rcx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xce;
                           (* MULX4 (% rcx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcf;
                           (* MULX4 (% rcx,% rax) (% rdx,% r15) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0xc1; 0xe3; 0x3f;  (* SHL (% rbx) (Imm8 (word 63)) *)
  0x49; 0x39; 0xdb;        (* CMP (% r11) (% rbx) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x48; 0x0f; 0x49; 0xc1;  (* CMOVNS (% rax) (% rcx) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_sqr_p25519_tmc = define_trimmed "bignum_sqr_p25519_tmc" bignum_sqr_p25519_mc;;

let BIGNUM_SQR_P25519_EXEC = X86_MK_CORE_EXEC_RULE bignum_sqr_p25519_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let p25519approxredlemma = prove
 (`!m n. n < 40 * 2 EXP 256 /\
         n <= 2 EXP 192 * m + 2 EXP 255 /\
         2 EXP 192 * m <= n
         ==> let q = m DIV 2 EXP 63 + 1 in
             q <= 80 /\
             q < 2 EXP 64 /\
             q * p_25519 <= n + p_25519 /\
             n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let BIGNUM_SQR_P25519_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x183) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_sqr_p25519_tmc) /\
                  read RIP s = word(pc + 0x9) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x179) /\
                  bignum_from_memory (z,4) s = (n EXP 2) MOD p_25519)
          (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                      R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** The initial squaring block with quotient estimate inside ***)

  X86_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (1--45) (1--45) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s2; sum_s23; sum_s27; sum_s29]`;
    `h = bignum_of_wordlist[sum_s33; sum_s35; sum_s41; sum_s43]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma --- fiddly proof ***)

  MP_TAC(SPECL [`2 EXP 64 * val(sum_s45:int64) + val(sum_s44:int64)`;
                `38 * h + l`] p25519approxredlemma) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    TRANS_TAC LE_TRANS
     `2 EXP 192 *
      (38 * (val(mulhi_s37:int64) + bitval carry_s41 + bitval carry_s40) +
       val(sum_s29:int64))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
      `x <= 2 EXP 192 * (38 * h + s) ==> x <= 2 EXP 192 * (38 * (h + c) + s)`);
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES;
                REAL_OF_NUM_DIV; p_25519] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN LET_TAC THEN STRIP_TAC] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC BIGNUM_SQR_P25519_EXEC (46--48) THEN
  ABBREV_TAC `hw:int64 = word_add
                   (word_subword ((word_join:int64->int64->int128)
                                   sum_s45 sum_s44) (63,64))
                   (word 1)` THEN
  SUBGOAL_THEN `q = val(hw:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `q < 2 EXP 64` THEN MAP_EVERY EXPAND_TAC ["hw"; "q"] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; VAL_WORD_ADD; VAL_WORD_1;
             ARITH_LE; ARITH_LT] THEN
    CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[MOD_LT];
    ALL_TAC] THEN

  (*** Actual accumulation of 38 * h + l + 19 * q ***)

  ABBREV_TAC `q19:int64 = word_mul hw (word 19)` THEN
  X86_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (50--65) (49--65) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [READ_RVALUE]) THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN

  SUBGOAL_THEN `&(val(q19:int64)):real = &19 * &(val(hw:int64))`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "q19" THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) <= 80` THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `val(word_shl (q19:int64) 63) = 2 EXP 63 * val(hw:int64) MOD 2`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MULT2; ARITH_RULE `2 EXP 64 = 2 EXP 63 * 2`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[VAL_MOD_2; BIT_LSB] THEN
    EXPAND_TAC "q19" THEN AP_TERM_TAC THEN
    REWRITE_TAC[word_mul; modular; ODD_VAL_WORD] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[ODD_MULT; ARITH];
    RULE_ASSUM_TAC(REWRITE_RULE
     [GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_OF_NUM_MOD])] THEN

  (*** Characterize both mangled and unmangled versions ***)

  SUBGOAL_THEN
   `(&(bignum_of_wordlist[sum_s53; sum_s56; sum_s59; sum_s62]):int ==
     &(38 * h + l) - &p_25519 * &(val(hw:int64))) (mod (&2 pow 255)) /\
    (&(bignum_of_wordlist[sum_s53; sum_s56; sum_s59; sum_s65]):int ==
     &(38 * h + l) - &p_25519 * &(val(hw:int64))) (mod (&2 pow 256))`
  MP_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_INT_CONGRUENCE] THEN
    REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_sub_th; int_pow_th; int_of_num_th; int_mul_th] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC] THEN

  (*** The final correction ***)

  X86_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (68--71) (66--76) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s76" THEN

  SUBGOAL_THEN
   `ival(sum_s65:int64) < &0 <=> 38 * h + l < val(hw:int64) * p_25519`
  SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS
     `2 EXP 255 <= bignum_of_wordlist[sum_s53; sum_s56; sum_s59; sum_s65]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MSB_IVAL; MSB_VAL; ARITH_RULE
        `2 EXP 255 <= x <=> 2 EXP 63 <= x DIV 2 EXP 192`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
      REWRITE_TAC[TAUT `(p <=> q) <=> (~q ==> ~p) /\ (q ==> p)`]] THEN
    REWRITE_TAC[INT_NOT_LE; NOT_LE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (can
     (term_match [] `(x:int == y) (mod (&2 pow 256))`) o concl))
    THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
       `(x == y) (mod n) ==> (x:int == y + n) (mod n)`))] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_IMP_EQ)) THEN
    REWRITE_TAC[NOT_IMP] THEN
    (ANTS_TAC THENL
      [MATCH_MP_TAC(INT_ARITH
        `(&0 <= x /\ x < e) /\ (&0 <= y /\ y < e) ==> abs(x - y:int) < e`) THEN
       CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC];
       ALL_TAC] THEN
     POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
     REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN INT_ARITH_TAC);
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT])] THEN

  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 255` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC `if val(hw:int64) * p_25519 <= 38 * h + l
              then &(38 * h + l) - &(val(hw:int64)) * &p_25519:int
              else &(38 * h + l) - (&(val(hw:int64)) - &1) * &p_25519` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INT_EQ_IMP_CONG THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[GSYM int_of_num_th; GSYM INT_OF_NUM_REM] THEN
    REWRITE_TAC[GSYM int_sub_th; GSYM int_mul_th] THEN
    ONCE_REWRITE_TAC[GSYM COND_RAND] THEN REWRITE_TAC[GSYM int_eq] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`val(hw:int64) * p_25519 <= (38 * h + l) + p_25519`;
        `38 * h + l < val(hw:int64) * p_25519 + p_25519`] THEN
      REWRITE_TAC[p_25519; GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      INTEGER_TAC]] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC
   `if val(hw:int64) * p_25519 <= 38 * h + l
    then &(bignum_of_wordlist [sum_s53; sum_s56; sum_s59; sum_s62]):int
    else &(bignum_of_wordlist [sum_s53; sum_s56; sum_s59; sum_s62]) +
         &p_25519` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (can
     (term_match [] `(x:int == y) (mod (&2 pow 255))`) o concl)) THEN
    SPEC_TAC(`(&2:int) pow 255`,`p:int`) THEN INTEGER_TAC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_pow_th; int_of_num_th] THEN
  ASM_SIMP_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  ABBREV_TAC `bb <=> val(hw:int64) * p_25519 <= 38 * h + l` THEN
  REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_MOD;
              GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_SQR_P25519_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_sqr_p25519_tmc) (z,8 * 4) /\
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_sqr_p25519_tmc); (x,8 * 4)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqr_p25519_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,4) s = n EXP 2 MOD p_25519)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                     memory :> bytes(word_sub stackpointer (word 40),40)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_sqr_p25519_tmc BIGNUM_SQR_P25519_CORRECT
   `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_SQR_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_sqr_p25519_mc) (z,8 * 4) /\
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_sqr_p25519_mc); (x,8 * 4)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqr_p25519_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,4) s = n EXP 2 MOD p_25519)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                     memory :> bytes(word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SQR_P25519_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_sqr_p25519_windows_mc = define_from_elf
   "bignum_sqr_p25519_windows_mc" "x86/curve25519/bignum_sqr_p25519.obj";;

let bignum_sqr_p25519_windows_tmc = define_trimmed "bignum_sqr_p25519_windows_tmc" bignum_sqr_p25519_windows_mc;;

let BIGNUM_SQR_P25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_sqr_p25519_windows_tmc) (z,8 * 4) /\
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_sqr_p25519_windows_tmc); (x,8 * 4)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqr_p25519_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,4) s = n EXP 2 MOD p_25519)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                     memory :> bytes(word_sub stackpointer (word 56),56)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_sqr_p25519_windows_tmc bignum_sqr_p25519_tmc BIGNUM_SQR_P25519_CORRECT
   `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_SQR_P25519_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_sqr_p25519_windows_mc) (z,8 * 4) /\
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_sqr_p25519_windows_mc); (x,8 * 4)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sqr_p25519_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,4) s = n EXP 2 MOD p_25519)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                     memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SQR_P25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

