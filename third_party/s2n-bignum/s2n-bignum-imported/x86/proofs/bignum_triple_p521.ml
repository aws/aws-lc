(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_521, the field characteristic for the NIST P-521 curve. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_triple_p521.o";;
 ****)

let bignum_triple_p521_mc = define_assert_from_elf "bignum_triple_p521_mc" "x86/p521/bignum_triple_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x48; 0x8b; 0x5e; 0x40;  (* MOV (% rbx) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x89; 0xda;        (* MOV (% rdx) (% rbx) *)
  0x48; 0xc1; 0xe3; 0x36;  (* SHL (% rbx) (Imm8 (word 54)) *)
  0x48; 0x01; 0xdb;        (* ADD (% rbx) (% rbx) *)
  0xf9;                    (* STCF *)
  0x48; 0x8b; 0x1e;        (* MOV (% rbx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% rax) (% rbx) *)
  0x48; 0x8b; 0x5e; 0x08;  (* MOV (% rbx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0xd9;        (* MOV (% rcx) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% rcx) (% rbx) *)
  0x48; 0x8b; 0x5e; 0x10;  (* MOV (% rbx) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x89; 0xd8;        (* MOV (% r8) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc3;
                           (* ADOX (% r8) (% rbx) *)
  0x48; 0x8b; 0x5e; 0x18;  (* MOV (% rbx) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x89; 0xd9;        (* MOV (% r9) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0x48; 0x8b; 0x5e; 0x20;  (* MOV (% rbx) (Memop Quadword (%% (rsi,32))) *)
  0x49; 0x89; 0xda;        (* MOV (% r10) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0x48; 0x8b; 0x5e; 0x28;  (* MOV (% rbx) (Memop Quadword (%% (rsi,40))) *)
  0x49; 0x89; 0xdb;        (* MOV (% r11) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0x48; 0x8b; 0x5e; 0x30;  (* MOV (% rbx) (Memop Quadword (%% (rsi,48))) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x5e; 0x38;  (* MOV (% rbx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x89; 0xde;        (* MOV (% rsi) (% rbx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% rsi) (% rbx) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% rbx) (% rbx) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% rdx) (% rbx) *)
  0x48; 0x81; 0xe3; 0x00; 0x02; 0x00; 0x00;
                           (* AND (% rbx) (Imm32 (word 512)) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0xbb; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 512)) *)
  0x48; 0x21; 0xd3;        (* AND (% rbx) (% rdx) *)
  0x48; 0x81; 0xfb; 0x00; 0x02; 0x00; 0x00;
                           (* CMP (% rbx) (Imm32 (word 512)) *)
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
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r12) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0x89; 0x77; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rsi) *)
  0x48; 0x19; 0xda;        (* SBB (% rdx) (% rbx) *)
  0x48; 0x89; 0x57; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rdx) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_triple_p521_tmc = define_trimmed "bignum_triple_p521_tmc" bignum_triple_p521_mc;;

let BIGNUM_TRIPLE_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_triple_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let overflowbit8lemma = prove
 (`!n:int64.
        val n < 2 EXP 9
        ==> (~(ival(word_shl n 54) + ival(word_shl n 54) =
               ival(word_add (word_shl n 54) (word_shl n 54))) <=>
             bit 8 n)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM UPPER_BITS_ZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `9`) THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  REWRITE_TAC[IVAL_VAL; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; INT_VAL_WORD_ADD_CASES] THEN
  REWRITE_TAC[WORD_RULE `word_add x x = word_shl x 1`; WORD_SHL_COMPOSE] THEN
  REWRITE_TAC[BIT_WORD_SHL; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH `x + x:int < &2 pow 64 <=> ~(&2 pow 63 <= x)`] THEN
  MP_TAC(ISPEC `word_shl (n:int64) 54` MSB_INT_VAL) THEN
  REWRITE_TAC[BIT_WORD_SHL; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC);;

let BIGNUM_TRIPLE_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x11b) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_triple_p521_tmc) /\
                  read RIP s = word(pc + 0x3) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = word (pc + 0x117) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11; RBX; R12] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_TRIPLE_P521_EXEC (1--63)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  (*** Deduce the bound on the top word specifically ***)

  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    EXPAND_TAC "n" THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_THEN(fun th ->
     ASSUME_TAC th THEN ASSUME_TAC(MATCH_MP overflowbit8lemma th))] THEN

  (*** Initial addition s = x + x' + 1 where x' is a 1-bit left rotation ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P521_EXEC
   [8;9;12;13;16;17;20;21;24;25;28;29;32;33;36;37;39;40;42] (1--42) THEN

  SUBGOAL_THEN
    `val(word_and sum_s39 (word 512):int64) = 512 * bitval(bit 8 (n_8:int64))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 9`); VAL_WORD_AND_POW2] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[BIT_VAL] THEN
    UNDISCH_TAC
     `&2 pow 64 * &(bitval carry_s39) + &(val(sum_s39:int64)):real =
      &(val(n_8:int64)) + &(val n_8) + &(bitval carry_s36)` THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN(MP_TAC o
     AP_TERM `\x. ODD(x DIV 2 EXP 9)` o MATCH_MP
      (ARITH_RULE `2 EXP 64 * c + s = n + n + b
                   ==> 2 EXP 9 * 2 EXP 55 * c + s = 2 * n + b`)) THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ODD_ADD; ODD_EXP; ODD_MULT; ARITH] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[bitval] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `s = bignum_of_wordlist
         [sum_s9; sum_s13; sum_s17; sum_s21;
          sum_s25; sum_s29; sum_s33; sum_s37;  sum_s42]` THEN
  SUBGOAL_THEN `0 < s /\ s < 2 * p_521 /\ (s == 3 * n + 1) (mod p_521)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CONGRUENCE; p_521] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[GSYM p_521] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN
     `&s:real = (&3 * &n + &1) - &p_521 * &(bitval(bit 8 (n_8:int64)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "s" THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
        BOUNDER_TAC[];
        REWRITE_TAC[INTEGER_CLOSED]] THEN
      CONJ_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_CLAUSES] THEN
          EXPAND_TAC "n" THEN REWRITE_TAC[bignum_of_wordlist] THEN
          SUBST1_TAC(ISPEC `n_8:int64` val_def) THEN
          REWRITE_TAC[DIMINDEX_64; ARITH_RULE `n < 64 <=> 0 <= n /\ n <= 63`;
                      GSYM numseg; p_521] THEN
          CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x < p ==> x - y:real < p`) THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
          UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC];
        MAP_EVERY EXPAND_TAC ["s"; "n"] THEN
        REWRITE_TAC[bignum_of_wordlist; p_521; GSYM REAL_OF_NUM_CLAUSES] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];

      REWRITE_TAC[CONJ_ASSOC] THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN REAL_INTEGER_TAC] THEN
      REWRITE_TAC[REAL_LT_SUB_RADD; REAL_SUB_LT; REAL_OF_NUM_CLAUSES] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "n" THEN
        REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
        REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
        REWRITE_TAC[DIMINDEX_64; ARITH_RULE `n < 64 <=> 0 <= n /\ n <= 63`;
                    val_def; GSYM numseg; p_521] THEN
        CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN ARITH_TAC;
        REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[ARITH_RULE `n < p ==> 3 * n + 1 < 2 * p + p * 1`] THEN
        MATCH_MP_TAC(ARITH_RULE
         `n < 2 EXP 520 /\ 2 EXP 521 <= p + 1
          ==> 3 * n + 1 < 2 * p + p * 0`) THEN
        REWRITE_TAC[p_521] THEN CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
        EXPAND_TAC "n" THEN
        REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
        MATCH_MP_TAC(ARITH_RULE
         `a < 2 EXP (64 * 8) /\ b < 2 EXP 8
          ==> a + 2 EXP 512 * b < 2 EXP 520`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
          REWRITE_TAC[LENGTH] THEN ARITH_TAC;
          REWRITE_TAC[BIGNUM_OF_WORDLIST_SING]] THEN
        REWRITE_TAC[GSYM UPPER_BITS_ZERO] THEN
        REWRITE_TAC[ARITH_RULE `8 <= i <=> i = 8 \/ 9 <= i`] THEN
        ASM_SIMP_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
        ASM_REWRITE_TAC[UPPER_BITS_ZERO]]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The net comparison s >= 2^521 ***)

  X86_STEPS_TAC BIGNUM_TRIPLE_P521_EXEC (43--44) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SYM(NUM_REDUCE_CONV `2 EXP 9`); GSYM WORD_OF_BITS_SING_AS_WORD;
    WORD_OF_BITS_SING_AND_WORD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [WORD_OF_BITS_SING_AS_WORD; NUM_REDUCE_CONV `2 EXP 9`]) THEN

  SUBGOAL_THEN `bit 9 (sum_s42:int64) <=> p_521 < s` SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS `2 EXP 521 <= s` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    SUBGOAL_THEN `s < 2 EXP 522` MP_TAC THENL
     [UNDISCH_TAC `s < 2 * p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE
       `(s < 2 EXP 522 <=> s DIV 2 EXP 512 < 2 EXP 10) /\
        (2 EXP 521 <= s <=> 2 EXP 9 <= s DIV 2 EXP 512)`]] THEN
    EXPAND_TAC "s" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[GSYM UPPER_BITS_ZERO; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `~(i < 9) <=> i = 9 \/ ~(i < 10)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  X86_STEPS_TAC BIGNUM_TRIPLE_P521_EXEC [45] THEN
  SUBGOAL_THEN
   `val(if p_521 < s then word 512 else word 0:int64) < 512 <=>
    ~(p_521 < s)`
  SUBST_ALL_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P521_EXEC
   [46;48;50;52;54;56;58;60;62] (46--63) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 9`;
    `if s <= p_521 then &s - &1:real else &s - &2 pow 521`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[GSYM NOT_LE] THEN ABBREV_TAC `bb <=> s <= p_521` THEN
    REWRITE_TAC[COND_SWAP; WORD_AND_MASK] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    TRANS_TAC EQ_TRANS `&((s - 1) MOD p_521):real` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ; GSYM CONG] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `(s == 3 * n + 1 ) (mod p) /\ s - 1 + 1 = s
        ==> (3 * n == s - 1) (mod p)`) THEN
      ASM_SIMP_TAC[SUB_ADD; LE_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `s < 2 * p ==> s - 1 < 2 * p`] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < s ==> (s - 1 < p <=> s <= p)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s - 1 - p_521 = s - 2 EXP 521` SUBST1_TAC THENL
     [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    UNDISCH_TAC `~(s <= p_521)` THEN REWRITE_TAC[p_521] THEN ARITH_TAC]);;

let BIGNUM_TRIPLE_P521_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_triple_p521_tmc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_triple_p521_tmc BIGNUM_TRIPLE_P521_CORRECT
    `[RBX; R12]` 16);;

let BIGNUM_TRIPLE_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_triple_p521_mc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_triple_p521_windows_mc = define_from_elf
   "bignum_triple_p521_windows_mc" "x86/p521/bignum_triple_p521.obj";;

let bignum_triple_p521_windows_tmc = define_trimmed "bignum_triple_p521_windows_tmc" bignum_triple_p521_windows_mc;;

let BIGNUM_TRIPLE_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_triple_p521_windows_tmc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_windows_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_triple_p521_windows_tmc bignum_triple_p521_tmc
    BIGNUM_TRIPLE_P521_CORRECT `[RBX; R12]` 16);;

let BIGNUM_TRIPLE_P521_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_triple_p521_windows_mc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_windows_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

