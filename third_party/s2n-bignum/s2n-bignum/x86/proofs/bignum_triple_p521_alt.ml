(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_521, the field characteristic for the NIST P-521 curve. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_triple_p521_alt.o";;
 ****)

let bignum_triple_p521_alt_mc = define_assert_from_elf "bignum_triple_p521_alt_mc" "x86/p521/bignum_triple_p521_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x48; 0xc7; 0xc1; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Imm32 (word 3)) *)
  0x4c; 0x8b; 0x46; 0x40;  (* MOV (% r8) (Memop Quadword (%% (rsi,64))) *)
  0x49; 0xc1; 0xe8; 0x08;  (* SHR (% r8) (Imm8 (word 8)) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x8b; 0x4e; 0x38;  (* MOV (% rcx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x8b; 0x76; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rsi,64))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0xc7; 0xc0; 0xff; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 255)) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x48; 0x8d; 0x34; 0x46;  (* LEA (% rsi) (%%% (rsi,1,rax)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x01; 0xca;        (* ADD (% rdx) (% rcx) *)
  0x48; 0x11; 0xc6;        (* ADC (% rsi) (% rax) *)
  0x48; 0x01; 0xc9;        (* ADD (% rcx) (% rcx) *)
  0x48; 0x11; 0xc6;        (* ADC (% rsi) (% rax) *)
  0x48; 0x01; 0xd1;        (* ADD (% rcx) (% rdx) *)
  0x48; 0x11; 0xc6;        (* ADC (% rsi) (% rax) *)
  0x48; 0x81; 0xfe; 0x00; 0x02; 0x00; 0x00;
                           (* CMP (% rsi) (Imm32 (word 512)) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x19; 0xc3;        (* SBB (% rbx) (% rax) *)
  0x48; 0x89; 0x5f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rbx) *)
  0x48; 0x19; 0xc5;        (* SBB (% rbp) (% rax) *)
  0x48; 0x89; 0x6f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rbp) *)
  0x49; 0x19; 0xc4;        (* SBB (% r12) (% rax) *)
  0x4c; 0x89; 0x67; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r12) *)
  0x48; 0x19; 0xc1;        (* SBB (% rcx) (% rax) *)
  0x48; 0x89; 0x4f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rcx) *)
  0x48; 0x19; 0xc6;        (* SBB (% rsi) (% rax) *)
  0x48; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rsi) (Imm32 (word 511)) *)
  0x48; 0x89; 0x77; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rsi) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_triple_p521_alt_tmc = define_trimmed "bignum_triple_p521_alt_tmc" bignum_triple_p521_alt_mc;;

let BIGNUM_TRIPLE_P521_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_triple_p521_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_TRIPLE_P521_ALT_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0xfe) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_triple_p521_alt_tmc) /\
                  read RIP s = word(pc + 0x4) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = word (pc + 0xf9) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11;
                      RBX; RBP; R12] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_TRIPLE_P521_ALT_EXEC (1--70)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  (*** Deduce the bound on the top word specifically ***)

  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    EXPAND_TAC "n" THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN

  (*** Initial addition s = x + x' + 1 where x' is a 1-bit left rotation ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P521_ALT_EXEC
   [4;6;8;9;11;13;14;16;18;19;21;23;24;26;28;29;31;33;34;36;39;40;
    45;46;47;48;49;50]
   (1--50) THEN
  ABBREV_TAC
   `s = bignum_of_wordlist
         [sum_s8; sum_s13; sum_s18; sum_s23; sum_s28; sum_s33; sum_s39;
          sum_s49; sum_s50]` THEN
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
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
        SUBGOAL_THEN
          `val(word(2 * val (word_and (word 255) (n_8:int64))):int64) =
           2 * val n_8 MOD 2 EXP 8`
        SUBST1_TAC THENL
         [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
          REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
          REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
          CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN
          BOUNDER_TAC[];
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES]] THEN
        REWRITE_TAC[REAL_OF_NUM_MOD; VAL_WORD_USHR] THEN
        SUBGOAL_THEN `val(n_8:int64) DIV 2 EXP 8 = bitval(bit 8 n_8)`
        SUBST1_TAC THENL
         [ALL_TAC; CONV_TAC NUM_REDUCE_CONV THEN REAL_INTEGER_TAC] THEN
        REWRITE_TAC[BIT_VAL; BITVAL_ODD] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `&(val(n_8:int64)):real < &2 pow 9` THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC];
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

  X86_STEPS_TAC BIGNUM_TRIPLE_P521_ALT_EXEC [51] THEN
  SUBGOAL_THEN `val(sum_s50:int64) < 512 <=> s <= p_521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "s" THEN
    SUBGOAL_THEN `p_521 = 2 EXP 521 - 1` SUBST1_TAC THENL
     [REWRITE_TAC[p_521] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `x <= 2 EXP 521 - 1 <=> x DIV 2 EXP 512 < 512`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN REFL_TAC;
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P521_ALT_EXEC
   [52;54;56;58;60;62;64;66;68] (52--70) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if s <= p_521 then &s - &1:real else &s - &2 pow 521`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ABBREV_TAC `bb <=> s <= p_521` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_INTEGER_TAC;
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

let BIGNUM_TRIPLE_P521_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),32) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,LENGTH bignum_triple_p521_alt_tmc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_alt_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_alt_tmc /\
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
                      memory :> bytes(word_sub stackpointer (word 24),24)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    bignum_triple_p521_alt_tmc BIGNUM_TRIPLE_P521_ALT_CORRECT
    `[RBX; RBP; R12]` 24);;

let BIGNUM_TRIPLE_P521_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),32) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,LENGTH bignum_triple_p521_alt_mc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_alt_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_alt_mc /\
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
                      memory :> bytes(word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P521_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_triple_p521_alt_windows_mc = define_from_elf
   "bignum_triple_p521_alt_windows_mc" "x86/p521/bignum_triple_p521_alt.obj";;

let bignum_triple_p521_alt_windows_tmc = define_trimmed "bignum_triple_p521_alt_windows_tmc" bignum_triple_p521_alt_windows_mc;;

let BIGNUM_TRIPLE_P521_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 40),48) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_triple_p521_alt_windows_tmc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_alt_windows_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_alt_windows_tmc /\
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
                      memory :> bytes(word_sub stackpointer (word 40),40)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_triple_p521_alt_windows_tmc bignum_triple_p521_alt_tmc
    BIGNUM_TRIPLE_P521_ALT_CORRECT `[RBX; RBP; R12]` 24);;

let BIGNUM_TRIPLE_P521_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 40),48) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_triple_p521_alt_windows_mc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p521_alt_windows_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p521_alt_windows_mc /\
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
                      memory :> bytes(word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P521_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

