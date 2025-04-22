(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Comparison >= test on bignums.                                            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_ge.o";;
 ****)

let bignum_ge_mc =
  define_assert_from_elf "bignum_ge_mc" "x86/generic/bignum_ge.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x48; 0x29; 0xd7;        (* SUB (% rdi) (% rdx) *)
  0x72; 0x31;              (* JB (Imm8 (word 49)) *)
  0x48; 0xff; 0xc7;        (* INC (% rdi) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x1d;              (* JE (Imm8 (word 29)) *)
  0x4a; 0x8b; 0x04; 0xc6;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x4a; 0x1b; 0x04; 0xc1;  (* SBB (% rax) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0xeb; 0x0b;              (* JMP (Imm8 (word 11)) *)
  0x4a; 0x8b; 0x04; 0xc6;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0xc3;                    (* RET *)
  0x48; 0x01; 0xd7;        (* ADD (% rdi) (% rdx) *)
  0x48; 0x29; 0xfa;        (* SUB (% rdx) (% rdi) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x10;              (* JE (Imm8 (word 16)) *)
  0x4a; 0x8b; 0x04; 0xc6;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x4a; 0x1b; 0x04; 0xc1;  (* SBB (% rax) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x4a; 0x1b; 0x04; 0xc1;  (* SBB (% rax) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xef;              (* JNE (Imm8 (word 239)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0xc3                     (* RET *)
];;

let bignum_ge_tmc = define_trimmed "bignum_ge_tmc" bignum_ge_mc;;

let BIGNUM_GE_EXEC = X86_MK_EXEC_RULE bignum_ge_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common tactic for slightly different standard and Windows variants.       *)
(* ------------------------------------------------------------------------- *)

let tac execth offset =
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`b:int64`; `y:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[GE] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_RANGE_TAC "m" "x" THEN BIGNUM_RANGE_TAC "n" "y" THEN

  (*** Case split following the initial branch, m >= n case then m < n ***)

  ASM_CASES_TAC `n:num <= m` THENL
   [SUBGOAL_THEN `~(m:num < n)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC (offset 0x2d)
     `\s. read RDI s = word (m - n + 1) /\
          read RSI s = a /\
          read RCX s = b /\
          read R8 s = word n /\
          bignum_from_memory (a,m) s = x /\
          bignum_from_memory (b,n) s = y /\
          (read CF s <=> lowdigits x n < lowdigits y n)` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--6) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; LT_REFL] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `n:num` (offset 0x10) (offset 0x1e)
       `\i s. (read RDI s = word (m - n + 1) /\
               read RSI s = a /\
               read RCX s = b /\
               read RDX s = word(n - i) /\
               read R8 s = word i /\
               bignum_from_memory (a,m) s = x /\
               bignum_from_memory (b,n) s = y /\
               (read CF s <=> lowdigits x i < lowdigits y i)) /\
              (read ZF s <=> i = n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--6) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; LT_REFL] THEN
        ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB] THEN
        CONV_TAC WORD_RULE;
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC execth (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add a (word(8 * i)))) s0 =
        word(bigdigit x i) /\
        read(memory :> bytes64(word_add b (word(8 * i)))) s0 =
        word(bigdigit y i)`
      ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      X86_STEPS_TAC execth (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB;
                   ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_IWORD; LOWDIGITS_CLAUSES] THEN
        SIMP_TAC[LEXICOGRAPHIC_LT; LOWDIGITS_BOUND] THEN
        SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
        REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        REWRITE_TAC[WORD_RULE
         `word_sub (iword(n - i)) (iword j) =
          word_sub (iword n) (iword(i + j))`] THEN
        REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
        REWRITE_TAC[GSYM WORD_IWORD; INT_OF_NUM_ADD] THEN
        GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
        MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC];
      ASM_CASES_TAC `m:num = n` THENL
       [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
        REWRITE_TAC[SUB_REFL; ADD_CLAUSES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
        REWRITE_TAC[GSYM NOT_LE] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      SUBGOAL_THEN `n:num < m /\ 0 < m - n /\ m - n < 2 EXP 64`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `m - n:num` (offset 0x22) (offset 0x30)
       `\i s. (read RDI s = word (m - n - i) /\
               read RSI s = a /\
               read R8 s = word(n + i) /\
               bignum_from_memory (a,m) s = x /\
               (read CF s <=> lowdigits x (n + i) < lowdigits y (n + i))) /\
              (read ZF s <=> i = m - n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SIMPLE_ARITH_TAC;
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
        CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
        REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_RULE
         `word(n + 1):int64 = word 1 <=> word n:int64 = word 0`] THEN
        ASM_SIMP_TAC[WORD_EQ_0; DIMINDEX_64; SUB_EQ_0; NOT_LE];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        X86_SIM_TAC execth (1--3) THEN
        SUBGOAL_THEN `y < 2 EXP (64 * m)` ASSUME_TAC THENL
         [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
          ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
          ASM_SIMP_TAC[LOWDIGITS_SELF; ARITH_RULE
           `m <= n ==> m + n - m:num = n`]] THEN
        REWRITE_TAC[GSYM NOT_LE] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < m /\ n + i < m` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `n + i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add a (word(8 * (n + i))))) s0 =
        word(bigdigit x (n + i))`
      ASSUME_TAC THENL
       [EXPAND_TAC "x" THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      X86_STEPS_TAC execth (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[WORD_RULE
         `word_sub x (word 1) = word y <=> x = word(y + 1)`] THEN
        AP_TERM_TAC THEN UNDISCH_TAC `n + i:num < m` THEN ARITH_TAC;
        CONV_TAC WORD_RULE;
        SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
        REWRITE_TAC[ADD_ASSOC; LOWDIGITS_CLAUSES] THEN
        SIMP_TAC[LEXICOGRAPHIC_LT; LOWDIGITS_BOUND] THEN
        SUBGOAL_THEN `bigdigit y (n + i) = 0` SUBST1_TAC THENL
         [MATCH_MP_TAC BIGDIGIT_ZERO THEN
          TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
          ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC;
          REWRITE_TAC[bitval] THEN ARITH_TAC];
        REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `n + i < m ==> (i + 1 = m - n <=> m - n - i = 1)`] THEN
        MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `m < 2 EXP 64` THEN ARITH_TAC]];

    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC (offset 0x54)
     `\s. read RDX s = word (n - m) /\
          read RSI s = a /\
          read RCX s = b /\
          read R8 s = word m /\
          bignum_from_memory (a,m) s = x /\
          bignum_from_memory (b,n) s = y /\
          (read CF s <=> lowdigits x m < lowdigits y m)` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m = 0` THENL
       [UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--7) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; LT_REFL; WORD_RULE
         `word_add (word_sub (word 0) x) x = word 0`] THEN
        CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `m:num` (offset 0x44) (offset 0x52)
       `\i s. (read RDX s = word (n - m) /\
               read RSI s = a /\
               read RCX s = b /\
               read RDI s = word(m - i) /\
               read R8 s = word i /\
               bignum_from_memory (a,m) s = x /\
               bignum_from_memory (b,n) s = y /\
               (read CF s <=> lowdigits x i < lowdigits y i)) /\
              (read ZF s <=> i = m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--7) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[LOWDIGITS_0; LT_REFL] THEN
        ASM_REWRITE_TAC[WORD_RULE `word_add (word_sub x y) y = x`] THEN
        ASM_REWRITE_TAC[WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add a (word(8 * i)))) s0 =
        word(bigdigit x i) /\
        read(memory :> bytes64(word_add b (word(8 * i)))) s0 =
        word(bigdigit y i)`
      ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      X86_STEPS_TAC execth (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB;
                   ARITH_RULE `i < m ==> i <= m /\ i + 1 <= m`] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_IWORD; LOWDIGITS_CLAUSES] THEN
        SIMP_TAC[LEXICOGRAPHIC_LT; LOWDIGITS_BOUND] THEN
        SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
        REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        REWRITE_TAC[WORD_RULE
         `word_sub (iword(m - i)) (iword j) =
          word_sub (iword m) (iword(i + j))`] THEN
        REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
        REWRITE_TAC[GSYM WORD_IWORD; INT_OF_NUM_ADD] THEN
        GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
        MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC];
      SUBGOAL_THEN `~(n = m) /\ m:num < n /\ 0 < n - m /\ n - m < 2 EXP 64`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `n - m:num` (offset 0x54) (offset 0x63)
       `\i s. (read RDX s = word (n - m - i) /\
               read RCX s = b /\
               read R8 s = word(m + i) /\
               bignum_from_memory (b,n) s = y /\
               (read CF s <=> lowdigits x (m + i) < lowdigits y (m + i))) /\
              (read ZF s <=> i = n - m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SIMPLE_ARITH_TAC;
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        X86_SIM_TAC execth (1--3) THEN
        SUBGOAL_THEN `x < 2 EXP (64 * n)` ASSUME_TAC THENL
         [TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
          ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
          ASM_SIMP_TAC[LOWDIGITS_SELF; ARITH_RULE
           `m <= n ==> m + n - m:num = n`]] THEN
        REWRITE_TAC[GSYM NOT_LE] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < n /\ m + i < n` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `m + i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add b (word(8 * (m + i))))) s0 =
        word(bigdigit y (m + i))`
      ASSUME_TAC THENL
       [EXPAND_TAC "y" THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      X86_STEPS_TAC execth (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[WORD_RULE
         `word_sub x (word 1) = word y <=> x = word(y + 1)`] THEN
        AP_TERM_TAC THEN UNDISCH_TAC `m + i:num < n` THEN ARITH_TAC;
        CONV_TAC WORD_RULE;
        SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
        REWRITE_TAC[ADD_ASSOC; LOWDIGITS_CLAUSES] THEN
        SIMP_TAC[LEXICOGRAPHIC_LT; LOWDIGITS_BOUND] THEN
        SUBGOAL_THEN `bigdigit x (m + i) = 0` SUBST1_TAC THENL
         [MATCH_MP_TAC BIGDIGIT_ZERO THEN
          TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
          ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC;
          REWRITE_TAC[bitval] THEN ARITH_TAC];
        REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `m + i < n ==> (i + 1 = n - m <=> n - m - i = 1)`] THEN
        MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `n < 2 EXP 64` THEN ARITH_TAC]]];;

(* ------------------------------------------------------------------------- *)
(* Correctness of standard ABI version.                                      *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_GE_CORRECT = prove
 (`!m a x n b y pc.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_ge_tmc /\
               read RIP s = word pc /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. (read RIP s' = word(pc + 0x38) \/
                 read RIP s' = word(pc + 0x6b)) /\
                C_RETURN s' = if x >= y then word 1 else word 0)
          (MAYCHANGE [RIP; RDI; RDX; RAX; R8] ,,
           MAYCHANGE SOME_FLAGS)`,
  tac BIGNUM_GE_EXEC (curry mk_comb `(+) (pc:num)` o mk_small_numeral));;

let BIGNUM_GE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_ge_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                C_RETURN s' = if x >= y then word 1 else word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_GE_EXEC BIGNUM_GE_CORRECT);;

let BIGNUM_GE_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_ge_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                C_RETURN s' = if x >= y then word 1 else word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_GE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_ge_windows_mc = define_from_elf
   "bignum_ge_windows_mc" "x86/generic/bignum_ge.obj";;

let bignum_ge_windows_tmc = define_trimmed "bignum_ge_windows_tmc" bignum_ge_windows_mc;;

let BIGNUM_GE_WINDOWS_CORRECT = prove
 (`!m a x n b y pc.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_ge_windows_tmc /\
               read RIP s = word(pc + 0xe) /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. (read RIP s' = word(pc + 0x46) \/
                 read RIP s' = word(pc + 0x7b)) /\
                C_RETURN s' = if x >= y then word 1 else word 0)
          (MAYCHANGE [RIP; RDI; RDX; RAX; R8] ,,
           MAYCHANGE SOME_FLAGS)`,
  tac (X86_MK_EXEC_RULE bignum_ge_windows_tmc)
      (curry mk_comb `(+) (pc:num)` o mk_small_numeral o
       (fun n -> if n < 0x38 then n + 14 else n + 16)));;

let BIGNUM_GE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_ge_windows_tmc); (a,8 * val m); (b,8 * val n)]
        ==> ensures x86
              (\s. bytes_loaded s (word pc) bignum_ge_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [m;a;n;b] s /\
                   bignum_from_memory(a,val m) s = x /\
                   bignum_from_memory(b,val n) s = y)
              (\s'. read RIP s' = returnaddress /\
                    read RSP s' = word_add stackpointer (word 8) /\
                    WINDOWS_C_RETURN s' = if x >= y then word 1 else word 0)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  GEN_X86_ADD_RETURN_STACK_TAC (X86_MK_EXEC_RULE bignum_ge_windows_tmc)
    BIGNUM_GE_WINDOWS_CORRECT `[RDI; RSI]` 16 (6,3));;

let BIGNUM_GE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_ge_windows_mc); (a,8 * val m); (b,8 * val n)]
        ==> ensures x86
              (\s. bytes_loaded s (word pc) bignum_ge_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [m;a;n;b] s /\
                   bignum_from_memory(a,val m) s = x /\
                   bignum_from_memory(b,val n) s = y)
              (\s'. read RIP s' = returnaddress /\
                    read RSP s' = word_add stackpointer (word 8) /\
                    WINDOWS_C_RETURN s' = if x >= y then word 1 else word 0)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_GE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

