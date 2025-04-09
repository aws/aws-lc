(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Subtraction of bignums.                                                   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_sub.o";;
 ****)

let bignum_sub_mc =
  define_assert_from_elf "bignum_sub_mc" "x86/generic/bignum_sub.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x48; 0x0f; 0x42; 0xd7;  (* CMOVB (% rdx) (% rdi) *)
  0x4c; 0x39; 0xc7;        (* CMP (% rdi) (% r8) *)
  0x4c; 0x0f; 0x42; 0xc7;  (* CMOVB (% r8) (% rdi) *)
  0x4c; 0x39; 0xc2;        (* CMP (% rdx) (% r8) *)
  0x72; 0x50;              (* JB (Imm8 (word 80)) *)
  0x48; 0x29; 0xd7;        (* SUB (% rdi) (% rdx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x48; 0xff; 0xc2;        (* INC (% rdx) *)
  0x4d; 0x85; 0xc0;        (* TEST (% r8) (% r8) *)
  0x74; 0x25;              (* JE (Imm8 (word 37)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x4b; 0x1b; 0x04; 0xd1;  (* SBB (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xeb; 0x0f;              (* JMP (Imm8 (word 15)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x0c;              (* JE (Imm8 (word 12)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf4;              (* JNE (Imm8 (word 244)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0xc3;                    (* RET *)
  0x4c; 0x29; 0xc7;        (* SUB (% rdi) (% r8) *)
  0x49; 0x29; 0xd0;        (* SUB (% r8) (% rdx) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x14;              (* JE (Imm8 (word 20)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x4b; 0x1b; 0x04; 0xd1;  (* SBB (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x4b; 0x1b; 0x04; 0xd1;  (* SBB (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xeb;              (* JNE (Imm8 (word 235)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x75; 0xb4;              (* JNE (Imm8 (word 180)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0xc3                     (* RET *)
];;

let bignum_sub_tmc = define_trimmed "bignum_sub_tmc" bignum_sub_mc;;

let BIGNUM_SUB_EXEC = X86_MK_EXEC_RULE bignum_sub_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common tactic for slightly different standard and Windows variants.       *)
(* ------------------------------------------------------------------------- *)

let tac execth cleanpost offset =
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`y:int64`; `b:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Remove redundancy in the conclusion ***)

  ENSURES_POSTCONDITION_TAC cleanpost THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[lowdigits; MOD_LT] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_REM;
                GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `e * c + a:int = z + b ==> (z == a - b) (mod e)`)) THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_REM_LT THEN
    REWRITE_TAC[INT_OF_NUM_POW; INT_POS; INT_OF_NUM_LT] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN

  (*** Reshuffle to handle clamping and just assume m <= p and n <= p ***)

  ENSURES_SEQUENCE_TAC (offset 0x11)
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read RDX s = word(MIN m p) /\
        read RCX s = x /\
        read R8 s = word(MIN n p) /\
        read R9 s = y /\
        read R10 s = word 0 /\
        bignum_from_memory(x,MIN m p) s = lowdigits a p /\
        bignum_from_memory(y,MIN n p) s = lowdigits b p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [GSYM COND_RAND] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
  SUBGOAL_THEN
   `lowdigits (a + b) p = lowdigits (lowdigits a p + lowdigits b p) p`
  SUBST1_TAC THENL
   [REWRITE_TAC[lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w n. w = z \/
          nonoverlapping_modulo (2 EXP 64) (val w,8 * n) (val z,8 * p)
          ==> w:int64 = z \/
              nonoverlapping_modulo (2 EXP 64)
                 (val w,8 * MIN n p) (val z,8 * p)`
   (fun th -> DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP th)))
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`p < 2 EXP 64`; `val(word p:int64) = p`] THEN
  SUBGOAL_THEN `MIN m p < 2 EXP 64 /\ MIN n p < 2 EXP 64` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  MP_TAC(ARITH_RULE `MIN m p <= p /\ MIN n p <= p`) THEN
  MAP_EVERY SPEC_TAC
   [`lowdigits a p`,`a:num`; `lowdigits b p`,`b:num`;
    `MIN m p`,`m:num`; `MIN n p`,`n:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  MAP_EVERY VAL_INT64_TAC [`m:num`; `n:num`] THEN
  BIGNUM_RANGE_TAC "m" "a" THEN BIGNUM_RANGE_TAC "n" "b" THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Case split following the initial branch, m >= n case then m < n ***)

  ASM_CASES_TAC `n:num <= m` THENL
   [SUBGOAL_THEN `~(m:num < n)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `b < 2 EXP (64 * m)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x49)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read RDX s = word(m - n + 1) /\
          read RCX s = x /\
          read R9 s = y /\
          read R10 s = word n /\
          bignum_from_memory (word_add x (word(8 * n)),m - n) s =
          highdigits a n /\
          2 EXP (64 * n) * bitval(read CF s) + lowdigits a n =
          bignum_from_memory(z,n) s + lowdigits b n` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--7) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `n:num` (offset 0x24) (offset 0x36)
       `\i s. (read RDI s = word(p - m) /\
               read RSI s = z /\
               read RDX s = word(m - n + 1) /\
               read RCX s = x /\
               read R9 s = y /\
               read R8 s = word(n - i) /\
               read R10 s = word i /\
               bignum_from_memory (word_add x (word(8 * i)),m - i) s =
               highdigits a i /\
               bignum_from_memory (word_add y (word(8 * i)),n - i) s =
               highdigits b i /\
               2 EXP (64 * i) * bitval(read CF s) + lowdigits a i =
               bignum_from_memory(z,i) s + lowdigits b i) /\
              (read ZF s <=> i = n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--7) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC execth (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> (i + 1 = n <=> n - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `n - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE
       `(t * e) * x + t * y + z:num = t * (e * x + y) + z`] THEN
      MP_TAC(SPECL
       [`cin:bool`; `word(bigdigit a i):int64`; `word(bigdigit b i):int64`]
       ACCUMULATE_SBB) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x4e)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read R10 s = word m /\
          2 EXP (64 * m) * bitval(read CF s) + lowdigits a m =
          bignum_from_memory(z,m) s + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m:num = n` THENL
       [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_REFL] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_BITVAL];
        ALL_TAC] THEN
      SUBGOAL_THEN `n < m /\ 0 < m - n /\ ~(m - n = 0)` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `m - n:num` THEN
      ENSURES_WHILE_PUP_TAC `m - n:num` (offset 0x3a) (offset 0x4c)
       `\i s. (read RDI s = word(p - m) /\
               read RSI s = z /\
               read RCX s = x /\
               read RDX s = word(m - n - i) /\
               read R10 s = word(n + i) /\
               bignum_from_memory(word_add x (word(8 * (n + i))),
                                  m - (n + i)) s =
               highdigits a (n + i) /\
               2 EXP (64 * (n + i)) * bitval(read CF s) + lowdigits a (n + i) =
               bignum_from_memory(z,n + i) s + lowdigits b (n + i)) /\
              (read ZF s <=> i = m - n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        ASM_REWRITE_TAC[WORD_RULE `word_sub (word(n + 1)) (word 1) = word n`];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[ARITH_RULE `n:num <= m ==> n + m - n = m`] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_BITVAL]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `n:num < m
        ==> (i < m - n <=> n + i < m) /\ (i = m - n <=> n + i = m)`] THEN
      REWRITE_TAC[ARITH_RULE `m - n - i:num = m - (n + i)`] THEN
      REWRITE_TAC[ARITH_RULE `n + i + 1 = (n + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n <= n + j`) THEN
      SPEC_TAC(`n + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> (i + 1 = n <=> n - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `m - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
     REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; ARITH_RULE
       `(t * e) * x + t * y + z:num = t * (e * x + y) + z`] THEN
      MP_TAC(SPECL
       [`cin:bool`; `word(bigdigit a i):int64`]
       ACCUMULATE_SBB_RZERO) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      MATCH_MP_TAC(NUM_RING
       `d = 0 ==> e * w + m + b = m + e * w + e * d + b`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    GHOST_INTRO_TAC `carryout:bool` `read CF` THEN

    ASM_CASES_TAC `m:num = p` THENL
     [UNDISCH_THEN `m:num = p` SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `e * c + a':num = m + b'
        ==> a' = a /\ b' = b ==> e * c + a = m + b`)) THEN
      CONJ_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN `0 < p - m /\ ~(p - m = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - m:num` THEN
    ENSURES_WHILE_PUP_TAC `p - m:num` (offset 0x56) (offset 0x60)
     `\i s. (read RDI s = word(p - m - i) /\
             read R10 s = word(m + i) /\
             read RSI s = z /\
             read RAX s = word_neg(word(bitval carryout)) /\
             2 EXP (64 * (m + i)) * bitval carryout + lowdigits a (m + i) =
             bignum_from_memory (z,m + i) s + lowdigits b (m + i)) /\
            (read ZF s <=> i = p - m)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES];
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `z:num` `bignum_from_memory(z,m + i)` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[ARITH_RULE `0 < m - n ==> n + m - n = m`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `e * c + a':num = m + b'
        ==> a' = a /\ b' = b ==> e * c + a = m + b`)) THEN
      CONJ_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL]] THEN
    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m <= m + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - m - (j + 1) = p - (m + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - m - j = p - (m + j)`] THEN
    REWRITE_TAC[ARITH_RULE `m + (j + 1) = (m + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - m
      ==> (j + 1 = p - m <=> (m + j) + 1 = p) /\
          (j < p - m <=> m + j < p) /\
          (j = p - m <=> m + j = p)`] THEN
    SPEC_TAC(`m + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC execth (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
      DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE
       `(t * 2 EXP 64) * b + t * h + l =
        (t * b + l) + (t * ((2 EXP 64 - 1) * b + h))`] THEN
      SUBGOAL_THEN `bigdigit a i = 0 /\ bigdigit b i = 0`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN MATCH_MP_TAC BIGDIGIT_ZERO THEN
        TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
        ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
        BOOL_CASES_TAC `carryout:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC];
      ASM_SIMP_TAC[ARITH_RULE `i < p ==> (i + 1 = p <=> p - i - 1 = 0)`] THEN
      REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
      REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];

    (**** The other branch, very similar mutatis mutandis ***)

    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `a < 2 EXP (64 * n)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x85)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R8 s = word(n - m) /\
          read R9 s = y /\
          read RCX s = x /\
          read R10 s = word m /\
          bignum_from_memory (word_add y (word(8 * m)),n - m) s =
          highdigits b m /\
          2 EXP (64 * m) * bitval(read CF s) + lowdigits a m =
          bignum_from_memory(z,m) s + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m = 0` THENL
       [UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--6) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `m:num` (offset 0x71) (offset 0x83)
       `\i s. (read RDI s = word(p - n) /\
               read RSI s = z /\
               read R8 s = word(n - m) /\
               read R9 s = y /\
               read RCX s = x /\
               read RDX s = word(m - i) /\
               read R10 s = word i /\
               bignum_from_memory (word_add y (word(8 * i)),n - i) s =
               highdigits b i /\
               bignum_from_memory (word_add x (word(8 * i)),m - i) s =
               highdigits a i /\
               2 EXP (64 * i) * bitval(read CF s) + lowdigits a i =
               bignum_from_memory(z,i) s + lowdigits b i) /\
              (read ZF s <=> i = m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--6) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> (i + 1 = m <=> m - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `m - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE
       `(t * e) * x + t * y + z:num = t * (e * x + y) + z`] THEN
      MP_TAC(SPECL
       [`cin:bool`; `word(bigdigit a i):int64`; `word(bigdigit b i):int64`]
       ACCUMULATE_SBB) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x9a)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R10 s = word n /\
          2 EXP (64 * n) * bitval(read CF s) + lowdigits a n =
          bignum_from_memory(z,n) s +lowdigits b n` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `~(m = n) /\ 0 < n - m /\ ~(n - m = 0)`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `n - m:num` THEN
      ENSURES_WHILE_PUP_TAC `n - m:num` (offset 0x85) (offset 0x98)
       `\i s. (read RDI s = word(p - n) /\
               read RSI s = z /\
               read R9 s = y /\
               read R8 s = word(n - m - i) /\
               read R10 s = word(m + i) /\
               bignum_from_memory(word_add y (word(8 * (m + i))),
                                  n - (m + i)) s =
               highdigits b (m + i) /\
               2 EXP (64 * (m + i)) * bitval(read CF s) + lowdigits a (m + i) =
               bignum_from_memory(z,m + i) s + lowdigits b (m + i)) /\
              (read ZF s <=> i = n - m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        ASM_REWRITE_TAC[WORD_RULE `word_sub (word(m + 1)) (word 1) = word m`];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> m + n - m = n`] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_BITVAL]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `m:num < n
        ==> (i < n - m <=> m + i < n) /\ (i = n - m <=> m + i = n)`] THEN
      REWRITE_TAC[ARITH_RULE `n - m - i:num = n - (m + i)`] THEN
      REWRITE_TAC[ARITH_RULE `m + i + 1 = (m + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m <= m + j`) THEN
      SPEC_TAC(`m + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> (i + 1 = m <=> m - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `n - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; ARITH_RULE
       `(t * e) * x + t * y + z:num = t * (e * x + y) + z`] THEN
      MP_TAC(SPECL
       [`cin:bool`; `word(bigdigit b i):int64`]
       ACCUMULATE_SBB_LZERO) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_SUB_LZERO] THEN
      ONCE_REWRITE_TAC[ARITH_RULE
       `t * ((w + b + c) + a):num = t * (w + a + b) + t * c`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SUBGOAL_THEN `bigdigit a i = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC BIGDIGIT_ZERO THEN
        TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
        ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
        ARITH_TAC];
      ALL_TAC] THEN

    GHOST_INTRO_TAC `carryout:bool` `read CF` THEN

    ASM_CASES_TAC `n:num = p` THENL
     [UNDISCH_THEN `n:num = p` SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `e * c + a':num = m + b'
        ==> a' = a /\ b' = b ==> e * c + a = m + b`)) THEN
      CONJ_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN `0 < p - n /\ ~(p - n = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - n:num` THEN
    ENSURES_WHILE_PUP_TAC `p - n:num` (offset 0x56) (offset 0x60)
     `\i s. (read RDI s = word(p - n - i) /\
             read R10 s = word(n + i) /\
             read RSI s = z /\
             read RAX s = word_neg(word(bitval carryout)) /\
             2 EXP (64 * (n + i)) * bitval carryout + lowdigits a (n + i) =
             bignum_from_memory (z,n + i) s + lowdigits b (n + i)) /\
            (read ZF s <=> i = p - n)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES];
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `z:num` `bignum_from_memory(z,n + i)` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[ARITH_RULE `0 < m - n ==> n + m - n = m`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `e * c + a':num = m + b'
        ==> a' = a /\ b' = b ==> e * c + a = m + b`)) THEN
      CONJ_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL]] THEN
    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n <= n + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - n - (j + 1) = p - (n + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - n - j = p - (n + j)`] THEN
    REWRITE_TAC[ARITH_RULE `n + (j + 1) = (n + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - n
      ==> (j + 1 = p - n <=> (n + j) + 1 = p) /\
          (j < p - n <=> n + j < p) /\
          (j = p - n <=> n + j = p)`] THEN
    SPEC_TAC(`n + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC execth (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
      DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE
       `(t * 2 EXP 64) * b + t * h + l =
        (t * b + l) + (t * ((2 EXP 64 - 1) * b + h))`] THEN
      SUBGOAL_THEN `bigdigit a i = 0 /\ bigdigit b i = 0`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN MATCH_MP_TAC BIGDIGIT_ZERO THEN
        TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
        ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
        BOOL_CASES_TAC `carryout:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC];
      ASM_SIMP_TAC[ARITH_RULE `i < p ==> (i + 1 = p <=> p - i - 1 = 0)`] THEN
      REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
      REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `p < 2 EXP 64` THEN
      ARITH_TAC]];;

(* ------------------------------------------------------------------------- *)
(* Correctness of standard ABI version.                                      *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_SUB_CORRECT = prove
 (`!p z m x a n y b pc.
        nonoverlapping (word pc,0xa6) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_tmc /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. (read RIP s = word(pc + 0x65) \/
                   read RIP s = word(pc + 0xa5)) /\
                  &(bignum_from_memory (z,val p) s) =
                  (&a - &b) rem &2 pow (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) + lowdigits a (val p) =
                  bignum_from_memory (z,val p) s + lowdigits b (val p))
             (MAYCHANGE [RIP; RAX; RDI; RDX; R8; R10] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  tac BIGNUM_SUB_EXEC
   `\s. (read RIP s = word(pc + 0x65) \/
         read RIP s = word(pc + 0xa5)) /\
        2 EXP (64 * p) * val(read RAX s) + lowdigits a p =
        bignum_from_memory (z,p) s + lowdigits b p`
 (curry mk_comb `(+) (pc:num)` o mk_small_numeral));;

let BIGNUM_SUB_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_sub_tmc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val p) s) =
                  (&a - &b) rem &2 pow (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) + lowdigits a (val p) =
                  bignum_from_memory (z,val p) s + lowdigits b (val p))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_SUB_EXEC BIGNUM_SUB_CORRECT);;

let BIGNUM_SUB_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_sub_mc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val p) s) =
                  (&a - &b) rem &2 pow (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) + lowdigits a (val p) =
                  bignum_from_memory (z,val p) s + lowdigits b (val p))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SUB_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_sub_windows_mc = define_from_elf
   "bignum_sub_windows_mc" "x86/generic/bignum_sub.obj";;

let bignum_sub_windows_tmc = define_trimmed "bignum_sub_windows_tmc" bignum_sub_windows_mc;;

let BIGNUM_SUB_WINDOWS_CORRECT = prove
 (`!p z m x a n y b pc.
        nonoverlapping (word pc,0xc2) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_windows_tmc /\
                  read RIP s = word(pc + 0x18) /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. (read RIP s = word(pc + 0x7d) \/
                   read RIP s = word(pc + 0xbf)) /\
                  &(bignum_from_memory (z,val p) s) =
                  (&a - &b) rem &2 pow (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) + lowdigits a (val p) =
                  bignum_from_memory (z,val p) s + lowdigits b (val p))
             (MAYCHANGE [RIP; RAX; RDI; RDX; R8; R10] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  tac (X86_MK_EXEC_RULE bignum_sub_windows_tmc)
   `\s. (read RIP s = word(pc + 0x7d) \/
         read RIP s = word(pc + 0xbf)) /\
        2 EXP (64 * p) * val(read RAX s) + lowdigits a p =
        bignum_from_memory (z,p) s + lowdigits b p`
   (curry mk_comb `(+) (pc:num)` o mk_small_numeral o
    (fun n -> if n < 0x65 then n + 24 else n + 26)));;

let BIGNUM_SUB_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_sub_windows_tmc); (x,8 * val m); (y,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_sub_windows_tmc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val p) s) =
                  (&a - &b) rem &2 pow (64 * val p) /\
                  2 EXP (64 * val p) * val(WINDOWS_C_RETURN s) +
                  lowdigits a (val p) =
                  bignum_from_memory (z,val p) s + lowdigits b (val p))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
  GEN_X86_ADD_RETURN_STACK_TAC (X86_MK_EXEC_RULE bignum_sub_windows_tmc)
    BIGNUM_SUB_WINDOWS_CORRECT
    `[RDI; RSI]` 16 (8,3));;

let BIGNUM_SUB_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_sub_windows_mc); (x,8 * val m); (y,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_sub_windows_mc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  &(bignum_from_memory (z,val p) s) =
                  (&a - &b) rem &2 pow (64 * val p) /\
                  2 EXP (64 * val p) * val(WINDOWS_C_RETURN s) +
                  lowdigits a (val p) =
                  bignum_from_memory (z,val p) s + lowdigits b (val p))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SUB_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

