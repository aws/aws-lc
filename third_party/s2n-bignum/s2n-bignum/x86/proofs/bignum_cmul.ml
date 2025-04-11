(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication of bignum by a single word.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_cmul.o";;
 ****)

let bignum_cmul_mc =
  define_assert_from_elf "bignum_cmul_mc" "x86/generic/bignum_cmul.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x39; 0xcf;        (* CMP (% rdi) (% rcx) *)
  0x48; 0x0f; 0x42; 0xcf;  (* CMOVB (% rcx) (% rdi) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0x85; 0xc9;        (* TEST (% rcx) (% rcx) *)
  0x74; 0x34;              (* JE (Imm8 (word 52)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0x89; 0x06;        (* MOV (Memop Quadword (%% (rsi,0))) (% rax) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0x39; 0xca;        (* CMP (% r10) (% rcx) *)
  0x74; 0x1d;              (* JE (Imm8 (word 29)) *)
  0x4b; 0x8b; 0x04; 0xd0;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r10))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0x39; 0xca;        (* CMP (% r10) (% rcx) *)
  0x72; 0xe3;              (* JB (Imm8 (word 227)) *)
  0x49; 0x39; 0xfa;        (* CMP (% r10) (% rdi) *)
  0x73; 0x1b;              (* JAE (Imm8 (word 27)) *)
  0x4e; 0x89; 0x1c; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% r11) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0x39; 0xfa;        (* CMP (% r10) (% rdi) *)
  0x73; 0x0c;              (* JAE (Imm8 (word 12)) *)
  0x4e; 0x89; 0x1c; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% r11) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0x39; 0xfa;        (* CMP (% r10) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_cmul_tmc = define_trimmed "bignum_cmul_tmc" bignum_cmul_mc;;

let BIGNUM_CMUL_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmul_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CMUL_CORRECT = prove
 (`!p z c n x a pc.
        nonoverlapping (word pc,0x6a) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmul_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = word(pc + 0x69) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (val c * a) (val p) /\
                  (p = n
                   ==> C_RETURN s = word(highdigits (val c * a) (val p))))
             (MAYCHANGE [RIP; RAX; RCX; RDX; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `c:num` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Target the end label, removing redundancy in conclusion ***)

  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x66`
   `\s. 2 EXP (64 * p) * val(read R11 s) + bignum_from_memory (z,p) s =
        c * lowdigits a p` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `t:int64` `read R11` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN
     `2 EXP (64 * p) * val(t:int64) + read (memory :> bytes (z,8 * p)) s1 =
      c * lowdigits a p`
     (fun th ->
        MP_TAC(AP_TERM `\x. x DIV 2 EXP (64 * p)` th) THEN
        MP_TAC(AP_TERM `\x. x MOD 2 EXP (64 * p)` th)) THEN
    ASM_SIMP_TAC[lowdigits; MOD_LT] THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES;
                 DIV_LT; MOD_LT_EQ; MOD_LT; BIGNUM_FROM_MEMORY_BOUND] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[highdigits] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    SIMP_TAC[RDIV_LT_EQ; DIMINDEX_64; EXP_EQ_0; ARITH_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN MATCH_MP_TAC LT_MULT2 THEN
    ASM_MESON_TAC[]] THEN

  (*** Reshuffle to handle clamping and just assume n <= p ***)

  ENSURES_SEQUENCE_TAC `pc + 0x7`
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read RDX s = word c /\
        read RCX s = word(MIN n p) /\
        read R8 s = x /\
        bignum_from_memory(x,MIN n p) s = lowdigits a p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
  SUBGOAL_THEN
   `!w n. w = z \/
          nonoverlapping_modulo (2 EXP 64) (val w,8 * n) (val z,8 * p)
          ==> w:int64 = z \/
              nonoverlapping_modulo (2 EXP 64)
                 (val w,8 * MIN n p) (val z,8 * p)`
   (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th))
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`c < 2 EXP 64`; `p < 2 EXP 64`; `val(word p:int64) = p`] THEN
  SUBGOAL_THEN `MIN n p < 2 EXP 64` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  MP_TAC(ARITH_RULE `MIN n p <= p`) THEN
  MAP_EVERY SPEC_TAC
   [`lowdigits a p`,`a:num`; `MIN n p`,`n:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  VAL_INT64_TAC `n:num` THEN BIGNUM_RANGE_TAC "n" "a" THEN
  SUBGOAL_THEN `a < 2 EXP (64 * p)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_REWRITE_TAC[ARITH_EQ; LE_MULT_LCANCEL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Do the part from the "tail" loop first ***)

  ENSURES_SEQUENCE_TAC `pc + 0x46`
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read R10 s = word n /\
        2 EXP (64 * n) * val(read R11 s) + bignum_from_memory(z,n) s =
        c * a` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ASSUME `n:num <= p`) THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
    ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
       `n < p ==> n < p /\ ~(p <= n)`))] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x58`
     `\s. read RDI s = word p /\
          read RSI s = z /\
          read R10 s = word(n + 1) /\
          read R11 s = word 0 /\
          bignum_from_memory(z,n+1) s = c * a /\
          (read CF s <=> n + 1 < p)` THEN
    CONJ_TAC THENL
     [GHOST_INTRO_TAC `h:int64` `read R11` THEN VAL_INT64_TAC `p - n:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE;
        REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
          BIGNUM_FROM_MEMORY_STEP] THEN
        GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN
        ASM_REWRITE_TAC[];
        VAL_INT64_TAC `n + 1` THEN ASM_REWRITE_TAC[GSYM WORD_ADD]];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = n + 1` THENL
     [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN
      X86_SIM_TAC BIGNUM_CMUL_EXEC [1] THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    ENSURES_WHILE_UP_TAC `p - n - 1` `pc + 0x5a` `pc + 0x61`
     `\i s. read RDI s = word p /\
            read RSI s = z /\
            read R10 s = word((n + 1) + i) /\
            read R11 s = word 0 /\
            bignum_from_memory (z,(n + 1) + i) s = c * a` THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_REWRITE_TAC[ARITH_RULE `p <= n + 1 <=> p = n + 1 \/ ~(n < p)`];
      ALL_TAC; (** Main invariant ***)
      REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      VAL_INT64_TAC `(n + 1) + i` THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `p - ((n + 1) + p - n - 1) = 0`] THEN
      SUBGOAL_THEN `(n + 1) + p - n - 1 = p` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `n:num < p` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES; LT_REFL]] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `(n + 1) + i` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_ASSOC] THEN CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
            BIGNUM_FROM_MEMORY_STEP] THEN
      ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]]] THEN

  (*** The trivial case n = 0 ***)

  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; SUB_0; MULT_CLAUSES] THEN
    REWRITE_TAC[ADD_CLAUSES; WORD_SUB_0];
    ALL_TAC] THEN

  (*** The first digit of the main part, done before the loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0x27`
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read R9 s = word c /\
        read RCX s = word n /\
        read R8 s = x /\
        read R10 s = word 1 /\
        (read ZF s <=> n = 1) /\
        bignum_from_memory(word_add x (word 8),n - 1) s = highdigits a 1 /\
        2 EXP 64 * val(read R11 s) + bignum_from_memory(z,1) s =
        c * lowdigits a 1` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory (x,n) s0 = highdigits a 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0];
      GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_CMUL_EXEC [7] (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LOWDIGITS_1] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** Now the case n = 1 ***)

  ASM_CASES_TAC `n = 1` THENL
   [UNDISCH_THEN `n = 1` SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[SUB_REFL; BIGNUM_FROM_MEMORY_TRIVIAL; HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF];
    ALL_TAC] THEN

  (*** The main loop ***)

  SUBGOAL_THEN `~(n - 1 = 0) /\ 0 < n - 1` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  ENSURES_WHILE_UP_TAC `n - 1` `pc + 0x29` `pc + 0x41`
   `\i s. read RDI s = word p /\
          read RSI s = z /\
          read R9 s = word c /\
          read RCX s = word n /\
          read R8 s = x /\
          read R10 s = word(i + 1) /\
          bignum_from_memory(word_add x (word (8 * (i + 1))),n - (i + 1)) s =
          highdigits a (i + 1) /\
          2 EXP (64 * (i + 1)) * val(read R11 s) +
          bignum_from_memory(z,i + 1) s =
          c * lowdigits a (i + 1)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GHOST_INTRO_TAC `hin:int64` `read R11` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[MULT_CLAUSES; BITVAL_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
    ALL_TAC; (*** Main loop invariant ***)
    REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    VAL_INT64_TAC `i + 1` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n - 1 ==> i + 1 < n`];
    ASM_SIMP_TAC[SUB_ADD; LE_1; SUB_REFL] THEN
    GHOST_INTRO_TAC `hin:int64` `read R11` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** the final loop invariant ***)

  X_GEN_TAC `j:num` THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `i < n - 1 ==> 0 < i + 1 /\ ~(i + 1 = 0) /\ i + 1 < n`) o CONJUNCT1) THEN
  SPEC_TAC(`j + 1`,`i:num`) THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < p` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `hin:int64` `read R11` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  X86_ACCSIM_TAC BIGNUM_CMUL_EXEC [2;3;4] (1--7) THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[EXP_ADD; MULT_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING);;

let BIGNUM_CMUL_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z c n x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_tmc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (val c * a) (val p) /\
                  (p = n
                   ==> C_RETURN s = word(highdigits (val c * a) (val p))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_cmul_tmc BIGNUM_CMUL_CORRECT);;

let BIGNUM_CMUL_SUBROUTINE_CORRECT = prove
 (`!p z c n x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_mc) (z,8 * val p) /\
        nonoverlapping (stackpointer,8) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (val c * a) (val p) /\
                  (p = n
                   ==> C_RETURN s = word(highdigits (val c * a) (val p))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmul_windows_mc = define_from_elf
   "bignum_cmul_windows_mc" "x86/generic/bignum_cmul.obj";;

let bignum_cmul_windows_tmc = define_trimmed "bignum_cmul_windows_tmc" bignum_cmul_windows_mc;;

let BIGNUM_CMUL_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z c n x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_windows_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_windows_tmc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (val c * a) (val p) /\
                  (p = n
                   ==> WINDOWS_C_RETURN s =
                       word(highdigits (val c * a) (val p))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_cmul_windows_tmc bignum_cmul_tmc
    BIGNUM_CMUL_CORRECT);;

let BIGNUM_CMUL_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z c n x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_windows_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_windows_mc) (z,8 * val p) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (val c * a) (val p) /\
                  (p = n
                   ==> WINDOWS_C_RETURN s =
                       word(highdigits (val c * a) (val p))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

