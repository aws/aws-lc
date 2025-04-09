(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiply-accumulate of bignum by a single word.                           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_cmadd.o";;
 ****)

let bignum_cmadd_mc =
  define_assert_from_elf "bignum_cmadd_mc" "x86/generic/bignum_cmadd.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x48; 0x39; 0xcf;        (* CMP (% rdi) (% rcx) *)
  0x48; 0x0f; 0x42; 0xcf;  (* CMOVB (% rcx) (% rdi) *)
  0x48; 0x29; 0xcf;        (* SUB (% rdi) (% rcx) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x85; 0xc9;        (* TEST (% rcx) (% rcx) *)
  0x74; 0x68;              (* JE (Imm8 (word 104)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0x01; 0x06;        (* ADD (Memop Quadword (%% (rsi,0))) (% rax) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x48; 0xff; 0xc9;        (* DEC (% rcx) *)
  0x74; 0x23;              (* JE (Imm8 (word 35)) *)
  0x4e; 0x13; 0x1c; 0xd6;  (* ADC (% r11) (Memop Quadword (%%% (rsi,3,r10))) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x4b; 0x8b; 0x04; 0xd0;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r10))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xc9;        (* DEC (% rcx) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x22;              (* JE (Imm8 (word 34)) *)
  0x4e; 0x01; 0x1c; 0xd6;  (* ADD (Memop Quadword (%%% (rsi,3,r10))) (% r11) *)
  0x41; 0xbb; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r11d) (Imm32 (word 0)) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x74; 0x0c;              (* JE (Imm8 (word 12)) *)
  0x4e; 0x11; 0x1c; 0xd6;  (* ADC (Memop Quadword (%%% (rsi,3,r10))) (% r11) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf4;              (* JNE (Imm8 (word 244)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_cmadd_tmc = define_trimmed "bignum_cmadd_tmc" bignum_cmadd_mc;;

let BIGNUM_CMADD_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmadd_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CMADD_CORRECT = prove
 (`!p z d c n x a pc.
        nonoverlapping (word pc,0x80) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmadd_tmc) /\
                  read RIP s = word(pc + 0x1) /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory(z,val p) s = d /\
                  bignum_from_memory(x,val n) s = a)
             (\s. read RIP s = word(pc + 0x7e) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (d + val c * a) (val p) /\
                  (val n <= val p
                   ==> C_RETURN s = word(highdigits (d + val c * a) (val p))))
             (MAYCHANGE [RIP; RAX; RDI; RCX; RDX; R9; R10; R11; RBX] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN MAP_EVERY X_GEN_TAC [`z:int64`; `d:num`] THEN
  W64_GEN_TAC `c:num` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Target the end label, removing redundancy in conclusion ***)

  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x7b`
   `\s. (2 EXP (64 * p) * val(read R11 s) + bignum_from_memory(z,p) s ==
         d + c * lowdigits a p) (mod (2 EXP (64 * (p + 1))))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `hin:int64` `read R11` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN REWRITE_TAC[lowdigits; MOD_UNIQUE] THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        BIGNUM_FROM_MEMORY_BOUND] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
       `(e * a + x == y') (mod n')
        ==> e divides n' /\ (y' == y) (mod e) ==>  (y == x) (mod e)`)) THEN
      SIMP_TAC[DIVIDES_EXP_LE; ARITH_LE; ARITH_LT] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;

      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONG_SYM]) THEN
      SUBGOAL_THEN `a < 2 EXP (64 * p)` ASSUME_TAC THENL
       [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
        UNDISCH_TAC `n:num <= p` THEN ARITH_TAC;
        ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[highdigits; DIV_MOD; GSYM EXP_ADD; CONG] THEN
      REWRITE_TAC[ARITH_RULE `64 * (p + 1) = 64 * p + 64`] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_MOD] THEN
      SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; EXP_EQ_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      SIMP_TAC[DIV_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
      SIMP_TAC[MOD_LT; VAL_BOUND_64]]] THEN

  (*** Reshuffle to handle clamping and just assume n <= p ***)

  ENSURES_SEQUENCE_TAC `pc + 0xb`
   `\s. read RDI s = word(p - MIN n p) /\
        read RSI s = z /\
        read RDX s = word c /\
        read RCX s = word(MIN n p) /\
        read R8 s = x /\
        bignum_from_memory (z,p) s = d /\
        bignum_from_memory(x,MIN n p) s = lowdigits a p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    REWRITE_TAC[WORD_SUB; ARITH_RULE `MIN n p <= p`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC;
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
  VAL_INT64_TAC `n:num` THEN
  BIGNUM_RANGE_TAC "n" "a" THEN BIGNUM_RANGE_TAC "p" "d" THEN
  SUBGOAL_THEN `a < 2 EXP (64 * p)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_REWRITE_TAC[ARITH_EQ; LE_MULT_LCANCEL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** The trivial case n = 0 ***)

  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; CONG_REFL; MULT_CLAUSES];
    ALL_TAC] THEN

  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Do the part from the "tail" loop first ***)

  ENSURES_SEQUENCE_TAC `pc + 0x54`
   `\s. read RDI s = word(p - n) /\
        read RSI s = z /\
        read R10 s = word n /\
        bignum_from_memory(word_add z (word(8 * n)),p - n) s =
        highdigits d n /\
        2 EXP (64 * n) * val(read R11 s) + bignum_from_memory(z,n) s =
        lowdigits d n + c * a` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ASSUME `n:num <= p`) THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
    ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      REWRITE_TAC[CONG_REFL];
      DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
       `n < p ==> n < p /\ ~(p <= n)`))] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x69`
     `\s. read RDI s = word(p - (n + 1)) /\
          read RSI s = z /\
          read R10 s = word(n + 1) /\
          read R11 s = word 0 /\
          (read ZF s <=> p = n + 1) /\
          bignum_from_memory(word_add z (word(8 * (n + 1))),p - (n + 1)) s =
          highdigits d (n + 1) /\
          2 EXP (64 * (n + 1)) * bitval(read CF s) +
          bignum_from_memory(z,n+1) s = lowdigits d (n + 1) + c * a` THEN
    CONJ_TAC THENL
     [GHOST_INTRO_TAC `h:int64` `read R11` THEN
      VAL_INT64_TAC `p - n:num` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_CMADD_EXEC [3] (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
       [VAL_INT64_TAC `p - (n + 1)` THEN ASM_REWRITE_TAC[] THEN
        SIMPLE_ARITH_TAC;
        REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC]] THEN
      FIRST_X_ASSUM(fun th ->
       GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = n + 1` THENL
     [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      X86_SIM_TAC BIGNUM_CMADD_EXEC (1--2) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
        `2 EXP e * b + c = n ==> n = 2 EXP e * b + c`)) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[VAL_WORD_BITVAL; CONG_REFL];
      ALL_TAC] THEN

    ENSURES_WHILE_PAUP_TAC `n + 1` `p:num` `pc + 0x6b` `pc + 0x75`
     `\i s. (read RDI s = word(p - i) /\
             read RSI s = z /\
             read R10 s = word i /\
             read R11 s = word 0 /\
             bignum_from_memory(word_add z (word (8 * i)),p - i) s =
             highdigits d i /\
             2 EXP (64 * i) * bitval(read CF s) +
             bignum_from_memory (z,i) s = lowdigits d i + c * a) /\
            (read ZF s <=> i = p)` THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES];
      ALL_TAC; (** Main invariant ***)
      REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      VAL_INT64_TAC `p - i:num` THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN SIMPLE_ARITH_TAC;
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; CONG_REFL; VAL_WORD_BITVAL]] THEN

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_ACCSTEPS_TAC BIGNUM_CMADD_EXEC [1] (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
      DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC];
      VAL_INT64_TAC `p - (i + 1)` THEN ASM_REWRITE_TAC[] THEN
      SIMPLE_ARITH_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; EXP_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING] THEN

  (*** Now back off the end label to "hightail" to avoid duplication ***)

  ENSURES_SEQUENCE_TAC `pc + 0x50`
   `\s. read RDI s = word(p - n) /\
        read RSI s = z /\
        read R10 s = word n /\
        bignum_from_memory(word_add z (word(8 * n)),p - n) s =
        highdigits d n /\
        2 EXP (64 * n) * (bitval(read CF s) + val(read R11 s)) +
        bignum_from_memory(z,n) s =
        lowdigits d n + c * a` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `hin:int64` `read R11` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN
    REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; VAL_WORD_BITVAL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
     `e * b + x:num = y
      ==> !c. (e * b + x = y ==> c = b) ==> e * c + x = y`)) THEN
    REWRITE_TAC[MOD_EQ_SELF; EXP_EQ_0; ARITH_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(e <= x ==> ee * e <= ee * x) /\ z < ee * e
      ==> ee * x + y = z ==> x < e`) THEN
    SIMP_TAC[LE_MULT_LCANCEL] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `e * 2 EXP 64 = e + (2 EXP 64 - 1) * e`] THEN
    MATCH_MP_TAC LTE_ADD2 THEN REWRITE_TAC[LOWDIGITS_BOUND] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
    UNDISCH_TAC `c < 2 EXP 64` THEN ARITH_TAC] THEN

  (*** The first digit of the main part, done before the loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2b`
   `\s. read RDI s = word(p - n) /\
        read RSI s = z /\
        read R9 s = word c /\
        read RCX s = word(n - 1) /\
        read R8 s = x /\
        read R10 s = word 1 /\
        (read ZF s <=> n = 1) /\
        bignum_from_memory (word_add z (word (8 * 1)),p - 1) s =
        highdigits d 1 /\
        bignum_from_memory (word_add x (word (8 * 1)),n - 1) s =
        highdigits a 1 /\
        2 EXP (64 * 1) * (bitval (read CF s) + val (read R11 s)) +
        bignum_from_memory (z,1) s =
        lowdigits d 1 + c * lowdigits a 1` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory(x,n) s0 = highdigits a 0 /\
                  bignum_from_memory(z,p) s0 = highdigits d 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
        [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_CMADD_EXEC [6;7] (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ;  VAL_WORD_1] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LOWDIGITS_1] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  (*** Now the case n = 1 ***)

  ASM_CASES_TAC `n = 1` THENL
   [UNDISCH_THEN `n = 1` SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[SUB_REFL; BIGNUM_FROM_MEMORY_TRIVIAL; HIGHDIGITS_ZERO] THEN
    GHOST_INTRO_TAC `hin:int64` `read R11` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF];
    ALL_TAC] THEN

  (*** The main loop ***)

  SUBGOAL_THEN `1 < n /\ ~(n - 1 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  ENSURES_WHILE_PAUP_TAC `1` `n:num` `pc + 0x2d` `pc + 0x4e`
   `\i s. (read RDI s = word(p - n) /\
           read RSI s = z /\
           read R9 s = word c /\
           read RCX s = word(n - i) /\
           read R8 s = x /\
           read R10 s = word i /\
           bignum_from_memory(word_add z (word (8 * i)),p - i) s =
           highdigits d i /\
           bignum_from_memory(word_add x (word (8 * i)),n - i) s =
           highdigits a i /\
           2 EXP (64 * i) * (bitval(read CF s) + val(read R11 s)) +
           bignum_from_memory(z,i) s =
           lowdigits d i + c * lowdigits a i) /\
          (read ZF s <=> i = n)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GHOST_INTRO_TAC `hin:int64` `read R11` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC; (*** Main loop invariant ***)
    REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUB_ADD; LE_1; SUB_REFL] THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read R11` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CMADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** the final loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < p` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read R11` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_ACCSTEPS_TAC BIGNUM_CMADD_EXEC [1;4] (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub x (word_neg y):int64 = word_add x y`]) THEN
  ACCUMULATE_ARITH_TAC "s5" THEN
  X86_ACCSTEPS_TAC BIGNUM_CMADD_EXEC [6] (6--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
    DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC];
    VAL_INT64_TAC `n - (i + 1)` THEN ASM_REWRITE_TAC[] THEN
    SIMPLE_ARITH_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV
   [ARITH_RULE `e * d1 + d0 + c * (e * a1 + a0):num =
                e * (c * a1 + d1) + d0 + c * a0`] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEN_REWRITE_TAC LAND_CONV
   [TAUT `p /\ q /\ r /\ s <=> p /\ s /\ q /\ r`] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let BIGNUM_CMADD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z d c n x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val p) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,LENGTH bignum_cmadd_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cmadd_tmc) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmadd_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory(z,val p) s = d /\
                  bignum_from_memory(x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (d + val c * a) (val p) /\
                  (val n <= val p
                   ==> C_RETURN s = word(highdigits (d + val c * a) (val p))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 8),8)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_cmadd_tmc BIGNUM_CMADD_CORRECT
   `[RBX]` 8);;

let BIGNUM_CMADD_SUBROUTINE_CORRECT = prove
 (`!p z d c n x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val p) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,LENGTH bignum_cmadd_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cmadd_mc) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmadd_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory(z,val p) s = d /\
                  bignum_from_memory(x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (d + val c * a) (val p) /\
                  (val n <= val p
                   ==> C_RETURN s = word(highdigits (d + val c * a) (val p))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 8),8)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMADD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmadd_windows_mc = define_from_elf
   "bignum_cmadd_windows_mc" "x86/generic/bignum_cmadd.obj";;

let bignum_cmadd_windows_tmc = define_trimmed "bignum_cmadd_windows_tmc" bignum_cmadd_windows_mc;;

let BIGNUM_CMADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z d c n x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val p) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,LENGTH bignum_cmadd_windows_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cmadd_windows_tmc) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmadd_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory(z,val p) s = d /\
                  bignum_from_memory(x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (d + val c * a) (val p) /\
                  (val n <= val p
                   ==> WINDOWS_C_RETURN s =
                       word(highdigits (d + val c * a) (val p))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 24),24)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_cmadd_windows_tmc bignum_cmadd_tmc
    BIGNUM_CMADD_CORRECT `[RBX]` 8);;

let BIGNUM_CMADD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z d c n x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val p) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,LENGTH bignum_cmadd_windows_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cmadd_windows_mc) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmadd_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory(z,val p) s = d /\
                  bignum_from_memory(x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (d + val c * a) (val p) /\
                  (val n <= val p
                   ==> WINDOWS_C_RETURN s =
                       word(highdigits (d + val c * a) (val p))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

