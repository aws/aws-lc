(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Normalization of a bignum in-place in constant time.                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_normalize.o";;
 ****)

let bignum_normalize_mc =
  define_assert_from_elf "bignum_normalize_mc" "x86/generic/bignum_normalize.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x49; 0x89; 0xf8;        (* MOV (% r8) (% rdi) *)
  0x49; 0x83; 0xe8; 0x01;  (* SUB (% r8) (Imm8 (word 1)) *)
  0x72; 0x72;              (* JB (Imm8 (word 114)) *)
  0x4a; 0x8b; 0x0c; 0xc6;  (* MOV (% rcx) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x74; 0x34;              (* JE (Imm8 (word 52)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x49; 0x89; 0xf9;        (* MOV (% r9) (% rdi) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0x0f; 0x45; 0xc2;  (* CMOVNE (% rax) (% rdx) *)
  0xba; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 0)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x4a; 0x8b; 0x14; 0xd6;  (* MOV (% rdx) (Memop Quadword (%%% (rsi,3,r10))) *)
  0x48; 0x0f; 0x42; 0xca;  (* CMOVB (% rcx) (% rdx) *)
  0x4a; 0x89; 0x0c; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rcx) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x75; 0xe9;              (* JNE (Imm8 (word 233)) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xcc;              (* JNE (Imm8 (word 204)) *)
  0xba; 0x7f; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 127)) *)
  0x48; 0x0f; 0xbd; 0xc9;  (* BSR (% rcx) (% rcx) *)
  0x48; 0x0f; 0x44; 0xca;  (* CMOVE (% rcx) (% rdx) *)
  0x48; 0x83; 0xf1; 0x3f;  (* XOR (% rcx) (Imm8 (word 63)) *)
  0x48; 0xc1; 0xe0; 0x06;  (* SHL (% rax) (Imm8 (word 6)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x4a; 0x8b; 0x14; 0xc6;  (* MOV (% rdx) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x4c; 0x0f; 0xa5; 0xca;  (* SHLD (% rdx) (% r9) (% cl) *)
  0x4a; 0x89; 0x14; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% rdx) *)
  0x4d; 0x89; 0xd1;        (* MOV (% r9) (% r10) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x72; 0xe6;              (* JB (Imm8 (word 230)) *)
  0xc3                     (* RET *)
];;

let bignum_normalize_tmc = define_trimmed "bignum_normalize_tmc" bignum_normalize_mc;;

let BIGNUM_NORMALIZE_EXEC = X86_MK_CORE_EXEC_RULE bignum_normalize_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_NORMALIZE_CORRECT = time prove
 (`!k z n pc.
        nonoverlapping (word pc,0x7f) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_normalize_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k; z] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = word(pc + 0x7e) /\
                  bignum_from_memory (z,val k) s =
                  2 EXP (64 * val k - bitsize n) * n /\
                  C_RETURN s = word(64 * val k - bitsize n))
             (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BITSIZE_0] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumption ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** The digitwise normalization "normloop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x46`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        bignum_from_memory(z,k) s = 2 EXP (64 * val(read RAX s)) * n /\
        read RCX s = word(bigdigit (bignum_from_memory(z,k) s) (k - 1)) /\
        val(read RAX s) <= k - 1 /\
        (n = 0 ==> val(read RAX s) = k - 1) /\
        (~(n = 0) ==> 2 EXP (64 * (k - 1)) <= bignum_from_memory(z,k) s)` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; SUB_REFL] THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add z (word(8 * val(word 0:int64))))) s0 =
        word n`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; MULT_CLAUSES]; ALL_TAC] THEN
      X86_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
      ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; EXP] THEN
      ASM_SIMP_TAC[VAL_WORD; GSYM LOWDIGITS_1; DIMINDEX_64; lowdigits; MOD_LT;
                   MULT_CLAUSES] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ARITH_RULE `k - 1 = 0 <=> k = 0 \/ k = 1`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    ENSURES_WHILE_PUP_TAC `k - 1` `pc + 0x12` `pc + 0x44`
     `\i s. (read RDI s = word k /\
             read RSI s = z /\
             read R8 s = word(k - 1 - i) /\
             bignum_from_memory(z,k) s = 2 EXP (64 * val(read RAX s)) * n /\
             read RCX s = word(bigdigit (bignum_from_memory(z,k) s) (k - 1)) /\
             val(read RAX s) <= i /\
             (n = 0 ==> val(read RAX s) = i) /\
             (~(n = 0) ==> 2 EXP (64 * i) <= bignum_from_memory(z,k) s)) /\
            (read ZF s <=> i = k - 1)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ARITH_RULE `k < 1 <=> k = 0`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      MP_TAC(ISPECL [`k:num`; `z:int64`; `s0:x86state`; `k - 1`]
         BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - 1 < k <=> ~(k = 0)`] THEN
      DISCH_THEN(MP_TAC o SYM) THEN
      GEN_REWRITE_TAC LAND_CONV [VAL_WORD_GALOIS] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC THEN
      SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[WORD_SUB; LE_1; VAL_WORD_1]; ALL_TAC] THEN
      VAL_INT64_TAC `k - 1` THEN
      X86_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUB_0; VAL_WORD_0; MULT_CLAUSES] THEN ARITH_TAC;
      ALL_TAC; (*** Do the main loop invariant below ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_NORMALIZE_EXEC [1];
      X86_SIM_TAC BIGNUM_NORMALIZE_EXEC [1]] THEN

    (*** Nested loop "shufloop" ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `m:num` `bignum_from_memory (z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN
    GHOST_INTRO_TAC `d:num` `\s. val(read RAX s)` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [VAL_WORD_GALOIS] THEN
    REWRITE_TAC[DIMINDEX_64] THEN GLOBALIZE_PRECONDITION_TAC THEN
    UNDISCH_THEN `m = 2 EXP (64 * d) * n` (ASSUME_TAC o SYM) THEN
    ABBREV_TAC `topz <=> bigdigit m (k - 1) = 0` THEN

    ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x2a` `pc + 0x3f`
     `\j s. (read RDI s = word k /\
             read RSI s = z /\
             read RAX s = (if topz then word(d + 1) else word d) /\
             read R8 s = word (k - 1 - i) /\
             read R9 s = word(k - j) /\
             read R10 s = word j /\
             read RDX s =
               (if j = 0 then word 0 else word(bigdigit m (j - 1))) /\
             (read CF s <=> ~topz) /\
             bignum_from_memory(word_add z (word(8 * j)),k - j) s =
             highdigits m j /\
             bignum_from_memory(z,j) s =
             lowdigits (if topz then 2 EXP 64 * m else m) j) /\
            (read RCX s =
             word(bigdigit (bignum_from_memory(z,j) s) (j - 1)) /\
             (read ZF s <=> j = k))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--7) THEN
      REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0] THEN
      ASM_SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_0; HIGHDIGITS_0; SUB_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[COND_SWAP; GSYM WORD_ADD];
      ALL_TAC; (*** Inner loop invariant below ***)
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      X86_SIM_TAC BIGNUM_NORMALIZE_EXEC [1] THEN
      VAL_INT64_TAC `k - 1` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> 1 <= k - 1 - i`];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ASSOC]] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM CONJ_ASSOC];
        W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
          lhand o lhand o snd) THEN
        REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
         [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i < k - 1`] THEN
        ARITH_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) LOWDIGITS_SELF o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "topz" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `m = lowdigits m ((k - 1) + 1)` SUBST1_TAC THENL
         [ASM_SIMP_TAC[SUB_ADD; LE_1; LOWDIGITS_SELF];
          ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; MULT_CLAUSES]] THEN
        SUBGOAL_THEN `64 * k = 64 + 64 * (k - 1)` SUBST1_TAC THENL
         [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
        SIMP_TAC[LT_MULT_LCANCEL; LOWDIGITS_BOUND; EXP_EQ_0; ARITH_EQ];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `bigdigit m (k - 1) = 0 <=> topz` (SUBST1_TAC o SYM) THEN
        UNDISCH_THEN `2 EXP (64 * d) * n = m` (SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `n = 0 ==> d:num = i` THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; DIV_0; MOD_0; bigdigit] THEN
        DISCH_THEN SUBST_ALL_TAC THEN VAL_INT64_TAC `i + 1` THEN
        ASM_REWRITE_TAC[LE_REFL];
        UNDISCH_THEN `n = 0 ==> d:num = i` (K ALL_TAC) THEN
        UNDISCH_TAC `~(n = 0) ==> 2 EXP (64 * i) <= m` THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      UNDISCH_THEN `bigdigit m (k - 1) = 0 <=> topz` (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; HIGHDIGITS_EQ_0] THEN
      ASM_CASES_TAC `m < 2 EXP (64 * (k - 1))` THEN ASM_REWRITE_TAC[] THENL
       [VAL_INT64_TAC `d + 1` THEN ASM_REWRITE_TAC[LE_ADD_RCANCEL] THEN
        REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (n + 1) = 64 + 64 * n`] THEN
        ASM_REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL];
        VAL_INT64_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
        ASM_SIMP_TAC[ARITH_RULE `d <= i ==> d <= i + 1`] THEN
        TRANS_TAC LE_TRANS `2 EXP (64 * (k - 1))` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `i < k - 1` THEN ARITH_TAC]] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_NORMALIZE_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ADD_SUB; GSYM WORD_ADD; ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `j < j + 1`] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `j < k ==> 1 <= k - j`];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ASSOC]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONJ_ASSOC];
      W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
        lhand o lhand o snd) THEN
      REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
       [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `j:num < k`] THEN
      ARITH_TAC] THEN
    UNDISCH_THEN `bigdigit m (k - 1) = 0 <=> topz` (SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `bigdigit m (k - 1) = 0` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LOWDIGITS_CLAUSES; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THENL
     [ALL_TAC; ARITH_TAC] THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP] THEN
    REWRITE_TAC[LOWDIGITS_0; VAL_WORD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[REWRITE_RULE[lowdigits] (GSYM LOWDIGITS_1)] THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_MULT] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    MATCH_MP_TAC(NUM_RING `x:num = y ==> a + e * x = e * y + a`) THEN
    SUBGOAL_THEN `j = SUC(j - 1)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
    THENL [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[bigdigit; EXP_ADD; ARITH_RULE `64 * SUC j = 64 + 64 * j`] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN

  (*** Ghost things up again ***)

  GHOST_INTRO_TAC `m:num` `bignum_from_memory (z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN
  GHOST_INTRO_TAC `d:num` `\s. val(read RAX s)` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [VAL_WORD_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_64] THEN GLOBALIZE_PRECONDITION_TAC THEN
  UNDISCH_THEN `m = 2 EXP (64 * d) * n` (ASSUME_TAC o SYM) THEN

  (*** The "bitloop" loop ***)

  ABBREV_TAC `c = 64 - bitsize(bigdigit m (k - 1))` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x64` `pc + 0x79`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read RAX s = word(64 * d + c) /\
          read R8 s = word i /\
          read RCX s = word c /\
          bignum_from_memory(word_add z (word (8 * i)),k - i) s =
          highdigits m i /\
          2 EXP (64 * i) * val(read R9 s) DIV 2 EXP (64 - c MOD 64) +
          bignum_from_memory(z,i) s =
          2 EXP (c MOD 64) * lowdigits m i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--8) THEN
    SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; DIV_0; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES;
                WORD_ADD_0; HIGHDIGITS_0; SUB_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN CONJ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    SIMP_TAC[GSYM VAL_EQ_0; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    EXPAND_TAC "c" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITSIZE_0; SUB_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
    SUBST1_TAC(ARITH_RULE `63 = 2 EXP 6 - 1`) THEN
    W(MP_TAC o PART_MATCH (rand o rand) WORD_SUB_MASK_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC VAL_WORD_LT THEN ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SUB] THEN
    REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND] THEN
    MP_TAC(ISPEC `word (bigdigit m (k - 1)):int64` WORD_CLZ_LT_DIMINDEX) THEN
    ASM_SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    SIMP_TAC[ARITH_RULE `i <= 63 <=> i < 64`] THEN DISCH_THEN(K ALL_TAC) THEN
    SIMP_TAC[WORD_CLZ_BITSIZE; WORD_SUB; DIMINDEX_64; BITSIZE_LE; VAL_WORD_LT;
             BIGDIGIT_BOUND; VAL_WORD_EQ] THEN
    CONV_TAC WORD_RULE;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `b:int64` `read R9` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--6) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; GSYM WORD_ADD;
             ARITH_RULE `64 - k <= 64`] THEN
    SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_64_CLAUSES; LOWDIGITS_CLAUSES] THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
     `ee * b + m:num = c * l
      ==> e * d + y = c * z + b
          ==> (ee * e) * d + m + ee * y = c * (ee * z + l)`)) THEN
    REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `64 - (64 - x MOD 64) = x MOD 64`] THEN
    SUBGOAL_THEN `2 EXP 64 = 2 EXP (c MOD 64) * 2 EXP (64 - c MOD 64)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC]] THEN
    REWRITE_TAC[DIVISION_SIMP];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--2);

    GHOST_INTRO_TAC `b:int64` `read R9` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    X86_SIM_TAC BIGNUM_NORMALIZE_EXEC (1--2)] THEN

  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `e * b + z = cn
    ==> (e * b < e * 1 ==> e * b = 0)
        ==> cn < e ==> z = cn`)) THEN
  ANTS_TAC THENL
   [SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; MULT_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC `n = 0 ==> d = k - 1` THEN
    UNDISCH_TAC `2 EXP (64 * d) * n = m` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; EXP_LT_0; ARITH_EQ] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "c" THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGDIGIT_0; BITSIZE_0] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    UNDISCH_THEN `n = 0 ==> d = k - 1` (K ALL_TAC) THEN
    UNDISCH_TAC `~(n = 0) ==> 2 EXP (64 * (k - 1)) <= m` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `64 * k = c MOD 64 + (64 * k - c MOD 64)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[EXP_ADD; LT_MULT_LCANCEL; ARITH_EQ; EXP_EQ_0]] THEN
    REWRITE_TAC[GSYM BITSIZE_LE] THEN
    SUBGOAL_THEN
     `m = 2 EXP (64 * (k - 1)) * highdigits m (k - 1) + lowdigits m (k - 1)`
    SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
    ASM_SIMP_TAC[HIGHDIGITS_TOP] THEN
    UNDISCH_THEN `64 - bitsize (bigdigit m (k - 1)) = c`
     (SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `bigdigit m (k - 1) = 0` THENL
     [ASM_REWRITE_TAC[BITSIZE_0; MULT_CLAUSES; ADD_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITSIZE_LE; SUB_0] THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * (k - 1))` THEN
      ASM_REWRITE_TAC[LOWDIGITS_BOUND; LE_EXP; ARITH_EQ] THEN ARITH_TAC;
      ASM_SIMP_TAC[BITSIZE_MULT_ADD; LOWDIGITS_BOUND]] THEN
    MATCH_MP_TAC(ARITH_RULE `a + c <= b ==> a <= b - c MOD 64`) THEN
    MATCH_MP_TAC(ARITH_RULE
     `~(k = 0) /\ b <= 64 ==> (64 * (k - 1) + b) + (64 - b) <= 64 * k`) THEN
    ASM_REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `c MOD 64 = c` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN EXPAND_TAC "c" THEN
    REWRITE_TAC[ARITH_RULE `64 - n < 64 <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[BITSIZE_EQ_0; GSYM HIGHDIGITS_TOP] THEN
    ASM_REWRITE_TAC[HIGHDIGITS_EQ_0; NOT_LT];
    ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `2 EXP (64 * d) * n = m`)) THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM EXP_ADD); MULT_ASSOC] THEN
  SUBGOAL_THEN `64 * k - bitsize n = 64 * d + c`
    (fun th -> REWRITE_TAC[th]) THEN
  EXPAND_TAC "c" THEN MATCH_MP_TAC(ARITH_RULE
   `b <= 64 * k /\ c <= 64 /\ 64 * k + c = 64 * (d + 1) + b
    ==> 64 * k - b = 64 * d + 64 - c`) THEN
  ASM_REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND] THEN
  ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; highdigits; BITSIZE_DIV] THEN
  MATCH_MP_TAC(ARITH_RULE `c:num <= b /\ a + b = c + d ==> a + b - c = d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_BITSIZE] THEN DISCH_THEN(K ALL_TAC) THEN
    TRANS_TAC LE_TRANS `2 EXP (64 * (k - 1))` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
    SUBST1_TAC(SYM(ASSUME `2 EXP (64 * d) * n = m`))] THEN
  REWRITE_TAC[BITSIZE_MULT] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC);;

let BIGNUM_NORMALIZE_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_normalize_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_normalize_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  2 EXP (64 * val k - bitsize n) * n /\
                  C_RETURN s = word(64 * val k - bitsize n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_normalize_tmc BIGNUM_NORMALIZE_CORRECT);;

let BIGNUM_NORMALIZE_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_normalize_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_normalize_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  2 EXP (64 * val k - bitsize n) * n /\
                  C_RETURN s = word(64 * val k - bitsize n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NORMALIZE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_normalize_windows_mc = define_from_elf
   "bignum_normalize_windows_mc" "x86/generic/bignum_normalize.obj";;

let bignum_normalize_windows_tmc = define_trimmed "bignum_normalize_windows_tmc" bignum_normalize_windows_mc;;

let BIGNUM_NORMALIZE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_normalize_windows_tmc) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),24))
            [(word pc,LENGTH bignum_normalize_windows_tmc);  (z,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_normalize_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  2 EXP (64 * val k - bitsize n) * n /\
                  WINDOWS_C_RETURN s = word(64 * val k - bitsize n))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_normalize_windows_tmc
    bignum_normalize_tmc BIGNUM_NORMALIZE_CORRECT);;

let BIGNUM_NORMALIZE_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_normalize_windows_mc) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),24))
            [(word pc,LENGTH bignum_normalize_windows_mc);  (z,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_normalize_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s =
                  2 EXP (64 * val k - bitsize n) * n /\
                  WINDOWS_C_RETURN s = word(64 * val k - bitsize n))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NORMALIZE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

