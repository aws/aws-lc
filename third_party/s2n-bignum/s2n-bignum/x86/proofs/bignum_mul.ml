(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication.                                                           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_mul.o";;
 ****)

let bignum_mul_mc =
  define_assert_from_elf "bignum_mul_mc" "x86/generic/bignum_mul.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x64;              (* JE (Imm8 (word 100)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x49; 0x0f; 0x42; 0xc7;  (* CMOVB (% rax) (% r15) *)
  0x48; 0x89; 0xeb;        (* MOV (% rbx) (% rbp) *)
  0x49; 0x39; 0xea;        (* CMP (% r10) (% rbp) *)
  0x49; 0x0f; 0x42; 0xda;  (* CMOVB (% rbx) (% r10) *)
  0x4c; 0x89; 0xd2;        (* MOV (% rdx) (% r10) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x48; 0x29; 0xc3;        (* SUB (% rbx) (% rax) *)
  0x76; 0x24;              (* JBE (Imm8 (word 36)) *)
  0x4c; 0x8d; 0x24; 0xc1;  (* LEA (% r12) (%%% (rcx,3,rax)) *)
  0x4d; 0x8d; 0x5c; 0xd1; 0xf8;
                           (* LEA (% r11) (%%%% (r9,3,rdx,-- &8)) *)
  0x49; 0x8b; 0x04; 0xdb;  (* MOV (% rax) (Memop Quadword (%%% (r11,3,rbx))) *)
  0x49; 0xf7; 0x24; 0x24;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (r12,0))) *)
  0x49; 0x83; 0xc4; 0x08;  (* ADD (% r12) (Imm8 (word 8)) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x75; 0xe5;              (* JNE (Imm8 (word 229)) *)
  0x4c; 0x89; 0x2e;        (* MOV (Memop Quadword (%% (rsi,0))) (% r13) *)
  0x4d; 0x89; 0xf5;        (* MOV (% r13) (% r14) *)
  0x4d; 0x89; 0xfe;        (* MOV (% r14) (% r15) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
  0x49; 0x39; 0xfa;        (* CMP (% r10) (% rdi) *)
  0x72; 0xa5;              (* JB (Imm8 (word 165)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_mul_tmc = define_trimmed "bignum_mul_tmc" bignum_mul_mc;;

let BIGNUM_MUL_EXEC = X86_MK_CORE_EXEC_RULE bignum_mul_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUL_CORRECT = prove
 (`!p m n z x y a b pc.
     ALL (nonoverlapping (z,8 * val p))
         [(word pc,0x81); (x,8 * val m); (y,8 * val n)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST bignum_mul_tmc) /\
               read RIP s = word(pc + 0xa) /\
               C_ARGUMENTS [p; z; m; x; n; y] s /\
               bignum_from_memory(x,val m) s = a /\
               bignum_from_memory(y,val n) s = b)
          (\s. read RIP s = word (pc + 0x76) /\
               bignum_from_memory(z,val p) s = lowdigits (a * b) (val p))
          (MAYCHANGE [RIP; R10; R11; R12; R13; R14; R15;
                      RAX; RBP; RBX; RDI; RDX; RSI] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,val p)])`,
  MAP_EVERY W64_GEN_TAC [`p:num`; `m:num`; `n:num`] THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_RANGE_TAC "m" "a" THEN
  BIGNUM_RANGE_TAC "n" "b" THEN

  (*** Degenerate case when output size is zero ***)

  ASM_CASES_TAC `p = 0` THENL
   [X86_SIM_TAC BIGNUM_MUL_EXEC (1--3) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0];
    ALL_TAC] THEN

  (*** Get basic bbounds from the nonoverlapping assumptions ***)

  SUBGOAL_THEN
   `8 * p < 2 EXP 64 /\ 8 * m < 2 EXP 64 /\ 8 * n < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th ->
      try MP_TAC
       (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2) th)
      with Failure _ -> ALL_TAC) THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Setup of the outer loop ***)

  ENSURES_WHILE_UP_TAC `p:num` `pc + 0x1b` `pc + 0x71`
   `\k s. read RDI s = word p /\
          read RSI s = word_add z (word(8 * k)) /\
          read RBP s = word m /\
          read RCX s = x /\
          read  R8 s = word n /\
          read  R9 s = y /\
          read R10 s = word k /\
          bignum_from_memory (x,m) s = a /\
          bignum_from_memory (y,n) s = b /\
          2 EXP (64 * k) * (2 EXP 64 * val(read R14 s) + val(read R13 s)) +
          bignum_from_memory(z,k) s =
          nsum {i,j | i < m /\ j < n /\ i + j < k}
            (\(i,j). 2 EXP (64 * (i + j)) * bigdigit a i * bigdigit b j)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_MUL_EXEC (1--6) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[VAL_WORD_0; CONJUNCT1 LT; MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
    REWRITE_TAC[SET_RULE `{(i,j) | F} = {}`; NSUM_CLAUSES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; WORD_ADD_0; SUB_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
    REWRITE_TAC[LOWDIGITS_0; ADD_CLAUSES];
    ALL_TAC; (*** This is the main loop invariant ***)
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k:num` THEN
    X86_SIM_TAC BIGNUM_MUL_EXEC (1--2);
    GHOST_INTRO_TAC `cout:int64` `read R13` THEN
    X86_SIM_TAC BIGNUM_MUL_EXEC (1--2) THEN
    MP_TAC(SPECL [`b:num`; `n:num`] BIGDIGITSUM_WORKS) THEN
    MP_TAC(SPECL [`a:num`; `m:num`] BIGDIGITSUM_WORKS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[GSYM NSUM_RMUL] THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
    SIMP_TAC[NSUM_NSUM_PRODUCT; FINITE_NUMSEG_LT] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `(e * a) * (f * b):num = (e * f) * a * b`] THEN
    REWRITE_TAC[lowdigits; GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC(MESON[MOD_LT]
     `x < n /\ x MOD n = y MOD n ==> x = y MOD n`) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; IN_ELIM_THM; GSYM CONG] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `n * q + y:num = a ==> (z == a) (mod n) ==> (y == z) (mod n)`)) THEN
    REWRITE_TAC[CONG] THEN
    REPLICATE_TAC 2
     (W(MP_TAC o PART_MATCH (lhand o rand) MOD_NSUM_MOD o lhand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{i:num | i < m} CROSS {i:num | i < n}` THEN
        REWRITE_TAC[FINITE_CROSS_EQ; FINITE_NUMSEG_LT] THEN
        REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS] THEN
        SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN SIMP_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[NOT_LT] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM DIVIDES_MOD] THEN MATCH_MP_TAC DIVIDES_RMUL THEN
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL]] THEN

  (*** The main outer loop invariant ***)

  X_GEN_TAC `k:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k:num` THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN
   `!f. nsum {i,j | i < m /\ j < n /\ i + j < k + 1} f =
        nsum {i,j | i < m /\ j < n /\ i + j < k} f +
        nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) m} (\i. f(i,k - i))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN X_GEN_TAC `f:num#num->num` THEN
    REWRITE_TAC[ARITH_RULE `i < k + 1 <=> i < k \/ i = k`] THEN
    REWRITE_TAC[LEFT_OR_DISTRIB; SET_RULE
     `{f x y | P x y \/ Q x y} = {f x y | P x y} UNION {f x y | Q x y}`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NSUM_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{i:num | i < m} CROSS {i:num | i < n}` THEN
          REWRITE_TAC[FINITE_CROSS_EQ; FINITE_NUMSEG_LT]) THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
                  DISJOINT; EXTENSION; IN_INTER] THEN
      SIMP_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC] THEN

    MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC `FST:num#num->num` THEN EXISTS_TAC `\i:num. i,k - i` THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
   `lowsum = nsum {i,j | i < m /\ j < n /\ i + j < k}
           (\(i,j). 2 EXP (64 * (i + j)) * bigdigit a i * bigdigit b j)` THEN

  GHOST_INTRO_TAC `zsum:num` `bignum_from_memory(z,k)` THEN
  GHOST_INTRO_TAC `h:num` `\s. val(read R14 s)` THEN
  GHOST_INTRO_TAC `l:num` `\s. val(read R13 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0x35`
   `\s. read RDI s = word p /\
        read RSI s = word_add z (word(8 * k)) /\
        read RBP s = word m /\
        read RCX s = x /\
        read  R8 s = word n /\
        read  R9 s = y /\
        read R10 s = word (k + 1) /\
        read RAX s = word ((k + 1) - n) /\
        read RBX s = word (MIN (k + 1) m) /\
        bignum_from_memory (x,m) s = a /\
        bignum_from_memory (y,n) s = b /\
        bignum_from_memory (z,k) s = zsum /\
        read R15 s = word 0 /\
        read R14 s = word h /\
        read R13 s = word l` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_MUL_EXEC (1--8) THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    VAL_INT64_TAC `k + 1` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_SUB; GSYM NOT_LT; COND_SWAP] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN COND_CASES_TAC THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** Separate and handle the final add/writeback to z ***)

  ENSURES_SEQUENCE_TAC `pc + 0x64`
   `\s. read RDI s = word p /\
        read RSI s = word_add z (word (8 * k)) /\
        read RBP s = word m /\
        read RCX s = x /\
        read R8 s = word n /\
        read R9 s = y /\
        read R10 s = word (k + 1) /\
        bignum_from_memory (x,m) s = a /\
        bignum_from_memory (y,n) s = b /\
        bignum_from_memory (z,k) s = zsum /\
        2 EXP 128 * val(read R15 s) +
        2 EXP 64 * val(read R14 s) + val(read R13 s) =
        (2 EXP 64 * h + l) +
        nsum {i | (k + 1) - n <= i /\ i < MIN (k + 1) m}
             (\i. bigdigit a i * bigdigit b (k - i))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `c':num` `\s. val(read R15 s)` THEN
    GHOST_INTRO_TAC `h':num` `\s. val(read R14 s)` THEN
    GHOST_INTRO_TAC `l':num` `\s. val(read R13 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC BIGNUM_MUL_EXEC (1--4) THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; GSYM WORD_ADD] THEN
    REWRITE_TAC[ARITH_RULE `64 * (k + 1) = 64 * k + 64`; EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE
     `(e * 2 EXP 64) * (2 EXP 64 * c' + h') + zsum + e * l' =
      e * (2 EXP 128 * c' + 2 EXP 64 * h' + l') + zsum`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE
     `e * ((a + a') + b) + c:num = (e * (a + a') + c) + e * b`] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `i < MIN (k + 1) m` THEN ARITH_TAC] THEN

 (*** Case split to trivialize the "no terms in sum" case ***)

  ASM_CASES_TAC `MIN (k + 1) m <= (k + 1) - n` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE
     `b:num <= a ==> !c. ~(a <= c /\ c < b)`) th]) THEN
    REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES; ADD_CLAUSES] THEN
    X86_SIM_TAC BIGNUM_MUL_EXEC (1--4) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_0] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM LE_LT] THEN
    MAP_EVERY VAL_INT64_TAC [`MIN (k + 1) m`; `(k + 1) - n`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Setup of the inner loop ***)

  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
  ENSURES_WHILE_PAUP_TAC `(k + 1) - n` `MIN (k + 1) m` `pc + 0x49` `pc + 0x62`
   `\i s. (read RDI s = word p /\
           read RSI s = word_add z (word (8 * k)) /\
           read RBP s = word m /\
           read RCX s = x /\
           read R8 s = word n /\
           read R9 s = y /\
           read R10 s = word (k + 1) /\
           bignum_from_memory (x,m) s = a /\
           bignum_from_memory (y,n) s = b /\
           bignum_from_memory (z,k) s = zsum /\
           read RBX s = word (MIN (k + 1) m - i) /\
           read R11 s =
           word_add y (word(8 * ((k + 1) - MIN (k + 1) m) + (2 EXP 64 - 8))) /\
           read R12 s = word_add x (word(8 * i)) /\
           2 EXP 128 * val (read R15 s) +
           2 EXP 64 * val (read R14 s) +
           val (read R13 s) =
           (2 EXP 64 * h + l) +
           nsum {j | (k + 1) - n <= j /\ j < i}
                (\j. bigdigit a j * bigdigit b (k - j))) /\
          (read ZF s <=> i = MIN (k + 1) m)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC BIGNUM_MUL_EXEC (1--4) THEN
    FIND_ASM_THEN lhand `read RIP s4` MP_TAC THEN
    MAP_EVERY VAL_INT64_TAC [`MIN (k + 1) m`; `(k + 1) - n`] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM LE_LT] THEN DISCH_TAC THEN
    X86_STEPS_TAC BIGNUM_MUL_EXEC (5--6) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[LET_ANTISYM; EMPTY_GSPEC; NSUM_CLAUSES] THEN
    ASM_SIMP_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_EQ;
                 DIMINDEX_64] THEN
    REWRITE_TAC[WORD_ADD; LEFT_SUB_DISTRIB] THEN
    MAP_EVERY ABBREV_TAC [`d = MIN (k + 1) m`; `e = (k + 1) - n`] THEN
    ONCE_REWRITE_TAC[WORD_SUB] THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[ARITH_RULE `8 * MIN a b <= 8 * a`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_RULE;
    ALL_TAC; (*** The inner loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC BIGNUM_MUL_EXEC [1];
    X86_SIM_TAC BIGNUM_MUL_EXEC [1]] THEN

  (*** The main inner loop invariant ***)

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `c':num` `\s. val(read R15 s)` THEN
  GHOST_INTRO_TAC `h':num` `\s. val(read R14 s)` THEN
  GHOST_INTRO_TAC `l':num` `\s. val(read R13 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[NUM_REDUCE_CONV `2 EXP 64 - 8`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  SUBGOAL_THEN
   `word((8 * ((k + 1) - MIN (k + 1) m) + 18446744073709551608) +
         8 * val(word(MIN (k + 1) m - j):int64)):int64 =
    word(8 * (k - j))`
  ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_ADD; WORD_SUB] THEN
    SUBGOAL_THEN `8 * j <= 8 * k` MP_TAC THENL
     [UNDISCH_TAC `j < MIN (k + 1) m` THEN ARITH_TAC;
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE] THEN DISCH_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * MIN a b <= 8 * a`] THEN
    SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_neg(word 8):int64`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add y (word (8 * (k - j))))) s0 =
    word(bigdigit b (k - j)) /\
    read (memory :> bytes64 (word_add x (word (8 * j)))) s0 =
    word(bigdigit a j)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    MAP_EVERY UNDISCH_TAC
     [`j < MIN (k + 1) m`; `(k + 1) - n <= j`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[WORD_VAL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC BIGNUM_MUL_EXEC [2;4;5;6] (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  ONCE_REWRITE_TAC[WORD_SUB] THEN
  ASM_SIMP_TAC[LT_IMP_LE; ARITH_RULE `j + 1 <= n <=> j < n`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    ALL_TAC;
    REWRITE_TAC[VAL_EQ_0; WORD_RULE
     `word_sub (word_sub x (word j)) (word k) = word_sub x (word(j + k))`] THEN
    REWRITE_TAC[WORD_SUB_EQ_0] THEN GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC [`m < 2 EXP 64`; `j < MIN (k + 1) m`] THEN
    ARITH_TAC] THEN

  SUBGOAL_THEN
   `{i | (k + 1) - n <= i /\ i < j + 1} =
    j INSERT {i | (k + 1) - n <= i /\ i < j}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    UNDISCH_TAC `(k + 1) - n <= j` THEN ARITH_TAC;
    ALL_TAC] THEN

  W(MP_TAC o PART_MATCH (lhand o rand) (CONJUNCT2 NSUM_CLAUSES) o
    rand o rand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < j}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN

  GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `a + b + c:num = b + a + c`] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`192`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE
     `ab < 2 EXP 64 * 2 EXP 64 /\ h < 2 EXP 64 /\ l < 2 EXP 64 /\
      s <= (2 EXP 64 - 1) * (2 EXP 64 - 1) EXP 2
      ==> ab + (2 EXP 64 * h + l) + s < 2 EXP 192`) THEN
    ASM_SIMP_TAC[BIGDIGIT_BOUND; LT_MULT2] THEN
    TRANS_TAC LE_TRANS
     `nsum {n | n < 2 EXP 64 - 1} (\i. bigdigit a i * bigdigit b (k - i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      MAP_EVERY UNDISCH_TAC [`j < MIN (k + 1) m`; `m < 2 EXP 64`] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM CARD_NUMSEG_LT] THEN
      MATCH_MP_TAC NSUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG_LT; EXP_2] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
      REWRITE_TAC[ARITH_RULE `x <= 2 EXP 64 - 1 <=> x < 2 EXP 64`] THEN
      REWRITE_TAC[BIGDIGIT_BOUND]];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MUL_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p m n z x y a b pc stackpointer returnaddress.
     nonoverlapping (z,8 * val p) (word_sub stackpointer (word 48),56) /\
     ALLPAIRS nonoverlapping
              [(z,8 * val p); (word_sub stackpointer (word 48),56)]
              [(word pc,LENGTH bignum_mul_tmc); (x,8 * val m); (y,8 * val n)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [p; z; m; x; n; y] s /\
               bignum_from_memory (x,val m) s = a /\
               bignum_from_memory (y,val n) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,val p) s =
               lowdigits (a * b) (val p))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val p);
                      memory :> bytes(word_sub stackpointer (word 48),56)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_mul_tmc BIGNUM_MUL_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MUL_SUBROUTINE_CORRECT = prove
 (`!p m n z x y a b pc stackpointer returnaddress.
     nonoverlapping (z,8 * val p) (word_sub stackpointer (word 48),56) /\
     ALLPAIRS nonoverlapping
              [(z,8 * val p); (word_sub stackpointer (word 48),56)]
              [(word pc,LENGTH bignum_mul_mc); (x,8 * val m); (y,8 * val n)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [p; z; m; x; n; y] s /\
               bignum_from_memory (x,val m) s = a /\
               bignum_from_memory (y,val n) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,val p) s =
               lowdigits (a * b) (val p))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val p);
                      memory :> bytes(word_sub stackpointer (word 48),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUL_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mul_windows_mc = define_from_elf
   "bignum_mul_windows_mc" "x86/generic/bignum_mul.obj";;

let bignum_mul_windows_tmc = define_trimmed "bignum_mul_windows_tmc" bignum_mul_windows_mc;;

let BIGNUM_MUL_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p m n z x y a b pc stackpointer returnaddress.
     nonoverlapping (z,8 * val p) (word_sub stackpointer (word 64),72) /\
     ALLPAIRS nonoverlapping
              [(z,8 * val p); (word_sub stackpointer (word 64),72)]
              [(word pc,LENGTH bignum_mul_windows_tmc); (x,8 * val m); (y,8 * val n)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [p; z; m; x; n; y] s /\
               bignum_from_memory (x,val m) s = a /\
               bignum_from_memory (y,val n) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,val p) s =
               lowdigits (a * b) (val p))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val p);
                      memory :> bytes(word_sub stackpointer (word 64),72)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_mul_windows_tmc bignum_mul_tmc
    BIGNUM_MUL_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MUL_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p m n z x y a b pc stackpointer returnaddress.
     nonoverlapping (z,8 * val p) (word_sub stackpointer (word 64),72) /\
     ALLPAIRS nonoverlapping
              [(z,8 * val p); (word_sub stackpointer (word 64),72)]
              [(word pc,LENGTH bignum_mul_windows_mc); (x,8 * val m); (y,8 * val n)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_mul_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [p; z; m; x; n; y] s /\
               bignum_from_memory (x,val m) s = a /\
               bignum_from_memory (y,val n) s = b)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               bignum_from_memory (z,val p) s =
               lowdigits (a * b) (val p))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val p);
                      memory :> bytes(word_sub stackpointer (word 64),72)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUL_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

