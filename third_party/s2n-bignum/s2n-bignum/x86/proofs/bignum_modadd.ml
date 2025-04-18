(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular addition of bignums.                                              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_modadd.o";;
 ****)

let bignum_modadd_mc =
  define_assert_from_elf "bignum_modadd_mc" "x86/generic/bignum_modadd.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x5a;              (* JE (Imm8 (word 90)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x49; 0x89; 0xfa;        (* MOV (% r10) (% rdi) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4a; 0x8b; 0x04; 0xca;  (* MOV (% rax) (Memop Quadword (%%% (rdx,3,r9))) *)
  0x4a; 0x13; 0x04; 0xc9;  (* ADC (% rax) (Memop Quadword (%%% (rcx,3,r9))) *)
  0x4a; 0x89; 0x04; 0xce;  (* MOV (Memop Quadword (%%% (rsi,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xfa;        (* MOV (% r10) (% rdi) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4a; 0x8b; 0x04; 0xce;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r9))) *)
  0x4b; 0x1b; 0x04; 0xc8;  (* SBB (% rax) (Memop Quadword (%%% (r8,3,r9))) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4b; 0x8b; 0x04; 0xc8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r9))) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4a; 0x19; 0x04; 0xce;  (* SBB (Memop Quadword (%%% (rsi,3,r9))) (% rax) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xe7;              (* JB (Imm8 (word 231)) *)
  0xc3                     (* RET *)
];;

let bignum_modadd_tmc = define_trimmed "bignum_modadd_tmc" bignum_modadd_mc;;

let BIGNUM_MODADD_EXEC = X86_MK_CORE_EXEC_RULE bignum_modadd_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODADD_CORRECT = prove
 (`!k z x y m a b n pc.
        nonoverlapping (word pc,0x60) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_modadd_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x5f) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RIP; RAX; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`;` n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN

  (*** Deal with degenerate case k = 0 first ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; ADD_CLAUSES; MOD_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64) (pc,96) (val(z:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** First addition, addloop ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0xe` `pc + 0x20`
    `\i s. (read RDI s = word k /\
            read RSI s = z /\
            read RDX s = x /\
            read RCX s = y /\
            read R8 s = m /\
            bignum_from_memory (m,k) s = n /\
            read R9 s = word i /\
            read R10 s = word(k - i) /\
            read R11 s = word 0 /\
            bignum_from_memory (word_add x (word(8 * i)),k - i) s =
            highdigits a i /\
            bignum_from_memory (word_add y (word(8 * i)),k - i) s =
            highdigits b i /\
            2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
            lowdigits a i + lowdigits b i) /\
           (read ZF s <=> i = k)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_ACCSTEPS_TAC BIGNUM_MODADD_EXEC [2] (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES];
       REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
       VAL_INT64_TAC `k - i:num` THEN
       ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN ARITH_TAC] THEN
     ONCE_REWRITE_TAC[ARITH_RULE
      `(a' + a) + (b' + b):num = (a' + b') + a + b`] THEN
     FIRST_X_ASSUM(fun th ->
       GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; EXP_ADD] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Comparison operation "cmploop" ***)

  GHOST_INTRO_TAC `hi:bool` `read CF` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x2c` `pc + 0x3a`
    `\i s. (read RDI s = word k /\
            read RSI s = z /\
            read R8 s = m /\
            bignum_from_memory (z,k) s = lo /\
            bignum_from_memory (m,k) s = n /\
            read R9 s = word i /\
            read R10 s = word(k - i) /\
            read R11 s = word(bitval hi) /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits lo i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            (read CF s <=> lowdigits lo i < lowdigits n i)) /\
           (read ZF s <=> i = k)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; LT_REFL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES];
       REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
       VAL_INT64_TAC `k - i:num` THEN
       ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN ARITH_TAC] THEN
     SIMP_TAC[LEXICOGRAPHIC_LT; LOWDIGITS_BOUND] THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Masked subtraction operation "subloop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x46` `pc + 0x5a`
    `\i s. read RDI s = word k /\
           read RSI s = z /\
           read R8 s = m /\
           read R9 s = word i /\
           val(word_neg(read R10 s)) <= 1 /\
           read R11 s = word_neg(word(bitval(n <= a + b))) /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           &(bignum_from_memory(z,i) s):real =
           &2 pow (64 * i) * &(val(word_neg(read R10 s))) +
           &(lowdigits lo i) - &(bitval(n <= a + b)) * &(lowdigits n i)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; LE_0] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     SUBGOAL_THEN
      `n <= a + b <=>
       2 EXP (64 * k) * 0 + n <= 2 EXP (64 * k) * bitval hi + lo`
     SUBST1_TAC THENL
      [ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES];
       ASM_SIMP_TAC[LEXICOGRAPHIC_LE; EXP_LT_0; ARITH_EQ; GSYM NOT_LE]] THEN
     MAP_EVERY ASM_CASES_TAC [`hi:bool`; `n:num <= lo`] THEN
     ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
     CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP (ARITH_RULE
      `e * c + lo:num = a + b
       ==> !n. e * 1 <= e * c /\ n < e /\ n <= lo /\ a < n /\ b < n
               ==> F`)) THEN
     ASM_REWRITE_TAC[BITVAL_CLAUSES; LE_REFL];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read R10 s))` THEN
     GLOBALIZE_PRECONDITION_TAC THEN
     FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
       GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
     REWRITE_TAC[VAL_EQ_BITVAL] THEN
     REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_ACCSTEPS_TAC BIGNUM_MODADD_EXEC [4] (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                 LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
     REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
              BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
     REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** The finale ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; BIGNUM_FROM_MEMORY_BOUND; LE_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; INTEGER_CLOSED] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`a:num < n`; `b:num < n`; `n < 2 EXP (64 * k)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `2 EXP (64 * k) * bitval hi + lo = a + b` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; GSYM REAL_OF_NUM_CLAUSES]] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `e * c + lo:real = a + b ==> lo = e * --c + a + b`)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
  REWRITE_TAC[REAL_FIELD
   `(&2 pow e * h + l) / &2 pow e = h + l / &2 pow e`] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MODADD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modadd_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_modadd_tmc BIGNUM_MODADD_CORRECT);;

let BIGNUM_MODADD_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modadd_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODADD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_modadd_windows_mc = define_from_elf
   "bignum_modadd_windows_mc" "x86/generic/bignum_modadd.obj";;

let bignum_modadd_windows_tmc = define_trimmed "bignum_modadd_windows_tmc" bignum_modadd_windows_mc;;

let BIGNUM_MODADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modadd_windows_tmc); (x,8 * val k); (y,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modadd_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_modadd_windows_tmc bignum_modadd_tmc
    BIGNUM_MODADD_CORRECT);;

let BIGNUM_MODADD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modadd_windows_mc); (x,8 * val k); (y,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modadd_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

