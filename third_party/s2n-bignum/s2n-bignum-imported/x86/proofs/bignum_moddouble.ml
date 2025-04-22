(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular doubling of bignums.                                              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_moddouble.o";;
 ****)

let bignum_moddouble_mc =
  define_assert_from_elf "bignum_moddouble_mc" "x86/generic/bignum_moddouble.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x55;              (* JE (Imm8 (word 85)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4e; 0x8b; 0x0c; 0xc2;  (* MOV (% r9) (Memop Quadword (%%% (rdx,3,r8))) *)
  0x4c; 0x0f; 0xac; 0xc8; 0x3f;
                           (* SHRD (% rax) (% r9) (Imm8 (word 63)) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4a; 0x1b; 0x04; 0xc1;  (* SBB (% rax) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x4a; 0x89; 0x04; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% rax) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x72; 0xde;              (* JB (Imm8 (word 222)) *)
  0x48; 0xc1; 0xe8; 0x3f;  (* SHR (% rax) (Imm8 (word 63)) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4e; 0x8b; 0x0c; 0xc1;  (* MOV (% r9) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x49; 0x21; 0xc1;        (* AND (% r9) (% rax) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4e; 0x13; 0x0c; 0xc6;  (* ADC (% r9) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x4e; 0x89; 0x0c; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% r9) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x72; 0xe3;              (* JB (Imm8 (word 227)) *)
  0xc3                     (* RET *)
];;

let bignum_moddouble_tmc = define_trimmed "bignum_moddouble_tmc" bignum_moddouble_mc;;

let BIGNUM_MODDOUBLE_EXEC = X86_MK_CORE_EXEC_RULE bignum_moddouble_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODDOUBLE_CORRECT = prove
 (`!k z x m a n pc.
        nonoverlapping (word pc,0x5b) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_moddouble_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k;z;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x5a) /\
                  (a < n ==> bignum_from_memory (z,val k) s = (2 * a) MOD n))
             (MAYCHANGE [RIP; RAX; R8; R9; R10] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `n:num`] THEN

  (*** Deal with degenerate case k = 0 first ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; MOD_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** The combined double-and-subtract loop "dubloop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xe` `pc + 0x2b`
    `\i s. read RDI s = word k /\
           read RSI s = z /\
           read RDX s = x /\
           read RCX s = m /\
           bignum_from_memory (m,k) s = n /\
           read R8 s = word i /\
           (read RAX s = if i = 0 then word 0 else word(bigdigit a (i - 1))) /\
           bignum_from_memory (word_add x (word(8 * i)),k - i) s =
           highdigits a i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           val(word_neg(read R10 s)) <= 1 /\
           &(bignum_from_memory(z,i) s):real =
           &2 pow (64 * i) * &(val(word_neg(read R10 s))) +
           &(lowdigits (2 * a) i) - &(lowdigits n i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
    REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LE_0] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read R10 s))` THEN
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
    X86_ACCSTEPS_TAC BIGNUM_MODDOUBLE_EXEC [4] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
    SIMP_TAC[GSYM WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
    MATCH_MP_TAC(REAL_RING
     `ee * y:real = w - z
      ==> --e * c + s = y ==> z + ee * s = (ee * e) * c + w`) THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ARITH
     `x - y:real = z <=> x = y + z`] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ARITH `(x:real) * &2 pow k = &2 pow k * x`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
     [REWRITE_TAC[ARITH_RULE `(2 EXP 64 * x) DIV 2 EXP 63 = 2 * x`] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `(highdigits a (i - 1) DIV 2 EXP 63) MOD 2 EXP 64` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 + 1 = i`; DIV_MOD] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `(a:num == a') (mod n)
        ==> (e * a + b == e * a' + b) (mod (n * e))`) THEN
      REWRITE_TAC[bigdigit; highdigits; CONG; MOD_MOD_EXP_MIN] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
      ASM_SIMP_TAC[bigdigit; EXP; DIV_MULT2; ARITH_EQ; ARITH_RULE
       `~(i = 0) ==> 64 * i = SUC(64 * (i - 1) + 63)`]];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Masked addition operation "corrloop" ***)

  GHOST_INTRO_TAC `hinn:num` `\s. val(word_neg(read R10 s))` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `hi:bool` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN
  REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x3d` `pc + 0x55`
    `\i s. read RDI s = word k /\
           read RSI s = z /\
           read RCX s = m /\
           read R8 s = word i /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           val(word_neg(read R10 s)) <= 1 /\
           (a < n
            ==> read RAX s = word_neg(word(bitval(2 * a < n))) /\
                &(bignum_from_memory(z,i) s):real =
                (&(lowdigits lo i) + &(bitval(2 * a < n)) * &(lowdigits n i)) -
                &2 pow (64 * i) * &(val(word_neg(read R10 s))))` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
     REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LE_0] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
     REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID] THEN
     DISCH_TAC THEN REWRITE_TAC[WORD_RULE
      `word_add a (word_neg b) = word_neg c <=> word_add c a = b`] THEN
     MP_TAC(GEN `x:int64` (ISPEC `x:int64` WORD_USHR_MSB)) THEN
     REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BITVAL; VAL_WORD_ADD_CASES] THEN
     SIMP_TAC[DIMINDEX_64; BITVAL_BOUND; ARITH_RULE
      `b <= 1 /\ c <= 1 ==> b + c < 2 EXP 64`] THEN
     SUBGOAL_THEN `2 * a < 2 * n /\ 2 * a < 2 * 2 EXP (64 * k)` MP_TAC THENL
      [ASM_REWRITE_TAC[LT_MULT_LCANCEL; ARITH_EQ]; ALL_TAC] THEN
     SUBGOAL_THEN
      `2 * a = 2 EXP (64 * k) *
               bitval(bit 63 (word(bigdigit a (k - 1)):int64)) +
               lowdigits (2 * a) k`
     SUBST1_TAC THENL
      [MP_TAC(SPECL [`2 * a`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
       DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
       AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
       MP_TAC(ISPEC `word(bigdigit a (k - 1)):int64` WORD_USHR_MSB) THEN
       REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       DISCH_THEN(MP_TAC o SYM o AP_TERM `val:int64->num`) THEN
       REWRITE_TAC[VAL_WORD_BITVAL; VAL_WORD_USHR] THEN
       DISCH_THEN SUBST1_TAC THEN
       SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
       ASM_SIMP_TAC[highdigits; ARITH_RULE
        `~(k = 0) ==> 64 * k = SUC(64 * (k - 1) + 63)`] THEN
       SIMP_TAC[DIV_MULT2; EXP; ARITH_EQ] THEN
       REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       REWRITE_TAC[bigdigit] THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC MOD_LT THEN
       ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
       ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 * (k - 1) + 64 = 64 * k`];
       ALL_TAC] THEN
     ASM_CASES_TAC `bit 63 (word(bigdigit a (k - 1)):int64)` THEN
     ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
      [ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ~(e + a < n)`] THEN
       UNDISCH_TAC
        `&lo:real =
          &2 pow (64 * k) * &(bitval hi) + &(lowdigits (2 * a) k) - &n` THEN
       UNDISCH_TAC `lo < 2 EXP (64 * k)` THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOOL_CASES_TAC `hi:bool` THEN
       ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
       REAL_ARITH_TAC;
       STRIP_TAC THEN AP_TERM_TAC THEN
       CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
       EXISTS_TAC `64 * k` THEN REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
       UNDISCH_THEN
        `&lo:real =
          &2 pow (64 * k) * &(bitval hi) + &(lowdigits (2 * a) k) - &n`
        (SUBST1_TAC o SYM) THEN
       ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0]];

     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read R10 s))` THEN
     GLOBALIZE_PRECONDITION_TAC THEN
     FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
       GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
     REWRITE_TAC[VAL_EQ_BITVAL] THEN
     REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
     GHOST_INTRO_TAC `hi:int64` `read RAX` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_ACCSTEPS_TAC BIGNUM_MODDOUBLE_EXEC [4] (1--7) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     SIMP_TAC[GSYM WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
     DISCH_THEN(fun th ->
       REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
       ASSUME_TAC th) THEN
     ASM_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
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
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** The finale ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
  ASM_CASES_TAC `a:num < n` THEN ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_ADD_CASES; MULT_2; ARITH_RULE
   `a < n ==> a + a < 2 * n`] THEN
  REWRITE_TAC[GSYM MULT_2] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LE_0; BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a:num < n`; `n < 2 EXP (64 * k)`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_FIELD `inv(&2 pow n) * &2 pow n = (&1:real)`] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  REWRITE_TAC[REAL_ARITH
   `--(&2) * e * a + e * b + c:real = e * (b - &2 * a) + c`] THEN
  MATCH_MP_TAC INTEGER_ADD THEN
  (CONJ_TAC THENL [ALL_TAC; REAL_INTEGER_TAC]) THEN
  REWRITE_TAC[REAL_ARITH `inv x * (a - b):real = (a - b) / x`] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_CONGRUENCE o snd) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let BIGNUM_MODDOUBLE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z x m a n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_moddouble_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_moddouble_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < n ==> bignum_from_memory (z,val k) s = (2 * a) MOD n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_moddouble_tmc BIGNUM_MODDOUBLE_CORRECT);;

let BIGNUM_MODDOUBLE_SUBROUTINE_CORRECT = prove
 (`!k z x m a n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_moddouble_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_moddouble_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < n ==> bignum_from_memory (z,val k) s = (2 * a) MOD n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODDOUBLE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_moddouble_windows_mc = define_from_elf
   "bignum_moddouble_windows_mc" "x86/generic/bignum_moddouble.obj";;

let bignum_moddouble_windows_tmc = define_trimmed "bignum_moddouble_windows_tmc" bignum_moddouble_windows_mc;;

let BIGNUM_MODDOUBLE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x m a n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_moddouble_windows_tmc); (x,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_moddouble_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_moddouble_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < n ==> bignum_from_memory (z,val k) s = (2 * a) MOD n))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_moddouble_windows_tmc bignum_moddouble_tmc
    BIGNUM_MODDOUBLE_CORRECT);;

let BIGNUM_MODDOUBLE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x m a n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_moddouble_windows_mc); (x,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_moddouble_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_moddouble_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < n ==> bignum_from_memory (z,val k) s = (2 * a) MOD n))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODDOUBLE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

