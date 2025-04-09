(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular doubling of bignums.                                              *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_moddouble.o";;
 ****)

let bignum_moddouble_mc =
  define_assert_from_elf "bignum_moddouble_mc" "arm/generic/bignum_moddouble.o"
[
  0xab1f0005;       (* arm_ADDS X5 X0 XZR *)
  0x54000300;       (* arm_BEQ (word 96) *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xeb1f03e4;       (* arm_NEGS X4 XZR *)
  0xf8646846;       (* arm_LDR X6 X2 (Register_Offset X4) *)
  0x93c8fcc8;       (* arm_EXTR X8 X6 X8 (rvalue (word 63)) *)
  0xf8646867;       (* arm_LDR X7 X3 (Register_Offset X4) *)
  0xfa070108;       (* arm_SBCS X8 X8 X7 *)
  0xf8246828;       (* arm_STR X8 X1 (Register_Offset X4) *)
  0xaa0603e8;       (* arm_MOV X8 X6 *)
  0x91002084;       (* arm_ADD X4 X4 (rvalue (word 8)) *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0xb5ffff05;       (* arm_CBNZ X5 (word 2097120) *)
  0xd37ffd08;       (* arm_LSR X8 X8 (rvalue (word 63)) *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xaa0003e5;       (* arm_MOV X5 X0 *)
  0xab1f03e4;       (* arm_ADDS X4 XZR XZR *)
  0xf8646826;       (* arm_LDR X6 X1 (Register_Offset X4) *)
  0xf8646867;       (* arm_LDR X7 X3 (Register_Offset X4) *)
  0x8a0800e7;       (* arm_AND X7 X7 X8 *)
  0xba0700c6;       (* arm_ADCS X6 X6 X7 *)
  0xf8246826;       (* arm_STR X6 X1 (Register_Offset X4) *)
  0x91002084;       (* arm_ADD X4 X4 (rvalue (word 8)) *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0xb5ffff25;       (* arm_CBNZ X5 (word 2097124) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MODDOUBLE_EXEC = ARM_MK_EXEC_RULE bignum_moddouble_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODDOUBLE_CORRECT = prove
 (`!k z x m a n pc.
        nonoverlapping (word pc,0x68) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_moddouble_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x64) /\
                  (a < n ==> bignum_from_memory (z,val k) s = (2 * a) MOD n))
             (MAYCHANGE [PC; X4; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** The combined double-and-subtract loop "dubloop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x10` `pc + 0x30`
    `\i s. read X0 s = word k /\
           read X1 s = z /\
           read X2 s = x /\
           read X3 s = m /\
           bignum_from_memory (m,k) s = n /\
           read X4 s = word(8 * i) /\
           read X5 s = word(k - i) /\
           (read X8 s = if i = 0 then word 0 else word(bigdigit a (i - 1))) /\
           bignum_from_memory (word_add x (word(8 * i)),k - i) s =
           highdigits a i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           &(bignum_from_memory(z,i) s):real =
           &2 pow (64 * i) * &(bitval(~read CF s)) +
           &(lowdigits (2 * a) i) - &(lowdigits n i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC BIGNUM_MODDOUBLE_EXEC [4] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
      REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
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
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODDOUBLE_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Masked addition operation "corrloop" ***)

  GHOST_INTRO_TAC `hi:bool` `read CF` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x44` `pc + 0x60`
    `\i s. read X0 s = word k /\
           read X1 s = z /\
           read X3 s = m /\
           read X4 s = word(8 * i) /\
           read X5 s = word(k - i) /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           (a < n
            ==> read X8 s = word_neg(word(bitval(2 * a < n))) /\
                &(bignum_from_memory(z,i) s):real =
                (&(lowdigits lo i) + &(bitval(2 * a < n)) * &(lowdigits n i)) -
                &2 pow (64 * i) * &(bitval(read CF s)))` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODDOUBLE_EXEC (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
     REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID] THEN
     DISCH_TAC THEN REWRITE_TAC[WORD_RULE
      `word_sub a b = word_neg c <=> word_add c a = b`] THEN
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
          &2 pow (64 * k) * &(bitval(~hi)) + &(lowdigits (2 * a) k) - &n` THEN
       UNDISCH_TAC `lo < 2 EXP (64 * k)` THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOOL_CASES_TAC `hi:bool` THEN
       ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
       REAL_ARITH_TAC;
       STRIP_TAC THEN AP_TERM_TAC THEN
       REWRITE_TAC[NOT_LT; TAUT `(p <=> ~q) <=> (~p <=> q)`] THEN
       CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN
       EXISTS_TAC `64 * k` THEN REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
       UNDISCH_THEN
        `&lo:real =
          &2 pow (64 * k) * &(bitval(~hi)) + &(lowdigits (2 * a) k) - &n`
        (SUBST1_TAC o SYM) THEN
       ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0]];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GHOST_INTRO_TAC `hi:int64` `read X8` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_ACCSTEPS_TAC BIGNUM_MODDOUBLE_EXEC [4] (1--7) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [CONV_TAC WORD_RULE;
       REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       DISCH_THEN(fun th ->
         REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
         ASSUME_TAC th) THEN
       ASM_REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
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
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODDOUBLE_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** The finale ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
  ASM_CASES_TAC `a:num < n` THEN ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODDOUBLE_EXEC [1] THEN
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

let BIGNUM_MODDOUBLE_SUBROUTINE_CORRECT = prove
 (`!k z x m a n pc returnaddress.
        nonoverlapping (word pc,0x68) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_moddouble_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  (a < n ==> bignum_from_memory (z,val k) s = (2 * a) MOD n))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MODDOUBLE_EXEC BIGNUM_MODDOUBLE_CORRECT);;
