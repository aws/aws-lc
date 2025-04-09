(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional addition of bignums.                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_optsubadd.o";;
 ****)

let bignum_optsubadd_mc =
  define_assert_from_elf "bignum_optsubadd_mc" "arm/generic/bignum_optsubadd.o"
[
  0xb4000240;       (* arm_CBZ X0 (word 72) *)
  0xeb1f007f;       (* arm_CMP X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xda9f53e5;       (* arm_CSETM X5 Condition_MI *)
  0xab0500bf;       (* arm_CMN X5 X5 *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xf8686887;       (* arm_LDR X7 X4 (Register_Offset X8) *)
  0xca0500e7;       (* arm_EOR X7 X7 X5 *)
  0xf8686846;       (* arm_LDR X6 X2 (Register_Offset X8) *)
  0x8a0300e7;       (* arm_AND X7 X7 X3 *)
  0xba0700c6;       (* arm_ADCS X6 X6 X7 *)
  0xf8286826;       (* arm_STR X6 X1 (Register_Offset X8) *)
  0x91002108;       (* arm_ADD X8 X8 (rvalue (word 8)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffff00;       (* arm_CBNZ X0 (word 2097120) *)
  0x9a1f03e0;       (* arm_ADC X0 XZR XZR *)
  0xcb0503e5;       (* arm_NEG X5 X5 *)
  0xca050000;       (* arm_EOR X0 X0 X5 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTSUBADD_EXEC = ARM_MK_EXEC_RULE bignum_optsubadd_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTSUBADD_CORRECT = prove
 (`!k z x p y a b pc.
        nonoverlapping (word pc,0x4c) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optsubadd_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read PC s = word(pc + 0x48) /\
                  &(bignum_from_memory(z,val k) s) =
                  (&a + int_sgn(ival p) * &b) rem &2 pow (64 * val k) /\
                  C_RETURN s =
                  iword(int_sgn(ival p) *
                        (&a + int_sgn(ival p) * &b) div &2 pow (64 * val k)))
             (MAYCHANGE [PC; X0; X3; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `p:int64`; `y:int64`;
    `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`] THEN

  (*** The trivial k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN RULE_ASSUM_TAC
    (REWRITE_RULE[ARITH_RULE `a < 2 EXP (64 * 0) <=> a = 0`]) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTSUBADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; MULT_CLAUSES; INT_POW] THEN
    REWRITE_TAC[INT_DIV_1; INT_REM_1; INT_MUL_RZERO; INT_ADD_LID] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `m <=> ~(p:int64 = word 0)` THEN
  ABBREV_TAC `q <=> bit 63 (p:int64)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x18` `pc + 0x38`
   `\i s. read X1 s = z /\
          read X2 s = x /\
          read X3 s = word_neg(word(bitval m)) /\
          read X5 s = word_neg(word(bitval q)) /\
          read X4 s = y /\
          read X0 s = word(k - i) /\
          read X8 s = word(8 * i) /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          bignum_from_memory (word_add y (word(8 * i)),k - i) s =
          highdigits b i /\
          &2 pow (64 * i) * &(bitval(read CF s)) +
          &(bignum_from_memory(z,i) s):int =
          &2 pow (64 * i) * &(bitval q) +
          &(lowdigits a i) +
          &(bitval m) * --(&1) pow bitval q * &(lowdigits b i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTSUBADD_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES;
                SUB_0; BITVAL_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; bitval; COND_SWAP] THEN
    ASM_REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k - i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTSUBADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTSUBADD_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; WORD_SUB_LZERO; WORD_NEG_NEG] THEN
    REWRITE_TAC[WORD_IWORD; WORD_BITWISE_RULE
     `word_xor x y = z <=> x = word_xor y z`] THEN
    FIRST_ASSUM(fun th ->
     MP_TAC(AP_TERM `\x. x rem &2 pow (64 * k)` th) THEN
     MP_TAC(AP_TERM `\x. x div &2 pow (64 * k)` th)) THEN
    SIMP_TAC[INT_REM_MUL_ADD; INT_DIV_MUL_ADD; INT_POW_EQ_0;
             INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_DIV; INT_OF_NUM_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_SELF] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM; GSYM
                INT_OF_NUM_DIV] THEN
    MATCH_MP_TAC(MESON[]
     `x = y /\ (x = y ==> p) ==> x rem n = y rem n /\ p`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_RING `x * y:int = z ==> a + x * y * b = a + z * b`) THEN
      MAP_EVERY EXPAND_TAC ["m"; "q"] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; EVEN_BITVAL] THEN
      ASM_CASES_TAC `p:int64 = word 0` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC[COND_SWAP; INT_MUL_LID] THEN CONV_TAC SYM_CONV THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_SGN_EQ] THEN
      REWRITE_TAC[INT_ARITH `p:int > &0 <=> ~(p = &0) /\ ~(p < &0)`] THEN
      ASM_REWRITE_TAC[IVAL_EQ_0] THEN
      ASM_REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH_RULE `64 - 1 = 63`];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[INT_SGN] THEN ASM_CASES_TAC `ival(p:int64) = &0` THENL
     [ASM_REWRITE_TAC[INT_LT_REFL; INT_MUL_LZERO; INT_ADD_RID] THEN
      ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_DIV; DIV_LT] THEN
      REWRITE_TAC[ADD_CLAUSES; GSYM WORD_IWORD] THEN
      CONV_TAC WORD_BITWISE_RULE;
      ASM_REWRITE_TAC[INT_ARITH `&0:int < p <=> ~(p = &0) /\ ~(p < &0)`]] THEN
    ASM_REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    SIMP_TAC[COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM WORD_IWORD; WORD_XOR_0; INT_ADD_LID; INT_MUL_LID] THEN
    REWRITE_TAC[INT_MUL_LNEG; INT_MUL_LID; GSYM INT_SUB] THEN
    SUBGOAL_THEN
     `(&a - &b) div &2 pow (64 * k) = -- &(bitval(a < b))`
    SUBST1_TAC THENL
     [SUBST1_TAC(INT_ARITH
       `&a - &b:int =
        &2 pow (64 * k) * --(&1) + &a + (&2 pow (64 * k) - &b)`) THEN
      SIMP_TAC[INT_DIV_MUL_ADD; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[INT_ARITH `--(&1) + x:int = --y <=> x = &1 - y`] THEN
      ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB;
                   BITVAL_BOUND; LT_IMP_LE; INT_OF_NUM_DIV] THEN
      MATCH_MP_TAC(ARITH_RULE
       `a <= 1 /\ b <= 1 /\ (a = 0 <=> b = 1) ==> a = 1 - b`) THEN
      REWRITE_TAC[BITVAL_BOUND; BITVAL_EQ_1] THEN
      SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH; LE_LDIV_EQ] THEN
      MAP_EVERY UNDISCH_TAC [`a < 2 EXP (64 * k)`; `b < 2 EXP (64 * k)`] THEN
      ARITH_TAC;
      REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
      CONV_TAC INT_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV]] THEN

  (*** Proof of the main invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BIGNUM_OPTSUBADD_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`];
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
  REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
   `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[WORD_XOR_MASK; WORD_AND_MASK] THEN
  UNDISCH_TAC `bit 63 (p:int64) <=> q` THEN
  UNDISCH_TAC `~(p:int64 = word 0) <=> m` THEN
  REWRITE_TAC[bitval] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0; MULT_CLAUSES] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; INT_VAL_WORD_NOT] THEN
  CONV_TAC WORD_REDUCE_CONV THEN INT_ARITH_TAC);;

let BIGNUM_OPTSUBADD_SUBROUTINE_CORRECT = prove
 (`!k z x p y a b pc returnaddress.
        nonoverlapping (word pc,0x4c) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optsubadd_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read PC s = returnaddress /\
                  &(bignum_from_memory(z,val k) s) =
                  (&a + int_sgn(ival p) * &b) rem &2 pow (64 * val k) /\
                  C_RETURN s =
                  iword(int_sgn(ival p) *
                        (&a + int_sgn(ival p) * &b) div &2 pow (64 * val k)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTSUBADD_EXEC BIGNUM_OPTSUBADD_CORRECT);;
