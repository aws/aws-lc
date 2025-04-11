(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* "Optional subtraction" function, subtracting iff a flag is nonzero.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_optsub.o";;
 ****)

let bignum_optsub_mc =
  define_assert_from_elf "bignum_optsub_mc" "arm/generic/bignum_optsub.o"
[
  0xb40001a0;       (* arm_CBZ X0 (word 52) *)
  0xeb1f007f;       (* arm_CMP X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xeb1f03e7;       (* arm_NEGS X7 XZR *)
  0xf8676845;       (* arm_LDR X5 X2 (Register_Offset X7) *)
  0xf8676886;       (* arm_LDR X6 X4 (Register_Offset X7) *)
  0x8a0300c6;       (* arm_AND X6 X6 X3 *)
  0xfa0600a5;       (* arm_SBCS X5 X5 X6 *)
  0xf8276825;       (* arm_STR X5 X1 (Register_Offset X7) *)
  0x910020e7;       (* arm_ADD X7 X7 (rvalue (word 8)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffff20;       (* arm_CBNZ X0 (word 2097124) *)
  0x9a9f27e0;       (* arm_CSET X0 Condition_CC *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTSUB_EXEC = ARM_MK_EXEC_RULE bignum_optsub_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTSUB_CORRECT = prove
 (`!k z x p y m n pc.
        nonoverlapping (word pc,0x38) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optsub_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; x; p; y] s /\
                  bignum_from_memory (x,val k) s = m /\
                  bignum_from_memory (y,val k) s = n)
             (\s. read PC s = word (pc + 0x34) /\
                  (bignum_from_memory (z,val k) s =
                   if p = word 0 then m
                   else if n <= m then m - n
                   else (2 EXP (64 * val k) + m) - n) /\
                  (C_RETURN s =
                   if ~(p = word 0) /\ m < n then word 1 else word 0))
          (MAYCHANGE [PC; X0; X3; X5; X6; X7] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `b:int64`; `y:int64`;
    `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`m:num`; `n:num`] THEN

  (*** The trivial k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN RULE_ASSUM_TAC
     (REWRITE_RULE[ARITH_RULE `a < 2 EXP (64 * 0) <=> a = 0`]) THEN
    ARM_SIM_TAC BIGNUM_OPTSUB_EXEC [1] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[COND_ID];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `p <=> ~(b:int64 = word 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x10` `pc + 0x2c`
   `\i s. read X1 s = z /\
          read X2 s = x /\
          read X4 s = y /\
          read X7 s = word (8 * i) /\
          read X3 s = word_neg(word(bitval p)) /\
          read X0 s = word(k - i) /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits m i /\
          bignum_from_memory (word_add y (word(8 * i)),k - i) s =
          highdigits n i /\
          &(bignum_from_memory(z,i) s):real =
          &(lowdigits m i) - &(bitval p) * &(lowdigits n i) +
          &2 pow (64 * i) * &(bitval(~read CF s))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_OPTSUB_EXEC (1--4) THEN
    REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; VAL_WORD_0; VAL_EQ_0; WORD_ADD_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
    ASM_REWRITE_TAC[WORD_MASK] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k - i:num` THEN
    ARM_SIM_TAC BIGNUM_OPTSUB_EXEC [1];
    GHOST_INTRO_TAC `cout:bool` `read CF` THEN
    ARM_SIM_TAC BIGNUM_OPTSUB_EXEC (1--2) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `&(read (memory :> bytes (z,8 * k)) s2) =
      &(lowdigits m k) - &(bitval p) * &(lowdigits n k) +
      &2 pow (64 * k) * &(bitval (~cout))` THEN
    UNDISCH_THEN `~(b:int64 = word 0) <=> p` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    ASM_CASES_TAC `b:int64 = word 0` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [ASM_CASES_TAC `cout:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_MUL_RZERO; REAL_MUL_LZERO;
        REAL_ADD_LID; REAL_ADD_RID; REAL_SUB_RZERO] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND;
                   ARITH_RULE `a:num < e ==> ~(a = m + e * 1)`];
      REWRITE_TAC[GSYM NOT_LT; REAL_MUL_LID; COND_SWAP] THEN
      ASM_CASES_TAC `cout:bool` THEN
      ASM_SIMP_TAC[BITVAL_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THENL
       [DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `&x:real = m - n + p * &0 ==> ~(m < n)`)) THEN
        SIMP_TAC[] THEN
        SIMP_TAC[REAL_OF_NUM_CLAUSES; NOT_LT; REAL_OF_NUM_SUB] THEN ARITH_TAC;
        DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `&x:real = m - n + p * &1 ==> &x < p ==> m < n`)) THEN
        ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; GSYM BIGNUM_FROM_MEMORY_BYTES;
                     BIGNUM_FROM_MEMORY_BOUND] THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE
         `n:num < e ==> n <= e + m`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC]]] THEN

  (*** Proof of the main invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  ARM_ACCSIM_TAC BIGNUM_OPTSUB_EXEC [4] (1--7) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`];
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_CLAUSES]] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[WORD_AND_MASK] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
  ASM_REWRITE_TAC[VAL_WORD_BIGDIGIT; REAL_VAL_WORD_NOT; BITVAL_CLAUSES] THEN
  REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REAL_ARITH_TAC);;

let BIGNUM_OPTSUB_SUBROUTINE_CORRECT = prove
 (`!k z x p y m n pc returnaddress.
        nonoverlapping (word pc,0x38) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optsub_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; x; p; y] s /\
                  bignum_from_memory (x,val k) s = m /\
                  bignum_from_memory (y,val k) s = n)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,val k) s =
                   if p = word 0 then m
                   else if n <= m then m - n
                   else (2 EXP (64 * val k) + m) - n) /\
                  (C_RETURN s =
                   if ~(p = word 0) /\ m < n then word 1 else word 0))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTSUB_EXEC
    BIGNUM_OPTSUB_CORRECT);;
