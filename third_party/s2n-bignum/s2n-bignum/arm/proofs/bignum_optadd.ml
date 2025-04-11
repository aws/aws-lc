(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional addition of bignums.                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_optadd.o";;
 ****)

let bignum_optadd_mc =
  define_assert_from_elf "bignum_optadd_mc" "arm/generic/bignum_optadd.o"
[
  0xb40001a0;       (* arm_CBZ X0 (word 52) *)
  0xeb1f007f;       (* arm_CMP X3 XZR *)
  0xda9f03e3;       (* arm_CSETM X3 Condition_NE *)
  0xab1f03e7;       (* arm_ADDS X7 XZR XZR *)
  0xf8676845;       (* arm_LDR X5 X2 (Register_Offset X7) *)
  0xf8676886;       (* arm_LDR X6 X4 (Register_Offset X7) *)
  0x8a0300c6;       (* arm_AND X6 X6 X3 *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0xf8276825;       (* arm_STR X5 X1 (Register_Offset X7) *)
  0x910020e7;       (* arm_ADD X7 X7 (rvalue (word 8)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffff20;       (* arm_CBNZ X0 (word 2097124) *)
  0x9a1f03e0;       (* arm_ADC X0 XZR XZR *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_OPTADD_EXEC = ARM_MK_EXEC_RULE bignum_optadd_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTADD_CORRECT = prove
 (`!k z x p y a b pc.
        nonoverlapping (word pc,0x38) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optadd_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read PC s = word(pc + 0x34) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (a + bitval(~(p = word 0)) * b) (val k) /\
                  C_RETURN s =
                  word(highdigits (a + bitval(~(p = word 0)) * b) (val k)))
             (MAYCHANGE [PC; X0; X3; X5; X6; X7] ,,
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `m <=> ~(p:int64 = word 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x10` `pc + 0x2c`
   `\i s. read X1 s = z /\
          read X2 s = x /\
          read X3 s = word_neg(word(bitval m)) /\
          read X4 s = y /\
          read X0 s = word(k - i) /\
          read X7 s = word(8 * i) /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          bignum_from_memory (word_add y (word(8 * i)),k - i) s =
          highdigits b i /\
          2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
          lowdigits a i + bitval m * lowdigits b i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTADD_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES;
                SUB_0; BITVAL_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; bitval; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `k - i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTADD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_OPTADD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_THEN
     `2 EXP (64 * k) * bitval cin + read (memory :> bytes (z,8 * k)) s2 =
      lowdigits a k + bitval m * lowdigits b k`
     (fun th -> MP_TAC(CONJ (AP_TERM `\x. lowdigits x k` th)
                            (AP_TERM `\x. highdigits x k` th))) THEN
    SIMP_TAC[lowdigits; highdigits; MOD_MULT_ADD; DIV_MULT_ADD;
             EXP_EQ_0; ARITH_EQ; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES]] THEN

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
  ARM_STEPS_TAC BIGNUM_OPTADD_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`];
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
  REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
   `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0; MULT_CLAUSES] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN ARITH_TAC);;

let BIGNUM_OPTADD_SUBROUTINE_CORRECT = prove
 (`!k z x p y a b pc returnaddress.
        nonoverlapping (word pc,0x38) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_optadd_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (a + bitval(~(p = word 0)) * b) (val k) /\
                  C_RETURN s =
                  word(highdigits (a + bitval(~(p = word 0)) * b) (val k)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_OPTADD_EXEC BIGNUM_OPTADD_CORRECT);;
