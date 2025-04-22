(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equality test on bignums.                                                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_eq.o";;
 ****)

let bignum_eq_mc = define_assert_from_elf "bignum_eq_mc" "arm/generic/bignum_eq.o"
[
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0x54000162;       (* arm_BCS (word 44) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xf8627864;       (* arm_LDR X4 X3 (Shiftreg_Offset X2 3) *)
  0xaa0400a5;       (* arm_ORR X5 X5 X4 *)
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0x54ffff81;       (* arm_BNE (word 2097136) *)
  0x14000006;       (* arm_B (word 24) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf8607824;       (* arm_LDR X4 X1 (Shiftreg_Offset X0 3) *)
  0xaa0400a5;       (* arm_ORR X5 X5 X4 *)
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0x54ffff81;       (* arm_BNE (word 2097136) *)
  0xb40000e0;       (* arm_CBZ X0 (word 28) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf8607824;       (* arm_LDR X4 X1 (Shiftreg_Offset X0 3) *)
  0xf8607862;       (* arm_LDR X2 X3 (Shiftreg_Offset X0 3) *)
  0xca020084;       (* arm_EOR X4 X4 X2 *)
  0xaa0400a5;       (* arm_ORR X5 X5 X4 *)
  0xb5ffff60;       (* arm_CBNZ X0 (word 2097132) *)
  0xeb1f00bf;       (* arm_CMP X5 XZR *)
  0x9a9f17e0;       (* arm_CSET X0 Condition_EQ *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EQ_EXEC = ARM_MK_EXEC_RULE bignum_eq_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EQ_CORRECT = prove
 (`!m a x n b y pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_eq_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read PC s' = word (pc + 0x5c) /\
                C_RETURN s' = if x = y then word 1 else word 0)
          (MAYCHANGE [PC; X0; X2; X4; X5] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`b:int64`; `y:num`] THEN
  X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_EQ_EXEC] THEN
  BIGNUM_RANGE_TAC "m" "x" THEN BIGNUM_RANGE_TAC "n" "y" THEN

  (*** Split into subgoals at "mmain" label and do the second part first ***)

  ABBREV_TAC `p = MIN m n` THEN VAL_INT64_TAC `p:num` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x38`
   `\s. read X0 s = word p /\
        read X1 s = a /\
        read X3 s = b /\
        bignum_from_memory (a,m) s = x /\
        bignum_from_memory (b,n) s = y /\
        (read X5 s = word 0 <=> highdigits x p = highdigits y p)` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    ASM_CASES_TAC `p = 0` THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0] THEN
      GHOST_INTRO_TAC `d:int64` `read X5` THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN
      REWRITE_TAC[COND_SWAP];
      ALL_TAC] THEN

    ENSURES_WHILE_DOWN_TAC `p:num` `pc + 0x3c` `pc + 0x50`
     `\i s. read X0 s = word i /\
            read X1 s = a /\
            read X3 s = b /\
            bignum_from_memory (a,m) s = x /\
            bignum_from_memory (b,n) s = y /\
            (read X5 s = word 0 <=> highdigits x i = highdigits y i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `d:int64` `read X5` THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN
      REWRITE_TAC[COND_SWAP]] THEN

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < m /\ i < n` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (i + 1)) (word 1):int64 = word i`) THEN
    VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `d:int64` `read X5` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add a (word (8 * i)))) s0 =
      word(bigdigit x i) /\
      read(memory :> bytes64(word_add b (word (8 * i)))) s0 =
      word(bigdigit y i)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                  BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      ASM_REWRITE_TAC[WORD_VAL];
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN
    GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV) [HIGHDIGITS_STEP] THEN
    SIMP_TAC[LEXICOGRAPHIC_EQ_64; BIGDIGIT_BOUND] THEN
    AP_TERM_TAC THEN REWRITE_TAC[WORD_XOR_EQ_0] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN
    REWRITE_TAC[DIMINDEX_64; BIGDIGIT_BOUND]] THEN

  (*** The case m = n, which is a simple drop-through ***)

  ASM_CASES_TAC `m:num = n` THENL
   [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `MIN n n = p ==> p = n`)) THEN
    ASM_SIMP_TAC[HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0];
    ALL_TAC] THEN

  (*** Now the n > m and m > n cases respectively, very similar proofs ***)

  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(m:num = n) ==> m < n \/ n < m`)) THEN
  UNDISCH_TAC `MIN m n = p` THEN
  ASM_SIMP_TAC[ARITH_RULE `m < n ==> MIN m n = m`;
               ARITH_RULE `n < m ==> MIN m n = n`] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[HIGHDIGITS_ZERO] THENL
   [ENSURES_WHILE_PDOWN_TAC `n - m:num` `pc + 0xc` `pc + 0x1c`
     `\i s. (read X0 s = word m /\
             read X1 s = a /\
             read X2 s = word(m + i) /\
             read X3 s = b /\
             bignum_from_memory (a,m) s = x /\
             bignum_from_memory (b,n) s = y /\
             (read X5 s = word 0 <=> highdigits y (m + i) = 0)) /\
            (read ZF s <=> i = 0)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `m:num < n` THEN ARITH_TAC;
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[GSYM NOT_LT; ARITH_RULE `m:num < n ==> m + n - m = n`] THEN
      ASM_SIMP_TAC[HIGHDIGITS_ZERO];
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `d:int64` `read X5` THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      MESON_TAC[]] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (m + i + 1)) (word 1):int64 = word(m + i)`) THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `m + i:num`] THEN
    GHOST_INTRO_TAC `d:int64` `read X5` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add b (word (8 * (m + i))))) s0 =
      word(bigdigit y (m + i))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                  BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_VAL] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0;
      WORD_RULE `word_sub (word m) (word (m + i)) = word_neg(word i)`] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
    REWRITE_TAC[DIMINDEX_64; BIGDIGIT_BOUND];

    ENSURES_WHILE_PDOWN_TAC `m - n:num` `pc + 0x24` `pc + 0x34`
     `\i s. (read X0 s = word(n + i) /\
             read X1 s = a /\
             read X2 s = word n /\
             read X3 s = b /\
             bignum_from_memory (a,m) s = x /\
             bignum_from_memory (b,n) s = y /\
             (read X5 s = word 0 <=> highdigits x (n + i) = 0)) /\
            (read ZF s <=> i = 0)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `n:num < m` THEN ARITH_TAC;
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `n:num <= m` ASSUME_TAC THENL
       [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `m:num < n ==> m + n - m = n`] THEN
      ASM_SIMP_TAC[HIGHDIGITS_ZERO; VAL_EQ_0; WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `d:int64` `read X5` THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (n + i + 1)) (word 1):int64 = word(n + i)`) THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `n + i:num`] THEN
    GHOST_INTRO_TAC `d:int64` `read X5` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add a (word (8 * (n + i))))) s0 =
      word(bigdigit x (n + i))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                  BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_VAL] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; WORD_RULE
     `word_sub (word (n + i)) (word n) = word i`] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
    REWRITE_TAC[DIMINDEX_64; BIGDIGIT_BOUND]]);;

let BIGNUM_EQ_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_eq_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read PC s' = returnaddress /\
                C_RETURN s' = if x = y then word 1 else word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_EQ_EXEC BIGNUM_EQ_CORRECT);;
