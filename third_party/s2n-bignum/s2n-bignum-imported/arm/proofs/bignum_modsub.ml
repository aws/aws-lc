(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular subtraction of bignums.                                           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_modsub.o";;
 ****)

let bignum_modsub_mc =
  define_assert_from_elf "bignum_modsub_mc" "arm/generic/bignum_modsub.o"
[
  0xab1f0006;       (* arm_ADDS X6 X0 XZR *)
  0x54000280;       (* arm_BEQ (word 80) *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8656847;       (* arm_LDR X7 X2 (Register_Offset X5) *)
  0xf8656868;       (* arm_LDR X8 X3 (Register_Offset X5) *)
  0xfa0800e7;       (* arm_SBCS X7 X7 X8 *)
  0xf8256827;       (* arm_STR X7 X1 (Register_Offset X5) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd10004c6;       (* arm_SUB X6 X6 (rvalue (word 1)) *)
  0xb5ffff46;       (* arm_CBNZ X6 (word 2097128) *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xaa0003e6;       (* arm_MOV X6 X0 *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8656827;       (* arm_LDR X7 X1 (Register_Offset X5) *)
  0xf8656888;       (* arm_LDR X8 X4 (Register_Offset X5) *)
  0x8a090108;       (* arm_AND X8 X8 X9 *)
  0xba0800e7;       (* arm_ADCS X7 X7 X8 *)
  0xf8256827;       (* arm_STR X7 X1 (Register_Offset X5) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd10004c6;       (* arm_SUB X6 X6 (rvalue (word 1)) *)
  0xb5ffff26;       (* arm_CBNZ X6 (word 2097124) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MODSUB_EXEC = ARM_MK_EXEC_RULE bignum_modsub_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODSUB_CORRECT = prove
 (`!k z x y m a b n pc.
        nonoverlapping (word pc,0x58) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_modsub_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x54) /\
                  &(bignum_from_memory (z,val k) s) = (&a - &b) rem &n)
             (MAYCHANGE [PC; X5; X6; X7; X8; X9] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODSUB_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_REM_0; INT_SUB_REFL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64) (pc,88) (val(z:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main subtraction, subloop ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xc` `pc + 0x24`
    `\i s. read X0 s = word k /\
           read X1 s = z /\
           read X2 s = x /\
           read X3 s = y /\
           read X4 s = m /\
           bignum_from_memory (m,k) s = n /\
           read X5 s = word(8 * i) /\
           read X6 s = word(k - i) /\
           bignum_from_memory (word_add x (word(8 * i)),k - i) s =
           highdigits a i /\
           bignum_from_memory (word_add y (word(8 * i)),k - i) s =
           highdigits b i /\
           &(bignum_from_memory(z,i) s):real =
           &2 pow (64 * i) * &(bitval(~read CF s)) +
           &(lowdigits a i) - &(lowdigits b i)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODSUB_EXEC (1--3) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN INT_ARITH_TAC;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_ACCSTEPS_TAC BIGNUM_MODSUB_EXEC [3] (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [CONV_TAC WORD_RULE;
       REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
     ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
     CONV_TAC REAL_RING;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODSUB_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Masked addition operation "addloop" ***)

  GHOST_INTRO_TAC `hi:bool` `read CF` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
  ASM_CASES_TAC
   `&2 pow (64 * k) * &(bitval (~hi)) + &a - &b:real = &lo` THEN
  ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

  SUBGOAL_THEN `hi <=> b:num <= a` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `64 * k` THEN
    ASM_REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x34` `pc + 0x50`
    `\i s. read X0 s = word k /\
           read X1 s = z /\
           read X4 s = m /\
           read X5 s = word(8 * i) /\
           read X6 s = word(k - i) /\
           read X9 s = word_neg(word(bitval(a < b))) /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           &(bignum_from_memory(z,i) s):real =
           (&(lowdigits lo i) + &(bitval(a < b)) * &(lowdigits n i)) -
           &2 pow (64 * i) * &(bitval(read CF s))` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODSUB_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
     REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID] THEN
     REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
     CONV_TAC WORD_REDUCE_CONV;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_ACCSTEPS_TAC BIGNUM_MODSUB_EXEC [4] (1--7) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [CONV_TAC WORD_RULE;
       REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
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
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODSUB_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** The finale ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODSUB_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  TRANS_TAC EQ_TRANS `(&a - &b) + &(bitval(a < b)) * &n:int` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[int_eq; int_add_th; int_sub_th; int_mul_th; int_of_num_th];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
    EXISTS_TAC `--(&(bitval(a < b))):int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
    MAP_EVERY UNDISCH_TAC [`a:num < n`; `b:num < n`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LT; bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a:num < n`; `b:num < n`; `n < 2 EXP (64 * k)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `&2 pow (64 * k) * &(bitval (a < b)) + &a - &b:real = &lo`
   (SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `a:num < b` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[real_sub; REAL_ADD_RID; GSYM REAL_ADD_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH `x / y:real = inv y * x`; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_MUL_RNEG; REAL_MUL_ASSOC] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MODSUB_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc returnaddress.
        nonoverlapping (word pc,0x58) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_modsub_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  &(bignum_from_memory (z,val k) s) = (&a - &b) rem &n)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MODSUB_EXEC BIGNUM_MODSUB_CORRECT);;
