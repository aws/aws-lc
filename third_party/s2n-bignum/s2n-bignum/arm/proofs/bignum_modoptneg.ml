(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional modular negation of bignum.                                      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_modoptneg.o";;
 ****)

let bignum_modoptneg_mc =
  define_assert_from_elf "bignum_modoptneg_mc" "arm/generic/bignum_modoptneg.o"
[
  0xb40002e0;       (* arm_CBZ X0 (word 92) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0xaa0700c6;       (* arm_ORR X6 X6 X7 *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xeb0000bf;       (* arm_CMP X5 X0 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xeb1f00df;       (* arm_CMP X6 XZR *)
  0x9a9f1042;       (* arm_CSEL X2 X2 XZR Condition_NE *)
  0xeb1f005f;       (* arm_CMP X2 XZR *)
  0xda9f03e2;       (* arm_CSETM X2 Condition_NE *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xab02005f;       (* arm_CMN X2 X2 *)
  0xf8657886;       (* arm_LDR X6 X4 (Shiftreg_Offset X5 3) *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0x8a0200c6;       (* arm_AND X6 X6 X2 *)
  0xca0200e7;       (* arm_EOR X7 X7 X2 *)
  0xba0700c6;       (* arm_ADCS X6 X6 X7 *)
  0xf8257826;       (* arm_STR X6 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a6;       (* arm_SUB X6 X5 X0 *)
  0xb5ffff06;       (* arm_CBNZ X6 (word 2097120) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MODOPTNEG_EXEC = ARM_MK_EXEC_RULE bignum_modoptneg_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODOPTNEG_CORRECT = prove
 (`!k z p x m a n pc.
        nonoverlapping (word pc,0x60) (z,8 * val k) /\
        (m = z \/ nonoverlapping (m,8 * val k) (z,8 * val k)) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_modoptneg_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;p;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x5c) /\
                  (a <= n
                   ==> bignum_from_memory(z,val k) s =
                       if p = word 0 \/ a = 0 then a else n - a))
             (MAYCHANGE [PC; X2; X5; X6; X7] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `p:int64`; `x:int64`; `m:int64`] THEN
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
    REWRITE_TAC[CONJUNCT1 LT] THEN ARM_SIM_TAC BIGNUM_MODOPTNEG_EXEC [1] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** The initial zero comparison loop "cmploop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xc` `pc + 0x18`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = p /\
          read X3 s = x /\
          read X4 s = m /\
          bignum_from_memory (x,k) s = a /\
          bignum_from_memory (m,k) s = n /\
          read X5 s = word i /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          (read X6 s = word 0 <=> lowdigits a i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--3) THEN
    REWRITE_TAC[HIGHDIGITS_0; LOWDIGITS_0; SUB_0; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `zorro:int64` `read X6` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    ARM_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--3) THEN
    REWRITE_TAC[GSYM WORD_ADD; LOWDIGITS_CLAUSES] THEN
    ASM_REWRITE_TAC[WORD_OR_EQ_0; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[WORD_EQ_0; DIMINDEX_64; BIGDIGIT_BOUND] THEN CONV_TAC TAUT;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2);
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** The main masked addition/subtraction loop "mainloop" ***)

  ABBREV_TAC `q <=> ~(p:int64 = word 0) /\ ~(a = 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x38` `pc + 0x54`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = word_neg(word(bitval q)) /\
          read X3 s = x /\
          read X4 s = m /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          bignum_from_memory (word_add m (word(8 * i)),k - i) s =
          highdigits n i /\
          read X5 s = word i /\
          &(bignum_from_memory(z,i) s):real =
          &2 pow (64 * i) * (&(bitval q) - &(bitval(read CF s))) +
          &(bitval q) * &(lowdigits n i) +
          --(&1) pow bitval q * &(lowdigits a i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GHOST_INTRO_TAC `zorro:int64` `read X6` THEN
    ARM_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--8) THEN
    ASM_REWRITE_TAC[WORD_UNMASK_64; VAL_WORD_0; VAL_EQ_0] THEN
    REWRITE_TAC[MESON[] `~((if ~p then x else z) = z) <=> ~(x = z) /\ ~p`] THEN
    ASM_REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; HIGHDIGITS_0; LOWDIGITS_0] THEN
    REWRITE_TAC[real_pow; BIGNUM_FROM_MEMORY_TRIVIAL; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    ARM_ACCSIM_TAC BIGNUM_MODOPTNEG_EXEC [5] (1--7) THEN
    REWRITE_TAC[GSYM WORD_ADD; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; LOWDIGITS_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; REAL_POW_ADD] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_AND_MASK; WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64; VAL_WORD_BIGDIGIT] THEN
    CONV_TAC REAL_RING;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2);
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** The finale with the case analysis ***)

  ARM_SIM_TAC BIGNUM_MODOPTNEG_EXEC (1--2) THEN
  ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[LE_0; BIGNUM_FROM_MEMORY_BOUND];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a:num <= n`; `n < 2 EXP (64 * k)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(RAND_CONV(LAND_CONV REAL_POLY_CONV)) THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_FIELD `&2 pow n * inv(&2 pow n) = &1`] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MODOPTNEG_SUBROUTINE_CORRECT = prove
 (`!k z p x m a n pc returnaddress.
        nonoverlapping (word pc,0x60) (z,8 * val k) /\
        (m = z \/ nonoverlapping (m,8 * val k) (z,8 * val k)) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_modoptneg_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;p;x;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  (a <= n
                   ==> bignum_from_memory(z,val k) s =
                       if p = word 0 \/ a = 0 then a else n - a))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MODOPTNEG_EXEC BIGNUM_MODOPTNEG_CORRECT);;
