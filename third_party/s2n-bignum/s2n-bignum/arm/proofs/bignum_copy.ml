(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying (with truncation or extension) bignums                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_copy.o";;
 ****)

let bignum_copy_mc =
  define_assert_from_elf "bignum_copy_mc" "arm/generic/bignum_copy.o"
[
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0x9a823002;       (* arm_CSEL X2 X0 X2 Condition_CC *)
  0xd2800004;       (* arm_MOV X4 (rvalue (word 0)) *)
  0xb40000c2;       (* arm_CBZ X2 (word 24) *)
  0xf8647865;       (* arm_LDR X5 X3 (Shiftreg_Offset X4 3) *)
  0xf8247825;       (* arm_STR X5 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb02009f;       (* arm_CMP X4 X2 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xf824783f;       (* arm_STR XZR X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_COPY_EXEC = ARM_MK_EXEC_RULE bignum_copy_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_COPY_CORRECT = prove
 (`!k z n x a pc.
     nonoverlapping (word pc,0x40) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read PC s = word (pc + 0x3c) /\
                bignum_from_memory (z,val k) s = lowdigits a (val k))
          (MAYCHANGE [PC; X2; X4; X5] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_COPY_EXEC] THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Simulate the initial computation of min(n,k) and then
   *** recast the problem with n' = min(n,k) so we can assume
   *** hereafter that n <= k. This makes life a bit easier since
   *** otherwise n can actually be any number < 2^64 without
   *** violating the preconditions.
   ***)

  ENSURES_SEQUENCE_TAC `pc + 0xc`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word(MIN n k) /\
        read X3 s = x /\
        read X4 s = word 0 /\
        bignum_from_memory (x,MIN n k) s = lowdigits a k` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
    REWRITE_TAC[ARITH_RULE `MIN n k = if k < n then k else n`] THEN
    MESON_TAC[];
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (vfree_in `k:num` o concl))) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MP_TAC(ARITH_RULE `MIN n k <= k`) THEN
    SPEC_TAC(`lowdigits a k`,`a:num`) THEN SPEC_TAC(`MIN n k`,`n:num`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    VAL_INT64_TAC `n:num` THEN BIGNUM_RANGE_TAC "n" "a"] THEN

  (*** Break at the start of the padding stage ***)

  ENSURES_SEQUENCE_TAC `pc + 0x24`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X4 s = word n /\
        bignum_from_memory(z,n) s = a` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[MESON[] `0 = a <=> a = 0`] THEN
      ARM_SIM_TAC BIGNUM_COPY_EXEC [1];
      ALL_TAC] THEN

    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

    (*** The main copying loop, in the case when n is nonzero ***)

    ENSURES_WHILE_UP_TAC `n:num` `pc + 0x10` `pc + 0x1c`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word n /\
            read X3 s = x /\
            read X4 s = word i /\
            bignum_from_memory(z,i) s = lowdigits a i /\
            bignum_from_memory(word_add x (word(8 * i)),n - i) s =
            highdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_COPY_EXEC [1]  THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      ARM_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_BIGDIGIT] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2);
      ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]];
    ALL_TAC] THEN

  (*** Degenerate case of no padding (initial k <= n) ***)

  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o
    MATCH_MP (ARITH_RULE `n:num <= k ==> n = k \/ n < k`))
  THENL [ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2); ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  (*** Main padding loop ***)

  SUBGOAL_THEN `~(k:num <= n)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NOT_LE]; ALL_TAC] THEN

  ENSURES_WHILE_AUP_TAC `n:num` `k:num` `pc + 0x2c` `pc + 0x34`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X4 s = word i /\
          bignum_from_memory(z,i) s = a` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2);
    ARM_SIM_TAC BIGNUM_COPY_EXEC (1--2)]);;

let BIGNUM_COPY_SUBROUTINE_CORRECT = prove
 (`!k z n x a pc returnaddress.
     nonoverlapping (word pc,0x40) (z,8 * val k) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc  /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_COPY_EXEC BIGNUM_COPY_CORRECT);;
