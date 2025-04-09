(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiply by 10 and add another word.                                      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_muladd10.o";;
 ****)

let bignum_muladd10_mc =
  define_assert_from_elf "bignum_muladd10_mc" "arm/generic/bignum_muladd10.o"
[
  0xb40001c0;       (* arm_CBZ X0 (word 56) *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xf8637825;       (* arm_LDR X5 X1 (Shiftreg_Offset X3 3) *)
  0xd37dfca4;       (* arm_LSR X4 X5 61 *)
  0x8b0500a5;       (* arm_ADD X5 X5 X5 *)
  0x8b440884;       (* arm_ADD X4 X4 (Shiftedreg X4 LSR 2) *)
  0xab0508a5;       (* arm_ADDS X5 X5 (Shiftedreg X5 LSL 2) *)
  0x9a1f0084;       (* arm_ADC X4 X4 XZR *)
  0xab0200a5;       (* arm_ADDS X5 X5 X2 *)
  0xf8237825;       (* arm_STR X5 X1 (Shiftreg_Offset X3 3) *)
  0x9a1f0082;       (* arm_ADC X2 X4 XZR *)
  0x91000463;       (* arm_ADD X3 X3 (rvalue (word 1)) *)
  0xeb00007f;       (* arm_CMP X3 X0 *)
  0x54fffea3;       (* arm_BCC (word 2097108) *)
  0xaa0203e0;       (* arm_MOV X0 X2 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MULADD10_EXEC = ARM_MK_EXEC_RULE bignum_muladd10_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MULADD10_CORRECT = time prove
 (`!k z d n pc.
        nonoverlapping (word pc,0x40) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_muladd10_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; d] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read PC s = word (pc + 0x3c) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (10 * n + val d) (val k) /\
                  C_RETURN s = word(highdigits (10 * n + val d) (val k)))
              (MAYCHANGE [PC; X0; X2; X3; X4; X5] ,,
               MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
               MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `d:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ARM_SIM_TAC BIGNUM_MULADD10_EXEC (1--2) THEN
    ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** Setup of the loop ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x8` `pc + 0x30`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X3 s = word i /\
          2 EXP (64 * i) * val(read X2 s) + bignum_from_memory(z,i) s =
          10 * lowdigits n i + d /\
          bignum_from_memory(word_add z (word (8 * i)),k - i) s =
          highdigits n i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_MULADD10_EXEC (1--2) THEN
    ASM_SIMP_TAC[LOWDIGITS_0; HIGHDIGITS_0; SUB_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; WORD_ADD_0] THEN ARITH_TAC;
    ALL_TAC; (*** The main loop invariant ***)
    REPEAT STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_MULADD10_EXEC (1--2);
    GHOST_INTRO_TAC `c:num` `\s. val(read X2 s)` THEN
    GHOST_INTRO_TAC `l:num` `bignum_from_memory(z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `l:num` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; VAL_WORD_GALOIS; DIMINDEX_64] THEN
    ARM_SIM_TAC BIGNUM_MULADD10_EXEC (1--3) THEN
    UNDISCH_THEN `2 EXP (64 * k) * c + l = 10 * n + d` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[lowdigits; highdigits; MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0;
                 MOD_LT; DIV_LT; ARITH_EQ; ADD_CLAUSES]] THEN

  (*** The loop invariant, starting with tweaking then simulation ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `c:num` `\s. val(read X2 s)` THEN
  GHOST_INTRO_TAC `l:num` `bignum_from_memory(z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `l:num` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  ARM_ACCSIM_TAC BIGNUM_MULADD10_EXEC [5;6;7;9] (1--10) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * (i + 2))` THEN
  REWRITE_TAC[EXP_ADD; LEFT_ADD_DISTRIB] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `l < e /\ e * (2 EXP 64 * s + t + 1) <= e * 2 EXP 128
      ==> (e * 2 EXP 64) * s + l + e * t < e * 2 EXP 128`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    ASM BOUNDER_TAC[];
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP 64 * e /\ d < 2 EXP 64 /\ 2 EXP 64 * 1 <= 2 EXP 64 * e
      ==> 10 * l + d < e * 2 EXP 128`) THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; LE_1] THEN
    REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `64 + 64 * i = 64 * (i + 1)`] THEN
    REWRITE_TAC[LOWDIGITS_BOUND];
    REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE
     `10 * (e * h + l) + d = e * 10 * h + 10 * l + d`]] THEN
  SUBST1_TAC(SYM(ASSUME`2 EXP (64 * i) * c + l = 10 * lowdigits n i + d`)) THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(w * s + t == 10 * d + c) (mod ww)
    ==> ((e * w) * s + l + e * t ==
         e * 10 * d + e * c + l) (mod (e * ww))`) THEN
  ONCE_REWRITE_TAC[GSYM VAL_WORD_BIGDIGIT] THEN
  REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
  REWRITE_TAC[WORD_RULE `word_add x x = word_shl x 1`] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  REWRITE_TAC[val_def; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_USHR; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC);;

let BIGNUM_MULADD10_SUBROUTINE_CORRECT = time prove
 (`!k z d n pc returnaddress.
        nonoverlapping (word pc,0x40) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_muladd10_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; d] s /\
                  bignum_from_memory (z,val k) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (10 * n + val d) (val k) /\
                  C_RETURN s = word(highdigits (10 * n + val d) (val k)))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MULADD10_EXEC BIGNUM_MULADD10_CORRECT);;
