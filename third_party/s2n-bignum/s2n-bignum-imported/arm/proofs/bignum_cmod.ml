(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modulus of bignum by a single word.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_cmod.o";;
 ****)

let bignum_cmod_mc =
  define_assert_from_elf "bignum_cmod_mc" "arm/generic/bignum_cmod.o"
[
  0xb4000a00;       (* arm_CBZ X0 (word 320) *)
  0xdac01043;       (* arm_CLZ X3 X2 *)
  0x9ac32044;       (* arm_LSLV X4 X2 X3 *)
  0xd350fc89;       (* arm_LSR X9 X4 16 *)
  0xd240c125;       (* arm_EOR X5 X9 (rvalue (word 562949953421311)) *)
  0x91000529;       (* arm_ADD X9 X9 (rvalue (word 1)) *)
  0xd360fca5;       (* arm_LSR X5 X5 32 *)
  0x9b05fd26;       (* arm_MNEG X6 X9 X5 *)
  0xd371fcca;       (* arm_LSR X10 X6 49 *)
  0x9b0a7d4a;       (* arm_MUL X10 X10 X10 *)
  0xd362fcc6;       (* arm_LSR X6 X6 34 *)
  0x8b060146;       (* arm_ADD X6 X10 X6 *)
  0xb262014a;       (* arm_ORR X10 X10 (rvalue (word 1073741824)) *)
  0x9b0a7cca;       (* arm_MUL X10 X6 X10 *)
  0xd35efd4a;       (* arm_LSR X10 X10 30 *)
  0xd36284a6;       (* arm_LSL X6 X5 30 *)
  0x9b0a18a5;       (* arm_MADD X5 X5 X10 X6 *)
  0xd35efca5;       (* arm_LSR X5 X5 30 *)
  0x9b05fd26;       (* arm_MNEG X6 X9 X5 *)
  0xd358fcc6;       (* arm_LSR X6 X6 24 *)
  0x9b057cc6;       (* arm_MUL X6 X6 X5 *)
  0xd370bca5;       (* arm_LSL X5 X5 16 *)
  0xd358fcc6;       (* arm_LSR X6 X6 24 *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x9b05fd26;       (* arm_MNEG X6 X9 X5 *)
  0xd360fcc6;       (* arm_LSR X6 X6 32 *)
  0x9b057cc6;       (* arm_MUL X6 X6 X5 *)
  0xd36180a5;       (* arm_LSL X5 X5 31 *)
  0xd351fcc6;       (* arm_LSR X6 X6 17 *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0x9bc57c86;       (* arm_UMULH X6 X4 X5 *)
  0x93caf0ca;       (* arm_EXTR X10 X6 X10 60 *)
  0xd361fca6;       (* arm_LSR X6 X5 33 *)
  0xaa2a03ea;       (* arm_MVN X10 X10 *)
  0x9b0a7cca;       (* arm_MUL X10 X6 X10 *)
  0xd37ff8a5;       (* arm_LSL X5 X5 1 *)
  0xd361fd4a;       (* arm_LSR X10 X10 33 *)
  0x8b0a00a5;       (* arm_ADD X5 X5 X10 *)
  0xb10004aa;       (* arm_ADDS X10 X5 (rvalue (word 1)) *)
  0xda8a114a;       (* arm_CINV X10 X10 Condition_EQ *)
  0x9bca7c86;       (* arm_UMULH X6 X4 X10 *)
  0xab0400df;       (* arm_CMN X6 X4 *)
  0x9a8a20a5;       (* arm_CSEL X5 X5 X10 Condition_CS *)
  0x9b04fca6;       (* arm_MNEG X6 X5 X4 *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf860782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X0 3) *)
  0x9b077cc9;       (* arm_MUL X9 X6 X7 *)
  0x9bc77cc7;       (* arm_UMULH X7 X6 X7 *)
  0xab0a0129;       (* arm_ADDS X9 X9 X10 *)
  0xba0800e7;       (* arm_ADCS X7 X7 X8 *)
  0x9a9f20c8;       (* arm_CSEL X8 X6 XZR Condition_CS *)
  0xab090108;       (* arm_ADDS X8 X8 X9 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xb5fffee0;       (* arm_CBNZ X0 (word 2097116) *)
  0x9bc77ca0;       (* arm_UMULH X0 X5 X7 *)
  0xab070000;       (* arm_ADDS X0 X0 X7 *)
  0x9a9f2086;       (* arm_CSEL X6 X4 XZR Condition_CS *)
  0x9b047c09;       (* arm_MUL X9 X0 X4 *)
  0x9bc47c0a;       (* arm_UMULH X10 X0 X4 *)
  0x8b06014a;       (* arm_ADD X10 X10 X6 *)
  0xeb090108;       (* arm_SUBS X8 X8 X9 *)
  0xfa0a00e7;       (* arm_SBCS X7 X7 X10 *)
  0x9a9f1089;       (* arm_CSEL X9 X4 XZR Condition_NE *)
  0xeb090108;       (* arm_SUBS X8 X8 X9 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0x9a9f1089;       (* arm_CSEL X9 X4 XZR Condition_NE *)
  0xcb090108;       (* arm_SUB X8 X8 X9 *)
  0x9bc87ca0;       (* arm_UMULH X0 X5 X8 *)
  0xab080000;       (* arm_ADDS X0 X0 X8 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0x93c004c0;       (* arm_EXTR X0 X6 X0 1 *)
  0xd2401463;       (* arm_EOR X3 X3 (rvalue (word 63)) *)
  0x9ac32400;       (* arm_LSRV X0 X0 X3 *)
  0x9b027c09;       (* arm_MUL X9 X0 X2 *)
  0xcb090108;       (* arm_SUB X8 X8 X9 *)
  0xeb020100;       (* arm_SUBS X0 X8 X2 *)
  0x9a882000;       (* arm_CSEL X0 X0 X8 Condition_CS *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMOD_EXEC = ARM_MK_EXEC_RULE bignum_cmod_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CMOD_CORRECT = prove
 (`!k x m a pc.
      ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_cmod_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [k;x;m] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read PC s = word(pc + 0x140) /\
              (~(val m = 0) ==> C_RETURN s = word(a MOD val m)))
         (MAYCHANGE [PC; X0; X3; X4; X5; X6; X7; X8; X9; X10] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `x:int64` THEN W64_GEN_TAC `m:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `a:num` THEN

  (*** Degenerate case when output size is zero ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ARM_SIM_TAC BIGNUM_CMOD_EXEC [1] THEN REWRITE_TAC[MOD_0];
    ALL_TAC] THEN

  (*** Introduce the scaled n = 2^e * m which is used for a while ***)

  ABBREV_TAC `e = word_clz(word m:int64)` THEN
  MP_TAC(ISPEC `word m:int64` WORD_CLZ_LE_DIMINDEX) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN VAL_INT64_TAC `e:num` THEN

  ABBREV_TAC `n = 2 EXP e * m` THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n"; "m"] THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND_CLZ] THEN
    ASM_REWRITE_TAC[LE_REFL];
    VAL_INT64_TAC `n:num`] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xc`
   `\s. read X0 s = word k /\
        read X1 s = x /\
        read X2 s = word m /\
        read X3 s = word e /\
        read X4 s = word n /\
        bignum_from_memory(x,k) s = a` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_CMOD_EXEC (1--3) THEN ASM_REWRITE_TAC[word_jshl] THEN
    ASM_CASES_TAC `m = 0` THENL
     [UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
      SUBGOAL_THEN `e < dimindex(:64)` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
       [SUBST1_TAC(SYM(ASSUME `word_clz (word m:int64) = e`)) THEN
        REWRITE_TAC[WORD_CLZ_LT_DIMINDEX] THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0];
        ASM_REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] word_shl]]];
    ALL_TAC] THEN

  (*** Now the effective clone of word_recip ***)

  ENSURES_SEQUENCE_TAC `pc + 0xb0`
   `\s. read X0 s = word k /\
        read X1 s = x /\
        read X2 s = word m /\
        read X3 s = word e /\
        read X4 s = word n /\
        bignum_from_memory(x,k) s = a /\
        (~(m = 0)
         ==> &2 pow 64 + &(val(read X5 s)) < &2 pow 128 / &n /\
             &2 pow 128 / &n <= &2 pow 64 + &(val(read X5 s)) + &1)` THEN
  CONJ_TAC THENL
   [(*** Start by globalizing the nonzero assumption ***)

    ASM_CASES_TAC `m = 0` THENL
     [ARM_ACCSIM_TAC BIGNUM_CMOD_EXEC (1--41) (1--41);
      ASM_REWRITE_TAC[]] THEN

    (*** Discard irrelevancies that are unchanged ***)

    SUBGOAL_THEN
     `ensures arm
       (\s. aligned_bytes_loaded s (word pc) bignum_cmod_mc /\
            read PC s = word (pc + 0xc) /\
            read X4 s = word n)
       (\s. read PC s = word (pc + 0xb0) /\
            &2 pow 64 + &(val (read X5 s)) < &2 pow 128 / &n /\
            &2 pow 128 / &n <= &2 pow 64 + &(val (read X5 s)) + &1)
       (MAYCHANGE [PC; X5; X6; X9; X10] ,,
        MAYCHANGE [NF; ZF; CF; VF] ,,
        MAYCHANGE [events])`
    MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_THEN(fun th ->
        ENSURES_INIT_TAC "s0" THEN MP_TAC th THEN
        ARM_BIGSTEP_TAC BIGNUM_CMOD_EXEC "s1") THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

    (*** Replace word n with a to allow easy copy of word_recip proof ***)

    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`a:num`,`aa:num`) THEN REPEAT STRIP_TAC THEN
    ABBREV_TAC `a:int64 = word n` THEN
    UNDISCH_THEN `val(a:int64) = n` (SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `bit (dimindex(:64) - 1) (a:int64)` MP_TAC THENL
     [REWRITE_TAC[MSB_VAL] THEN
      UNDISCH_THEN `2 EXP e * m = val(a:int64)` (SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`word m:int64`; `word_clz(word m:int64) + 1`]
         VAL_BOUND_CLZ) THEN
      REWRITE_TAC[ARITH_RULE `~(a + 1 <= a)`] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN
      REWRITE_TAC[DIMINDEX_64; EXP_ADD] THEN ARITH_TAC;
      REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`]] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN

    (*** Now segue into a copy of the word_recip proof ***)

    ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN

    (*** Handle the special case a = 2^63 explicitly ***)

    ASM_CASES_TAC `a:int64 = word(2 EXP 63)` THENL
     [UNDISCH_THEN `a:int64 = word(2 EXP 63)` SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      ARM_STEPS_TAC BIGNUM_CMOD_EXEC (1--41) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN

    (*** Establish initial range of the input ***)

    SUBGOAL_THEN
     `(&2:real) pow 63 + &1 <= &(val(a:int64)) /\
      &(val(a:int64)):real <= &2 pow 64 - &1`
    STRIP_ASSUME_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN MP_TAC(ISPEC `a:int64` MSB_VAL) THEN
      MP_TAC(SPEC `a:int64` VAL_BOUND_64) THEN
      REWRITE_TAC[DIMINDEX_64; REAL_OF_NUM_LE] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM VAL_EQ]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** Initial switch to a shorter b, initial approximation x = z0 ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [1] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t1:int64`; `e1:real`] THEN
    STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [2] THEN
    MP_TAC(ISPECL [`49`; `t1:int64`] WORD_SUB_MASK_WORD) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM BOUNDER_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WORD_XOR_SYM] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SUB) THEN
    CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [3] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
    ASM_REWRITE_TAC[VAL_WORD_1] THEN
    ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:int64`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
    SUBGOAL_THEN
     `&2 pow 47 + &1 <= &(val(b:int64)) /\ &(val(b:int64)) <= &2 pow 48`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
      POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
      ALL_TAC] THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [4] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z0:int64`; `e4:real`] THEN
    ASM_REWRITE_TAC[REAL_ARITH
     `&562949953421311 - x = &2 pow 49 - (x + &1)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM)) THEN

    SUBGOAL_THEN
     `&2 pow 15 <= &(val(z0:int64)) /\
      &(val(z0:int64)) <= &2 pow 16 + &2 pow 15 - &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
      POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `&2 pow 64 - &2 pow 62 - &2 pow 48 <=
      &(val(b:int64)) * &(val(z0:int64)) /\
      &(val(b:int64)) * &(val(z0:int64)) <= &2 pow 64`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
       (PAT_CONV `\z:real. l <= b * z /\ b * z <= u`) [SYM th]) THEN
      REWRITE_TAC[REAL_ARITH
       `b * ((&2 pow 49 - b) / &2 pow 32 - e) =
        &2 pow 64 - (&2 pow 48 - b) pow 2 / &2 pow 32 - b * e`] THEN
      ASM PURE_BOUNDER_TAC[];
      ALL_TAC] THEN

    (*** Computation of initial error d0 ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [5] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
    ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:int64`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
    W(fun (asl,w) ->
        FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

    (*** Accumulation of the polynomial giving z1 ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [6] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t6:int64`; `e6:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [7] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t7:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [8] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t8:int64`; `e8:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [9] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t9:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [10] THEN
    MP_TAC(ISPECL [`t7:int64`; `word 1073741824:int64`] WORD_ADD_OR) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[WORD_AND_EQ_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[SET_RULE `DISJOINT s {a} <=> ~(a IN s)`] THEN
      REWRITE_TAC[IN_BITS_OF_WORD; BIT_VAL] THEN
      MATCH_MP_TAC(MESON[ODD; DIV_LT] `a < n ==> ~ODD(a DIV n)`) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
      DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `t10:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [11] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t11:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [12] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t12:int64`; `e12:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [13] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t13:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [14] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MADD) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t14:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [15] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z1:int64`; `e15:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o GSYM)) THEN

    (*** Accuracy of z1 then bounds on z1 and tidying up ***)

    SUBGOAL_THEN
     `&2 pow 64 - (&2 pow 54 + &2 pow 50) <=
      &(val(b:int64)) * &(val(z1:int64)) /\
      &(val(b:int64)) * &(val(z1:int64)) <= &2 pow 64`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH
       `b * ((a * z + z * c) / &2 pow 30 - e:real) =
        (b * z) * (a + c) / &2 pow 30 - b * e`] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
         `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
        ASM BOUNDER_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `(x * x + x') * (x * x + a):real =
          a * x' + a * x * x + x' * x * x + x * x * x * x`] THEN
      REWRITE_TAC[REAL_ARITH
       `bz * (&2 pow 30 + x / &2 pow 30 - e) / &2 pow 30 - be <= u <=>
        bz * (&2 pow 60 + x)
        <= &2 pow 60 * (u + be + bz * e / &2 pow 30)`] THEN
      REWRITE_TAC[REAL_ARITH
       `(x - d) * (y - e):real = x * y - (d * y + e * (x - d)) /\
        (x - d) + (y - e):real = (x + y) - (d + e) /\
        &c * (x - y) = (&c * x - &c * y)`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `bz * (&2 pow 60 + x) <= &2 pow 124 /\ &0 <= u /\ &0 <= bz * y
        ==> bz * (&2 pow 60 + x - y) <= &2 pow 60 * (&2 pow 64 + u)`) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
         `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
        ASM BOUNDER_TAC[];
        ASM BOUNDER_TAC[];
        SUBGOAL_THEN
         `&(val(t6:int64)) <= &2 pow 15 /\ &(val(t8:int64)) <= &2 pow 30`
        STRIP_ASSUME_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
        MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
         [`&(val(t6:int64)) = &(val(d0:int64)) / &2 pow 49 - e6`;
          `&(val(t8:int64)) = &(val(d0:int64)) / &2 pow 34 - e8`] THEN
        ASM BOUNDER_TAC[]];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `&2 pow 15 <= &(val(z1:int64)) /\ &(val(z1:int64)) <= &130945`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THENL
       [ALL_TAC; ASM BOUNDER_TAC[]] THEN
      REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
       `&(val x) = a ==> a = &(val x)`))) THEN
      ASM BOUNDER_TAC[];
      DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

    (*** First Newton step ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [16] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
    ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:int64`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
    W(fun (asl,w) ->
        FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [17] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t17:int64`; `e17:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [18] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t18:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [19] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t19:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [20] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t20:int64`; `e20:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [21] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
    DISCH_THEN(X_CHOOSE_THEN `z2:int64`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

    SUBGOAL_THEN
     `&2 pow 80 - &5 / &4 * &2 pow 60 <= &(val(b:int64)) * &(val(z2:int64)) /\
      &(val(b:int64)) * &(val(z2:int64)) <= &2 pow 80`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
         `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
      CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH
       `(&2 pow 64 - d) * (&2 pow 16 + (d / &2 pow 24 - e) / &2 pow 24) =
        (&2 pow 128 - d pow 2) / &2 pow 48 -
        (&2 pow 64 - d) * e / &2 pow 24`] THEN
      CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
      ASM PURE_BOUNDER_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `&2 pow 31 <= &(val(z2:int64)) /\ &(val(z2:int64)) <= &2 pow 33 - &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SHARPEN_INEQ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
         `&(val x) = a ==> a = &(val x)`))) THEN
        ASM BOUNDER_TAC[];
        MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(b:int64))` THEN
        CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
        GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN ASM PURE_BOUNDER_TAC[]];
      DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

    (*** Second Newton step ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [22] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_IWORD) THEN
    DISCH_THEN(MP_TAC o SPEC
     `&2 pow 80 - &(val(b:int64)) * &(val(z2:int64)):int`) THEN
    REWRITE_TAC[int_le; int_lt; int_sub_th; int_mul_th;
                  int_pow_th; int_of_num_th] THEN
    ANTS_TAC THENL
     [REPEAT(CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ALL_TAC]) THEN
      MATCH_MP_TAC(INTEGER_RULE
       `e divides n /\ (b == b') (mod e) /\ (z == z') (mod e)
        ==> (&0 - b * z:int == n - b' * z') (mod e)`) THEN
      REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
       (INST_TYPE [`:64`,`:N`]IVAL_VAL_CONG)] THEN
      MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:int64`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
    W(fun (asl,w) ->
        FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [23] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t23:int64`; `e23:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [24] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t24:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [25] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t25:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [26] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t26:int64`; `e26:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [27] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
    ASM_REWRITE_TAC[REAL_ARITH
     `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(b:int64))` THEN
      CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
         `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`)) THEN
      GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN
      ASM BOUNDER_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
    DISCH_THEN(X_CHOOSE_THEN `z3:int64`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

    SUBGOAL_THEN
     `&2 pow 111 - &201 / &128 * &2 pow 71
      <= &(val(b:int64)) * &(val(z3:int64)) /\
      &(val(b:int64)) * &(val(z3:int64)) <= &2 pow 111`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
         `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`))
      THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH
       `(&2 pow 80 - d) * (&2 pow 31 + (d / &2 pow 32 - e) / &2 pow 17) =
        (&2 pow 160 - d pow 2) / &2 pow 49 -
        (&2 pow 80 - d) * e / &2 pow 17`] THEN
      CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
      ASM PURE_BOUNDER_TAC[];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `&2 pow 62 <= &(val(z3:int64)) /\ &(val(z3:int64)) <= &2 pow 64 - &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
      SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
       `&(val x) = a ==> a = &(val x)`))) THEN
      ASM BOUNDER_TAC[];
      DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

    (*** Transfer accuracy to original input a, throw away facts about b ***)

    SUBGOAL_THEN
     `&2 pow 127 - &2 pow 88 + &1 <= &(val(a:int64)) * &(val(z3:int64)) /\
      &(val(a:int64)) * &(val(z3:int64)) <= &2 pow 127`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `a / &2 pow 16 - e + &1 = b ==> a = &2 pow 16 * (b + e - &1)`)) THEN
     REWRITE_TAC[REAL_ARITH `(c * (b + x)) * z:real = c * (b * z + x * z)`] THEN
     CONJ_TAC THEN ASM PURE_BOUNDER_TAC[];
     REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `b:int64` o concl)))] THEN

    (*** Observe this, which implies in particular the result is not exact ***)

    SUBGOAL_THEN `!w p. ~(val(a:int64) * w = 2 EXP p)` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ_ALT] PRIME_POWER_MULT)) THEN
      REWRITE_TAC[PRIME_2] THEN STRIP_TAC THEN
      SUBGOAL_THEN `2 EXP 63 < val(a:int64) /\ val a < 2 EXP 64` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
        ASM_REWRITE_TAC[LT_EXP] THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** The full-sized Newton step ***)

    ARM_ACCSTEPS_TAC BIGNUM_CMOD_EXEC [28] (28--30) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [31] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t31:int64`; `e31:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [32] THEN
    REABBREV_TAC `bf = read X10 s32` THEN
    SUBGOAL_THEN
     `?e. &0 <= e /\ e <= &1 /\
          &(val(bf:int64)):real =
          (&2 pow 127 - &(val(a:int64)) * &(val(z3:int64))) / &2 pow 60 - e`
    (X_CHOOSE_THEN `e32:real` STRIP_ASSUME_TAC) THENL
     [MP_TAC(SPEC `&2 pow 127 - &(val(a:int64)) * &(val(z3:int64)):real`
            INTEGER_POS) THEN
      ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `d3:num`) THEN
      SUBGOAL_THEN `&d3:real <= &2 pow 88 - &1` ASSUME_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        ASM BOUNDER_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `d3 < 2 EXP 88` ASSUME_TAC THENL
       [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `1 <= d3` ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES; REAL_SUB_0] THEN
        DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM int_of_num_th] THEN
      SUBGOAL_THEN `&(val(bf:int64)):int = &((d3 - 1) DIV 2 EXP 60)`
      SUBST1_TAC THENL
       [EXPAND_TAC "bf" THEN
        SIMP_TAC[GSYM WORD_SUBWORD_NOT; GSYM WORD_JOIN_NOT;
                 DIMINDEX_64; DIMINDEX_128; ARITH] THEN
        SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; DIMINDEX_128;
                 ARITH_LE; ARITH_LT] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM;
                    GSYM INT_OF_NUM_DIV; INT_VAL_WORD_NOT; DIMINDEX_64] THEN
        REWRITE_TAC[INT_ARITH
          `e * (e - &1 - h) + e - &1 - l:int = e * e - &1 - (e * h + l)`] THEN
        SIMP_TAC[INT_DIV_REM; INT_POS; INT_POW_LE; GSYM INT_POW_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
        FIRST_ASSUM(MP_TAC o check (is_eq o concl)) THEN
        REWRITE_TAC[IMP_IMP; REAL_EQ_SUB_RADD] THEN
        GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [REAL_OF_NUM_CLAUSES] THEN
        GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
         [GSYM INT_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[GSYM INT_EQ_SUB_RADD] THEN DISCH_THEN(fun th ->
          REWRITE_TAC[th; INT_ARITH
          `&2 pow 128 - &1 - x:int = (&2 pow 127 - &1) + &2 pow 127 - x`]) THEN
        SUBGOAL_THEN `(&2 pow 127 - &1 + &d3) rem &2 pow 124 = &(d3 - 1)`
        SUBST1_TAC THENL
         [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN MATCH_MP_TAC INT_REM_UNIQ THEN
          EXISTS_TAC `&8:int` THEN CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[INT_SUB_LE; INT_LT_SUB_RADD] THEN
          REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_ABS_NUM] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
          REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_CLAUSES] THEN ARITH_TAC];
        ASM_REWRITE_TAC[int_of_num_th]] THEN
      EXISTS_TAC `&((d3 - 1) MOD 2 EXP 60 + 1):real / &2 pow 60` THEN
      SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
       [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [33] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t33:int64` STRIP_ASSUME_TAC) THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC (34--35) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t35:int64`; `e35:real`] THEN STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [36] THEN

    (*** Analysis of provisional result w before the final truncation ***)

    ABBREV_TAC `w = 2 * val(z3:int64) + val(t35:int64)` THEN
    SUBGOAL_THEN
     `&2 pow 128 - &2 pow 62 <= &(val(a:int64)) * &w + &(val a) /\
      &(val(a:int64)) * &w <= &2 pow 128`
    STRIP_ASSUME_TAC THENL
     [ABBREV_TAC `d3 = &2 pow 127 - &(val(a:int64)) * &(val(z3:int64))` THEN
      SUBGOAL_THEN `&0 <= d3 /\ d3:real <= &2 pow 88 - &1`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "d3" THEN ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "w" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `a * (&2 * z + ((z / &2 pow 33 - d) * c) / &2 pow 33 - f):real =
        (a * z) * (&2 + c / &2 pow 66) - d * c * a / &2 pow 33 - a * f`] THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
         `&2 pow 127 - a * z = d ==> a * z:real = &2 pow 127 - d`)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `&0 <= a * (&1 - e) /\ l <= b - c
          ==> l:real <= b - c - a * e + a`) THEN
        CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ASM BOUNDER_TAC[]];
        REWRITE_TAC[REAL_ARITH
         `(&2 pow 127 - d) * (&2 + (d / &2 pow 60 - e) / &2 pow 66) =
          (&2 pow 254 - d pow 2) / &2 pow 126 -
          (&2 pow 127 - d) * e / &2 pow 66`] THEN
        SUBST1_TAC(SYM(ASSUME `&(val(bf:int64)) = d3 / &2 pow 60 - e32`)) THEN
        ASM PURE_BOUNDER_TAC[]];
      ALL_TAC] THEN

    (*** Now the computed result with implicit 1 bit ***)

    ABBREV_TAC `z:int64 = word_add (word_shl z3 1) t35` THEN
    SUBGOAL_THEN `&w:real = (&2 pow 64) + &(val(z:int64))` SUBST_ALL_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL] THEN
      REWRITE_TAC[DIMINDEX_64; EXP_1] THEN CONV_TAC MOD_DOWN_CONV THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `2 EXP 64 <= w /\ w < 2 * 2 EXP 64` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_LT; ARITH_RULE `a <= b <=> a < b + 1`];
        SIMP_TAC[GSYM NOT_LE; MOD_CASES; GSYM REAL_OF_NUM_SUB] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THEN
      (MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(a:int64))` THEN
       CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC])
      THENL
       [REWRITE_TAC[REAL_ARITH `a * (w + &1):real = a * w + a`] THEN
        TRANS_TAC REAL_LTE_TRANS `&2 pow 128 - &2 pow 62`;
        TRANS_TAC REAL_LET_TRANS `&2 pow 128`] THEN
      ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[];
      ALL_TAC] THEN

    (*** In this non-trivial case the increment does not wrap ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC (37--38) THEN
    REABBREV_TAC `z' = read X10 s38` THEN
    SUBGOAL_THEN `&(val(z':int64)):real = &(val(z:int64)) + &1` ASSUME_TAC THENL
     [EXPAND_TAC "z'" THEN
      SUBGOAL_THEN `val(z:int64) + 1 < 2 EXP 64` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES];
        SIMP_TAC[VAL_WORD_ADD_CASES; DIMINDEX_64; VAL_WORD_1;
                 ADD_EQ_0; ARITH_EQ] THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES]] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&2 pow 63 + &1) * (&2 pow 64 + z) <= &2 pow 128
        ==> z + &1 < &2 pow 64`) THEN
      TRANS_TAC REAL_LE_TRANS
       `&(val(a:int64)) * (&2 pow 64 + &(val(z:int64)))` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN ASM BOUNDER_TAC[];
      ALL_TAC] THEN

    (*** The final bounds check and selection ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC (39--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ;
                 REAL_ARITH `&2 pow 63 + &1 <= a ==> &0 < a`] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64; LT_MULT2;
             ARITH_RULE `a < 2 EXP 64 * 2 EXP 64 ==> a DIV 2 EXP 64 < 2 EXP 64`;
             ARITH_RULE `2 EXP 64 <= h DIV 2 EXP 64 + a <=>
                         2 EXP 128 <= 2 EXP 64 * a + h`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; LT_LE] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;

    GHOST_INTRO_TAC `w:int64` `read X5` THEN GLOBALIZE_PRECONDITION_TAC] THEN

  (*** The main loop resulting in a 128-bit modular equivalent ***)

  ENSURES_WHILE_DOWN_TAC `k:num` `pc + 0xbc` `pc + 0xe0`
   `\i s. read X1 s = x /\
          read X2 s = word m /\
          read X3 s = word e /\
          read X4 s = word n /\
          read X5 s = w /\
          read X0 s = word i /\
          (~(m = 0) ==> (val(read X6 s) == 2 EXP 128) (mod m)) /\
          (~(m = 0) ==> (bignum_of_wordlist[read X8 s; read X7 s] ==
                         highdigits a i) (mod m)) /\
          bignum_from_memory(x,i) s = lowdigits a i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_CMOD_EXEC (1--3) THEN
    ASM_SIMP_TAC[bignum_of_wordlist; LOWDIGITS_SELF; VAL_WORD_0] THEN
    ASM_SIMP_TAC[HIGHDIGITS_ZERO; ADD_CLAUSES; MULT_CLAUSES; CONG_REFL] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
     [UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      STRIP_TAC] THEN
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC INT_CONG_TRANS THEN
    EXISTS_TAC `&2 pow 128 - (&2 pow 64 + &(val(w:int64))) * &n:int` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_EQ_IMP_CONG;
      UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC NUMBER_RULE] THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 64` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `&0 <= x /\ x:int < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
      REWRITE_TAC[INT_LE_SUB_LADD; INT_LT_SUB_RADD] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_POS; VAL_BOUND_64; ADD_CLAUSES] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `a:real <= (e + w + &1) * n /\ n < e ==> a < e + (e + w) * n`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES];
      MATCH_MP_TAC(INTEGER_RULE
       `e divides ee /\ (a == --(w * n)) (mod e)
        ==> (a:int == ee - (e + w) * n) (mod e)`) THEN
      SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
      W(MP_TAC o PART_MATCH (lhand o rator) VAL_IWORD_CONG o
        lhand o rator o snd) THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      MATCH_MP_TAC(INTEGER_RULE
       `(w:int == w') (mod e) /\ (n == n') (mod e)
        ==> (&0 - w * n == --(w' * n')) (mod e)`) THEN
      REWRITE_TAC[GSYM DIMINDEX_64; IVAL_VAL_CONG; IVAL_WORD_CONG]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
    ASM_CASES_TAC `m = 0` THENL
     [ARM_SIM_TAC BIGNUM_CMOD_EXEC (1--9) THEN CONV_TAC WORD_RULE;
      ASM_REWRITE_TAC[]] THEN
    GHOST_INTRO_TAC `r:int64` `read X6` THEN
    GHOST_INTRO_TAC `h:int64` `read X7` THEN
    GHOST_INTRO_TAC `l:int64` `read X8` THEN
    MP_TAC(WORD_RULE `word_sub (word(i + 1)) (word 1):int64 = word i`) THEN
    DISCH_TAC THEN
    ARM_ACCSIM_TAC BIGNUM_CMOD_EXEC [3;5;6;8;9] (1--9) THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC
     `bignum_of_wordlist[word(bigdigit a i); l] +
      val(r:int64) * val(h:int64)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
       `(a == h) (mod m)
        ==> (e * a + b == x) (mod m)
            ==> (x == e * h + b) (mod m)`)) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_CONV) THEN
      REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN MATCH_MP_TAC(NUMBER_RULE
       `(r == e EXP 2) (mod m)
        ==> (e * (l + e * h) + d == (d + e * l) + r * h) (mod m)`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `2 EXP 64 EXP 2 = 2 EXP 128`]] THEN
    ABBREV_TAC `z:num = bignum_of_wordlist[word(bigdigit a i); l] +
                        val(r:int64) * val(h:int64)` THEN
    ASM_REWRITE_TAC[REAL_CONGRUENCE; REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN
     `&(bignum_of_wordlist [sum_s8; sum_s9]):real =
      if &z < &2 pow 128 then &z else &z - (&2 pow 128 - &(val(r:int64)))`
    SUBST1_TAC THENL
     [ALL_TAC;
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO;
         INTEGER_CLOSED; REAL_ARITH `z - (a - b) - z:real = b - a`] THEN
      UNDISCH_TAC `(val(r:int64) == 2 EXP 128) (mod m)` THEN
      ASM_REWRITE_TAC[REAL_CONGRUENCE; REAL_OF_NUM_EQ] THEN
      REWRITE_TAC[real_div; GSYM REAL_OF_NUM_CLAUSES]] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "z" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&z:real < &2 pow 128 <=> ~carry_s6` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_REAL_LT THEN
      EXISTS_TAC `128` THEN
      ACCUMULATOR_POP_ASSUM_LIST
       (MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      EXPAND_TAC "z" THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      EXPAND_TAC "z" THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_CMOD_EXEC [1];
    ALL_TAC] THEN

  (*** Globalize the nonzeroness for the rest of the proofs ***)

  ASM_CASES_TAC `m = 0` THENL
   [ARM_SIM_TAC BIGNUM_CMOD_EXEC (1--24);
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
    [UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
     ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
     STRIP_TAC] THEN

  (*** Reduction from 128 bits to 64 bits ***)

  ASM_SIMP_TAC[HIGHDIGITS_0; LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x118`
   `\s. read X2 s = word m /\
        read X3 s = word e /\
        read X5 s = w /\
        read X4 s = word n /\
        (val(read X8 s) == a) (mod m)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `h:int64` `read X7` THEN
    GHOST_INTRO_TAC `l:int64` `read X8` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

    (*** Initial quotient multiple ***)

    ABBREV_TAC
     `q = ((2 EXP 64 + val(w:int64)) * val(h:int64)) DIV 2 EXP 64` THEN
    UNDISCH_THEN `val(word n:int64) = n` (K ALL_TAC) THEN
    ARM_ACCSTEPS_TAC BIGNUM_CMOD_EXEC [2;3;5;7;8;9] (1--9) THEN
    SUBGOAL_THEN
     `&(bignum_of_wordlist[sum_s8; sum_s9]) =
      &(bignum_of_wordlist [l; h]) - &q * &n`
    MP_TAC THENL
     [EXPAND_TAC "q" THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_DIV; bignum_of_wordlist; REAL_ADD_RID;
                    GSYM REAL_OF_NUM_CLAUSES; REAL_MUL_RZERO] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= l /\ &0 <= m * n /\ q * n:real <= h
           ==> &0 <= (l + h) - (q - m) * n`) THEN
        SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LE_DIV; REAL_POW_LE] THEN
        REWRITE_TAC[REAL_ARITH
         `(x * h) / &2 pow 64 * n <= &2 pow 64 * h <=>
          (x * n) * h <= &2 pow 128 * h`] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LT_IMP_LE; REAL_POS];
        MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x:real < n ==> x - y < n`) THEN
        SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN BOUNDER_TAC[];
        SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ]] THEN
      UNDISCH_THEN
       `&2 pow 64 * &(val(mulhi_s2:int64)) + &(val(mullo_s2:int64)) =
        &(val(w:int64)) * &(val(h:int64))`
       (MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x. x DIV 2 EXP 64`) THEN
      SIMP_TAC[DIV_MULT_ADD; DIV_LT; VAL_BOUND_64; EXP_EQ_0; ARITH_EQ] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BITVAL_CLAUSES; VAL_WORD_0] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `z0 = bignum_of_wordlist [sum_s8; sum_s9]` THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    ABBREV_TAC
     `zf0 <=>
      val(word_sub h (word_add sum_s7 (word(bitval carry_s8))):int64) = 0` THEN
    SUBGOAL_THEN `zf0 <=> z0 < 2 EXP 64` SUBST_ALL_TAC THENL
     [TRANS_TAC EQ_TRANS `val (sum_s9:int64) = 0` THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (~p ==> ~q)`] THEN
        EXPAND_TAC "z0" THEN SIMP_TAC[bignum_of_wordlist] THEN
        CONJ_TAC THENL [DISCH_TAC THEN BOUNDER_TAC[]; ARITH_TAC]] THEN
      EXPAND_TAC "zf0" THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[WORD_RULE `word_sub x y = z <=> word_add y z = x`] THEN
      REWRITE_TAC[GSYM VAL_CONG; VAL_WORD_ADD; VAL_WORD_BITVAL; CONG] THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `--e * c + s = h - i - j ==> (i + j) + s = e * c + h`)) THEN
      SIMP_TAC[REAL_OF_NUM_CLAUSES; MOD_MULT_ADD];
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
    SUBGOAL_THEN `z0 < 2 EXP 64 + 2 * n` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      EXPAND_TAC "q" THEN
      SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[REAL_OF_NUM_DIV; REAL_MUL_RZERO; REAL_ADD_RID] THEN
      MATCH_MP_TAC(REAL_ARITH
       `l:real < e /\ m * n <= &1 * n /\
        eh <= (h + q + &1) * n
        ==> (l + eh) - (h + q - m) * n < e + &2 * n`) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REPEAT CONJ_TAC THENL
       [BOUNDER_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN
        SIMP_TAC[REAL_POS; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH
       `e * h <= (h + (w * h) / a + &1) * n <=>
        h * (e - (&1 + w / a) * n) <= n`] THEN
      TRANS_TAC REAL_LE_TRANS `&(val(h:int64)) * &n / &2 pow 64` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        UNDISCH_TAC `&2 pow 128 <= (&2 pow 64 + &(val(w:int64)) + &1) * &n` THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH
         `h * n / &2 pow 64 <= n <=> h * n <= &2 pow 64 * n`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[REAL_POS] THEN BOUNDER_TAC[]];
      ALL_TAC] THEN

    (*** First correction ***)

    ARM_ACCSTEPS_TAC BIGNUM_CMOD_EXEC [11;12] (10--12) THEN
    SUBGOAL_THEN
     `&(bignum_of_wordlist[sum_s11; sum_s12]) =
      if 2 EXP 64 <= z0 then &z0 - &n else &z0`
    MP_TAC THENL
     [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`z0 < 2 EXP 64 + 2 * n`; `n < 2 EXP 64`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      EXPAND_TAC "z0" THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BITVAL_CLAUSES; VAL_WORD_0] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `z1 = bignum_of_wordlist [sum_s11; sum_s12]` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    ABBREV_TAC
     `zf1 <=>
      val(word_sub sum_s9 (word (0 + bitval carry_s11)):int64) = 0` THEN
    SUBGOAL_THEN `zf1 <=> z1 < 2 EXP 64` SUBST_ALL_TAC THENL
     [TRANS_TAC EQ_TRANS `val (sum_s12:int64) = 0` THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (~p ==> ~q)`] THEN
        EXPAND_TAC "z1" THEN SIMP_TAC[bignum_of_wordlist] THEN
        CONJ_TAC THENL [DISCH_TAC THEN BOUNDER_TAC[]; ARITH_TAC]] THEN
      EXPAND_TAC "zf1" THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[WORD_RULE `word_sub x y = z <=> word_add y z = x`] THEN
      REWRITE_TAC[GSYM VAL_CONG; ADD_CLAUSES; VAL_WORD_ADD; VAL_WORD_BITVAL;
                  CONG; DIMINDEX_64] THEN
      CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `--e * c + s = h - i - j ==> (i + j) + s = e * c + h`)) THEN
      SIMP_TAC[REAL_OF_NUM_CLAUSES;ADD_CLAUSES;  MOD_MULT_ADD];
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
    SUBGOAL_THEN `z0 < 2 EXP 64 + 2 * n` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      EXPAND_TAC "q" THEN
      SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[REAL_OF_NUM_DIV; REAL_MUL_RZERO; REAL_ADD_RID] THEN
      MATCH_MP_TAC(REAL_ARITH
       `l:real < e /\ m * n <= &1 * n /\
        eh <= (h + q + &1) * n
        ==> (l + eh) - (h + q - m) * n < e + &2 * n`) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REPEAT CONJ_TAC THENL
       [BOUNDER_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN
        SIMP_TAC[REAL_POS; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH
       `e * h <= (h + (w * h) / a + &1) * n <=>
        h * (e - (&1 + w / a) * n) <= n`] THEN
      TRANS_TAC REAL_LE_TRANS `&(val(h:int64)) * &n / &2 pow 64` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        UNDISCH_TAC `&2 pow 128 <= (&2 pow 64 + &(val(w:int64)) + &1) * &n` THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH
         `h * n / &2 pow 64 <= n <=> h * n <= &2 pow 64 * n`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[REAL_POS] THEN BOUNDER_TAC[]];
      ALL_TAC] THEN

    (*** Second correction ***)

    ARM_STEPS_TAC BIGNUM_CMOD_EXEC [13;14] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `z0:num` THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `&(bignum_of_wordlist [l; h]) - &q * &n:real = &z0` THEN
      REWRITE_TAC[REAL_EQ_SUB_RADD] THEN
      UNDISCH_TAC `(bignum_of_wordlist[l; h] == a) (mod m)` THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      CONV_TAC NUMBER_RULE] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `z1:num` THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `(if &2 pow 64 <= &z0 then &z0 - &n:real else &z0) = &z1` THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_EQ_SUB_RADD] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      CONV_TAC NUMBER_RULE] THEN
    MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `if 2 EXP 64 <= z1 then z1 - n else z1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_CONG THEN
      MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
      REWRITE_TAC[VAL_BOUND_64] THEN CONJ_TAC THENL
       [REWRITE_TAC[COND_RAND; COND_RATOR] THEN
        REWRITE_TAC[ARITH_RULE `z - n:num < 2 EXP 64 <=> z < n + 2 EXP 64`] THEN
        UNDISCH_TAC `z0 < 2 EXP 64 + 2 * n` THEN
        UNDISCH_TAC `n < 2 EXP 64` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        UNDISCH_TAC
         `(if &2 pow 64 <= &z0 then &z0 - &n:real else &z0) = &z1` THEN
        REAL_ARITH_TAC;
        EXPAND_TAC "z1" THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
        REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES;
                    WORD_SUB_0]
        THENL [ALL_TAC; CONV_TAC NUMBER_RULE] THEN
        DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP (ARITH_RULE
         `a <= b ==> !n. n < a ==> n <= b`)) THEN
        ASM_SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB] THEN
        DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[INT_VAL_WORD_SUB_CASES] THEN
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
        COND_CASES_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
        CONV_TAC INTEGER_RULE];
      COND_CASES_TAC THEN REWRITE_TAC[CONG_REFL] THEN
      SUBGOAL_THEN `n:num <= z1` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`n < 2 EXP 64`; `2 EXP 64 <= z1`] THEN
        ARITH_TAC;
        SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB]] THEN
      UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE];
    ALL_TAC] THEN

  (*** The final one-word reciprocal multiplication ***)

  GHOST_INTRO_TAC `z:int64` `read X8` THEN
  ABBREV_TAC
   `q = ((2 EXP 64 + val(w:int64)) * val(z:int64)) DIV 2 EXP (128 - e)` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BIGNUM_CMOD_EXEC [1;2] (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_BITVAL; COND_SWAP]) THEN
  MP_TAC(ISPEC `word m:int64` WORD_CLZ_LT_DIMINDEX) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM VAL_EQ] THEN
  ASM_REWRITE_TAC[VAL_WORD_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_jushr
      (word_subword ((word_join:int64->int64->int128)
                     (word (bitval carry_s2)) sum_s2) (1,64))
      (word_xor (word e) (word 63)):int64 =
    word q`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[word_jushr; DIMINDEX_64] THEN
    ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
    REWRITE_TAC[ARITH_RULE `63 = 2 EXP 6 - 1`] THEN
    ASM_SIMP_TAC[WORD_XOR_MASK_WORD; VAL_WORD_LT; VAL_WORD_SUB_CASES;
                 ARITH_RULE `e < 64 ==> e < 2 EXP 6`] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    ASM_REWRITE_TAC[ARITH_RULE `e <= 63 <=> e < 64`] THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `63 - e < 64`] THEN
    SIMP_TAC[word_ushr; VAL_WORD_SUBWORD_JOIN; DIMINDEX_64;
             ARITH_LE; ARITH_LT; VAL_WORD_BITVAL; EXP_1] THEN
    SIMP_TAC[MOD_LT; BITVAL_BOUND; VAL_BOUND_64; DIV_DIV; ARITH_RULE
     `c <= 1 /\ s < 2 EXP 64 ==> (2 EXP 64 * c + s) DIV 2 < 2 EXP 64`] THEN
    AP_TERM_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    SUBGOAL_THEN `128 - e = 64 + SUC(63 - e)` SUBST1_TAC THENL
     [UNDISCH_TAC `e < 64` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
    ASM_REWRITE_TAC[ARITH_RULE `a + z:num = z + b <=> a = b`] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    SIMP_TAC[DIV_LT; VAL_BOUND_64; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ADD_CLAUSES];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  SUBGOAL_THEN `q * m:num <= val(z:int64)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= m * n /\ (n * q) * inv e <= z ==> (q / e - m) * n <= z`) THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL] THEN
    SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH_EQ;
                 ARITH_RULE `e <= 64 ==> e <= 128`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(m * ww) * e:real = (e * m) * ww`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `q < 2 EXP 64 /\ q * m < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `!z. q * m <= z /\ z < e /\ q * 1 <= q * m
          ==> q < e /\ q * m < e`) THEN
    EXISTS_TAC `val(z:int64)` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL; VAL_BOUND_64] THEN ASM_SIMP_TAC[LE_1];
    ALL_TAC] THEN
  ARM_STEPS_TAC BIGNUM_CMOD_EXEC (7--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  REABBREV_TAC `z' = read X8 s8` THEN
  SUBGOAL_THEN
   `val(z':int64) < 2 * m /\ a MOD m = val(z':int64) MOD m`
  (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THENL
   [SUBGOAL_THEN `val(z':int64) = val(z:int64) - q * m` SUBST1_TAC THENL
    [EXPAND_TAC "z'" THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
     ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64];
     ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `q * m <= a /\ a < (q + 2) * m ==> a - q * m < 2 * m`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "q" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
      MATCH_MP_TAC(REAL_ARITH
       `m * n <= &1 * n /\ z < (q + &1) * n
        ==> z:real < (q - m + &2) * n`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_LT_POW2] THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
        SIMP_TAC[MOD_LT_EQ; LT_IMP_LE; EXP_EQ_0; ARITH_EQ];
        ASM_SIMP_TAC[REAL_POS; REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH_EQ;
                     ARITH_RULE `e <= 64 ==> e <= 128`] THEN
        REWRITE_TAC[REAL_FIELD
         `(wz / (&2 pow d / &2 pow e) + &1) * m =
          (wz / &2 pow d + &1 / &2 pow e) * (&2 pow e * m)`] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[REAL_ARITH `z < ((ww * z) / &2 pow 128 + e) * n <=>
                         z * (&2 pow 128 - ww * n) < &2 pow 128 * e * n`] THEN
        TRANS_TAC REAL_LET_TRANS `&(val(z:int64)) * &n` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1] THEN
        TRANS_TAC REAL_LTE_TRANS `(&2:real) pow 64` THEN
        SIMP_TAC[REAL_OF_NUM_CLAUSES; VAL_BOUND_64] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; real_div; REAL_MUL_LID] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
        REWRITE_TAC[GSYM REAL_POW_ADD] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `e <= 64` THEN ARITH_TAC];
      UNDISCH_TAC `(val(z:int64) == a) (mod m)` THEN
      ASM_REWRITE_TAC[GSYM CONG; num_congruent] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE];
    ASM_SIMP_TAC[MOD_CASES]] THEN
  ARM_STEPS_TAC BIGNUM_CMOD_EXEC (9--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0] THEN
  ASM_REWRITE_TAC[WORD_SUB; WORD_VAL]);;

let BIGNUM_CMOD_SUBROUTINE_CORRECT = prove
 (`!k x m a pc returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_cmod_mc /\
              read PC s = word pc /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [k;x;m] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read PC s = returnaddress /\
              (~(val m = 0) ==> C_RETURN s = word(a MOD val m)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMOD_EXEC BIGNUM_CMOD_CORRECT);;
