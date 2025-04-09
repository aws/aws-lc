(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Division by 10 with remainder.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_divmod10.o";;
 ****)

let bignum_divmod10_mc =
  define_assert_from_elf "bignum_divmod10_mc" "arm/generic/bignum_divmod10.o"
[
  0xb4000240;       (* arm_CBZ X0 (word 72) *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xb200e7e5;       (* arm_MOV X5 (rvalue (word 3689348814741910323)) *)
  0x910004a6;       (* arm_ADD X6 X5 (rvalue (word 1)) *)
  0x92406ca5;       (* arm_AND X5 X5 (rvalue (word 268435455)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf8607822;       (* arm_LDR X2 X1 (Shiftreg_Offset X0 3) *)
  0x93c27483;       (* arm_EXTR X3 X4 X2 29 *)
  0xd3417044;       (* arm_UBFM X4 X2 1 28 *)
  0x8b040064;       (* arm_ADD X4 X3 X4 *)
  0x9b057c63;       (* arm_MUL X3 X3 X5 *)
  0x9bc67c84;       (* arm_UMULH X4 X4 X6 *)
  0x8b040063;       (* arm_ADD X3 X3 X4 *)
  0xf8207823;       (* arm_STR X3 X1 (Shiftreg_Offset X0 3) *)
  0x8b030863;       (* arm_ADD X3 X3 (Shiftedreg X3 LSL 2) *)
  0xcb030444;       (* arm_SUB X4 X2 (Shiftedreg X3 LSL 1) *)
  0xb5fffea0;       (* arm_CBNZ X0 (word 2097108) *)
  0xaa0403e0;       (* arm_MOV X0 X4 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DIVMOD10_EXEC = ARM_MK_EXEC_RULE bignum_divmod10_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let divmodsteplemma = prove
 (`(2 EXP 64 * h + l) DIV 10 =
   2 EXP 64 * h DIV 10 + (2 EXP 64 * h MOD 10 + l) DIV 10 /\
   (2 EXP 64 * h + l) MOD 10 =
   (2 EXP 64 * h MOD 10 + l) MOD 10`,
  MATCH_MP_TAC DIVMOD_UNIQ THEN ARITH_TAC);;

let BIGNUM_DIVMOD10_CORRECT = time prove
 (`!k z n pc.
      nonoverlapping (word pc,0x4c) (z,8 * val k)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_divmod10_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [k; z] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read PC s = word (pc + 0x48) /\
                bignum_from_memory (z,val k) s = n DIV 10 /\
                C_RETURN s = word(n MOD 10))
          (MAYCHANGE [PC; X0; X2; X3; X4; X5; X6] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ARM_SIM_TAC BIGNUM_DIVMOD10_EXEC [1] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** Setup of the loop ***)

  ENSURES_WHILE_DOWN_TAC `k:num` `pc + 0x14` `pc + 0x40`
   `\i s. read X1 s = z /\
          read X6 s = word 0x3333333333333334 /\
          read X5 s = word 0x3333333 /\
          read X0 s = word i /\
          bignum_from_memory(z,i) s = lowdigits n i /\
          bignum_from_memory (word_add z (word (8 * i)),k - i) s =
          highdigits n i DIV 10 /\
          read X4 s = word(highdigits n i MOD 10)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_DIVMOD10_EXEC (1--5) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC; (*** The main loop invariant ***)
    REPEAT STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_DIVMOD10_EXEC [1];
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    ARM_SIM_TAC BIGNUM_DIVMOD10_EXEC (1--2) THEN
    ASM_REWRITE_TAC[HIGHDIGITS_0]] THEN

  (*** The loop invariant, starting with tweaking then simulation ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  ASSUME_TAC(WORD_RULE `word_sub (word(i + 1)) (word 1):int64 = word i`) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP] THEN
  MP_TAC(SPEC `k - i:num` BIGNUM_FROM_MEMORY_EXPAND) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word(8 * i))) (word 8) =
    word_add z (word(8 * (i + 1)))`] THEN
  ONCE_REWRITE_TAC[divmodsteplemma] THEN
  MAP_EVERY ABBREV_TAC
   [`q = highdigits n (i + 1) DIV 10`; `r = highdigits n (i + 1) MOD 10`] THEN
  SUBGOAL_THEN `r <= 9` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ARITH_TAC; ALL_TAC] THEN
  ARM_SIM_TAC BIGNUM_DIVMOD10_EXEC (1--11) THEN

  (*** The basic mathematics, reducing to the quotient computation ***)

  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_subword
     ((word_join:int64->int64->int128) (word r) (word (bigdigit n i)))
     (29,64)`;
    `l:int64 = word_subword(word(bigdigit n i):int64) (1,28)`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[WORD_RULE
   `word_sub x (word_shl (word_add q (word_shl q 2)) 1) =
    (y:int64) <=>
    word_add y (word(10 * val(q:int64))) = x`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word a) (word(10 * val(b:int64))):int64 =
    word(10 * val b + a)`] THEN
  MATCH_MP_TAC(MESON[ADD_SYM]
   `(x:num = y ==> q) /\ x = y ==> x + a = a + y /\ q`) THEN
  CONJ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG; DIVISION_SIMP] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_USHR; VAL_WORD_ZX_GEN] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN UNDISCH_TAC `r <= 9` THEN
    MP_TAC(SPECL [`n:num`; `i:num`] BIGDIGIT_BOUND) THEN ARITH_TAC;
    CONV_TAC WORD_REDUCE_CONV] THEN

  (*** The re-splitting into h and l ***)

  SUBGOAL_THEN `val(l:int64) < 2 EXP 28` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[VAL_WORD_SUBWORD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(h:int64) < 2 EXP 39` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    MATCH_MP_TAC(ARITH_RULE
     `r <= 9 /\ w < 2 EXP 64
      ==> 2 EXP (64 - 29) * r MOD 2 EXP 29 + w DIV 2 EXP 29 < 2 EXP 39`) THEN
    REWRITE_TAC[VAL_BOUND_64] THEN MATCH_MP_TAC VAL_WORD_LE THEN
    EXPAND_TAC "r" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(2 EXP 64 * r + bigdigit n i) DIV 10 =
    (2 EXP 28 * val(h:int64) + val(l:int64)) DIV 5`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_BIGDIGIT] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `r <= 9 ==> r < 2 EXP MIN 64 29`] THEN
    REWRITE_TAC[ARITH_RULE
     `(2 EXP 64 * h + l) DIV 2 = 2 EXP 63 * h + l DIV 2`] THEN
    REWRITE_TAC[GSYM DIV_MOD; ARITH_RULE `2 EXP 64 = 2 EXP 36 * 2 EXP 28`] THEN
    SIMP_TAC[DIV_MULT2; GSYM DIV_DIV; EXP_EQ_0; ARITH_EQ; ARITH_RULE
     `2 EXP 36 = 2 EXP 35 * 2 /\ 2 EXP 29 = 2 * 2 EXP 28`] THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The core reciprocal multiplication ***)

  REWRITE_TAC[VAL_WORD; DIMINDEX_64; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
  REWRITE_TAC[CONG_ADD_LCANCEL_EQ; ARITH_RULE
   `(2 EXP 28 * h + l) DIV 5 = h * 53687091 + (h + l) DIV 5`] THEN
  ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; DIMINDEX_128; MOD_LT; ARITH_RULE
    `h < 2 EXP 39 /\ l < 2 EXP 28
      ==> h + l < 2 EXP 64 /\
          (h + l) * 3689348814741910324 < 2 EXP 128`] THEN
  MATCH_MP_TAC EQ_IMP_CONG THEN
  MAP_EVERY UNDISCH_TAC
   [`val(l:int64) < 2 EXP 28`; `val(h:int64) < 2 EXP 39`] THEN
  ARITH_TAC);;

let BIGNUM_DIVMOD10_SUBROUTINE_CORRECT = time prove
 (`!k z n pc returnaddress.
      nonoverlapping (word pc,0x4c) (z,8 * val k)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_divmod10_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; z] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,val k) s = n DIV 10 /\
                C_RETURN s = word (n MOD 10))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DIVMOD10_EXEC BIGNUM_DIVMOD10_CORRECT);;
