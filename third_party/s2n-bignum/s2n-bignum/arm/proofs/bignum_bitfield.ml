(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time bitfield selection from bignum.                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_bitfield.o";;
 ****)

let bignum_bitfield_mc =
  define_assert_from_elf "bignum_bitfield_mc" "arm/generic/bignum_bitfield.o"
[
  0xb4000340;       (* arm_CBZ X0 (word 104) *)
  0x92401448;       (* arm_AND X8 X2 (rvalue (word 63)) *)
  0xd346fc42;       (* arm_LSR X2 X2 (rvalue (word 6)) *)
  0x91000442;       (* arm_ADD X2 X2 (rvalue (word 1)) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xf8667827;       (* arm_LDR X7 X1 (Shiftreg_Offset X6 3) *)
  0xeb0200df;       (* arm_CMP X6 X2 *)
  0x9a8430e4;       (* arm_CSEL X4 X7 X4 Condition_CC *)
  0x9a8500e5;       (* arm_CSEL X5 X7 X5 Condition_EQ *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xeb0000df;       (* arm_CMP X6 X0 *)
  0x54ffff43;       (* arm_BCC (word 2097128) *)
  0xeb0200df;       (* arm_CMP X6 X2 *)
  0x9a8433e4;       (* arm_CSEL X4 XZR X4 Condition_CC *)
  0xeb1f011f;       (* arm_CMP X8 XZR *)
  0x9a8503e5;       (* arm_CSEL X5 XZR X5 Condition_EQ *)
  0x9ac82484;       (* arm_LSR X4 X4 X8 *)
  0xcb0803e8;       (* arm_NEG X8 X8 *)
  0x9ac820a5;       (* arm_LSL X5 X5 X8 *)
  0xaa050087;       (* arm_ORR X7 X4 X5 *)
  0xf101007f;       (* arm_CMP X3 (rvalue (word 64)) *)
  0x9a9f27e8;       (* arm_CSET X8 Condition_CC *)
  0x9ac32108;       (* arm_LSL X8 X8 X3 *)
  0xd1000508;       (* arm_SUB X8 X8 (rvalue (word 1)) *)
  0x8a0800e0;       (* arm_AND X0 X7 X8 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_BITFIELD_EXEC = ARM_MK_EXEC_RULE bignum_bitfield_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_BITFIELD_CORRECT = prove
 (`!k x n l a pc.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_bitfield_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [k;x;n;l] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read PC s = word(pc + 0x68) /\
              C_RETURN s = word((a DIV (2 EXP val n)) MOD (2 EXP val l)))
         (MAYCHANGE [PC; X0; X2; X4; X5; X6; X7; X8] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY W64_GEN_TAC [`n:num`; `l:num`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `a:num` THEN

  (*** The trivial case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_BITFIELD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN

  (*** Ghost the uninitialized variable d, which gets assigned in the loop ***)

  GHOST_INTRO_TAC `d0:int64` `read X4` THEN

  (*** Main loop setup ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x18` `pc + 0x2c`
   `\i s. read X0 s = word k /\
          read X1 s = x /\
          read X2 s = word(n DIV 64 + 1) /\
          read X3 s = word l /\
          read X4 s = (if i = 0 then d0
                       else word(bigdigit a (MIN (i - 1) (n DIV 64)))) /\
          read X5 s = (if i <= n DIV 64 + 1 then word 0
                       else word(bigdigit a (n DIV 64 + 1))) /\
          read X6 s = word i /\
          read X8 s = word(n MOD 64) /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits a i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LOWDIGITS_0; BIGDIGIT_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[HIGHDIGITS_0; LE_0] THEN
    REWRITE_TAC[ARITH_RULE `64 = 2 EXP 6 /\ 63 = 2 EXP 6 - 1`] THEN
    ASM_REWRITE_TAC[word_ushr; WORD_ADD] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[WORD_VAL_GALOIS; VAL_WORD_AND_MASK_WORD] THEN
    ASM_REWRITE_TAC[MOD_MOD_EXP_MIN; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    VAL_INT64_TAC `n DIV 64 + 1` THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
    CONJ_TAC THEN AP_TERM_TAC THENL
     [SIMP_TAC[ARITH_RULE `~(i < n + 1) ==> MIN (i - 1) n = n`] THEN
      REWRITE_TAC[ADD_SUB; ARITH_RULE
       `MIN i n = if i < n + 1 then i else n`] THEN
      ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ARITH_RULE `0 < n + 1`] THEN
      MESON_TAC[];
      ASM_CASES_TAC `i = n DIV 64 + 1` THEN
      ASM_REWRITE_TAC[LE_ADD_RCANCEL; ARITH_RULE `~(n + 1 <= n)`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `i <= n + 1 <=> i = n + 1 \/ i <= n`]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Outcome of the digit-pair selection tidied up and uncluttered ***)

  ENSURES_SEQUENCE_TAC `pc + 0x3c`
   `\s. read X3 s = word l /\
        read X4 s = word(bigdigit a (n DIV 64)) /\
        read X5 s = word(bigdigit a (n DIV 64 + 1)) /\
        read X8 s = word(n MOD 64)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    VAL_INT64_TAC `n DIV 64 + 1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `k < n + 1 <=> k <= n`] THEN
    SIMP_TAC[ARITH_RULE `~(k <= n) ==> MIN (k - 1) n = n`] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIGDIGIT_ZERO THEN
    TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[LE_EXP] THENL
     [UNDISCH_TAC `k <= n DIV 64`; UNDISCH_TAC `k <= n DIV 64 + 1`] THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The fiddling round to make the final bitfield ***)

  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VAL_INT64_TAC `n MOD 64` THEN
  ASM_REWRITE_TAC[WORD_SUB_0; WORD_SUB_LZERO; word_jshl; word_jushr] THEN
  REWRITE_TAC[word_shl; word_ushr; DIMINDEX_64; VAL_WORD_1; MULT_CLAUSES] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; MOD_MOD_REFL] THEN

  SUBGOAL_THEN
   `word_sub
     (word (val(if 64 <= l then word 0 else word 1:int64) * 2 EXP (l MOD 64)))
     (word 1):int64 =
    word(2 EXP l - 1)`
  SUBST1_TAC THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[GSYM MASK_WORD_SUB] THEN
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[MOD_LT; VAL_WORD_0; VAL_WORD_1; MULT_CLAUSES] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64; GSYM DIVIDES_MOD] THEN
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_AND_MASK_WORD]] THEN

  GEN_REWRITE_TAC BINOP_CONV [GSYM WORD_MOD_SIZE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `MIN a b = MIN b a`] THEN
  REWRITE_TAC[GSYM MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN

  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; WORD_OR_0; EXP; DIV_1] THEN
    SIMP_TAC[VAL_WORD; MOD_MOD_REFL; bigdigit; DIMINDEX_64; MOD_MOD_REFL] THEN
    MP_TAC(SPECL [`n:num`; `64`] (CONJUNCT2 DIVISION_SIMP)) THEN
    ASM_SIMP_TAC[ADD_CLAUSES];
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND]] THEN

  SUBGOAL_THEN
   `val(word_neg(word (n MOD 64)):int64) MOD 64 = 64 - n MOD 64`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `64` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(n MOD 64 = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `n - b + b = n /\ (a + b == 0) (mod n) ==> (a == n - b) (mod n)`) THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `word(n MOD 64):int64` CONG_WORD_NEG) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o SPEC `2 EXP 6` o MATCH_MP (NUMBER_RULE
     `!m:num. (a == b) (mod n) ==> m divides n ==> (a == b) (mod m)`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN

  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o
    lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_AND] THEN
    MP_TAC(ISPECL [`word(bigdigit a (n DIV 64)):int64`; `n MOD 64`]
        BIT_WORD_USHR) THEN
    MP_TAC(ISPECL [`word(bigdigit a (n DIV 64 + 1)):int64`; `64 - n MOD 64`]
        BIT_WORD_SHL) THEN
    REWRITE_TAC[word_ushr; word_shl] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    REWRITE_TAC[ARITH_RULE `64 - n MOD 64 <= i <=> 64 <= i + n MOD 64`] THEN
    REWRITE_TAC[GSYM DIMINDEX_64] THEN MESON_TAC[BIT_TRIVIAL];
    DISCH_THEN SUBST1_TAC] THEN

  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN

  MP_TAC(ARITH_RULE `n = 64 * n DIV 64 + n MOD 64`) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  REWRITE_TAC[GSYM highdigits; EXP_ADD; GSYM DIV_DIV] THEN
  REPLICATE_TAC 2 (ONCE_REWRITE_TAC[HIGHDIGITS_STEP]) THEN

  REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD; ARITH_RULE
   `(e * (e * a + b) + c):num = (e * e) * a + e * b + c`] THEN
  SUBGOAL_THEN
   `2 EXP (64 + 64) =
    2 EXP (n MOD 64 + 64) * 2 EXP (64 - n MOD 64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM MULT_ASSOC; MOD_MULT_ADD]] THEN

  REWRITE_TAC[GSYM DIV_MOD; EXP_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP 64 = 2 EXP (n MOD 64) * 2 EXP (64 - n MOD 64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH]] THEN
  ARITH_TAC);;

let BIGNUM_BITFIELD_SUBROUTINE_CORRECT = prove
 (`!k x n l a pc returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_bitfield_mc /\
              read PC s = word pc /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [k;x;n;l] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word((a DIV (2 EXP val n)) MOD (2 EXP val l)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_BITFIELD_EXEC BIGNUM_BITFIELD_CORRECT);;
