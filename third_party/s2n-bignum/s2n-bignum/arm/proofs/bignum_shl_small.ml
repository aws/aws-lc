(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shifting of a bignum left < 64 bits.                                      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_shl_small.o";;
 ****)

let bignum_shl_small_mc =
  define_assert_from_elf "bignum_shl_small_mc" "arm/generic/bignum_shl_small.o"
[
  0xeb00005f;       (* arm_CMP X2 X0 *)
  0x9a822002;       (* arm_CSEL X2 X0 X2 Condition_CS *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xb40001a2;       (* arm_CBZ X2 (word 52) *)
  0xf240149f;       (* arm_TST X4 (rvalue (word 63)) *)
  0xda9f03e8;       (* arm_CSETM X8 Condition_NE *)
  0xcb0403e5;       (* arm_NEG X5 X4 *)
  0xf86a7869;       (* arm_LDR X9 X3 (Shiftreg_Offset X10 3) *)
  0x9ac42126;       (* arm_LSL X6 X9 X4 *)
  0xaa0700c6;       (* arm_ORR X6 X6 X7 *)
  0x9ac52527;       (* arm_LSR X7 X9 X5 *)
  0x8a0800e7;       (* arm_AND X7 X7 X8 *)
  0xf82a7826;       (* arm_STR X6 X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xeb02015f;       (* arm_CMP X10 X2 *)
  0x54ffff03;       (* arm_BCC (word 2097120) *)
  0xeb00015f;       (* arm_CMP X10 X0 *)
  0x54000142;       (* arm_BCS (word 40) *)
  0xf82a7827;       (* arm_STR X7 X1 (Shiftreg_Offset X10 3) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xeb00015f;       (* arm_CMP X10 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xf82a783f;       (* arm_STR XZR X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xeb00015f;       (* arm_CMP X10 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xaa0703e0;       (* arm_MOV X0 X7 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SHL_SMALL_EXEC = ARM_MK_EXEC_RULE bignum_shl_small_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let lemma1 = prove
 (`!n c. word_and (word_jushr (word n) (word_neg (word c)))
                  (word_neg (word (bitval (~(c MOD 64 = 0))))):int64 =
         word_ushr (word n) (64 - c MOD 64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_AND_MASK; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
    REWRITE_TAC[SUB_0] THEN MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[VAL_BOUND_64];
    W(MP_TAC o PART_MATCH (lhand o rand) WORD_JUSHR_NEG o lhand o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_64; MOD_64_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC DIVIDES_CONV]);;

let BIGNUM_SHL_SMALL_CORRECT = prove
 (`!p z n x a c pc.
        nonoverlapping (word pc,0x78) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_shl_small_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = word(pc + 0x74) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (2 EXP (val c MOD 64) * a) (val p) /\
                  (p = n
                   ==> C_RETURN s =
                       word(highdigits (2 EXP (val c MOD 64) * a) (val p))))
             (MAYCHANGE [PC; X0; X2; X5; X6; X7; X8; X9; X10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `a:num` THEN W64_GEN_TAC `c:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Remove some redundancy in conclusion ***)

  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x70`
   `\s. 2 EXP (64 * p) * val(read X7 s) + bignum_from_memory(z,p) s =
        2 EXP (c MOD 64) * lowdigits a p` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `carryout:int64` `read X7` THEN
    ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC [1] THEN
    UNDISCH_THEN
     `2 EXP (64 * p) * val(carryout:int64) +
      read (memory :> bytes (z,8 * p)) s1 =
      2 EXP (c MOD 64) * lowdigits a p`
     (fun th -> MP_TAC(AP_TERM `\x. x DIV 2 EXP (64 * p)` th) THEN
                MP_TAC(AP_TERM `\x. x MOD 2 EXP (64 * p)` th)) THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES;
      DIV_LT; MOD_LT_EQ; MOD_LT; lowdigits; highdigits;
      REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] BIGNUM_FROM_MEMORY_BOUND] THEN
    CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[VAL_WORD_GALOIS] THEN
    REPLICATE_TAC 2 (DISCH_THEN(K ALL_TAC)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN ASM_SIMP_TAC[MOD_LT]] THEN

  (*** Reshuffle to handle clamping and just assume n <= p ***)

  ENSURES_SEQUENCE_TAC `pc + 0x10`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word(MIN n p) /\
        read X3 s = x /\
        read X4 s = word c /\
        read X7 s = word 0 /\
        read X10 s = word 0 /\
        bignum_from_memory(x,MIN n p) s = lowdigits a p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
  SUBGOAL_THEN
   `!w n. w = z \/
          nonoverlapping_modulo (2 EXP 64) (val w,8 * n) (val z,8 * p)
          ==> w:int64 = z \/
              nonoverlapping_modulo (2 EXP 64)
                 (val w,8 * MIN n p) (val z,8 * p)`
   (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th))
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`c < 2 EXP 64`; `p < 2 EXP 64`;
    `val(word c:int64) = c`; `val(word p:int64) = p`] THEN
  SUBGOAL_THEN `MIN n p < 2 EXP 64` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  MP_TAC(ARITH_RULE `MIN n p <= p`) THEN
  MAP_EVERY SPEC_TAC
   [`lowdigits a p`,`a:num`; `MIN n p`,`n:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  VAL_INT64_TAC `n:num` THEN BIGNUM_RANGE_TAC "n" "a" THEN
  SUBGOAL_THEN `a < 2 EXP (64 * p)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_REWRITE_TAC[ARITH_EQ; LE_MULT_LCANCEL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Break into two pieces at "tail", handle main loop "loop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x44`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X10 s = word n /\
        2 EXP (64 * n) * val (read X7 s) + bignum_from_memory(z,n) s =
        2 EXP (c MOD 64) * a` THEN
  CONJ_TAC THENL

(* ------------------------------------------------------------------------- *)
(* TOOD                                                                      *)
(* ------------------------------------------------------------------------- *)

   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_SHL_SMALL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; ADD_CLAUSES];
      ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `n:num` `pc + 0x20` `pc + 0x3c`
     `\i s. read X0 s = word p /\
            read X1 s = z /\
            read X2 s = word n /\
            read X3 s = x /\
            read X4 s = word c /\
            read X5 s = word_neg(word c) /\
            read X8 s = word_neg(word(bitval(~(c MOD 64 = 0)))) /\
            read X10 s = word i /\
            bignum_from_memory(word_add x (word (8 * i)),n - i) s =
            highdigits a i /\
            2 EXP (64 * i) * val(read X7 s) +
            bignum_from_memory(z,i) s =
            2 EXP (c MOD 64) * lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--4) THEN
      SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[LOWDIGITS_0; DIV_0; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES;
                  WORD_ADD_0; HIGHDIGITS_0; SUB_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_SUB_LZERO] THEN
      SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)) THEN
      ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN REWRITE_TAC[GSYM WORD_MASK] THEN
      SUBST1_TAC(ARITH_RULE `63 = 2 EXP 6 - 1`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_64_CLAUSES];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `i:num < p` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      GHOST_INTRO_TAC `b:int64` `read X7` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - i = 0 <=> ~(i < n)`] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_64_CLAUSES; LOWDIGITS_CLAUSES] THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `ee * b + m:num = c * l
        ==> e * d + y = c * z + b
            ==> (ee * e) * d + m + ee * y = c * (ee * z + l)`)) THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL; lemma1] THEN
      REWRITE_TAC[word_jshl; MOD_64_CLAUSES; DIMINDEX_64; VAL_WORD_USHR] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o
        rand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_AND] THEN
        SIMP_TAC[BIT_WORD_SHL; DIMINDEX_64] THEN MATCH_MP_TAC(MESON[]
         `(!i. q i ==> ~s i) ==> !i. p i ==> ~((q i /\ r i) /\ (s i))`) THEN
        REWRITE_TAC[UPPER_BITS_ZERO] THEN
        UNDISCH_THEN
         `2 EXP (64 * i) * val(b:int64) + read (memory :> bytes (z,8 * i)) s7 =
          2 EXP (c MOD 64) * lowdigits a i`
         (MP_TAC o AP_TERM `\x. x DIV 2 EXP (64 * i)`) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        SIMP_TAC[DIV_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
        DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
        GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
        REWRITE_TAC[LT_MULT_LCANCEL; LOWDIGITS_BOUND; EXP_EQ_0; ARITH_EQ];
        DISCH_THEN SUBST1_TAC] THEN
      SIMP_TAC[VAL_WORD_SHL; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      SUBGOAL_THEN `2 EXP 64 = 2 EXP (c MOD 64) * 2 EXP (64 - c MOD 64)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[MOD_MULT2; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB]] THEN
      REWRITE_TAC[DIVISION_SIMP];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2);

      GHOST_INTRO_TAC `b:int64` `read X7` THEN
      ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]];

    ALL_TAC] THEN

  (*** The case p = n ***)

  ASM_CASES_TAC `p:num = n` THENL
   [UNDISCH_THEN `p:num = n` (SUBST_ALL_TAC o SYM) THEN
    ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2);
    ALL_TAC] THEN

  (*** The case p = n + 1 ***)

  ASM_CASES_TAC `p = n + 1` THENL
   [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN
    GHOST_INTRO_TAC `b:int64` `read X7` THEN VAL_INT64_TAC `n + 1` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ARITH_RULE `~(n + 1 <= n)`) THEN DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD; LE_REFL] THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** the tail loop "zloop" ***)

  ENSURES_WHILE_AUP_TAC `n + 1` `p:num` `pc + 0x60` `pc + 0x68`
   `\i s. read X0 s = word p /\
          read X1 s = z /\
          read X10 s = word i /\
          read X7 s = word 0 /\
          bignum_from_memory (z,i) s = 2 EXP (c MOD 64) * a` THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;

    GHOST_INTRO_TAC `b:int64` `read X7` THEN VAL_INT64_TAC `n + 1` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ARITH_RULE `n:num <= p ==> (p <= n <=> p = n)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_SHL_SMALL_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `p <= n + 1 <=> p <= n \/ p = n + 1`] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2) THEN
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2);

    ARM_SIM_TAC BIGNUM_SHL_SMALL_EXEC (1--2) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES]]);;

let BIGNUM_SHL_SMALL_SUBROUTINE_CORRECT = prove
 (`!p z n x a c pc returnaddress.
        nonoverlapping (word pc,0x78) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_shl_small_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p;z;n;x;c] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (2 EXP (val c MOD 64) * a) (val p) /\
                  (p = n
                   ==> C_RETURN s =
                       word(highdigits (2 EXP (val c MOD 64) * a) (val p))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_SHL_SMALL_EXEC BIGNUM_SHL_SMALL_CORRECT);;
