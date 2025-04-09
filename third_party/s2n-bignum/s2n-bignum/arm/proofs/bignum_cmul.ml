(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication of bignum by a single word.                                *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_cmul.o";;
 ****)

let bignum_cmul_mc =
  define_assert_from_elf "bignum_cmul_mc" "arm/generic/bignum_cmul.o"
[
  0xeb00007f;       (* arm_CMP X3 X0 *)
  0x9a832003;       (* arm_CSEL X3 X0 X3 Condition_CS *)
  0xcb030000;       (* arm_SUB X0 X0 X3 *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xb4000243;       (* arm_CBZ X3 (word 72) *)
  0xf9400088;       (* arm_LDR X8 X4 (Immediate_Offset (word 0)) *)
  0x9b087c47;       (* arm_MUL X7 X2 X8 *)
  0x9bc87c46;       (* arm_UMULH X6 X2 X8 *)
  0xf9000027;       (* arm_STR X7 X1 (Immediate_Offset (word 0)) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0x54000160;       (* arm_BEQ (word 44) *)
  0xab1f03ff;       (* arm_CMN XZR XZR *)
  0xf8656888;       (* arm_LDR X8 X4 (Register_Offset X5) *)
  0x9b087c47;       (* arm_MUL X7 X2 X8 *)
  0xba0600e7;       (* arm_ADCS X7 X7 X6 *)
  0x9bc87c46;       (* arm_UMULH X6 X2 X8 *)
  0xf8256827;       (* arm_STR X7 X1 (Register_Offset X5) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd1000463;       (* arm_SUB X3 X3 (rvalue (word 1)) *)
  0xb5ffff23;       (* arm_CBNZ X3 (word 2097124) *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xb4000120;       (* arm_CBZ X0 (word 36) *)
  0xf8256826;       (* arm_STR X6 X1 (Register_Offset X5) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xf1000400;       (* arm_SUBS X0 X0 (rvalue (word 1)) *)
  0x540000a0;       (* arm_BEQ (word 20) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xf825683f;       (* arm_STR XZR X1 (Register_Offset X5) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffffa0;       (* arm_CBNZ X0 (word 2097140) *)
  0xaa0603e0;       (* arm_MOV X0 X6 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMUL_EXEC = ARM_MK_EXEC_RULE bignum_cmul_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CMUL_CORRECT = prove
 (`!p z c n x a pc.
        nonoverlapping (word pc,0x88) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = word(pc + 0x84) /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (val c * a) (val p) /\
                  (p = n
                   ==> C_RETURN s = word(highdigits (val c * a) (val p))))
             (MAYCHANGE [PC; X0; X3; X5; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `c:num` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Target the end label, removing redundancy in conclusion ***)

  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x80`
   `\s. 2 EXP (64 * p) * val(read X6 s) + bignum_from_memory (z,p) s =
        c * lowdigits a p` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `t:int64` `read X6` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN
     `2 EXP (64 * p) * val(t:int64) + read (memory :> bytes (z,8 * p)) s1 =
      c * lowdigits a p`
     (fun th ->
        MP_TAC(AP_TERM `\x. x DIV 2 EXP (64 * p)` th) THEN
        MP_TAC(AP_TERM `\x. x MOD 2 EXP (64 * p)` th)) THEN
    ASM_SIMP_TAC[lowdigits; MOD_LT] THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES;
                 DIV_LT; MOD_LT_EQ; MOD_LT; BIGNUM_FROM_MEMORY_BOUND] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[highdigits] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    SIMP_TAC[RDIV_LT_EQ; DIMINDEX_64; EXP_EQ_0; ARITH_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN MATCH_MP_TAC LT_MULT2 THEN
    ASM_MESON_TAC[]] THEN

  (*** Reshuffle to handle clamping and just assume n <= p ***)

  ENSURES_SEQUENCE_TAC `pc + 0x8`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word c /\
        read X3 s = word(MIN n p) /\
        read X4 s = x /\
        bignum_from_memory(x,MIN n p) s = lowdigits a p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
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
   [`c < 2 EXP 64`; `p < 2 EXP 64`; `val(word p:int64) = p`] THEN
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

  (*** Do the part from the "tail" loop first ***)

  ENSURES_SEQUENCE_TAC `pc + 0x5c`
   `\s. read X0 s = word(p - n) /\
        read X1 s = z /\
        read X5 s = word(8 * n) /\
        2 EXP (64 * n) * val(read X6 s) + bignum_from_memory(z,n) s =
        c * a` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ASSUME `n:num <= p`) THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
    ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
       `n < p ==> n < p /\ ~(p <= n)`))] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x6c`
     `\s. read X0 s = word(p - (n + 1)) /\
          read X1 s = z /\
          read X5 s = word(8 * n) /\
          read X6 s = word 0 /\
          bignum_from_memory(z,n+1) s = c * a /\
          (read ZF s <=> p = n + 1)` THEN
    CONJ_TAC THENL
     [GHOST_INTRO_TAC `h:int64` `read X6` THEN VAL_INT64_TAC `p - n:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
        REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
            BIGNUM_FROM_MEMORY_STEP] THEN
        GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
        VAL_INT64_TAC `p - n:num` THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = n + 1` THENL
     [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN
      ARM_SIM_TAC BIGNUM_CMUL_EXEC [1] THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    ENSURES_WHILE_UP_TAC `p - n - 1` `pc + 0x70` `pc + 0x7c`
     `\i s. read X0 s = word(p - ((n + 1) + i)) /\
            read X1 s = z /\
            read X5 s = word(8 * (n + i)) /\
            read X6 s = word 0 /\
            bignum_from_memory (z,(n + 1) + i) s = c * a` THEN
    REPEAT CONJ_TAC THENL
     [SIMPLE_ARITH_TAC;
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES];
      ALL_TAC; (** Main invariant ***)
      REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      VAL_INT64_TAC `p - ((n + 1) + i)` THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `p - ((n + 1) + p - n - 1) = 0`] THEN
      SUBGOAL_THEN `(n + 1) + p - n - 1 = p` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `n:num < p` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_ASSOC] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
       [ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      CONV_TAC WORD_RULE;
      REWRITE_TAC[REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
            BIGNUM_FROM_MEMORY_STEP] THEN
      ASM_REWRITE_TAC[WORD_RULE
       `word(8 * ((n + 1) +  i)) =
        word_add (word (8 * (n + i))) (word 8)`] THEN
      ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]]] THEN

  (*** The trivial case n = 0 ***)

  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; SUB_0; MULT_CLAUSES] THEN
    REWRITE_TAC[ADD_CLAUSES; WORD_SUB_0];
    ALL_TAC] THEN

  (*** The first digit of the main part, done before the loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0x30`
   `\s. read X0 s = word(p - n) /\
        read X1 s = z /\
        read X2 s = word c /\
        read X3 s = word(n - 1) /\
        read X4 s = x /\
        read X5 s = word 8 /\
        (read ZF s <=> n = 1) /\
        bignum_from_memory(word_add x (word 8),n - 1) s = highdigits a 1 /\
        2 EXP 64 * val(read X6 s) + bignum_from_memory(z,1) s =
        c * lowdigits a 1` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory (x,n) s0 = highdigits a 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0];
      GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_CMUL_EXEC [7] (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    CONV_TAC(LAND_CONV(RAND_CONV BIGNUM_EXPAND_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LOWDIGITS_1] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND];
    ALL_TAC] THEN

  (*** Now the case n = 1 ***)

  ASM_CASES_TAC `n = 1` THENL
   [UNDISCH_THEN `n = 1` SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[SUB_REFL; BIGNUM_FROM_MEMORY_TRIVIAL; HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF];
    ALL_TAC] THEN

  (*** The main loop ***)

  SUBGOAL_THEN `~(n - 1 = 0) /\ 0 < n - 1` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  ENSURES_WHILE_UP_TAC `n - 1` `pc + 0x38` `pc + 0x54`
   `\i s. read X0 s = word(p - n) /\
          read X1 s = z /\
          read X2 s = word c /\
          read X3 s = word(n - (i + 1)) /\
          read X4 s = x /\
          read X5 s = word(8 * (i + 1)) /\
          bignum_from_memory(word_add x (word (8 * (i + 1))),n - (i + 1)) s =
          highdigits a (i + 1) /\
          2 EXP (64 * (i + 1)) * (bitval(read CF s) + val(read X6 s)) +
          bignum_from_memory(z,i + 1) s =
          c * lowdigits a (i + 1)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GHOST_INTRO_TAC `hin:int64` `read X6` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[MULT_CLAUSES; BITVAL_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
    ALL_TAC; (*** Main loop invariant ***)
    REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    VAL_INT64_TAC `n - (i + 1)` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n - 1 ==> i + 1 < n`];
    ASM_SIMP_TAC[SUB_ADD; LE_1; SUB_REFL] THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read X6` THEN
    ARM_ACCSIM_TAC BIGNUM_CMUL_EXEC [2] (1--2) THEN
    UNDISCH_TAC
     `2 EXP (64 * n) * (bitval cin + val(hin:int64)) +
      read (memory :> bytes (z,8 * n)) s2 =
      c * lowdigits a n` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN FIRST_X_ASSUM(SUBST1_TAC o
      MATCH_MP (REAL_ARITH `x:real = a + b ==> b + a = x`)) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(~(e * c = 0) ==> z < c * e)
      ==> e * (c + s) + m = z ==> e * s + m = z`) THEN
    REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; MULT_EQ_0; ARITH_EQ; BITVAL_EQ_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES] THEN
    MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[]] THEN

  (*** the final loop invariant ***)

  X_GEN_TAC `j:num` THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `i < n - 1 ==> 0 < i + 1 /\ ~(i + 1 = 0) /\ i + 1 < n`) o CONJUNCT1) THEN
  SPEC_TAC(`j + 1`,`i:num`) THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < p` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read X6` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ARM_ACCSIM_TAC BIGNUM_CMUL_EXEC [3;4] (1--7) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
    CONV_TAC WORD_RULE;
    REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[EXP_ADD; MULT_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING);;

let BIGNUM_CMUL_SUBROUTINE_CORRECT = prove
 (`!p z c n x a pc returnaddress.
        nonoverlapping (word pc,0x88) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,val p) s =
                  lowdigits (val c * a) (val p) /\
                  (p = n
                   ==> C_RETURN s = word(highdigits (val c * a) (val p))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMUL_EXEC BIGNUM_CMUL_CORRECT);;
