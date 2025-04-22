(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negating multiply-accumulate of bignum by a single word.                  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_cmnegadd.o";;
 ****)

let bignum_cmnegadd_mc =
  define_assert_from_elf "bignum_cmnegadd_mc" "arm/generic/bignum_cmnegadd.o"
[
  0xeb00007f;       (* arm_CMP X3 X0 *)
  0x9a832003;       (* arm_CSEL X3 X0 X3 Condition_CS *)
  0xcb030000;       (* arm_SUB X0 X0 X3 *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xb4000543;       (* arm_CBZ X3 (word 168) *)
  0xf9400088;       (* arm_LDR X8 X4 (Immediate_Offset (word 0)) *)
  0xaa2803e8;       (* arm_ORN X8 XZR X8 *)
  0x9b087c47;       (* arm_MUL X7 X2 X8 *)
  0x9bc87c46;       (* arm_UMULH X6 X2 X8 *)
  0xab0200e7;       (* arm_ADDS X7 X7 X2 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xf9400029;       (* arm_LDR X9 X1 (Immediate_Offset (word 0)) *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0xf9000029;       (* arm_STR X9 X1 (Immediate_Offset (word 0)) *)
  0xd2800105;       (* arm_MOV X5 (rvalue (word 8)) *)
  0xd1000463;       (* arm_SUB X3 X3 (rvalue (word 1)) *)
  0xb40001a3;       (* arm_CBZ X3 (word 52) *)
  0xf8656888;       (* arm_LDR X8 X4 (Register_Offset X5) *)
  0xf8656829;       (* arm_LDR X9 X1 (Register_Offset X5) *)
  0xaa2803e8;       (* arm_ORN X8 XZR X8 *)
  0x9b087c47;       (* arm_MUL X7 X2 X8 *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0x9bc87c46;       (* arm_UMULH X6 X2 X8 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0xf8256829;       (* arm_STR X9 X1 (Register_Offset X5) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd1000463;       (* arm_SUB X3 X3 (rvalue (word 1)) *)
  0xb5fffea3;       (* arm_CBNZ X3 (word 2097108) *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xcb060046;       (* arm_SUB X6 X2 X6 *)
  0xb40001e0;       (* arm_CBZ X0 (word 60) *)
  0xf8656829;       (* arm_LDR X9 X1 (Register_Offset X5) *)
  0xeb060129;       (* arm_SUBS X9 X9 X6 *)
  0xf8256829;       (* arm_STR X9 X1 (Register_Offset X5) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb40000e0;       (* arm_CBZ X0 (word 28) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xf8656829;       (* arm_LDR X9 X1 (Register_Offset X5) *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xf8256829;       (* arm_STR X9 X1 (Register_Offset X5) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffff60;       (* arm_CBNZ X0 (word 2097132) *)
  0x9a9f27e0;       (* arm_CSET X0 Condition_CC *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xaa0603e0;       (* arm_MOV X0 X6 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMNEGADD_EXEC = ARM_MK_EXEC_RULE bignum_cmnegadd_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CMNEGADD_CORRECT = prove
 (`!p z d c n x a pc.
        nonoverlapping (word pc,0xc0) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmnegadd_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory(z,val p) s = d /\
                  bignum_from_memory(x,val n) s = a)
             (\s. read PC s = word(pc + 0xbc) /\
                  &(bignum_from_memory (z,val p) s) =
                  (&d - &(val c) * &a) rem (&2 pow (64 * val p)) /\
                  (val n <= val p
                   ==> &(bignum_from_memory (z,val p) s) -
                       &2 pow (64 * val p) * &(val(C_RETURN s)):int =
                       &d - &(val c) * &a))
             (MAYCHANGE [PC; X0; X3; X5; X6; X7; X8; X9] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN MAP_EVERY X_GEN_TAC [`z:int64`; `d:num`] THEN
  W64_GEN_TAC `c:num` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Target the end label, removing redundancy in conclusion ***)

  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN
  ENSURES_SEQUENCE_TAC `pc + 0xb8`
   `\s. &(bignum_from_memory (z,p) s) -
        &2 pow (64 * p) * &(val(read X6 s)):int =
        &d - &c * &(lowdigits a p)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[int_eq; int_sub_th; int_mul_th; int_pow_th; int_of_num_th];
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read X6` THEN
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[INT_REM_UNIQUE] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_ABS_NUM] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; LE_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; GSYM INT_OF_NUM_CLAUSES] THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (INT_ARITH
        `a - b:int = c ==> a = b + c`)) THEN
      REWRITE_TAC[lowdigits; GSYM INT_REM_EQ; GSYM INT_OF_NUM_REM] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN CONV_TAC INTEGER_RULE;
      DISCH_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
      MATCH_MP_TAC LOWDIGITS_SELF THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
      UNDISCH_TAC `n:num <= p` THEN ARITH_TAC]] THEN

  (*** Reshuffle to handle clamping and just assume n <= p ***)

  ENSURES_SEQUENCE_TAC `pc + 0x10`
   `\s. read X0 s = word(p - MIN n p) /\
        read X1 s = z /\
        read X2 s = word c /\
        read X3 s = word(MIN n p) /\
        read X4 s = x /\
        read X6 s = word 0 /\
        bignum_from_memory (z,p) s = d /\
        bignum_from_memory(x,MIN n p) s = lowdigits a p` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMNEGADD_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    REWRITE_TAC[WORD_SUB; ARITH_RULE `MIN n p <= p`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC;
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
  VAL_INT64_TAC `n:num` THEN
  BIGNUM_RANGE_TAC "n" "a" THEN BIGNUM_RANGE_TAC "p" "d" THEN
  SUBGOAL_THEN `a < 2 EXP (64 * p)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_REWRITE_TAC[ARITH_EQ; LE_MULT_LCANCEL];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** The trivial case n = 0 ***)

  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Split at the "tail" label and do the main loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0x74`
   `\s. read X0 s = word(p - n) /\
        read X1 s = z /\
        read X2 s = word c /\
        read X5 s = word(8 * n) /\
        bignum_from_memory(word_add z (word(8 * n)),p - n) s =
        highdigits d n /\
        &(bignum_from_memory (z,n) s):real =
        &(lowdigits d n) - &c * &a +
        &2 pow (64 * n) *
        (&c - &(bitval(read CF s)) - &(val(read X6 s)))` THEN
  CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x40`
     `\s. read X0 s = word(p - n) /\
          read X1 s = z /\
          read X2 s = word c /\
          read X3 s = word(n - 1) /\
          read X4 s = x /\
          read X5 s = word 8 /\
          bignum_from_memory (word_add z (word (8 * 1)),p - 1) s =
          highdigits d 1 /\
          bignum_from_memory (word_add x (word (8 * 1)),n - 1) s =
          highdigits a 1 /\
          &(bignum_from_memory (z,1) s):real =
          &(lowdigits d 1) - &c * &(lowdigits a 1) +
          &2 pow (64 * 1) *
          (&c - &(bitval(read CF s)) - &(val(read X6 s)))` THEN
    CONJ_TAC THENL
     [ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `bignum_from_memory(x,n) s0 = highdigits a 0 /\
                    bignum_from_memory(z,p) s0 = highdigits d 0` MP_TAC THENL
       [ASM_REWRITE_TAC[HIGHDIGITS_0];
        GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
          [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
        STRIP_TAC] THEN
      ARM_ACCSTEPS_TAC BIGNUM_CMNEGADD_EXEC [4;6;7;9] (1--12) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING] THEN
      REWRITE_TAC[MULT_CLAUSES] THEN
      ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; LOWDIGITS_1] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN

    (*** Now the case n = 1 ***)

    ASM_CASES_TAC `n = 1` THENL
     [UNDISCH_THEN `n = 1` SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[SUB_REFL; BIGNUM_FROM_MEMORY_TRIVIAL; HIGHDIGITS_ZERO] THEN
      ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; MULT_CLAUSES];
      ALL_TAC] THEN

    (*** The main loop ***)

    SUBGOAL_THEN `1 < n /\ ~(n - 1 = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN

    ENSURES_WHILE_AUP_TAC `1` `n:num` `pc + 0x44` `pc + 0x70`
     `\i s. read X0 s = word(p - n) /\
            read X1 s = z /\
            read X2 s = word c /\
            read X3 s = word(n - i) /\
            read X4 s = x /\
            read X5 s = word(8 * i) /\
            bignum_from_memory(word_add z (word (8 * i)),p - i) s =
            highdigits d i /\
            bignum_from_memory(word_add x (word (8 * i)),n - i) s =
            highdigits a i /\
            &(bignum_from_memory (z,i) s):real =
            &(lowdigits d i) - &c * &(lowdigits a i) +
            &2 pow (64 * i) *
            (&c - &(bitval(read CF s)) - &(val(read X6 s)))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GHOST_INTRO_TAC `hin:int64` `read X6` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1] THEN
      VAL_INT64_TAC `n - 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
      ALL_TAC; (*** Main loop invariant ***)
      REPEAT STRIP_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMNEGADD_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      VAL_INT64_TAC `n - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
      ASM_SIMP_TAC[SUB_ADD; LE_1; SUB_REFL] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X6` THEN
      ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

    (*** the final loop invariant ***)

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
    ARM_ACCSIM_TAC BIGNUM_CMNEGADD_EXEC [4;5;7;8] (1--11) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
      CONV_TAC WORD_RULE;
      REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    GEN_REWRITE_TAC LAND_CONV
     [TAUT `p /\ q /\ r /\ s <=> p /\ r /\ q /\ s`] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

    ALL_TAC] THEN

  (*** The absorption of the carry flag adjusting h ***)

  ENSURES_SEQUENCE_TAC `pc + 0x7c`
   `\s. read X0 s = word(p - n) /\
        read X1 s = z /\
        read X5 s = word(8 * n) /\
        bignum_from_memory(word_add z (word(8 * n)),p - n) s =
        highdigits d n /\
        &(bignum_from_memory (z,n) s):real =
        &(lowdigits d n) - &c * &a +
        &2 pow (64 * n) * &(val(read X6 s))` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `hin:int64` `read X6` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC (1--2) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `z = d - ca + e * c
      ==> (c < &0 ==> e * c <= e * --(&1)) /\
          &0 <= z /\ &0 <= ca /\ d < e
          ==> &0 <= c`)) THEN
    ANTS_TAC THENL
     [SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_POW2] THEN CONJ_TAC THENL
       [SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; LOWDIGITS_BOUND]];
      REWRITE_TAC[REAL_ARITH `&0 <= c - b - h <=> h + b <= c`]] THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [COND_RAND] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REWRITE_TAC[VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; DIMINDEX_64; VAL_WORD_BITVAL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `h <= c ==> c < 2 EXP 64 ==> h < 2 EXP 64 /\ h <= c`)) THEN
    ASM_SIMP_TAC[VAL_BOUND_64; VAL_WORD_EQ; DIMINDEX_64] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Case n = p where the tail part is trivial ***)

  MP_TAC(ASSUME `n:num <= p`) THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
  ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THENL
   [GHOST_INTRO_TAC `h:int64` `read X6` THEN
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN REAL_ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n < p ==> n < p /\ ~(p <= n)`))] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x94`
   `\s. read X0 s = word(p - (n + 1)) /\
        read X1 s = z /\
        read X5 s = word(8 * n) /\
        read X6 s = word 0 /\
        bignum_from_memory(word_add z (word(8 * (n + 1))),p - (n + 1)) s =
        highdigits d (n + 1) /\
        &(bignum_from_memory (z,n+1) s):real =
        &(lowdigits d (n + 1)) - &c * &a +
        &2 pow (64 * (n + 1)) * &(bitval(~read CF s))` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `h:int64` `read X6` THEN
    VAL_INT64_TAC `p - n:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_ACCSIM_TAC BIGNUM_CMNEGADD_EXEC [3] (1--6) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC]] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN

  ASM_CASES_TAC `p = n + 1` THENL
   [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC (1--3) THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; BITVAL_CLAUSES; VAL_WORD_0; VAL_WORD_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  ENSURES_WHILE_AUP_TAC `n + 1` `p:num` `pc + 0x98` `pc + 0xac`
   `\i s. read X0 s = word(p - i) /\
          read X1 s = z /\
          read X5 s = word_sub (word(8 * i)) (word 8) /\
          read X6 s = word 0 /\
          bignum_from_memory(word_add z (word (8 * i)),p - i) s =
          highdigits d i /\
          &(bignum_from_memory (z,i) s):real =
          &(lowdigits d i) - &c * &a +
          &2 pow (64 * i) * &(bitval(~read CF s))` THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1] THEN
    VAL_INT64_TAC `p - (n + 1)` THEN ASM_REWRITE_TAC[SUB_EQ_0] THEN
    ASM_REWRITE_TAC[ARITH_RULE `p <= n + 1 <=> p <= n \/ p = n + 1`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC; (** Main invariant ***)
    REPEAT STRIP_TAC THEN VAL_INT64_TAC `p - i:num` THEN
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC [1];
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ARM_SIM_TAC BIGNUM_CMNEGADD_EXEC (1--3) THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; BITVAL_CLAUSES; VAL_WORD_0; VAL_WORD_1] THEN
    REAL_ARITH_TAC] THEN

  (*** Tail loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_CMNEGADD_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x y) y = x`]) THEN
  ARM_ACCSTEPS_TAC BIGNUM_CMNEGADD_EXEC [3] (2--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_ADD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

let BIGNUM_CMNEGADD_SUBROUTINE_CORRECT = prove
 (`!p z d c n x a pc returnaddress.
        nonoverlapping (word pc,0xc0) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmnegadd_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p;z;c;n;x] s /\
                  bignum_from_memory(z,val p) s = d /\
                  bignum_from_memory(x,val n) s = a)
             (\s. read PC s = returnaddress /\
                  &(bignum_from_memory (z,val p) s) =
                  (&d - &(val c) * &a) rem (&2 pow (64 * val p)) /\
                  (val n <= val p
                   ==> &(bignum_from_memory (z,val p) s) -
                       &2 pow (64 * val p) * &(val(C_RETURN s)):int =
                       &d - &(val c) * &a))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMNEGADD_EXEC BIGNUM_CMNEGADD_CORRECT);;
