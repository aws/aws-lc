(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of bignums.                                                      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_add.o";;
 ****)

let bignum_add_mc =
  define_assert_from_elf "bignum_add_mc" "arm/generic/bignum_add.o"
[
  0xeb00005f;       (* arm_CMP X2 X0 *)
  0x9a822002;       (* arm_CSEL X2 X0 X2 Condition_CS *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x9a842004;       (* arm_CSEL X4 X0 X4 Condition_CS *)
  0xeb04005f;       (* arm_CMP X2 X4 *)
  0x540002c3;       (* arm_BCC (word 88) *)
  0xcb020000;       (* arm_SUB X0 X0 X2 *)
  0xcb040042;       (* arm_SUB X2 X2 X4 *)
  0xea1f03e6;       (* arm_ANDS X6 XZR XZR *)
  0xb4000104;       (* arm_CBZ X4 (word 32) *)
  0xf8667867;       (* arm_LDR X7 X3 (Shiftreg_Offset X6 3) *)
  0xf86678a8;       (* arm_LDR X8 X5 (Shiftreg_Offset X6 3) *)
  0xba0800e7;       (* arm_ADCS X7 X7 X8 *)
  0xf8267827;       (* arm_STR X7 X1 (Shiftreg_Offset X6 3) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5ffff44;       (* arm_CBNZ X4 (word 2097128) *)
  0xb40000e2;       (* arm_CBZ X2 (word 28) *)
  0xf8667867;       (* arm_LDR X7 X3 (Shiftreg_Offset X6 3) *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xf8267827;       (* arm_STR X7 X1 (Shiftreg_Offset X6 3) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5ffff62;       (* arm_CBNZ X2 (word 2097132) *)
  0xb50002e0;       (* arm_CBNZ X0 (word 92) *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xcb040000;       (* arm_SUB X0 X0 X4 *)
  0xcb020084;       (* arm_SUB X4 X4 X2 *)
  0xea1f03e6;       (* arm_ANDS X6 XZR XZR *)
  0xb4000102;       (* arm_CBZ X2 (word 32) *)
  0xf8667867;       (* arm_LDR X7 X3 (Shiftreg_Offset X6 3) *)
  0xf86678a8;       (* arm_LDR X8 X5 (Shiftreg_Offset X6 3) *)
  0xba0800e7;       (* arm_ADCS X7 X7 X8 *)
  0xf8267827;       (* arm_STR X7 X1 (Shiftreg_Offset X6 3) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5ffff42;       (* arm_CBNZ X2 (word 2097128) *)
  0xf86678a7;       (* arm_LDR X7 X5 (Shiftreg_Offset X6 3) *)
  0xba0703e7;       (* arm_ADCS X7 XZR X7 *)
  0xf8267827;       (* arm_STR X7 X1 (Shiftreg_Offset X6 3) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5ffff64;       (* arm_CBNZ X4 (word 2097132) *)
  0xb5000060;       (* arm_CBNZ X0 (word 12) *)
  0x9a9f37e0;       (* arm_CSET X0 Condition_CS *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0xf8267827;       (* arm_STR X7 X1 (Shiftreg_Offset X6 3) *)
  0x14000002;       (* arm_B (word 8) *)
  0xf826783f;       (* arm_STR XZR X1 (Shiftreg_Offset X6 3) *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xb5ffffa0;       (* arm_CBNZ X0 (word 2097140) *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_ADD_EXEC = ARM_MK_EXEC_RULE bignum_add_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_ADD_CORRECT = prove
 (`!p z m x a n y b pc.
        nonoverlapping (word pc,0xe0) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. (read PC s = word(pc + 0x68) \/
                   read PC s = word(pc + 0xb8) \/
                   read PC s = word(pc + 0xdc)) /\
                  bignum_from_memory (z,val p) s =
                  (a + b) MOD 2 EXP (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) +
                  bignum_from_memory (z,val p) s =
                  lowdigits a (val p) + lowdigits b (val p))
             (MAYCHANGE [PC; X0; X2; X4; X6; X7; X8] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`y:int64`; `b:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Remove redundancy in the conclusion ***)

  ENSURES_POSTCONDITION_TAC
   `\s. (read PC s = word(pc + 0x68) \/
         read PC s = word(pc + 0xb8) \/
         read PC s = word(pc + 0xdc)) /\
        2 EXP (64 * p) * val(read X0 s) +
        bignum_from_memory (z,p) s = lowdigits a p + lowdigits b p` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[lowdigits; MOD_LT] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP (64 * p)`) THEN
    SIMP_TAC[MOD_MULT_ADD; MOD_LT; BIGNUM_FROM_MEMORY_BOUND] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Reshuffle to handle clamping and just assume m <= p and n <= p ***)

  ENSURES_SEQUENCE_TAC `pc + 0x10`
   `\s. read X0 s = word p /\
        read X1 s = z /\
        read X2 s = word(MIN m p) /\
        read X3 s = x /\
        read X4 s = word(MIN n p) /\
        read X5 s = y /\
        bignum_from_memory(x,MIN m p) s = lowdigits a p /\
        bignum_from_memory(y,MIN n p) s = lowdigits b p` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_ADD_EXEC (1--4) THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [GSYM COND_RAND] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
  SUBGOAL_THEN
   `lowdigits (a + b) p = lowdigits (lowdigits a p + lowdigits b p) p`
  SUBST1_TAC THENL
   [REWRITE_TAC[lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w n. w = z \/
          nonoverlapping_modulo (2 EXP 64) (val w,8 * n) (val z,8 * p)
          ==> w:int64 = z \/
              nonoverlapping_modulo (2 EXP 64)
                 (val w,8 * MIN n p) (val z,8 * p)`
   (fun th -> DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP th)))
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`p < 2 EXP 64`; `val(word p:int64) = p`] THEN
  SUBGOAL_THEN `MIN m p < 2 EXP 64 /\ MIN n p < 2 EXP 64` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  MP_TAC(ARITH_RULE `MIN m p <= p /\ MIN n p <= p`) THEN
  MAP_EVERY SPEC_TAC
   [`lowdigits a p`,`a:num`; `lowdigits b p`,`b:num`;
    `MIN m p`,`m:num`; `MIN n p`,`n:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  MAP_EVERY VAL_INT64_TAC [`m:num`; `n:num`] THEN
  BIGNUM_RANGE_TAC "m" "a" THEN BIGNUM_RANGE_TAC "n" "b" THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Case split following the initial branch, m >= n case then m < n ***)

  ASM_CASES_TAC `n:num <= m` THENL
   [SUBGOAL_THEN `~(m:num < n)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `b < 2 EXP (64 * m)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC `pc + 0x44`
     `\s. read X0 s = word(p - m) /\
          read X1 s = z /\
          read X2 s = word(m - n) /\
          read X3 s = x /\
          read X5 s = y /\
          read X6 s = word n /\
          bignum_from_memory (word_add x (word(8 * n)),m - n) s =
          highdigits a n /\
          2 EXP (64 * n) * bitval(read CF s) + bignum_from_memory(z,n) s =
          lowdigits a n + lowdigits b n` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN
        ARM_SIM_TAC BIGNUM_ADD_EXEC (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_UP_TAC `n:num` `pc + 0x28` `pc + 0x40`
       `\i s. read X0 s = word(p - m) /\
              read X1 s = z /\
              read X2 s = word(m - n) /\
              read X3 s = x /\
              read X5 s = y /\
              read X4 s = word(n - i) /\
              read X6 s = word i /\
              bignum_from_memory (word_add x (word(8 * i)),m - i) s =
              highdigits a i /\
              bignum_from_memory (word_add y (word(8 * i)),n - i) s =
              highdigits b i /\
              2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
              lowdigits a i + lowdigits b i` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[SUB_0] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `n - i:num` THEN
        ASM_REWRITE_TAC[] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC [1];
        ARM_SIM_TAC BIGNUM_ADD_EXEC [1]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      ARM_STEPS_TAC BIGNUM_ADD_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
       `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC `pc + 0x60`
     `\s. read X0 s = word(p - m) /\
          read X1 s = z /\
          read X6 s = word m /\
          2 EXP (64 * m) * bitval(read CF s) + bignum_from_memory(z,m) s =
          lowdigits a m + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m:num = n` THENL
       [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[SUB_REFL] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        ARM_SIM_TAC BIGNUM_ADD_EXEC [1] THEN ASM_REWRITE_TAC[VAL_WORD_BITVAL];
        ALL_TAC] THEN
      SUBGOAL_THEN `n < m /\ 0 < m - n /\ ~(m - n = 0)` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `m - n:num` THEN
      ENSURES_WHILE_UP_TAC `m - n:num` `pc + 0x48` `pc + 0x5c`
       `\i s. read X0 s = word(p - m) /\
              read X1 s = z /\
              read X3 s = x /\
              read X2 s = word(m - n - i) /\
              read X6 s = word(n + i) /\
              bignum_from_memory(word_add x (word(8 * (n + i))),
                                 m - (n + i)) s =
              highdigits a (n + i) /\
              2 EXP (64 * (n + i)) * bitval(read CF s) +
              bignum_from_memory(z,n + i) s =
              lowdigits a (n + i) + lowdigits b (n + i)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC [1] THEN
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        ASM_REWRITE_TAC[WORD_RULE `word_sub (word(n + 1)) (word 1) = word n`];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        VAL_INT64_TAC `m - n - i:num` THEN ASM_REWRITE_TAC[] THEN
        ARM_SIM_TAC BIGNUM_ADD_EXEC [1];
        ASM_SIMP_TAC[ARITH_RULE `n:num <= m ==> n + m - n = m`] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        ARM_SIM_TAC BIGNUM_ADD_EXEC [1]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `n:num < m
        ==> (i < m - n <=> n + i < m) /\ (i = m - n <=> n + i = m)`] THEN
      REWRITE_TAC[ARITH_RULE `m - n - i:num = m - (n + i)`] THEN
      REWRITE_TAC[ARITH_RULE `n + i + 1 = (n + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n <= n + j`) THEN
      SPEC_TAC(`n + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      ARM_STEPS_TAC BIGNUM_ADD_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC_0; ADD_CLAUSES; ARITH_RULE
       `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(NUM_RING `b = 0 ==> x = e * b + x`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ASM_CASES_TAC `m:num = p` THENL
     [UNDISCH_THEN `m:num = p` SUBST_ALL_TAC THEN
      GHOST_INTRO_TAC `cout:bool` `read CF` THEN ASM_REWRITE_TAC[] THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--2) THEN
      ASM_REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < p - m /\ ~(p - m = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - m:num` THEN
    ENSURES_SEQUENCE_TAC `pc + 0xcc`
     `\s. read X0 s = word(p - m) /\
          read X1 s = z /\
          read X6 s = word m /\
          bignum_from_memory(z,m + 1) s = a + b` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      GHOST_INTRO_TAC `cout:bool` `read CF` THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--4) THEN
      GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN
      ASM_REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = m + 1` THENL
     [UNDISCH_THEN `p = m + 1` SUBST_ALL_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--4) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `0 < p - (m + 1) /\ ~(p - (m + 1) = 0) /\ ~(p - m = 1) /\ m + 1 <= p`
    STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_WHILE_UP_TAC `p - (m + 1):num` `pc + 0xc8` `pc + 0xd4`
     `\i s. read X0 s = word(p - (m + 1) - i) /\
            read X6 s = word((m + 1) + i) /\
            read X1 s = z /\
            bignum_from_memory(z,(m + 1) + i) s = a + b` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUB_0] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC (1--3) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_1] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
      REWRITE_TAC[ARITH_RULE `p - (m + 1) = p - m - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      VAL_INT64_TAC `p - (m + 1) - i` THEN
      ASM_REWRITE_TAC[] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC [1];
      ASM_SIMP_TAC[ARITH_RULE `0 < m - n ==> n + m - n = m`] THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--2) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]] THEN

    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m + 1 <= (m + 1) + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - (m + 1) - (j + 1) = p - ((m + 1) + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - (m + 1) - j = p - ((m + 1) + j)`] THEN
    REWRITE_TAC[ARITH_RULE `(m + 1) + (j + 1) = ((m + 1) + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - (m + 1)
      ==> (j + 1 = p - (m + 1) <=> ((m + 1) + j) + 1 = p) /\
          (j < p - (m + 1) <=> (m + 1) + j < p) /\
          (j = p - (m + 1) <=> (m + 1) + j = p)`] THEN
    SPEC_TAC(`(m + 1) + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_SIM_TAC BIGNUM_ADD_EXEC (1--3) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];

    (**** The other branch, very similar mutatis mutandis ***)

    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `a < 2 EXP (64 * n)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC `pc + 0x98`
     `\s. read X0 s = word(p - n) /\
          read X1 s = z /\
          read X4 s = word(n - m) /\
          read X5 s = y /\
          read X3 s = x /\
          read X6 s = word m /\
          bignum_from_memory (word_add y (word(8 * m)),n - m) s =
          highdigits b m /\
          2 EXP (64 * m) * bitval(read CF s) + bignum_from_memory(z,m) s =
          lowdigits a m + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m = 0` THENL
       [UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[SUB_0] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_UP_TAC `m:num` `pc + 0x7c` `pc + 0x94`
       `\i s. read X0 s = word(p - n) /\
              read X1 s = z /\
              read X4 s = word(n - m) /\
              read X5 s = y /\
              read X3 s = x /\
              read X2 s = word(m - i) /\
              read X6 s = word i /\
              bignum_from_memory (word_add y (word(8 * i)),n - i) s =
              highdigits b i /\
              bignum_from_memory (word_add x (word(8 * i)),m - i) s =
              highdigits a i /\
              2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
              lowdigits a i + lowdigits b i` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `m - i:num` THEN
        ASM_REWRITE_TAC[] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC [1];
        ARM_SIM_TAC BIGNUM_ADD_EXEC [1]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      ARM_STEPS_TAC BIGNUM_ADD_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
       `(t * e) * y + z + t * x:num = t * (e * y + x) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC `pc + 0xb0`
     `\s. read X0 s = word(p - n) /\
          read X1 s = z /\
          read X6 s = word n /\
          2 EXP (64 * n) * bitval(read CF s) + bignum_from_memory(z,n) s =
          lowdigits a n + lowdigits b n` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `~(m = n) /\ 0 < n - m /\ ~(n - m = 0)`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `n - m:num` THEN
      ENSURES_WHILE_UP_TAC `n - m:num` `pc + 0x98` `pc + 0xac`
       `\i s. read X0 s = word(p - n) /\
              read X1 s = z /\
              read X5 s = y /\
              read X4 s = word(n - m - i) /\
              read X6 s = word(m + i) /\
              bignum_from_memory(word_add y (word(8 * (m + i))),
                                 n - (m + i)) s =
              highdigits b (m + i) /\
              2 EXP (64 * (m + i)) * bitval(read CF s) +
              bignum_from_memory(z,m + i) s =
              lowdigits a (m + i) + lowdigits b (m + i)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        VAL_INT64_TAC `n - m - i:num` THEN
        ARM_SIM_TAC BIGNUM_ADD_EXEC [1];
        ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> m + n - m = n`] THEN
        ARM_SIM_TAC BIGNUM_ADD_EXEC [1] THEN
        ASM_REWRITE_TAC[VAL_WORD_BITVAL]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `m:num < n
        ==> (i < n - m <=> m + i < n) /\ (i = n - m <=> m + i = n)`] THEN
      REWRITE_TAC[ARITH_RULE `n - m - i:num = n - (m + i)`] THEN
      REWRITE_TAC[ARITH_RULE `m + i + 1 = (m + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m <= m + j`) THEN
      SPEC_TAC(`m + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      ARM_STEPS_TAC BIGNUM_ADD_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC_0; ADD_CLAUSES; ARITH_RULE
       `(t * e) * y + z + t * x:num = t * (e * y + x) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(NUM_RING `a = 0 ==> x + y + z = e * a + y + x + z`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ASM_CASES_TAC `n:num = p` THENL
     [UNDISCH_THEN `n:num = p` SUBST_ALL_TAC THEN
      GHOST_INTRO_TAC `cout:bool` `read CF` THEN ASM_REWRITE_TAC[] THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--2) THEN
      ASM_REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < p - n /\ ~(p - n = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - n:num` THEN
    ENSURES_SEQUENCE_TAC `pc + 0xcc`
     `\s. read X0 s = word(p - n) /\
          read X1 s = z /\
          read X6 s = word n /\
          bignum_from_memory(z,n + 1) s = a + b` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN ASM_REWRITE_TAC[] THEN
      GHOST_INTRO_TAC `cout:bool` `read CF` THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--4) THEN
      GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN
      ASM_REWRITE_TAC[COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = n + 1` THENL
     [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--4) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `0 < p - (n + 1) /\ ~(p - (n + 1) = 0) /\ ~(p - n = 1) /\ n + 1 <= p`
    STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_WHILE_UP_TAC `p - (n + 1):num` `pc + 0xc8` `pc + 0xd4`
     `\i s. read X0 s = word(p - (n + 1) - i) /\
            read X6 s = word((n + 1) + i) /\
            read X1 s = z /\
            bignum_from_memory(z,(n + 1) + i) s = a + b` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUB_0] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC (1--3) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_1] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
      REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      VAL_INT64_TAC `p - (n + 1) - i` THEN
      ASM_REWRITE_TAC[] THEN ARM_SIM_TAC BIGNUM_ADD_EXEC [1];
      ASM_SIMP_TAC[ARITH_RULE `0 < n - m ==> m + n - m = n`] THEN
      ARM_SIM_TAC BIGNUM_ADD_EXEC (1--2) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]] THEN
    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n + 1 <= (n + 1) + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - (n + 1) - (j + 1) = p - ((n + 1) + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - (n + 1) - j = p - ((n + 1) + j)`] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + (j + 1) = ((n + 1) + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - (n + 1)
      ==> (j + 1 = p - (n + 1) <=> ((n + 1) + j) + 1 = p) /\
          (j < p - (n + 1) <=> (n + 1) + j < p) /\
          (j = p - (n + 1) <=> (n + 1) + j = p)`] THEN
    SPEC_TAC(`(n + 1) + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_SIM_TAC BIGNUM_ADD_EXEC (1--3) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`]]);;

let BIGNUM_ADD_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc returnaddress.
        nonoverlapping (word pc,0xe0) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_add_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,val p) s =
                  (a + b) MOD 2 EXP (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) +
                  bignum_from_memory (z,val p) s =
                  lowdigits a (val p) + lowdigits b (val p))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_EXEC BIGNUM_ADD_CORRECT);;
