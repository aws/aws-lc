(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_emontredc.o";;
 ****)

let bignum_emontredc_mc =
  define_assert_from_elf "bignum_emontredc_mc" "arm/generic/bignum_emontredc.o"
[
  0xb4000460;       (* arm_CBZ X0 (word 140) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xf9400029;       (* arm_LDR X9 X1 (Immediate_Offset (word 0)) *)
  0x9b037d26;       (* arm_MUL X6 X9 X3 *)
  0xf940004b;       (* arm_LDR X11 X2 (Immediate_Offset (word 0)) *)
  0x9b0b7cca;       (* arm_MUL X10 X6 X11 *)
  0x9bcb7cc8;       (* arm_UMULH X8 X6 X11 *)
  0xf9000026;       (* arm_STR X6 X1 (Immediate_Offset (word 0)) *)
  0xab0a013f;       (* arm_CMN X9 X10 *)
  0xd2800025;       (* arm_MOV X5 (rvalue (word 1)) *)
  0xd100040b;       (* arm_SUB X11 X0 (rvalue (word 1)) *)
  0xb400018b;       (* arm_CBZ X11 (word 48) *)
  0xf865784b;       (* arm_LDR X11 X2 (Shiftreg_Offset X5 3) *)
  0xf8657829;       (* arm_LDR X9 X1 (Shiftreg_Offset X5 3) *)
  0x9b0b7cca;       (* arm_MUL X10 X6 X11 *)
  0xba080129;       (* arm_ADCS X9 X9 X8 *)
  0x9bcb7cc8;       (* arm_UMULH X8 X6 X11 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab0a0129;       (* arm_ADDS X9 X9 X10 *)
  0xf8257829;       (* arm_STR X9 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000ab;       (* arm_SUB X11 X5 X0 *)
  0xb5fffecb;       (* arm_CBNZ X11 (word 2097112) *)
  0xba070108;       (* arm_ADCS X8 X8 X7 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0xf860782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X0 3) *)
  0xab0b0108;       (* arm_ADDS X8 X8 X11 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xf8207828;       (* arm_STR X8 X1 (Shiftreg_Offset X0 3) *)
  0x91002021;       (* arm_ADD X1 X1 (rvalue (word 8)) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54fffc43;       (* arm_BCC (word 2097032) *)
  0xaa0703e0;       (* arm_MOV X0 X7 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EMONTREDC_EXEC = ARM_MK_EXEC_RULE bignum_emontredc_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EMONTREDC_CORRECT = time prove
 (`!k z m w a n pc.
        nonoverlapping (word pc,0x90) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x8c) /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE [PC; X0; X1; X4; X5; X6; X7; X8; X9; X10; X11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
    REWRITE_TAC[MULT_CLAUSES; CONG] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** The outer loop setup with start and end ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xc` `pc + 0x80`
   `\i s. read X0 s = word k /\
          read X1 s = word_add z (word(8 * i)) /\
          read X2 s = m /\
          read X3 s = word w /\
          bignum_from_memory (m,k) s = n /\
          read X4 s = word i /\
          bignum_from_memory(word_add z (word(8 * (k + i))),
                             2 * k - (k + i)) s =
          highdigits a (k + i) /\
          ?r. r < 2 EXP (64 * i) /\
              2 EXP (64 * i) *
              (2 EXP (64 * k) * val(read X7 s) +
               bignum_from_memory(word_add z (word(8 * i)),k) s) + r =
              bignum_from_memory(z,i) s * n + lowdigits a (k + i) /\
              ((n * w + 1 == 0) (mod (2 EXP 64)) ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; EXP] THEN
    EXISTS_TAC `0` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC; (*** This is the main loop invariant: save for later ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--2);
    GHOST_INTRO_TAC `cout:int64` `read X7` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--3) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` MP_TAC) THEN
    ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2] THEN REWRITE_TAC[MULT_SYM]] THEN

  (*** Start on the main outer loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read X7 s)` THEN
  GHOST_INTRO_TAC `z1:num`
   `bignum_from_memory(word_add z (word (8 * i)),k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `q:num` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  (*** Rebase some things at z' = z + 8 * i ***)

  ABBREV_TAC `z':int64 = word_add z (word (8 * i))` THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN

  SUBGOAL_THEN
   `word_add z (word (8 * (k + i))):int64 = word_add z' (word(8 * k)) /\
    word_add z (word (8 * (k + i + 1))) = word_add z' (word(8 * (k + 1))) /\
    word_add z (word (8 * (i + 1))):int64 = word_add z' (word(8 * 1))`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
    [EXPAND_TAC "z'" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n - (k + i + 1) = n - (k + i) - 1`] THEN
  REWRITE_TAC[ARITH_RULE `2 * k - (k + i) = 2 * k - i - k`] THEN

  ABBREV_TAC `p = 2 * k - i` THEN
  SUBGOAL_THEN `~(p = 0) /\ 0 < p /\ k < p` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN UNDISCH_TAC `i:num < k` THEN ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z',8 * p) (z:int64,8 * i) /\
    nonoverlapping (z',8 * p) (m,8 * k) /\
    nonoverlapping (z',8 * p) (word pc,144)`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [PC; X0; X1; X4; X5; X6; X7; X8; X9; X10; X11] ,,
    MAYCHANGE [memory :> bytes (z',8 * p)] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,,
    MAYCHANGE [events]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x30`
   `\s. read X0 s = word k /\
        read X1 s = z' /\
        read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (z,i) s = q /\
        read X4 s = word i /\
        bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
        highdigits a (k + i) /\
        read X7 s = word cout /\
        bignum_from_memory(word_add z' (word 8),k - 1) s = highdigits z1 1 /\
        read (memory :> bytes64 z') s = word q0 /\
        read X5 s = word 1 /\
        read X6 s = word q0 /\
        read X11 s = word(k - 1) /\
        ?r0. r0 < 2 EXP 64 /\
             2 EXP 64 * (bitval(read CF s) + val(read X8 s)) + r0 =
             q0 * bigdigit n 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z',k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_EXEC [4;7] (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(TAUT `k /\ (k ==> q) ==> k /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    EXISTS_TAC `val(sum_s7:int64)` THEN REWRITE_TAC[VAL_BOUND_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `carin:bool` `read CF` THEN
  GHOST_INTRO_TAC `mulin:int64` `read X8` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN

  ENSURES_SEQUENCE_TAC `pc + 0x60`
   `\s. read X0 s = word k /\
        read X1 s = z' /\
        read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (z,i) s = q /\
        read X4 s = word i /\
        bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
        highdigits a (k + i) /\
        read X7 s = word cout /\
        read (memory :> bytes64 z') s = word q0 /\
        read X5 s = word k /\
        read X6 s = word q0 /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read X8 s)) +
        bignum_from_memory(z',k) s + r0 =
        q0 + lowdigits z1 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
      ASM_REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0x34` `pc + 0x58`
     `\j s. read X0 s = word k /\
            read X1 s = z' /\
            read X2 s = m /\
            read X3 s = word w /\
            bignum_from_memory (m,k) s = n /\
            bignum_from_memory (z,i) s = q /\
            read X4 s = word i /\
            bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
            highdigits a (k + i) /\
            read X7 s = word cout /\
            bignum_from_memory (word_add z' (word (8 * j)),k - j) s =
            highdigits z1 j /\
            bignum_from_memory (word_add m (word (8 * j)),k - j) s =
            highdigits n j /\
            read (memory :> bytes64 z') s = word q0 /\
            read X5 s = word j /\
            read X6 s = word q0 /\
            2 EXP (64 * j) * (bitval(read CF s) + val(read X8 s)) +
            bignum_from_memory(z',j) s + r0 =
            q0 + lowdigits z1 j + q0 * lowdigits n j` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_SING] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X8` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      SUBGOAL_THEN
       `nonoverlapping (word_add z' (word (8 * j)):int64,8)
                       (word_add z' (word (8 * k)),8 * (p - k))`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [SUBGOAL_THEN `word_add z' (word (8 * k)):int64 =
                    word_add (word_add z' (word (8 * j)))
                             (word(8 + 8 * ((k - j) - 1)))`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
          NONOVERLAPPING_TAC];
        DISCH_TAC] THEN
      ABBREV_TAC `z'':int64 = word_add z' (word (8 * k))` THEN
      ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_EXEC [3;4;6;7] (1--9) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; GSYM WORD_ADD] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `q + (e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + q + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
         [TAUT `k /\ q /\ r /\ s <=> k /\ r /\ q /\ s`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--2);
      ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--2)];
    ALL_TAC] THEN

  SUBGOAL_THEN `cout < 2` MP_TAC THENL
   [SUBGOAL_THEN `q * n + lowdigits a (k + i) < 2 EXP (64 * (k + i)) * 2`
    MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
      REWRITE_TAC[LOWDIGITS_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * i + 64 * k`] THEN
      ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE `64 * k + 64 * i = 64 * (i + k)`] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `a + b:num < c ==> a < c`)) THEN
      REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `tc:bool` SUBST_ALL_TAC)] THEN

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read X8` THEN
  GHOST_INTRO_TAC `z2:num` `bignum_from_memory (z',k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z2:num` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  ARM_ACCSIM_TAC BIGNUM_EMONTREDC_EXEC [1;2;4;5] (1--8) THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  EXISTS_TAC `2 EXP (64 * i) * r0 + r` THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    MATCH_MP_TAC(ARITH_RULE
      `q1 < e /\ q0 < ee /\ (q1 < e ==> (q1 + 1) * ee <= e * ee)
       ==> ee * q1 + q0 < ee * e`) THEN
     ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
     ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`];
     ALL_TAC] THEN
  CONJ_TAC THENL
    [ALL_TAC;
     DISCH_THEN(fun th ->
       REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
       ASSUME_TAC th) THEN
     ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     ASM_REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
      `ee * x + w + r = q + z
       ==> e divides ee /\ (w == q) (mod e) /\ (z == 0) (mod e)
           ==> (r == 0) (mod e)`)) THEN
     REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
       UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
       EXPAND_TAC "z2" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
       ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       CONV_TAC NUMBER_RULE;
       UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
       REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
       REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
        `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
       ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM LEFT_ADD_DISTRIB] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 1 + k - 1 = k`] THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
   [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `k + i + 1 = (k + i) + 1`] THEN
  REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * k + 64 * i`; EXP_ADD] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check
   (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
  UNDISCH_TAC `read (memory :> bytes (z',8 * k)) s8 = z2` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [BIGNUM_FROM_MEMORY_EXPAND] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES;
               BIGDIGIT_BOUND] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING);;

let BIGNUM_EMONTREDC_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc returnaddress.
        nonoverlapping (word pc,0x90) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_EMONTREDC_EXEC BIGNUM_EMONTREDC_CORRECT);;
