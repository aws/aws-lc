(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_25519, basepoint order for curve25519/edwards25519.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_mod_n25519.o";;
 ****)

let bignum_mod_n25519_mc =
  define_assert_from_elf "bignum_mod_n25519_mc" "arm/curve25519/bignum_mod_n25519.o"
[
  0xf100103f;       (* arm_CMP X1 (rvalue (word 4)) *)
  0x540007c3;       (* arm_BCC (word 248) *)
  0xd1001021;       (* arm_SUB X1 X1 (rvalue (word 4)) *)
  0xd37df027;       (* arm_LSL X7 X1 3 *)
  0x8b0200e7;       (* arm_ADD X7 X7 X2 *)
  0xa94118e5;       (* arm_LDP X5 X6 X7 (Immediate_Offset (iword (&16))) *)
  0xa94010e3;       (* arm_LDP X3 X4 X7 (Immediate_Offset (iword (&0))) *)
  0xd29a7dab;       (* arm_MOV X11 (rvalue (word 54253)) *)
  0xf2ab9eab;       (* arm_MOVK X11 (word 23797) 16 *)
  0xf2cc634b;       (* arm_MOVK X11 (word 25370) 32 *)
  0xf2eb024b;       (* arm_MOVK X11 (word 22546) 48 *)
  0xd2939acc;       (* arm_MOV X12 (rvalue (word 40150)) *)
  0xf2b45eec;       (* arm_MOVK X12 (word 41719) 16 *)
  0xf2df3bcc;       (* arm_MOVK X12 (word 63966) 32 *)
  0xf2e29bcc;       (* arm_MOVK X12 (word 5342) 48 *)
  0xd37cfccd;       (* arm_LSR X13 X6 60 *)
  0x9240ecc6;       (* arm_AND X6 X6 (rvalue (word 1152921504606846975)) *)
  0x9b0d7d67;       (* arm_MUL X7 X11 X13 *)
  0x9b0d7d88;       (* arm_MUL X8 X12 X13 *)
  0x9bcd7d69;       (* arm_UMULH X9 X11 X13 *)
  0xab090108;       (* arm_ADDS X8 X8 X9 *)
  0x9bcd7d89;       (* arm_UMULH X9 X12 X13 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xeb070063;       (* arm_SUBS X3 X3 X7 *)
  0xfa080084;       (* arm_SBCS X4 X4 X8 *)
  0xfa0900a5;       (* arm_SBCS X5 X5 X9 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0x9a9f3167;       (* arm_CSEL X7 X11 XZR Condition_CC *)
  0x9a9f3188;       (* arm_CSEL X8 X12 XZR Condition_CC *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0x924400e7;       (* arm_AND X7 X7 (rvalue (word 1152921504606846976)) *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xb4000341;       (* arm_CBZ X1 (word 104) *)
  0x93c5f0cd;       (* arm_EXTR X13 X6 X5 60 *)
  0x9240eca5;       (* arm_AND X5 X5 (rvalue (word 1152921504606846975)) *)
  0xcb46f1ad;       (* arm_SUB X13 X13 (Shiftedreg X6 LSR 60) *)
  0x92440cc6;       (* arm_AND X6 X6 (rvalue (word 17293822569102704640)) *)
  0x8b0600a5;       (* arm_ADD X5 X5 X6 *)
  0x9b0d7d67;       (* arm_MUL X7 X11 X13 *)
  0x9b0d7d88;       (* arm_MUL X8 X12 X13 *)
  0x9bcd7d69;       (* arm_UMULH X9 X11 X13 *)
  0xab090108;       (* arm_ADDS X8 X8 X9 *)
  0x9bcd7d89;       (* arm_UMULH X9 X12 X13 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xf861784d;       (* arm_LDR X13 X2 (Shiftreg_Offset X1 3) *)
  0xeb0701a7;       (* arm_SUBS X7 X13 X7 *)
  0xfa080068;       (* arm_SBCS X8 X3 X8 *)
  0xfa090089;       (* arm_SBCS X9 X4 X9 *)
  0xfa1f00aa;       (* arm_SBCS X10 X5 XZR *)
  0x9a9f3163;       (* arm_CSEL X3 X11 XZR Condition_CC *)
  0x9a9f3184;       (* arm_CSEL X4 X12 XZR Condition_CC *)
  0xab0300e3;       (* arm_ADDS X3 X7 X3 *)
  0x92440086;       (* arm_AND X6 X4 (rvalue (word 1152921504606846976)) *)
  0xba040104;       (* arm_ADCS X4 X8 X4 *)
  0xba1f0125;       (* arm_ADCS X5 X9 XZR *)
  0x9a060146;       (* arm_ADC X6 X10 X6 *)
  0xb5fffd01;       (* arm_CBNZ X1 (word 2097056) *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xb4ffff21;       (* arm_CBZ X1 (word 2097124) *)
  0xf9400043;       (* arm_LDR X3 X2 (Immediate_Offset (word 0)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffec0;       (* arm_BEQ (word 2097112) *)
  0xf9400444;       (* arm_LDR X4 X2 (Immediate_Offset (word 8)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffe60;       (* arm_BEQ (word 2097100) *)
  0xf9400845;       (* arm_LDR X5 X2 (Immediate_Offset (word 16)) *)
  0x17fffff1        (* arm_B (word 268435396) *)
];;

let BIGNUM_MOD_N25519_EXEC = ARM_MK_EXEC_RULE bignum_mod_n25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_25519 = define `n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989`;;

let BIGNUM_MOD_N25519_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0x130) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n25519_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = word (pc + 0xf8) /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Case split over the k < 4 case, which is a different path ***)

  ASM_CASES_TAC `k < 4` THENL
   [SUBGOAL_THEN `n MOD n_25519 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP (64 * 3)` THEN
      ASM_REWRITE_TAC[LE_EXP; n_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
   BIGNUM_DIGITIZE_TAC "n_" `read(memory :> bytes(x,8 * 4)) s0` THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `k < 4 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
   REWRITE_TAC[bignum_of_wordlist] THEN ASM_REWRITE_TAC[] THENL
    [ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--9);
     ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--12);
     ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--15);
     ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--17)] THEN
   ENSURES_FINAL_STATE_TAC THEN
   ASM_REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC;
   FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN

  (*** Initial 4-digit modulus ***)

  ENSURES_SEQUENCE_TAC `pc + 0x88`
   `\s. bignum_from_memory(x,k) s = n /\
        read X0 s = z /\
        read X2 s = x /\
        read X1 s = word(k - 4) /\
        read X11 s = word 0x5812631a5cf5d3ed /\
        read X12 s = word 0x14def9dea2f79cd6 /\
        bignum_of_wordlist[read X3 s; read X4 s; read X5 s; read X6 s] =
        (highdigits n (k - 4)) MOD n_25519` THEN
  CONJ_TAC THENL
   [ABBREV_TAC `j = k - 4` THEN VAL_INT64_TAC `j:num` THEN
    SUBGOAL_THEN `word_sub (word k) (word 4):int64 = word j` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
      REWRITE_TAC[WORD_SUB] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[highdigits] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_DIV] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 <= k ==> k - (k - 4) = 4`] THEN
    ABBREV_TAC `m = bignum_from_memory(word_add x (word (8 * j)),4) s0` THEN
    SUBGOAL_THEN `m < 2 EXP (64 * 4)` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
    BIGNUM_LDIGITIZE_TAC "m_"
     `read (memory :> bytes (word_add x (word(8 * j)),8 * 4)) s0` THEN
    ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_shl (word j) 3) x = word_add x (word(8 * j))`]) THEN
    ARM_ACCSTEPS_TAC BIGNUM_MOD_N25519_EXEC
     [18;19;21;23;24;25;26;27;30;31;33;34] (6--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s34" THEN

    (*** Quotient and associated mangling ***)

    ABBREV_TAC `q:int64 = word_ushr m_3 60` THEN
    SUBGOAL_THEN
     `&(val(word_and (m_3:int64) (word 1152921504606846975))):real =
      &(val m_3) - &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL [EXPAND_TAC "q" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN

    (*** Main reasoning including quotient estimate correctness ***)

    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s27`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        EXPAND_TAC "m" THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s27:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      SUBGOAL_THEN `val(q:int64) = m DIV 2 EXP 252` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "q"] THEN
        CONV_TAC(RAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[VAL_WORD_USHR];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN

  (*** Finish off the k = 4 case which is now just the writeback ***)

  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `4 <= k ==> k = 4 \/ 4 < k`))
  THENL
   [GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `0 < k - 4 /\ ~(k - 4 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Setup of loop invariant ***)

  ENSURES_WHILE_DOWN_TAC `k - 4` `pc + 0x8c` `pc + 0xec`
   `\i s. bignum_from_memory(x,k) s = n /\
          read X0 s = z /\
          read X2 s = x /\
          read X1 s = word i /\
          read X11 s = word 0x5812631a5cf5d3ed /\
          read X12 s = word 0x14def9dea2f79cd6 /\
          bignum_of_wordlist[read X3 s; read X4 s; read X5 s; read X6 s] =
          (highdigits n i) MOD n_25519` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [VAL_INT64_TAC `k - 4` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N25519_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN

  (*** Mathematics of main loop with decomposition and quotient estimate ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `m1:int64` `read X3` THEN
  GHOST_INTRO_TAC `m2:int64` `read X4` THEN
  GHOST_INTRO_TAC `m3:int64` `read X5` THEN
  GHOST_INTRO_TAC `m4:int64` `read X6` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m0:int64 = word(bigdigit n i)` THEN
  ABBREV_TAC `m = bignum_of_wordlist[m0; m1; m2; m3; m4]` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(SPEC `m0:int64` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[n_25519] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `highdigits n i MOD n_25519 = m MOD n_25519` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    EXPAND_TAC "m0" THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Full simulation interrupted to tweak the load address ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BIGNUM_MOD_N25519_EXEC [6;7;9;11] (1--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word(i + 1)) (word 1) = word i`]) THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:int64`; `s12:armstate`; `i:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word:num->int64` o SYM) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN
  ARM_ACCSTEPS_TAC BIGNUM_MOD_N25519_EXEC
   [14;15;16;17;20;22;23;24] (13--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s24" THEN

  (*** Quotient and associated mangling ***)

  ABBREV_TAC
   `q:int64 =
    word_sub (word_subword((word_join:int64->int64->int128) m4 m3) (60,64))
             (word_ushr m4 60)` THEN

  SUBGOAL_THEN
   `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
    val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN
     `word_ushr (m4:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
      word_subword ((word_join:int64->int64->int128) m4 m3) (60,64):int64 =
      word(m DIV 2 EXP 252)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
      REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
      REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
     [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
      REWRITE_TAC[n_25519] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      ARITH_TAC];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&(val(word_add (word_and m3 (word 1152921504606846975))
                   (word_and m4 (word 17293822569102704640)):int64)):real =
    (&2 pow 64 * &(val(m4:int64)) + &(val(m3:int64))) -
    &2 pow 60 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_OR o
      rand o rand o lhand o snd) THEN
    ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN SUBST1_TAC] THEN
    POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `q + x:real = y ==> q = y - x`)) THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE
     `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
      (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC WORD_BLAST;
    POP_ASSUM(K ALL_TAC)] THEN

  (*** Main reasoning including quotient estimate correctness ***)

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  EXISTS_TAC `256` THEN
  EXISTS_TAC
   `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
         &n_25519:real` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `m < val(q:int64) * n_25519 <=> carry_s17`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      EXPAND_TAC "m" THEN
      REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      BOOL_CASES_TAC `carry_s17:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
    MAP_EVERY UNDISCH_TAC
     [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
      `m < 2 EXP 64 * n_25519`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
    COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let BIGNUM_MOD_N25519_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc returnaddress.
      nonoverlapping (word pc,0x130) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n25519_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD n_25519)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_N25519_EXEC BIGNUM_MOD_N25519_CORRECT);;
