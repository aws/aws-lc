(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Division of bignum by a single word when known a priori to be exact.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_cdiv_exact.o";;
 ****)

let bignum_cdiv_exact_mc =
  define_assert_from_elf "bignum_cdiv_exact_mc" "arm/generic/bignum_cdiv_exact.o"
[
  0xb40005c0;       (* arm_CBZ X0 (word 184) *)
  0xcb0403ea;       (* arm_NEG X10 X4 *)
  0x8a04014a;       (* arm_AND X10 X10 X4 *)
  0xdac0114a;       (* arm_CLZ X10 X10 *)
  0xd240154a;       (* arm_EOR X10 X10 (rvalue (word 63)) *)
  0x9280000b;       (* arm_MOVN X11 (word 0) 0 *)
  0x9aca256b;       (* arm_LSRV X11 X11 X10 *)
  0x9aca2484;       (* arm_LSRV X4 X4 X10 *)
  0xcb040885;       (* arm_SUB X5 X4 (Shiftedreg X4 LSL 2) *)
  0xd27f00a5;       (* arm_EOR X5 X5 (rvalue (word 2)) *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0x9b051886;       (* arm_MADD X6 X4 X5 X6 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b0514c5;       (* arm_MADD X5 X6 X5 X5 *)
  0x9b077ce6;       (* arm_MUL X6 X7 X7 *)
  0x9b0514e5;       (* arm_MADD X5 X7 X5 X5 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b0514c5;       (* arm_MADD X5 X6 X5 X5 *)
  0x9b0514e5;       (* arm_MADD X5 X7 X5 X5 *)
  0xaa0403e8;       (* arm_MOV X8 X4 *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xb4000082;       (* arm_CBZ X2 (word 16) *)
  0xf8408469;       (* arm_LDR X9 X3 (Postimmediate_Offset (iword (&8))) *)
  0x9aca2529;       (* arm_LSRV X9 X9 X10 *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xaa1f03ec;       (* arm_MOV X12 XZR *)
  0xeb0200df;       (* arm_CMP X6 X2 *)
  0x54000042;       (* arm_BCS (word 8) *)
  0xf866786c;       (* arm_LDR X12 X3 (Shiftreg_Offset X6 3) *)
  0x9aca2d8c;       (* arm_RORV X12 X12 X10 *)
  0x8a2b0187;       (* arm_BIC X7 X12 X11 *)
  0xaa070127;       (* arm_ORR X7 X9 X7 *)
  0x8a0b0189;       (* arm_AND X9 X12 X11 *)
  0xab0800e7;       (* arm_ADDS X7 X7 X8 *)
  0x9b057ced;       (* arm_MUL X13 X7 X5 *)
  0x9a9f37e8;       (* arm_CSET X8 Condition_CS *)
  0xaa2d03ec;       (* arm_MVN X12 X13 *)
  0xf826782c;       (* arm_STR X12 X1 (Shiftreg_Offset X6 3) *)
  0x9b047dac;       (* arm_MUL X12 X13 X4 *)
  0x9bc47dad;       (* arm_UMULH X13 X13 X4 *)
  0xab07018c;       (* arm_ADDS X12 X12 X7 *)
  0x9a0801a8;       (* arm_ADC X8 X13 X8 *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xeb0000df;       (* arm_CMP X6 X0 *)
  0x54fffda3;       (* arm_BCC (word 2097076) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CDIV_EXACT_EXEC = ARM_MK_EXEC_RULE bignum_cdiv_exact_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_CDIV_EXACT_CORRECT = prove
 (`!k z n x m a pc.
        nonoverlapping (word pc,0xbc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cdiv_exact_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = word(pc + 0xb8) /\
                  (~(val m = 0) /\ val m divides a
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k)))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `n:num` THEN
  X_GEN_TAC `x:int64` THEN W64_GEN_TAC `m:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN

  (*** Degenerate case when output size is zero ***)

  ASM_CASES_TAC `k = 0` THENL
   [ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC [1] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Introduce the initial decomposition into m = 2^e * m', replace m ***)

  ABBREV_TAC `e = index 2 m` THEN
  SUBGOAL_THEN `e < 64` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC INDEX_LT THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    VAL_INT64_TAC `e:num`] THEN

  MP_TAC(SPECL [`m:num`; `2`] INDEX_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; ARITH_EQ; DIVIDES_2; NOT_EVEN] THEN
  X_GEN_TAC `m':num` THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`m':num`,`m:num`) THEN X_GEN_TAC `m:num` THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN

  SUBGOAL_THEN `m < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LET_TRANS `2 EXP e * m` THEN
    ASM_REWRITE_TAC[ARITH_RULE `m <= e * m <=> 1 * m <= e * m`] THEN
    SIMP_TAC[LE_MULT_RCANCEL; LE_1; EXP_EQ_0; ARITH_EQ];
    VAL_INT64_TAC `m:num`] THEN

  (*** Verify the initial breakdown computation ***)

  ENSURES_SEQUENCE_TAC `pc + 0x20`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word n /\
        read X3 s = x /\
        bignum_from_memory (x,n) s = a /\
        read X4 s = word m /\
        read X10 s = word(if m = 0 then 127 else e) /\
        read X11 s = word(2 EXP (if m = 0 then 1 else 64 - e) - 1)` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--8) THEN
    REWRITE_TAC[WORD_SUB_LZERO] THEN ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
    REWRITE_TAC[WORD_CTZ_EMULATION_AND_NEG_REV; DIMINDEX_64] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_USHR_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[WORD_CTZ_INDEX; GSYM VAL_EQ_0; MULT_EQ_0;
                    EXP_EQ_0; ARITH_EQ; MOD_64_CLAUSES; MOD_LT] THEN
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `e < 64` THEN SPEC_TAC(`e:num`,`e:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    ASM_SIMP_TAC[word_jushr; DIMINDEX_64; MOD_LT] THEN
    ASM_SIMP_TAC[word_ushr; DIV_MULT; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN

  (*** The negated modular inverse computation ****)

  ENSURES_SEQUENCE_TAC `pc + 0x4c`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word n /\
        read X3 s = x /\
        bignum_from_memory (x,n) s = a /\
        read X4 s = word m /\
        read X10 s = word(if m = 0 then 127 else e) /\
        read X11 s = word(2 EXP (if m = 0 then 1 else 64 - e) - 1) /\
        (~(m = 0) ==> (m * val(read X5 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--11) THEN
    DISCH_TAC THEN UNDISCH_TAC `m = 0 \/ ODD m` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MP_TAC(SPEC `m:num` WORD_NEGMODINV_SEED_LEMMA_16) THEN
    ASM_REWRITE_TAC[FORALL_UNWIND_THM1] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; CONG; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `16 = 2 EXP 4`) THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 2 EXP 4 EXP 16`) THEN
    SPEC_TAC(`2 EXP 4`,`p:num`) THEN CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:int64` `read X5` THEN GLOBALIZE_PRECONDITION_TAC] THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x68` `pc + 0xb0`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = word(if n = 0 then 0 else n - 1) /\
          read X3 s = (if n = 0 then x else word_add x (word 8)) /\
          read X4 s = word m /\
          read X10 s = word (if m = 0 then 127 else e) /\
          read X11 s = word (2 EXP (if m = 0 then 1 else 64 - e) - 1) /\
          read X5 s = w /\
          read X6 s = word i /\
          (~(m = 0) ==> read X9 s = word(bigdigit a i DIV 2 EXP e)) /\
          bignum_from_memory(word_add x (word (8 * i)),MIN n (k + 1) - i) s =
          highdigits (lowdigits a (k + 1)) i /\
          (~(m = 0)
           ==> &(lowdigits (a DIV 2 EXP e) i) +
               (&2 pow (64 * i) - &(bignum_from_memory(z,i) s)) * &m:real =
               &2 pow (64 * i) * &(val(read X8 s)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--4) THEN
      REWRITE_TAC[ARITH_RULE `MIN 0 n = 0`; LOWDIGITS_0; SUB_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; DIV_0; BIGDIGIT_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL;
                  LOWDIGITS_TRIVIAL; HIGHDIGITS_0] THEN
      REWRITE_TAC[LOWDIGITS_0; MULT_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[HIGHDIGITS_0; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `read (memory :> bytes64 x) s0 = word(bigdigit a 0)`
    ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      ASM_SIMP_TAC[LE_1; MULT_CLAUSES; WORD_ADD_0; WORD_VAL];
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_CDIV_EXACT_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; LE] THEN
    ASM_SIMP_TAC[WORD_SUB; LE_1; word_jushr; DIMINDEX_64; MOD_LT] THEN
    REWRITE_TAC[word_ushr; VAL_WORD_BIGDIGIT] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    REAL_ARITH_TAC;

    ALL_TAC; (*** The main loop invariant ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--2);

    GHOST_INTRO_TAC `c:int64` `read X8` THEN
    GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `q:num` THEN
    ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--2) THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    UNDISCH_TAC `m = 0 \/ ODD m` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * k)` THEN
    ASM_REWRITE_TAC[LOWDIGITS_BOUND] THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `lowdigits (a DIV 2 EXP e) k` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN FIRST_ASSUM(SUBST1_TAC o
        MATCH_MP(REAL_ARITH
         `l + (e - q) * m:real = e * c ==> (m * q - l) = e * (m - c)`)) THEN
      REWRITE_TAC[REAL_FIELD `(&2 pow e * a) / &2 pow e = a`] THEN
      REAL_INTEGER_TAC;
      REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[GSYM DIV_DIV] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_DIV_MULT; DIVIDES_DIVIDES_DIV_IMP]]] THEN

  (*** Start tackling the main loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `c:int64` `read X8` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `q:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

  (*** The optional load depending on whether i < n ***)

  ENSURES_SEQUENCE_TAC `pc + 0x78`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word(if n = 0 then 0 else n - 1) /\
        read X3 s = (if n = 0 then x else word_add x (word 8)) /\
        read X4 s = word m /\
        read X10 s = word (if m = 0 then 127 else e) /\
        read X11 s = word (2 EXP (if m = 0 then 1 else 64 - e) - 1) /\
        read X5 s = w /\
        read X6 s = word i /\
        (~(m = 0) ==> read X9 s = word(bigdigit a i DIV 2 EXP e)) /\
        bignum_from_memory(word_add x (word (8 * i)),MIN n (k + 1) - i) s =
        highdigits (lowdigits a (k + 1)) i /\
        read X8 s = c /\
        bignum_from_memory (z,i) s = q /\
        read X12 s = word(bigdigit a (i + 1))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `val(word(if n = 0 then 0 else n - 1):int64) <= i <=>
                  ~(i + 1 < n)`
    MP_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; LT; LE_0] THEN
      ASM_SIMP_TAC[WORD_SUB; LE_1; VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
      UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN

    ASM_CASES_TAC `i + 1 < n` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes64(word_add x (word(8 + 8 * i)))) s0 =
        word(bigdigit (highdigits (lowdigits a (k + 1)) i) 1)`
      MP_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `i + 1 < n /\ i < k ==> 1 < MIN n (k + 1) - i`] THEN
        REWRITE_TAC[WORD_VAL] THEN AP_THM_TAC THEN
        REPLICATE_TAC 3 AP_TERM_TAC THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[BIGDIGIT_HIGHDIGITS; BIGDIGIT_LOWDIGITS] THEN
        ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `~(n = 0)`
       (fun th -> REWRITE_TAC[th] THEN
                  RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
       [UNDISCH_TAC `i + 1 < n` THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_CDIV_EXACT_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--3) THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
      UNDISCH_TAC `~(i + 1 < n)` THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Now the main Montgomery part ***)

  GHOST_INTRO_TAC `d:int64` `read X9` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS_ALT] THEN
  REWRITE_TAC[ARITH_RULE `n - i - 1 = n - (i + 1)`] THEN
  SUBGOAL_THEN
   `nonoverlapping (word_add z (word (8 * i):int64),8)
            (word_add x (word (8 * (i + 1))),8 * (MIN n (k + 1) - (i + 1)))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [ASM_CASES_TAC `i + 1 < MIN n (k + 1)` THENL
     [NONOVERLAPPING_TAC;
      ASM_SIMP_TAC[ARITH_RULE `~(i < n) ==> 8 * (n - i) = 0`] THEN
      REWRITE_TAC[nonoverlapping_modulo; LT]];
    DISCH_TAC] THEN
  UNDISCH_THEN `val(word m:int64) = m` (K ALL_TAC) THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [ARM_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--14) THEN REWRITE_TAC[WORD_ADD];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  UNDISCH_TAC `m = 0 \/ ODD m` THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN

  ARM_ACCSIM_TAC BIGNUM_CDIV_EXACT_EXEC [5;10;12;13] (1--14) THEN
  ASM_REWRITE_TAC
   [REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL] THEN
  ASM_SIMP_TAC[MOD_64_CLAUSES; MOD_LT; GSYM WORD_BIGDIGIT_DIV; LT_IMP_LE] THEN
  ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64;
               WORD_NEG_NEG; VAL_WORD_BITVAL] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[word_jror] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
    ASM_SIMP_TAC[VAL_WORD_ROR; DIMINDEX_64; LT_IMP_LE] THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT;
        MESON[DIV_LE; LET_TRANS; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND]
         `val(word(bigdigit a i DIV m):int64) = bigdigit a i DIV m`] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `e < 64 ==> e + 64 - e = 64`] THEN
    REWRITE_TAC[BIGDIGIT_BOUND];
    DISCH_THEN SUBST_ALL_TAC] THEN
  SUBGOAL_THEN
   `word_or (word (bigdigit a i DIV 2 EXP e))
            (word_and (word_jror (word (bigdigit a (i + 1))) (word e))
                      (word_not (word (2 EXP (64 - e) - 1)))):int64 =
    word(bigdigit (a DIV 2 EXP e) i)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BIGDIGIT] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      VAL_WORD_OR_DISJOINT o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(WORD_BITWISE_RULE
       `word_and a c = word 0 ==> word_and a (word_and b c) = word 0`) THEN
      SIMP_TAC[WORD_AND_EQ_0; bits_of_word; BIT_MASK_WORD; BIT_WORD_NOT] THEN
      REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC(SET_RULE
       `(!x. ~P x ==> ~(x IN s))
        ==> DISJOINT s {x | Q x /\ ~(Q x /\ P x)}`) THEN
      REWRITE_TAC[NOT_LT; IN_ELIM_THM; UPPER_BITS_ZERO] THEN
      MATCH_MP_TAC VAL_WORD_LT THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      ASM_SIMP_TAC[ARITH_RULE `e < 64 ==> e + 64 - e = 64`; BIGDIGIT_BOUND];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_NOT_MASK_WORD; word_jror] THEN
    ASM_SIMP_TAC[VAL_WORD_ROR; DIMINDEX_64; LT_IMP_LE] THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT;
        MESON[DIV_LE; LET_TRANS; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND]
         `val(word(bigdigit a i DIV m):int64) = bigdigit a i DIV m`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_DIV; GSYM EXP_ADD; DIV_LT; BIGDIGIT_BOUND; ADD_CLAUSES;
                 ARITH_RULE `e < 64 ==> e + 64 - e = 64`] THEN
    ASM_SIMP_TAC[BIGDIGIT_DIV; LT_IMP_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * (i + 1) + 64`; `&0:real`] THEN
  REWRITE_TAC[REAL_POW_ADD; INTEGER_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= l /\ &0 <= q * m /\ &0 <= e * m /\
      q * m < e * m /\ l + e * m < e * &2 pow 64
      ==> &0 <= l + (e - q) * m /\ l + (e - q) * m < e * &2 pow 64`) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN BOUNDER_TAC[];
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1] THEN
      REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= ee * v /\ q < ee ==> q + ee * (e - &1 - v) < ee * e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN EXPAND_TAC "q" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
      MATCH_MP_TAC(REAL_ARITH
       `l < e /\ e * (m + &1) <= e * &2 pow 64
        ==> l + e * m < e * &2 pow 64`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LOWDIGITS_BOUND] THEN
      REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m + 1 <= 2 EXP 64 <=> m < 2 EXP 64`]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[LE_0; VAL_BOUND_64];
    ALL_TAC] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[REAL_FIELD `(a - &2 pow e * b) / (&2 pow e * &2 pow f) =
                          a / &2 pow f / &2 pow e - b / &2 pow f`] THEN
  REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REWRITE_TAC[REAL_ARITH
   `(a + b) + (ee * e - (q + ee * (e - &1 - v))) * m:real =
    (b + (ee - q) * m) + ee * v * m + a`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; REAL_FIELD
   `(&2 pow e * x) / &2 pow 64 / (&2 pow e * &2 pow 64) = x / &2 pow 128`] THEN
  ABBREV_TAC `qd:int64 = word(val(sum_s5:int64) * val(w:int64))` THEN

  REWRITE_TAC[REAL_ARITH
   `(x + q * m + l) / &2 pow 128 - s / &2 pow 64 =
    ((l + x) + (q * m - &2 pow 64 * s)) / &2 pow 128`] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  ONCE_REWRITE_TAC[GSYM VAL_WORD_BIGDIGIT] THEN
  FIRST_X_ASSUM(fun th ->
   GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [SYM th]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `&2 pow 64 * b + s = x ==> s = x - &2 pow 64 * b`)) THEN
  REWRITE_TAC[VAL_WORD_BITVAL] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `&2 pow 64 * b + s = x + y
    ==> (&2 pow 64 * b + s = x + y ==> s = &0)
        ==> y = &2 pow 64 * b - x`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 64 * c + s = x ==> s = x - &2 pow 64 * c`)) THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
      `e * c + s:real = qm - e * h + t ==> e * (c + h) + s = qm + t`)) THEN
    EXPAND_TAC "qd" THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    SIMP_TAC[DIMINDEX_64; MOD_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `(s * w) * m + s = (m * w + 1) * s`] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM DIVIDES_MOD] THEN
    UNDISCH_TAC `(m * val(w:int64) + 1 == 0) (mod (2 EXP 64))` THEN
    SPEC_TAC(`2 EXP 64`,`p:num`) THEN CONV_TAC NUMBER_RULE;
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 64 * c + s = x ==> x = &2 pow 64 * c + s`)) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN DISCH_THEN SUBST1_TAC THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_CDIV_EXACT_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc returnaddress.
        nonoverlapping (word pc,0xbc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cdiv_exact_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read PC s = returnaddress /\
                  (~(val m = 0) /\ val m divides a
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_CDIV_EXACT_EXEC BIGNUM_CDIV_EXACT_CORRECT);;
