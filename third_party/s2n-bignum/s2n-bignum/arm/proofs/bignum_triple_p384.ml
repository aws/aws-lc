(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_384, the field characteristic for the NIST P-384 curve. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_triple_p384.o";;
 ****)

let bignum_triple_p384_mc = define_assert_from_elf "bignum_triple_p384_mc" "arm/p384/bignum_triple_p384.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xa9422027;       (* arm_LDP X7 X8 X1 (Immediate_Offset (iword (&32))) *)
  0xd37ff862;       (* arm_LSL X2 X3 (rvalue (word 1)) *)
  0xab030042;       (* arm_ADDS X2 X2 X3 *)
  0x93c3fc83;       (* arm_EXTR X3 X4 X3 (rvalue (word 63)) *)
  0xba040063;       (* arm_ADCS X3 X3 X4 *)
  0x93c4fca4;       (* arm_EXTR X4 X5 X4 (rvalue (word 63)) *)
  0xba050084;       (* arm_ADCS X4 X4 X5 *)
  0x93c5fcc5;       (* arm_EXTR X5 X6 X5 (rvalue (word 63)) *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0x93c6fce6;       (* arm_EXTR X6 X7 X6 (rvalue (word 63)) *)
  0xba0700c6;       (* arm_ADCS X6 X6 X7 *)
  0x93c7fd07;       (* arm_EXTR X7 X8 X7 (rvalue (word 63)) *)
  0xba0800e7;       (* arm_ADCS X7 X7 X8 *)
  0xd37ffd08;       (* arm_LSR X8 X8 (rvalue (word 63)) *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xd3607d0a;       (* arm_LSL X10 X8 (rvalue (word 32)) *)
  0xeb0a0109;       (* arm_SUBS X9 X8 X10 *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab090042;       (* arm_ADDS X2 X2 X9 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xda9f23e8;       (* arm_CSETM X8 Condition_CC *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xab090042;       (* arm_ADDS X2 X2 X9 *)
  0xca080129;       (* arm_EOR X9 X9 X8 *)
  0xba090063;       (* arm_ADCS X3 X3 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a080129;       (* arm_AND X9 X9 X8 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x9a0800e7;       (* arm_ADC X7 X7 X8 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TRIPLE_P384_EXEC = ARM_MK_EXEC_RULE bignum_triple_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let p384genshortredlemma = prove
 (`!n. n < 3 * 2 EXP 384
       ==> let q = (n DIV 2 EXP 384) + 1 in
           q <= 3 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let BIGNUM_TRIPLE_P384_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0xac) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = word (pc + 0xa8) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `6` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  (*** Input load and initial multiplication by 3 ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_EXEC (1--17) (1--17) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s5; sum_s7; sum_s9; sum_s11; sum_s13; sum_s15; sum_s17] =
    3 * n`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN EXPAND_TAC "mullo_s16" THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_0; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 = 1 + 63`; EXP_ADD; MOD_MULT2] THEN
    REWRITE_TAC[ADD_SUB; DIV_0; REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read (rvalue y) s = x`; `word_subword a b = c`; `word_shl a b = c`] THEN
    DISCARD_FLAGS_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = (3 * n) DIV 2 EXP 384` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 6)` THEN EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s17:int64 = word h` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `3 * n` p384genshortredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 6)` THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of 3 * n - (h + 1) * p_384 ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_EXEC (22--27) (18--28) THEN
  MP_TAC(SPECL
   [`word_neg(word(bitval(~carry_s27))):int64`;
    `&(bignum_of_wordlist
        [sum_s22; sum_s23; sum_s24; sum_s25; sum_s26; sum_s27]):real`;
    `384`; `3 * n`; `(h + 1) * p_384`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_384 <= 3 * n + p_384`;
        `3 * n < (h + 1) * p_384 + p_384`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist
      [sum_s5; sum_s7; sum_s9; sum_s11; sum_s13; sum_s15; word h] =
      3 * n`)) THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[REAL_VAL_WORD_MASK; REAL_BITVAL_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [WORD_MASK] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[COND_SWAP] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_EXEC [31;33;36;37;38;39] (29--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> 3 * n < (h + 1) * p_384` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &(3 * n) - y + z ==> &(3 * n) = x + y - z`)) THEN
  REWRITE_TAC[p_384] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TRIPLE_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0xac) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TRIPLE_P384_EXEC
    BIGNUM_TRIPLE_P384_CORRECT);;
