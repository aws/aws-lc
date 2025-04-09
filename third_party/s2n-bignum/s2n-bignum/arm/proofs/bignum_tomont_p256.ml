(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 4-word (256-bit) bignum to Montgomery form modulo p_256.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p256/bignum_tomont_p256.o";;
 ****)

let bignum_tomont_p256_mc =
  define_assert_from_elf "bignum_tomont_p256_mc" "arm/p256/bignum_tomont_p256.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x92800001;       (* arm_MOVN X1 (word 0) 0 *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0xb26083e9;       (* arm_MOV X9 (rvalue (word 18446744069414584321)) *)
  0xeb010041;       (* arm_SUBS X1 X2 X1 *)
  0xfa070067;       (* arm_SBCS X7 X3 X7 *)
  0xfa1f0088;       (* arm_SBCS X8 X4 XZR *)
  0xfa0900a9;       (* arm_SBCS X9 X5 X9 *)
  0x9a813042;       (* arm_CSEL X2 X2 X1 Condition_CC *)
  0x9a873063;       (* arm_CSEL X3 X3 X7 Condition_CC *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93c480a9;       (* arm_EXTR X9 X5 X4 (rvalue (word 32)) *)
  0xba09009f;       (* arm_ADCS XZR X4 X9 *)
  0xd360fca9;       (* arm_LSR X9 X5 (rvalue (word 32)) *)
  0xba0900a9;       (* arm_ADCS X9 X5 X9 *)
  0xda9f33e6;       (* arm_CSETM X6 Condition_CS *)
  0xaa060129;       (* arm_ORR X9 X9 X6 *)
  0xd3607d27;       (* arm_LSL X7 X9 (rvalue (word 32)) *)
  0xd360fd28;       (* arm_LSR X8 X9 (rvalue (word 32)) *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0x9a0800a5;       (* arm_ADC X5 X5 X8 *)
  0xeb0903e6;       (* arm_NEGS X6 X9 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xeb0603e6;       (* arm_NEGS X6 X6 *)
  0xfa070042;       (* arm_SBCS X2 X2 X7 *)
  0xfa080063;       (* arm_SBCS X3 X3 X8 *)
  0xfa090084;       (* arm_SBCS X4 X4 X9 *)
  0xfa0900a5;       (* arm_SBCS X5 X5 X9 *)
  0xab0500c6;       (* arm_ADDS X6 X6 X5 *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0500e7;       (* arm_AND X7 X7 X5 *)
  0xba070042;       (* arm_ADCS X2 X2 X7 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x8a0500e7;       (* arm_AND X7 X7 X5 *)
  0x9a070084;       (* arm_ADC X4 X4 X7 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93c38089;       (* arm_EXTR X9 X4 X3 (rvalue (word 32)) *)
  0xba09007f;       (* arm_ADCS XZR X3 X9 *)
  0xd360fc89;       (* arm_LSR X9 X4 (rvalue (word 32)) *)
  0xba090089;       (* arm_ADCS X9 X4 X9 *)
  0xda9f33e5;       (* arm_CSETM X5 Condition_CS *)
  0xaa050129;       (* arm_ORR X9 X9 X5 *)
  0xd3607d27;       (* arm_LSL X7 X9 (rvalue (word 32)) *)
  0xd360fd28;       (* arm_LSR X8 X9 (rvalue (word 32)) *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0x9a080084;       (* arm_ADC X4 X4 X8 *)
  0xeb0903e5;       (* arm_NEGS X5 X9 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xeb0503e5;       (* arm_NEGS X5 X5 *)
  0xfa0700c6;       (* arm_SBCS X6 X6 X7 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa090063;       (* arm_SBCS X3 X3 X9 *)
  0xfa090084;       (* arm_SBCS X4 X4 X9 *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0400e7;       (* arm_AND X7 X7 X4 *)
  0xba0700c6;       (* arm_ADCS X6 X6 X7 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x8a0400e7;       (* arm_AND X7 X7 X4 *)
  0x9a070063;       (* arm_ADC X3 X3 X7 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93c28069;       (* arm_EXTR X9 X3 X2 (rvalue (word 32)) *)
  0xba09005f;       (* arm_ADCS XZR X2 X9 *)
  0xd360fc69;       (* arm_LSR X9 X3 (rvalue (word 32)) *)
  0xba090069;       (* arm_ADCS X9 X3 X9 *)
  0xda9f33e4;       (* arm_CSETM X4 Condition_CS *)
  0xaa040129;       (* arm_ORR X9 X9 X4 *)
  0xd3607d27;       (* arm_LSL X7 X9 (rvalue (word 32)) *)
  0xd360fd28;       (* arm_LSR X8 X9 (rvalue (word 32)) *)
  0xab070042;       (* arm_ADDS X2 X2 X7 *)
  0x9a080063;       (* arm_ADC X3 X3 X8 *)
  0xeb0903e4;       (* arm_NEGS X4 X9 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xeb0403e4;       (* arm_NEGS X4 X4 *)
  0xfa0700a5;       (* arm_SBCS X5 X5 X7 *)
  0xfa0800c6;       (* arm_SBCS X6 X6 X8 *)
  0xfa090042;       (* arm_SBCS X2 X2 X9 *)
  0xfa090063;       (* arm_SBCS X3 X3 X9 *)
  0xab030084;       (* arm_ADDS X4 X4 X3 *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0300e7;       (* arm_AND X7 X7 X3 *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x8a0300e7;       (* arm_AND X7 X7 X3 *)
  0x9a070042;       (* arm_ADC X2 X2 X7 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93c68049;       (* arm_EXTR X9 X2 X6 (rvalue (word 32)) *)
  0xba0900df;       (* arm_ADCS XZR X6 X9 *)
  0xd360fc49;       (* arm_LSR X9 X2 (rvalue (word 32)) *)
  0xba090049;       (* arm_ADCS X9 X2 X9 *)
  0xda9f33e3;       (* arm_CSETM X3 Condition_CS *)
  0xaa030129;       (* arm_ORR X9 X9 X3 *)
  0xd3607d27;       (* arm_LSL X7 X9 (rvalue (word 32)) *)
  0xd360fd28;       (* arm_LSR X8 X9 (rvalue (word 32)) *)
  0xab0700c6;       (* arm_ADDS X6 X6 X7 *)
  0x9a080042;       (* arm_ADC X2 X2 X8 *)
  0xeb0903e3;       (* arm_NEGS X3 X9 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xeb0303e3;       (* arm_NEGS X3 X3 *)
  0xfa070084;       (* arm_SBCS X4 X4 X7 *)
  0xfa0800a5;       (* arm_SBCS X5 X5 X8 *)
  0xfa0900c6;       (* arm_SBCS X6 X6 X9 *)
  0xfa090042;       (* arm_SBCS X2 X2 X9 *)
  0xab020063;       (* arm_ADDS X3 X3 X2 *)
  0xb2407fe7;       (* arm_MOV X7 (rvalue (word 4294967295)) *)
  0x8a0200e7;       (* arm_AND X7 X7 X2 *)
  0xba070084;       (* arm_ADCS X4 X4 X7 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x8a0200e7;       (* arm_AND X7 X7 X2 *)
  0x9a0700c6;       (* arm_ADC X6 X6 X7 *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TOMONT_P256_EXEC = ARM_MK_EXEC_RULE bignum_tomont_p256_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let p256longredlemma = prove
 (`!n. n < 2 EXP 64 * p_256
       ==> let q = MIN ((n DIV 2 EXP 192 + n DIV 2 EXP 224 + 1) DIV 2 EXP 64)
                       (2 EXP 64 - 1) in
           q < 2 EXP 64 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

(*** A generic tactic corresponding to the modular reduction macro ***)

let modstep256_tac regs topw n =
  let [d4;d3;d2;d1;d0; t1;t2;t3] = dest_list regs in
  let modterm = subst
   ([d0,`X6`; d1,`X2`; d2,`X3`; d3,`X4`; d4,`X5`;
     t1,`X7`; t2,`X8`; t3,`X9`] @
    [topw,`x_3:int64`] @
    (map (fun i -> mk_var("s"^string_of_int(i+n-13),`:armstate`),
                   mk_var("s"^string_of_int(i),`:armstate`))
         (13--40)))
  and modstring =
   C assoc
    (zip (statenames "s" (13--40)) (statenames "s" (n--(n+27)))) in
  MP_TAC(SPEC `2 EXP 64 * a` p256longredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `a < p_256` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `q = MIN (((2 EXP 64 * a) DIV 2 EXP 192 +
             (2 EXP 64 * a) DIV 2 EXP 224 + 1) DIV 2 EXP 64)
            (2 EXP 64 - 1)` THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MAP_EVERY (fun s ->
    ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P256_EXEC s THEN
    (if mem s (map modstring ["s16"; "s18"])
     then ACCUMULATE_ARITH_TAC s else ALL_TAC) THEN
    CLARIFY_TAC)
   (map modstring (statenames "s" (14--18))) THEN
  SUBGOAL_THEN (modterm
   `2 EXP 64 * bitval(read CF s18) + val(read X9 s18) =
    ((2 EXP 64 * a) DIV 2 EXP 192 +
     (2 EXP 64 * a) DIV 2 EXP 224 + 1) DIV 2 EXP 64`)
  MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `224 = 192 + 32 /\ 192 = 64 + 64 + 64`] THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_DIV] THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT; VAL_WORD_USHR] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    W(MP_TAC o C SPEC VAL_BOUND_64 o rand o rand o lhand o lhand o snd) THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MAP_EVERY (ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P256_EXEC)
            (map modstring ["s19"; "s20"]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   (modterm `!q. read X9 s = q' ==> q' = q ==> read X9 s = q`))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COND_SWAP] THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[ARITH_RULE `MIN a b = if b < a then b else a`] THEN
    GEN_REWRITE_TAC BINOP_CONV [COND_RAND] THEN
    REWRITE_TAC[GSYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[WORD_OR_NOT0; WORD_OR_0] THEN
    MATCH_MP_TAC(MESON[]
     `(c ==> p /\ x = a) /\ (~c ==> ~p /\ y = b)
      ==> (if c then x else y) = (if p then a else b)`) THEN
    CONJ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM
     (MP_TAC o check
       (can (term_match [] `2 EXP 64 * h + l = x`) o concl)) THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THENL
     [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
      REWRITE_TAC[WORD_VAL] THEN
      MATCH_MP_TAC(ARITH_RULE `n < 2 EXP 64 ==> ~(2 EXP 64 - 1 < n)`) THEN
      REWRITE_TAC[VAL_BOUND_64]];
    DISCH_TAC] THEN
  (*** Pre-reduction subtraction ****)
  ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P256_EXEC (modstring "s21") THEN
  MAP_EVERY (fun s ->
    ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P256_EXEC s THEN
    ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   (map modstring (statenames "s" (22--32))) THEN
  SUBGOAL_THEN (modterm
   `read X5 s32 = word_neg (word (bitval(2 EXP 64 * a < q * p_256))) /\
    &(bignum_of_wordlist
        [read X6 s32; read X2 s32; read X3 s32; read X4 s32]) =
    if 2 EXP 64 * a < q * p_256
    then &(2 EXP 64 * a) - &(q * p_256) + &2 pow 256
    else &(2 EXP 64 * a) - &(q * p_256)`)
  MP_TAC THENL
   [MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_LT THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`q * p_256 <= 2 EXP 64 * a + p_256`;
        `2 EXP 64 * a < q * p_256 + p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_VAL_WORD_MASK; DIMINDEX_64]) THEN
    SUBGOAL_THEN `val(word q:int64) = q` (SUBST_ALL_TAC o SYM) THENL
     [ASM_REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[p_256] THEN CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)] THEN
  (*** Final correction ****)
   MAP_EVERY (fun s ->
    ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P256_EXEC s THEN
    TRY(ACCUMULATE_ARITH_TAC s))
   (map modstring (statenames "s" (33--40))) THEN
  SUBGOAL_THEN (modterm
   `bignum_of_wordlist
     [read X6 s40; read X2 s40; read X3 s40; read X4 s40] =
    (2 EXP 64 * a) MOD p_256`)
  MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
    MAP_EVERY EXISTS_TAC [`q:num`; `256`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `(a - b) - (c - d) * p:real = (a - c * p) + (d * p - b)`] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[REAL_ARITH
      `(x:real = if p then y + e else y) <=>
       (y = if p then x - e else x)`] THEN
    DISCH_THEN SUBST1_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_AND_MASK; GSYM REAL_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[p_256] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN ASM_REWRITE_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `q:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl))) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue y) s = x`] THEN
  DISCARD_FLAGS_TAC THEN
  SUBGOAL_THEN `(2 EXP 64 * a) MOD p_256 < p_256` MP_TAC THENL
   [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`(2 EXP 64 * a) MOD p_256`,`a:num`) THEN
  REPEAT STRIP_TAC;;

let BIGNUM_TOMONT_P256_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x1f0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_p256_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x1ec) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256)
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initial reduction of the input mod p_256 ***)

  BIGNUM_TERMRANGE_TAC `4` `a:num` THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_P256_EXEC (1--13) (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN `carry_s9 <=> a < p_256` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ABBREV_TAC
   `a1 = bignum_of_wordlist
          [read X2 s13; read X3 s13; read X4 s13; read X5 s13]` THEN
  SUBGOAL_THEN `a1 = a MOD p_256` SUBST_ALL_TAC THENL
   [EXPAND_TAC "a1" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `a < 2 EXP (64 * 4)` THEN REWRITE_TAC[p_256] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "a" THEN ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
      ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x:real < y ==> x - &n < y`) THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; p_256] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    POP_ASSUM MP_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`read X0 s13 = z`; `read PC s13 = word (pc + 52)`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read Xnn s = y`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl))) THEN
    DISCH_TAC THEN DISCH_TAC] THEN

  SUBGOAL_THEN
   `(2 EXP 256 * a) MOD p_256 = (2 EXP 256 * a MOD p_256) MOD p_256`
  SUBST1_TAC THENL [CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a MOD p_256 < p_256` MP_TAC THENL
   [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`a MOD p_256`,`a:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`x_0 = read X2 s13`; `x_1 = read X3 s13`; `x_2 = read X4 s13`;
    `x_3 = read X5 s13`] THEN
  DISCH_TAC THEN

  (*** Break down the goal into 4 steps at the outset ***)

  SUBGOAL_THEN
   `(2 EXP 256 * a) MOD p_256 =
    (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * a)
     MOD p_256) MOD p_256) MOD p_256) MOD p_256`
  SUBST1_TAC THENL
   [CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** 4 iterations of the modulus tactic ***)

  modstep256_tac `[X5;X4;X3;X2;X6; X7;X8;X9]` `x_3:int64` 13 THEN

  modstep256_tac `[X4;X3;X2;X6;X5; X7;X8;X9]` `sum_s40:int64` 40 THEN

  modstep256_tac `[X3;X2;X6;X5;X4; X7;X8;X9]` `sum_s67:int64` 67 THEN

  modstep256_tac `[X2;X6;X5;X4;X3; X7;X8;X9]` `sum_s94:int64` 94 THEN

 (*** Final writeback and wrapup of proof ***)

  ARM_STEPS_TAC BIGNUM_TOMONT_P256_EXEC (122--123) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "a" THEN CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let BIGNUM_TOMONT_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x1f0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_p256_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TOMONT_P256_EXEC
    BIGNUM_TOMONT_P256_CORRECT);;
