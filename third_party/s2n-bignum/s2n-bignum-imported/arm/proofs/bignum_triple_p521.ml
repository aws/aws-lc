(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_521, the field characteristic for the NIST P-521 curve. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_triple_p521.o";;
 ****)

let bignum_triple_p521_mc = define_assert_from_elf "bignum_triple_p521_mc" "arm/p521/bignum_triple_p521.o"
[
  0xf940202c;       (* arm_LDR X12 X1 (Immediate_Offset (word 64)) *)
  0xd3492183;       (* arm_LSL X3 X12 (rvalue (word 55)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0x93c3fc83;       (* arm_EXTR X3 X4 X3 (rvalue (word 63)) *)
  0x93c4fca2;       (* arm_EXTR X2 X5 X4 (rvalue (word 63)) *)
  0xba030084;       (* arm_ADCS X4 X4 X3 *)
  0xa9411c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0x93c5fcc3;       (* arm_EXTR X3 X6 X5 (rvalue (word 63)) *)
  0xba0200a5;       (* arm_ADCS X5 X5 X2 *)
  0x93c6fce2;       (* arm_EXTR X2 X7 X6 (rvalue (word 63)) *)
  0xba0300c6;       (* arm_ADCS X6 X6 X3 *)
  0xa9422428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&32))) *)
  0x93c7fd03;       (* arm_EXTR X3 X8 X7 (rvalue (word 63)) *)
  0xba0200e7;       (* arm_ADCS X7 X7 X2 *)
  0x93c8fd22;       (* arm_EXTR X2 X9 X8 (rvalue (word 63)) *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0xa9432c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&48))) *)
  0x93c9fd43;       (* arm_EXTR X3 X10 X9 (rvalue (word 63)) *)
  0xba020129;       (* arm_ADCS X9 X9 X2 *)
  0x93cafd62;       (* arm_EXTR X2 X11 X10 (rvalue (word 63)) *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x93cbfd83;       (* arm_EXTR X3 X12 X11 (rvalue (word 63)) *)
  0xba02016b;       (* arm_ADCS X11 X11 X2 *)
  0x92402063;       (* arm_AND X3 X3 (rvalue (word 511)) *)
  0xba03018c;       (* arm_ADCS X12 X12 X3 *)
  0xf1080183;       (* arm_SUBS X3 X12 (rvalue (word 512)) *)
  0xda9f33e3;       (* arm_CSETM X3 Condition_CS *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0x92770063;       (* arm_AND X3 X3 (rvalue (word 512)) *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xda03018c;       (* arm_SBC X12 X12 X3 *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200c;       (* arm_STR X12 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TRIPLE_P521_EXEC = ARM_MK_EXEC_RULE bignum_triple_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_521_AS_WORDLIST = prove
 (`p_521 =
   bignum_of_wordlist
    [word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word(0x1FF)]`,
  REWRITE_TAC[p_521; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_EQ_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] = p_521 <=>
   (!i. i < 64
        ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
            bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
   (!i. i < 9 ==> bit i n8) /\ (!i. i < 64 ==> 9 <= i ==> ~bit i n8)`,
  REWRITE_TAC[P_521_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let BIGNUM_FROM_MEMORY_LE_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] <= p_521 <=>
   !i. i < 64 ==> 9 <= i ==> ~bit i n8`,
  SIMP_TAC[P_521; ARITH_RULE `p_521 = 2 EXP 521 - 1 ==>
    (n <= p_521 <=> n DIV 2 EXP (8 * 64) < 2 EXP 9)`] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `8`; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV; EXP; DIV_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; GSYM UPPER_BITS_ZERO] THEN
  MP_TAC(ISPEC `n8:int64` BIT_TRIVIAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MESON_TAC[NOT_LE]);;

let BIGNUM_FROM_MEMORY_LT_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] < p_521 <=>
   (!i. i < 64 ==> 9 <= i ==> ~bit i n8) /\
   ~((!i. i < 64
          ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
              bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
     (!i. i < 9 ==> bit i n8))`,
  GEN_REWRITE_TAC LAND_CONV [LT_LE] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_P521; BIGNUM_FROM_MEMORY_LE_P521] THEN
  MESON_TAC[]);;

let BIGNUM_TRIPLE_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0xb0) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0xac) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_TRIPLE_P521_EXEC (1--43)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  (*** Initial rotate-and-add simulation ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_P521_EXEC
   [7;10;12;15;17;20;22;24;26] (1--26) THEN

  (*** Deduce what the rotated part actually is ***)

  ABBREV_TAC
   `m = bignum_of_wordlist
         [word_subword(word_join (n_0:int64) (word_shl n_8 55):int128) (63,64);
          word_subword(word_join (n_1:int64) n_0:int128) (63,64);
          word_subword(word_join (n_2:int64) n_1:int128) (63,64);
          word_subword(word_join (n_3:int64) n_2:int128) (63,64);
          word_subword(word_join (n_4:int64) n_3:int128) (63,64);
          word_subword(word_join (n_5:int64) n_4:int128) (63,64);
          word_subword(word_join (n_6:int64) n_5:int128) (63,64);
          word_subword(word_join (n_7:int64) n_6:int128) (63,64);
          word_and (word_subword(word_join (n_8:int64) n_7:int128) (63,64))
                   (word 511)]` THEN
  SUBGOAL_THEN `(3 * n) MOD p_521 = (((2 * n) MOD p_521) + n) MOD p_521`
  SUBST1_TAC THENL
   [CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * n) MOD p_521 = m` MP_TAC THENL
   [REWRITE_TAC[MOD_UNIQUE] THEN
    UNDISCH_TAC `n < p_521` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_LT_P521; bignum_of_wordlist] THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
     (LABEL_TAC "*" o CONV_RULE(RAND_CONV CONJ_CANON_CONV))) THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_AND; BIT_WORD_1;
                BIT_WORD_SHL; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV CONJ_CANON_CONV))) THEN
    ASM_REWRITE_TAC[REAL_CONGRUENCE; p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC;
    DISCH_THEN(fun th -> SUBST1_TAC th THEN MP_TAC
     (MATCH_MP(MESON[MOD_LT_EQ] `x MOD n = y ==> ~(n = 0) ==> y < n`) th)) THEN
    ANTS_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC]] THEN

  (*** Now the result of the addition ***)

  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s7;sum_s10;sum_s12;sum_s15;sum_s17;sum_s20;sum_s22;sum_s24;sum_s26] =
    m + n + 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`576`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[p_521] THEN REAL_ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The net comparison s >= 2^521 <=> x + x' >= p_521 ***)

  ARM_STEPS_TAC BIGNUM_TRIPLE_P521_EXEC (27--28) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64; NOT_LT]) THEN
  SUBGOAL_THEN `512 <= val(sum_s26:int64) <=> p_521 <= m + n`
  SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS `512 <= (m + n + 1) DIV 2 EXP 512` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The final optional subtraction of either 1 or 2^521 ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_P521_EXEC (29::(31--38)) (29--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 9`;
    `if p_521 <= m + n then &(m + n + 1) - &2 pow 521
     else &(m + n + 1) - &1:real`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_ADD_CASES; GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC] THEN
  ABBREV_TAC `s = m + n + 1` THEN POP_ASSUM(K ALL_TAC) THEN EXPAND_TAC "s" THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM NOT_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TRIPLE_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0xb0) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s = (3 * n) MOD p_521))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TRIPLE_P521_EXEC
    BIGNUM_TRIPLE_P521_CORRECT);;
