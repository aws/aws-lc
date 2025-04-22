(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_521.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_deamont_p521.o";;
 ****)

let bignum_deamont_p521_mc =
  define_assert_from_elf "bignum_deamont_p521_mc" "arm/p521/bignum_deamont_p521.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0xf940202a;       (* arm_LDR X10 X1 (Immediate_Offset (word 64)) *)
  0xd377d84b;       (* arm_LSL X11 X2 (rvalue (word 9)) *)
  0x93c2dc62;       (* arm_EXTR X2 X3 X2 (rvalue (word 55)) *)
  0x93c3dc83;       (* arm_EXTR X3 X4 X3 (rvalue (word 55)) *)
  0x8a03004c;       (* arm_AND X12 X2 X3 *)
  0x93c4dca4;       (* arm_EXTR X4 X5 X4 (rvalue (word 55)) *)
  0x8a04018c;       (* arm_AND X12 X12 X4 *)
  0x93c5dcc5;       (* arm_EXTR X5 X6 X5 (rvalue (word 55)) *)
  0x8a05018c;       (* arm_AND X12 X12 X5 *)
  0x93c6dce6;       (* arm_EXTR X6 X7 X6 (rvalue (word 55)) *)
  0x8a06018c;       (* arm_AND X12 X12 X6 *)
  0x93c7dd07;       (* arm_EXTR X7 X8 X7 (rvalue (word 55)) *)
  0x8a07018c;       (* arm_AND X12 X12 X7 *)
  0x93c8dd28;       (* arm_EXTR X8 X9 X8 (rvalue (word 55)) *)
  0x8a08018c;       (* arm_AND X12 X12 X8 *)
  0x93c9dd49;       (* arm_EXTR X9 X10 X9 (rvalue (word 55)) *)
  0xd377fd4a;       (* arm_LSR X10 X10 (rvalue (word 55)) *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xd377d96c;       (* arm_LSL X12 X11 (rvalue (word 9)) *)
  0xba0c013f;       (* arm_ADCS XZR X9 X12 *)
  0xb277d94a;       (* arm_ORR X10 X10 (rvalue (word 18446744073709551104)) *)
  0xd377fd6b;       (* arm_LSR X11 X11 (rvalue (word 55)) *)
  0xba0b015f;       (* arm_ADCS XZR X10 X11 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba0c0129;       (* arm_ADCS X9 X9 X12 *)
  0x9a0b014a;       (* arm_ADC X10 X10 X11 *)
  0x9240214a;       (* arm_AND X10 X10 (rvalue (word 511)) *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200a;       (* arm_STR X10 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEAMONT_P521_EXEC = ARM_MK_EXEC_RULE bignum_deamont_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let LEXICOGRAPHIC_LE_MAXIMAL = prove
 (`!d e x y.
        x < e
        ==> (e * d - 1 <= x + e * y <=>
             d <= y \/ x = e - 1 /\ y = d - 1)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[] THENL [ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:num`; `d - 1`; `e - 1`; `y:num`; `x:num`]
   LEXICOGRAPHIC_LE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC EQ_IMP] THEN
  REPLICATE_TAC 2 (BINOP_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB;
               LE_1; MULT_EQ_0] THEN
  REAL_ARITH_TAC);;

let BIGNUM_DEAMONT_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0xac) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0xa8) /\
                  bignum_from_memory (z,9) s =
                   (inverse_mod p_521 (2 EXP 576) * n) MOD p_521)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12] ,,
              MAYCHANGE [memory :> bytes(z,8 * 9)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Digitize and break the input into n = 2 * 55 * h + l ***)

  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN
  MAP_EVERY ABBREV_TAC [`h = n DIV 2 EXP 55`; `l = n MOD 2 EXP 55`] THEN
  SUBGOAL_THEN `l < 2 EXP 55` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h < 2 EXP 521` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 55 < 2 EXP 521 <=> n < 2 EXP (64 * 9)`] THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(inverse_mod p_521 (2 EXP 576) * n) MOD p_521 =
    (h + 2 EXP 466 * l) MOD p_521`
  SUBST1_TAC THENL
   [SUBST1_TAC(ARITH_RULE
     `n = 2 EXP 55 * n DIV 2 EXP 55 + n MOD 2 EXP 55`) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!e. (e * i == 1) (mod n) /\ (e * hl == a) (mod n)
          ==> (i * a == hl) (mod n)`) THEN
    EXISTS_TAC `2 EXP 576` THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 576`); INVERSE_MOD_RMUL_EQ] THEN
    REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_521] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** The actual computations of h and l ***)

  ARM_STEPS_TAC BIGNUM_DEAMONT_P521_EXEC (1--21) THEN
  MAP_EVERY ABBREV_TAC
   [`d0:int64 =
       word_subword ((word_join:int64->int64->int128) x_1 x_0) (55,64)`;
    `d1:int64 =
       word_subword ((word_join:int64->int64->int128) x_2 x_1) (55,64)`;
    `d2:int64 =
       word_subword ((word_join:int64->int64->int128) x_3 x_2) (55,64)`;
    `d3:int64 =
       word_subword ((word_join:int64->int64->int128) x_4 x_3) (55,64)`;
    `d4:int64 =
       word_subword ((word_join:int64->int64->int128) x_5 x_4) (55,64)`;
    `d5:int64 =
       word_subword ((word_join:int64->int64->int128) x_6 x_5) (55,64)`;
    `d6:int64 =
       word_subword ((word_join:int64->int64->int128) x_7 x_6) (55,64)`;
    `d7:int64 =
       word_subword ((word_join:int64->int64->int128) x_8 x_7) (55,64)`;
    `d8:int64 = word_ushr x_8 55`] THEN
  SUBGOAL_THEN `word_shl (x_0:int64) 9 = word(2 EXP 9 * l)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "n"] THEN REWRITE_TAC[word_shl; WORD_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(1,8)] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 = 55 + 9`; EXP_ADD] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; MOD_MULT_ADD] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(a:num == b) (mod n) ==> (a * e == e * b) (mod (n * e))`) THEN
    REWRITE_TAC[CONG; BIGNUM_OF_WORDLIST_SING] THEN CONV_TAC MOD_DOWN_CONV THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `n DIV 2 EXP 55 = bignum_of_wordlist[d0;d1;d2;d3;d4;d5;d6;d7;d8]`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(x_0:int64) MOD 2 EXP 55` THEN
    REWRITE_TAC[ARITH_RULE `x MOD 2 EXP 55 < 2 EXP 55`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN EXPAND_TAC "n" THEN
    MAP_EVERY EXPAND_TAC
     ["d0"; "d1"; "d2"; "d3"; "d4"; "d5"; "d6"; "d7"; "d8"] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_AND;
                BIT_WORD_USHR; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ONCE_REWRITE_TAC[BIT_GUARD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  (*** The (condensed) comparison ***)

  SUBGOAL_THEN
   `&(val(word_or d8 (word 18446744073709551104):int64)):real =
    &2 pow 9 * (&2 pow 55 - &1) + &(val d8)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; EQ_ADD_LCANCEL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
    EXPAND_TAC "d8" THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_USHR; DIMINDEX_64] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
    ALL_TAC] THEN

  SUBGOAL_THEN
   `bignum_of_wordlist
     [word_shl (word (512 * l)) 9; word_ushr (word (512 * l)) 55] =
    2 EXP 18 * l`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; VAL_WORD_SHL; VAL_WORD_USHR] THEN
    REWRITE_TAC[DIMINDEX_64; EXP_ADD; ARITH_RULE `64 = 9 + 55`] THEN
    REWRITE_TAC[MOD_MULT2; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN MATCH_MP_TAC(ARITH_RULE
     `x = 512 * l
      ==> 2 EXP 9 * (x MOD 2 EXP 55 + 2 EXP 55 * x DIV 2 EXP 55) =
          2 EXP 18 * l`) THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_DEAMONT_P521_EXEC [22;24;27] (22--27) THEN
  SUBGOAL_THEN `carry_s27 <=> p_521 <= h + 2 EXP 466 * l` SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS
     `2 EXP 192 <=
      bignum_of_wordlist
       [word_and
         (word_and (word_and (word_and (word_and (word_and d0 d1) d2) d3)
             d4) d5) d6;
        d7; word_or d8 (word 18446744073709551104)] +
      bignum_of_wordlist
       [word 1; word_shl (word (512 * l)) 9;
        word_ushr (word (512 * l)) 55]` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; VAL_WORD_1]) THEN BOUNDER_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
        [BIGNUM_OF_WORDLIST_SPLIT_RULE(1,2)] THEN
      ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; VAL_WORD_1] THEN
      EXPAND_TAC "h" THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(7,2)] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(1,2)] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(1,1)] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; BIGNUM_OF_WORDLIST_SING] THEN
      REWRITE_TAC[REAL_ARITH
       `&2 pow 192 <=
        (a + &2 pow 64 * (b + &2 pow 64 * (&2 pow 9 * (&2 pow 55 - &1) + c))) +
        &1 + &2 pow 64 * &2 pow 18 * l <=>
        &2 pow 137 - &1 <=
        a + &2 pow 64 * (b + &2 pow 18 * l + &2 pow 64 * c)`] THEN
      REWRITE_TAC[REAL_ARITH
       `(a + &2 pow 448 * (b + c)) + &2 pow 466 * d:real =
        a + &2 pow 448 * (b + &2 pow 18 * d + c)`] THEN
      REWRITE_TAC[P_521] THEN
      SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB; EXP_EQ_0; LE_1;
               ARITH_EQ] THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `137 = 64 + 73 /\ 521 = 448 + 73`] THEN
      REWRITE_TAC[ARITH_RULE `448 = 64 * 7`] THEN
      SIMP_TAC[LEXICOGRAPHIC_LE_MAXIMAL; BIGNUM_OF_WORDLIST_BOUND; ARITH_SUC;
               LENGTH; LE_REFL; VAL_BOUND_64; BIGNUM_OF_WORDLIST_EQ_MAX] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM DIMINDEX_64; VAL_EQ_MAX; ALL] THEN
      CONV_TAC WORD_BITWISE_RULE];
    ACCUMULATOR_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final addition ***)

  ABBREV_TAC `hl = h + 2 EXP 466 * l` THEN
  ARM_ACCSTEPS_TAC BIGNUM_DEAMONT_P521_EXEC (28--36) (28--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + 2 EXP 466 * l < p_521
     then &(h + 2 EXP 466 * l)
     else &(h + 2 EXP 466 * l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN EXPAND_TAC "hl" THEN
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN MATCH_MP_TAC MOD_CASES THEN
    MAP_EVERY UNDISCH_TAC [`h < 2 EXP 521`; `l < 2 EXP 55`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  ABBREV_TAC `bb <=> p_521 <= hl` THEN MAP_EVERY EXPAND_TAC ["hl"; "h"] THEN
  SUBGOAL_THEN
   `2 EXP 466 * l =
    2 EXP 448 * bignum_of_wordlist
      [word_shl (word (512 * l)) 9; word_ushr (word (512 * l)) 55]`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DEAMONT_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0xac) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,9) s =
                    (inverse_mod p_521 (2 EXP 576) * n) MOD p_521)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DEAMONT_P521_EXEC
    BIGNUM_DEAMONT_P521_CORRECT);;
