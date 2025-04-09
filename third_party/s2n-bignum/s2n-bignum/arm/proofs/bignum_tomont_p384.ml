(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 6-word (384-bit) bignum to Montgomery form modulo p_384.  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_tomont_p384.o";;
 ****)

let bignum_tomont_p384_mc =
  define_assert_from_elf "bignum_tomont_p384_mc" "arm/p384/bignum_tomont_p384.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0xb2607fe9;       (* arm_MOV X9 (rvalue (word 18446744069414584320)) *)
  0x9280002a;       (* arm_MOVN X10 (word 1) 0 *)
  0xeb080048;       (* arm_SUBS X8 X2 X8 *)
  0xfa090069;       (* arm_SBCS X9 X3 X9 *)
  0xfa0a008a;       (* arm_SBCS X10 X4 X10 *)
  0xba1f00ab;       (* arm_ADCS X11 X5 XZR *)
  0xba1f00cc;       (* arm_ADCS X12 X6 XZR *)
  0xba1f00e1;       (* arm_ADCS X1 X7 XZR *)
  0x9a883042;       (* arm_CSEL X2 X2 X8 Condition_CC *)
  0x9a893063;       (* arm_CSEL X3 X3 X9 Condition_CC *)
  0x9a8a3084;       (* arm_CSEL X4 X4 X10 Condition_CC *)
  0x9a8b30a5;       (* arm_CSEL X5 X5 X11 Condition_CC *)
  0x9a8c30c6;       (* arm_CSEL X6 X6 X12 Condition_CC *)
  0x9a8130e7;       (* arm_CSEL X7 X7 X1 Condition_CC *)
  0xb10004e7;       (* arm_ADDS X7 X7 (rvalue (word 1)) *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0x8b0b00e7;       (* arm_ADD X7 X7 X11 *)
  0xaa2b03eb;       (* arm_ORN X11 XZR X11 *)
  0xd10004ea;       (* arm_SUB X10 X7 (rvalue (word 1)) *)
  0xcb0703e9;       (* arm_NEG X9 X7 *)
  0xd3607d28;       (* arm_LSL X8 X9 (rvalue (word 32)) *)
  0x93c98149;       (* arm_EXTR X9 X10 X9 (rvalue (word 32)) *)
  0xd360fd4a;       (* arm_LSR X10 X10 (rvalue (word 32)) *)
  0xab070108;       (* arm_ADDS X8 X8 X7 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0xab090042;       (* arm_ADDS X2 X2 X9 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0xba070084;       (* arm_ADCS X4 X4 X7 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xab090108;       (* arm_ADDS X8 X8 X9 *)
  0xca0b0129;       (* arm_EOR X9 X9 X11 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xba090063;       (* arm_ADCS X3 X3 X9 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9a0b00c6;       (* arm_ADC X6 X6 X11 *)
  0xb10004c6;       (* arm_ADDS X6 X6 (rvalue (word 1)) *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0x8b0b00c6;       (* arm_ADD X6 X6 X11 *)
  0xaa2b03eb;       (* arm_ORN X11 XZR X11 *)
  0xd10004ca;       (* arm_SUB X10 X6 (rvalue (word 1)) *)
  0xcb0603e9;       (* arm_NEG X9 X6 *)
  0xd3607d27;       (* arm_LSL X7 X9 (rvalue (word 32)) *)
  0x93c98149;       (* arm_EXTR X9 X10 X9 (rvalue (word 32)) *)
  0xd360fd4a;       (* arm_LSR X10 X10 (rvalue (word 32)) *)
  0xab0600e7;       (* arm_ADDS X7 X7 X6 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xab090108;       (* arm_ADDS X8 X8 X9 *)
  0xba0a0042;       (* arm_ADCS X2 X2 X10 *)
  0xba060063;       (* arm_ADCS X3 X3 X6 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xab0900e7;       (* arm_ADDS X7 X7 X9 *)
  0xca0b0129;       (* arm_EOR X9 X9 X11 *)
  0xba090108;       (* arm_ADCS X8 X8 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xba090042;       (* arm_ADCS X2 X2 X9 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a0b00a5;       (* arm_ADC X5 X5 X11 *)
  0xb10004a5;       (* arm_ADDS X5 X5 (rvalue (word 1)) *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0x8b0b00a5;       (* arm_ADD X5 X5 X11 *)
  0xaa2b03eb;       (* arm_ORN X11 XZR X11 *)
  0xd10004aa;       (* arm_SUB X10 X5 (rvalue (word 1)) *)
  0xcb0503e9;       (* arm_NEG X9 X5 *)
  0xd3607d26;       (* arm_LSL X6 X9 (rvalue (word 32)) *)
  0x93c98149;       (* arm_EXTR X9 X10 X9 (rvalue (word 32)) *)
  0xd360fd4a;       (* arm_LSR X10 X10 (rvalue (word 32)) *)
  0xab0500c6;       (* arm_ADDS X6 X6 X5 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab0900e7;       (* arm_ADDS X7 X7 X9 *)
  0xba0a0108;       (* arm_ADCS X8 X8 X10 *)
  0xba050042;       (* arm_ADCS X2 X2 X5 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xab0900c6;       (* arm_ADDS X6 X6 X9 *)
  0xca0b0129;       (* arm_EOR X9 X9 X11 *)
  0xba0900e7;       (* arm_ADCS X7 X7 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xba090108;       (* arm_ADCS X8 X8 X9 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x9a0b0084;       (* arm_ADC X4 X4 X11 *)
  0xb1000484;       (* arm_ADDS X4 X4 (rvalue (word 1)) *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0x8b0b0084;       (* arm_ADD X4 X4 X11 *)
  0xaa2b03eb;       (* arm_ORN X11 XZR X11 *)
  0xd100048a;       (* arm_SUB X10 X4 (rvalue (word 1)) *)
  0xcb0403e9;       (* arm_NEG X9 X4 *)
  0xd3607d25;       (* arm_LSL X5 X9 (rvalue (word 32)) *)
  0x93c98149;       (* arm_EXTR X9 X10 X9 (rvalue (word 32)) *)
  0xd360fd4a;       (* arm_LSR X10 X10 (rvalue (word 32)) *)
  0xab0400a5;       (* arm_ADDS X5 X5 X4 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba04014a;       (* arm_ADCS X10 X10 X4 *)
  0x9a1f03e4;       (* arm_ADC X4 XZR XZR *)
  0xab0900c6;       (* arm_ADDS X6 X6 X9 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xba040108;       (* arm_ADCS X8 X8 X4 *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xab0900a5;       (* arm_ADDS X5 X5 X9 *)
  0xca0b0129;       (* arm_EOR X9 X9 X11 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xba0900e7;       (* arm_ADCS X7 X7 X9 *)
  0xba0b0108;       (* arm_ADCS X8 X8 X11 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9a0b0063;       (* arm_ADC X3 X3 X11 *)
  0xb1000463;       (* arm_ADDS X3 X3 (rvalue (word 1)) *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0x8b0b0063;       (* arm_ADD X3 X3 X11 *)
  0xaa2b03eb;       (* arm_ORN X11 XZR X11 *)
  0xd100046a;       (* arm_SUB X10 X3 (rvalue (word 1)) *)
  0xcb0303e9;       (* arm_NEG X9 X3 *)
  0xd3607d24;       (* arm_LSL X4 X9 (rvalue (word 32)) *)
  0x93c98149;       (* arm_EXTR X9 X10 X9 (rvalue (word 32)) *)
  0xd360fd4a;       (* arm_LSR X10 X10 (rvalue (word 32)) *)
  0xab030084;       (* arm_ADDS X4 X4 X3 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba03014a;       (* arm_ADCS X10 X10 X3 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xab0900a5;       (* arm_ADDS X5 X5 X9 *)
  0xba0a00c6;       (* arm_ADCS X6 X6 X10 *)
  0xba0300e7;       (* arm_ADCS X7 X7 X3 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xca0b0129;       (* arm_EOR X9 X9 X11 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0xba0b0108;       (* arm_ADCS X8 X8 X11 *)
  0x9a0b0042;       (* arm_ADC X2 X2 X11 *)
  0xb1000442;       (* arm_ADDS X2 X2 (rvalue (word 1)) *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0x8b0b0042;       (* arm_ADD X2 X2 X11 *)
  0xaa2b03eb;       (* arm_ORN X11 XZR X11 *)
  0xd100044a;       (* arm_SUB X10 X2 (rvalue (word 1)) *)
  0xcb0203e9;       (* arm_NEG X9 X2 *)
  0xd3607d23;       (* arm_LSL X3 X9 (rvalue (word 32)) *)
  0x93c98149;       (* arm_EXTR X9 X10 X9 (rvalue (word 32)) *)
  0xd360fd4a;       (* arm_LSR X10 X10 (rvalue (word 32)) *)
  0xab020063;       (* arm_ADDS X3 X3 X2 *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xab090084;       (* arm_ADDS X4 X4 X9 *)
  0xba0a00a5;       (* arm_ADCS X5 X5 X10 *)
  0xba0200c6;       (* arm_ADCS X6 X6 X2 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xb2407fe9;       (* arm_MOV X9 (rvalue (word 4294967295)) *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0xca0b0129;       (* arm_EOR X9 X9 X11 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x92800029;       (* arm_MOVN X9 (word 1) 0 *)
  0x8a0b0129;       (* arm_AND X9 X9 X11 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0x9a0b0108;       (* arm_ADC X8 X8 X11 *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TOMONT_P384_EXEC = ARM_MK_EXEC_RULE bignum_tomont_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let p384longredlemma = prove
 (`!n. n < 2 EXP 64 * p_384
       ==> let q = MIN (n DIV 2 EXP 384 + 1) (2 EXP 64 - 1) in
           q < 2 EXP 64 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

(*** A generic tactic corresponding to the modular reduction macro ***)

let modstep384_tac regs topw n =
  let [d6;d5;d4;d3;d2;d1;d0; t1;t2;t3] = dest_list regs in
  let modterm = subst
   ([d0,`X8`; d1,`X2`; d2,`X3`; d3,`X4`; d4,`X5`; d5,`X6`; d6,`X7`;
     t1,`X9`; t2,`X10`; t3,`X11`] @
    [topw,`x_5:int64`] @
    (map (fun i -> mk_var("s"^string_of_int(i+n-18),`:armstate`),
                   mk_var("s"^string_of_int(i),`:armstate`))
         (19--48)))
  and modstring =
   C assoc
    (zip (statenames "s" (18--48)) (statenames "s" (n--(n+30)))) in
  MP_TAC(SPEC `2 EXP 64 * a` p384longredlemma) THEN ANTS_TAC THENL
   [UNDISCH_TAC `a < p_384` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `(2 EXP 64 * a) DIV 2 EXP 384 = a DIV 2 EXP (64 + 64 + 64 + 64 + 64)`] THEN
  EXPAND_TAC "a" THEN
  REWRITE_TAC[GSYM DIV_DIV; EXP_ADD; BIGNUM_OF_WORDLIST_DIV] THEN
  ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
  ABBREV_TAC (modterm `q = MIN (val(x_5:int64) + 1) (2 EXP 64 - 1)`) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MAP_EVERY (ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P384_EXEC)
            (map modstring (statenames "s" (19--22))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   (modterm `!q. read X7 s = q' ==> q' = q ==> read X7 s = q`))) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "q" THEN SIMP_TAC[VAL_BOUND_64; ARITH_RULE
     `x < 2 EXP 64 ==> (MIN (x + 1) (2 EXP 64 - 1) =
      if x + 1 < 2 EXP 64 then x + 1 else x)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC WORD_RULE;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o
   SPEC(modterm`word_neg(word(bitval(val(x_5:int64) + 1 < 2 EXP 64))):int64`) o
   MATCH_MP (MESON[] `!m. read X11 s = m' ==> m' = m ==> read X11 s = m`)) THEN
  ANTS_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV;
    DISCH_TAC] THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ARITH_TAC; ALL_TAC] THEN
  (*** Computation of the q * r term ***)
  MAP_EVERY (ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P384_EXEC)
            (map modstring (statenames "s" (23--27))) THEN
  SUBGOAL_THEN (modterm
   `&(bignum_of_wordlist[read X8 s27; read X9 s27; read X10 s27]):real =
    (&2 pow 96 - &2 pow 32) * &q`)
  ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word q:int64) = q` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64]; ALL_TAC] THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    SIMP_TAC[VAL_WORD_SHL; VAL_WORD_USHR; GSYM REAL_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_0; VAL_WORD_1] THEN
    ASM_REWRITE_TAC[DIMINDEX_64; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_REWRITE_TAC[CONJUNCT1 LE; REAL_ARITH
     `a:real = (b - c) * d <=> a + c * d = b * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    MAP_EVERY UNDISCH_TAC [`~(q = 0)`; `q < 2 EXP 64`] THEN
    REWRITE_TAC[EXP_ADD; MOD_MULT2; ARITH_RULE `64 = 32 + 32`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (REABBREV_TAC o modterm)
   [`a0 = read X8 s27`; `a1 = read X9 s27`; `a2 = read X10 s27`] THEN
  MAP_EVERY (fun s ->
    ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P384_EXEC s THEN
    ACCUMULATE_ARITH_TAC s)
   (map modstring (statenames "s" (28--37))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN (modterm
   `read X11 s37 = word_neg (word (bitval(2 EXP 64 * a < q * p_384))) /\
    &(bignum_of_wordlist
        [read X8 s37; read X2 s37; read X3 s37; read X4 s37; read X5 s37;
         read X6 s37]) =
    if 2 EXP 64 * a < q * p_384
    then &(2 EXP 64 * a) - &(q * p_384) + &2 pow 384
    else &(2 EXP 64 * a) - &(q * p_384)`)
  MP_TAC THENL
   [MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_LT THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`q * p_384 <= 2 EXP 64 * a + p_384`;
        `2 EXP 64 * a < q * p_384 + p_384`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&q * &p_384:real =
      (&2 pow 384 - &2 pow 128) * &q -
      (&(bignum_of_wordlist[a0; a1; a2]) + &q)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[p_384] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_VAL_WORD_MASK; DIMINDEX_64]) THEN
    SUBGOAL_THEN (modterm
     `&(bitval(val(x_5:int64) + 1 < 2 EXP 64)) = &q - &(val x_5)`)
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "q" THEN SIMP_TAC[VAL_BOUND_64; ARITH_RULE
       `x < 2 EXP 64
        ==> (MIN (x + 1) (2 EXP 64 - 1) =
             if x + 1 < 2 EXP 64 then x + 1 else x)`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word q:int64) = q` (SUBST_ALL_TAC o SYM) THENL
     [ASM_REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)] THEN
  MAP_EVERY (fun s ->
    ARM_SINGLE_STEP_TAC BIGNUM_TOMONT_P384_EXEC s THEN
    TRY(ACCUMULATE_ARITH_TAC s))
   (map modstring (statenames "s" (38--48))) THEN
  SUBGOAL_THEN (modterm
   `bignum_of_wordlist
     [read X8 s48; read X2 s48; read X3 s48; read X4 s48; read X5 s48;
      read X6 s48] = (2 EXP 64 * a) MOD p_384`)
  MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
    MAP_EVERY EXISTS_TAC [`q:num`; `384`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
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
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[p_384] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN ASM_REWRITE_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `q:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl))) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue y) s = x`] THEN
  DISCARD_FLAGS_TAC THEN
  SUBGOAL_THEN `(2 EXP 64 * a) MOD p_384 < p_384` MP_TAC THENL
   [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`(2 EXP 64 * a) MOD p_384`,`a:num`) THEN
  REPEAT STRIP_TAC;;

let BIGNUM_TOMONT_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x328) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + 0x324) /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initial reduction of the input mod p_384 ***)

  BIGNUM_TERMRANGE_TAC `6` `a:num` THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  ARM_ACCSTEPS_TAC BIGNUM_TOMONT_P384_EXEC (1--18) (1--18) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN `carry_s12 <=> p_384 <= a` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  ABBREV_TAC
   `a1 = bignum_of_wordlist
        [read X2 s18; read X3 s18; read X4 s18; read X5 s18; read X6 s18;
         read X7 s18]` THEN
  SUBGOAL_THEN `a1 = a MOD p_384` SUBST_ALL_TAC THENL
   [EXPAND_TAC "a1" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    ASM_REWRITE_TAC[NOT_LE] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `a < 2 EXP (64 * 6)` THEN REWRITE_TAC[p_384] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "a" THEN ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; GSYM REAL_OF_NUM_SUB] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_TAC `a < 2 EXP (64 * 6)` THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; p_384] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    POP_ASSUM MP_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`read X0 s18 = z`; `read PC s18 = word (pc + 72)`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read Xnn s = y`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl))) THEN
    DISCH_TAC THEN DISCH_TAC] THEN

  SUBGOAL_THEN
   `(2 EXP 384 * a) MOD p_384 = (2 EXP 384 * a MOD p_384) MOD p_384`
  SUBST1_TAC THENL [CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a MOD p_384 < p_384` MP_TAC THENL
   [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`a MOD p_384`,`a:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`x_0 = read X2 s18`; `x_1 = read X3 s18`; `x_2 = read X4 s18`;
    `x_3 = read X5 s18`; `x_4 = read X6 s18`; `x_5 = read X7 s18`] THEN
  DISCH_TAC THEN

  (*** Break down the goal into 6 steps at the outset ***)

  SUBGOAL_THEN
   `(2 EXP 384 * a) MOD p_384 =
    (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * a)
     MOD p_384) MOD p_384) MOD p_384) MOD p_384) MOD p_384) MOD p_384`
  SUBST1_TAC THENL
   [CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** 6 iterations of the modulus tactic ***)

  modstep384_tac `[X7;X6;X5;X4;X3;X2;X8; X9;X10;X11]` `x_5:int64` 18 THEN

  modstep384_tac `[X6;X5;X4;X3;X2;X8;X7; X9;X10;X11]` `sum_s48:int64` 48 THEN

  modstep384_tac `[X5;X4;X3;X2;X8;X7;X6; X9;X10;X11]` `sum_s78:int64` 78 THEN

  modstep384_tac `[X4;X3;X2;X8;X7;X6;X5; X9;X10;X11]` `sum_s108:int64` 108 THEN

  modstep384_tac `[X3;X2;X8;X7;X6;X5;X4; X9;X10;X11]` `sum_s138:int64` 138 THEN

  modstep384_tac `[X2;X8;X7;X6;X5;X4;X3; X9;X10;X11]` `sum_s168:int64` 168 THEN

  (*** Final writeback and wrapup of proof ***)

  ARM_STEPS_TAC BIGNUM_TOMONT_P384_EXEC (199--201) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "a" THEN CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let BIGNUM_TOMONT_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x328) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_tomont_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,6) s = (2 EXP 384 * a) MOD p_384)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TOMONT_P384_EXEC
    BIGNUM_TOMONT_P384_CORRECT);;
