(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Squaring modulo p_25519, the field characteristic for curve25519.          *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/curve25519/bignum_sqr_p25519.o";;
 ****)

let bignum_sqr_p25519_mc = define_assert_from_elf "bignum_sqr_p25519_mc" "arm/curve25519/bignum_sqr_p25519.o"
[
  0xa9401c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&0))) *)
  0xa9412c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&16))) *)
  0x9b0a7cc4;       (* arm_MUL X4 X6 X10 *)
  0x9b0b7ce9;       (* arm_MUL X9 X7 X11 *)
  0x9bca7ccc;       (* arm_UMULH X12 X6 X10 *)
  0xeb0700cd;       (* arm_SUBS X13 X6 X7 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0xda9f23e3;       (* arm_CSETM X3 Condition_CC *)
  0xeb0a0162;       (* arm_SUBS X2 X11 X10 *)
  0xda822442;       (* arm_CNEG X2 X2 Condition_CC *)
  0x9b027da8;       (* arm_MUL X8 X13 X2 *)
  0x9bc27da2;       (* arm_UMULH X2 X13 X2 *)
  0xda832063;       (* arm_CINV X3 X3 Condition_CC *)
  0xca030108;       (* arm_EOR X8 X8 X3 *)
  0xca030042;       (* arm_EOR X2 X2 X3 *)
  0xab0c0085;       (* arm_ADDS X5 X4 X12 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9bcb7ced;       (* arm_UMULH X13 X7 X11 *)
  0xab0900a5;       (* arm_ADDS X5 X5 X9 *)
  0xba0d018c;       (* arm_ADCS X12 X12 X13 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab09018c;       (* arm_ADDS X12 X12 X9 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xb100047f;       (* arm_CMN X3 (rvalue (word 1)) *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0x9a0301ad;       (* arm_ADC X13 X13 X3 *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba0500a5;       (* arm_ADCS X5 X5 X5 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0x9b067cc2;       (* arm_MUL X2 X6 X6 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cc3;       (* arm_UMULH X3 X6 X6 *)
  0x9bc77ce9;       (* arm_UMULH X9 X7 X7 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab080084;       (* arm_ADDS X4 X4 X8 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b0a7d46;       (* arm_MUL X6 X10 X10 *)
  0x9b0b7d68;       (* arm_MUL X8 X11 X11 *)
  0x9b0b7d4f;       (* arm_MUL X15 X10 X11 *)
  0x9bca7d47;       (* arm_UMULH X7 X10 X10 *)
  0x9bcb7d69;       (* arm_UMULH X9 X11 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0c00c6;       (* arm_ADDS X6 X6 X12 *)
  0xba0d00e7;       (* arm_ADCS X7 X7 X13 *)
  0xba0e0108;       (* arm_ADCS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd28004ca;       (* arm_MOV X10 (rvalue (word 38)) *)
  0x92407ccb;       (* arm_AND X11 X6 (rvalue (word 4294967295)) *)
  0xd360fccc;       (* arm_LSR X12 X6 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b0c7d4c;       (* arm_MUL X12 X10 X12 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x92407ceb;       (* arm_AND X11 X7 (rvalue (word 4294967295)) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b077d47;       (* arm_MUL X7 X10 X7 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x92407d0b;       (* arm_AND X11 X8 (rvalue (word 4294967295)) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b087d48;       (* arm_MUL X8 X10 X8 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x92407d2b;       (* arm_AND X11 X9 (rvalue (word 4294967295)) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b097d49;       (* arm_MUL X9 X10 X9 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0xd3607d8b;       (* arm_LSL X11 X12 32 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0x93cc80eb;       (* arm_EXTR X11 X7 X12 32 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0x93c7810b;       (* arm_EXTR X11 X8 X7 32 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x93c8812b;       (* arm_EXTR X11 X9 X8 32 *)
  0xba0b00a5;       (* arm_ADCS X5 X5 X11 *)
  0xd360fd2b;       (* arm_LSR X11 X9 32 *)
  0x9a0b00c6;       (* arm_ADC X6 X6 X11 *)
  0xab0500bf;       (* arm_CMN X5 X5 *)
  0xb24100a5;       (* arm_ORR X5 X5 (rvalue (word 9223372036854775808)) *)
  0x9a0600cd;       (* arm_ADC X13 X6 X6 *)
  0xd280026a;       (* arm_MOV X10 (rvalue (word 19)) *)
  0x9b0d294b;       (* arm_MADD X11 X10 X13 X10 *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a9f314a;       (* arm_CSEL X10 X10 XZR Condition_CC *)
  0xeb0a0042;       (* arm_SUBS X2 X2 X10 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0x9240f8a5;       (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_P25519_EXEC = ARM_MK_EXEC_RULE bignum_sqr_p25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 2 EXP 255 - 19`;;

let lemma1 = prove
 (`!(x0:num) x1 (y0:num) y1.
       (if y0 <= y1
        then if x1 <= x0 then word 0 else word 18446744073709551615
        else word_not
         (if x1 <= x0 then word 0 else word 18446744073709551615)):int64 =
   word_neg(word(bitval(y0 <= y1 <=> x0 < x1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let lemma2 = prove
 (`!(x0:int64) (x1:int64) (y0:int64) (y1:int64).
        &(val(if val x1 <= val x0 then word_sub x0 x1
              else word_neg (word_sub x0 x1))) *
        &(val(if val y0 <= val y1 then word_sub y1 y0
              else word_neg (word_sub y1 y0))):real =
        --(&1) pow bitval(val y0 <= val y1 <=> val x0 < val x1) *
        (&(val x0) - &(val x1)) * (&(val y1) - &(val y0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE; WORD_NEG_SUB] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(m:num <= n) ==> n <= m /\ ~(m <= n)`))) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let shiftandlemma = prove
 (`!x:int64. &(val(word_and x (word 4294967295))):real =
             &(val x) - &2 pow 32 * &(val(word_ushr x 32))`,
  GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[val_def; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ARITH_TAC);;

let BIGNUM_SQR_P25519_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x1cc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p25519_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x1c8) /\
                  bignum_from_memory (z,4) s = (n EXP 2) MOD p_25519)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC
   [3; 4; 11; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29;
    30; 31; 32; 33; 34; 35; 39; 40; 41; 42; 43; 44; 45; 46; 47;
    48; 49; 50; 51; 52; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65]
   (1--65) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s33; sum_s42; sum_s45; sum_s46]`;
    `h = bignum_of_wordlist[sum_s62; sum_s63; sum_s64; sum_s65]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter(is_ratconst o rand o concl) o
                DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC
   [69;70;71;74;75;76;79;80;81;84;85;86;89;91;93;95;97]
   (66--97) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist
          [sum_s89; sum_s91; sum_s93; sum_s95; sum_s97]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    TRANS_TAC EQ_TRANS
     `bignum_of_wordlist[sum_s71; sum_s76; sum_s81; sum_s86;
                       word(bitval carry_s86)] +
      2 EXP 32 *
      bignum_of_wordlist[mullo_s70; mullo_s75; mullo_s80; mullo_s85]` THEN
    CONJ_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THENL
     [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 snd o chop_list 5);
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE o
                                 fst o chop_list 5)] THEN
    REWRITE_TAC[shiftandlemma] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_0] THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_ARITH
      `x + --c * y:real = z <=> x = c * y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM ADD_ASSOC] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LT; ARITH_LE] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`; MOD_MULT2] THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (98--100) (98--100) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s89; sum_s91; sum_s93;
    word_or sum_s95 (word 9223372036854775808)]` THEN
    SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s89; sum_s91; sum_s93] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(sum_s100:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 63 = (2 * n) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s98; sum_s100] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ARM_STEPS_TAC BIGNUM_SQR_P25519_EXEC (101--102) THEN
  ABBREV_TAC `qm:int64 = word(19 + 19 * val(sum_s100:int64))` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * (&(val(sum_s100:int64)) + &1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `c + c * q = c * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s100:int64) + 1 <= 78` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (103--114) (103--114) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s100:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(sum_s100:int64) + 1) * p_25519 <=> ~carry_s106`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s106:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_SQR_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x1cc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p25519_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (n EXP 2) MOD p_25519)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_SQR_P25519_EXEC BIGNUM_SQR_P25519_CORRECT);;
