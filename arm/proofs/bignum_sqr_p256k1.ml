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
(* Squaring modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/secp256k1/bignum_sqr_p256k1.o";;
 ****)

let bignum_sqr_p256k1_mc = define_assert_from_elf "bignum_sqr_p256k1_mc" "arm/secp256k1/bignum_sqr_p256k1.o"
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
  0xd2807a31;       (* arm_MOV X17 (rvalue (word 977)) *)
  0xb2600230;       (* arm_ORR X16 X17 (rvalue (word 4294967296)) *)
  0x9b067e0a;       (* arm_MUL X10 X16 X6 *)
  0x9bc67e0d;       (* arm_UMULH X13 X16 X6 *)
  0x92407ce6;       (* arm_AND X6 X7 (rvalue (word 4294967295)) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9b067e2b;       (* arm_MUL X11 X17 X6 *)
  0x9b071a26;       (* arm_MADD X6 X17 X7 X6 *)
  0xab06816b;       (* arm_ADDS X11 X11 (Shiftedreg X6 LSL 32) *)
  0xd360fcc6;       (* arm_LSR X6 X6 32 *)
  0x9a0600ee;       (* arm_ADC X14 X7 X6 *)
  0x9b087e0c;       (* arm_MUL X12 X16 X8 *)
  0x9bc87e08;       (* arm_UMULH X8 X16 X8 *)
  0x92407d26;       (* arm_AND X6 X9 (rvalue (word 4294967295)) *)
  0xd360fd27;       (* arm_LSR X7 X9 32 *)
  0x9b067e29;       (* arm_MUL X9 X17 X6 *)
  0x9b071a26;       (* arm_MADD X6 X17 X7 X6 *)
  0xab068129;       (* arm_ADDS X9 X9 (Shiftedreg X6 LSL 32) *)
  0xd360fcc6;       (* arm_LSR X6 X6 32 *)
  0x9a0600ef;       (* arm_ADC X15 X7 X6 *)
  0xab0a0042;       (* arm_ADDS X2 X2 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0x9a9f37e6;       (* arm_CSET X6 Condition_CS *)
  0xab0d0063;       (* arm_ADDS X3 X3 X13 *)
  0xba0e0084;       (* arm_ADCS X4 X4 X14 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0x9a0f00c6;       (* arm_ADC X6 X6 X15 *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0x9b067e2a;       (* arm_MUL X10 X17 X6 *)
  0xd360fccb;       (* arm_LSR X11 X6 32 *)
  0xab06814a;       (* arm_ADDS X10 X10 (Shiftedreg X6 LSL 32) *)
  0x9a0b03eb;       (* arm_ADC X11 XZR X11 *)
  0xab0a0042;       (* arm_ADDS X2 X2 X10 *)
  0xba0b0063;       (* arm_ADCS X3 X3 X11 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0x9a9f3210;       (* arm_CSEL X16 X16 XZR Condition_CC *)
  0xeb100042;       (* arm_SUBS X2 X2 X16 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_SQR_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_sqr_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

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

let p256k1redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256k1 - 1)
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let BIGNUM_SQR_P256K1_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x1bc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x1b8) /\
                  bignum_from_memory (z,4) s = (n EXP 2) MOD p_256k1)
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

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P256K1_EXEC
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
    `(2 EXP 256 * h + l) MOD p_256k1 = (4294968273 * h + l) MOD p_256k1`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `4294968273 * h + l` p256k1redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_256k1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits, with fiddly hybrid muls ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P256K1_EXEC [68;74;76] (66--76) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s76:int64)) + &(val(sum_s74:int64)):real =
    &4294968273 * &(val(sum_s63:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE o
        fst o chop_list 2) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SYM(DEPTH_CONV WORD_NUM_RED_CONV `word(2 EXP 32 - 1)`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; VAL_WORD; ADD_CLAUSES] THEN
    SIMP_TAC[DIMINDEX_64; VAL_BOUND_64; MOD_LT;
             ARITH_RULE `977 * x MOD 2 EXP 32 < 2 EXP 64`;
             ARITH_RULE `y < 2 EXP 64
                 ==> x MOD 2 EXP 32 + 977 * y DIV 2 EXP 32 < 2 EXP 64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    REWRITE_TAC[ARITH_RULE
     `(2 EXP 32 * x) DIV 2 EXP 64 = x DIV 2 EXP 32`] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST
     (MP_TAC o end_itlist CONJ o rev o  snd o chop_list 2) THEN
    STRIP_TAC THEN DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P256K1_EXEC [77;83;85] (77--85) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s85:int64)) + &(val(sum_s83:int64)):real =
    &4294968273 * &(val(sum_s65:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE o
        fst o chop_list 2) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SYM(DEPTH_CONV WORD_NUM_RED_CONV `word(2 EXP 32 - 1)`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_USHR; VAL_WORD; ADD_CLAUSES] THEN
    SIMP_TAC[DIMINDEX_64; VAL_BOUND_64; MOD_LT;
             ARITH_RULE `977 * x MOD 2 EXP 32 < 2 EXP 64`;
             ARITH_RULE `y < 2 EXP 64
                 ==> x MOD 2 EXP 32 + 977 * y DIV 2 EXP 32 < 2 EXP 64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    REWRITE_TAC[ARITH_RULE
     `(2 EXP 32 * x) DIV 2 EXP 64 = x DIV 2 EXP 32`] THEN
    REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST
     (MP_TAC o end_itlist CONJ o rev o  snd o chop_list 2) THEN
    STRIP_TAC THEN DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P256K1_EXEC [86;87;88;89;91;92;93;94]
    (86--94) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s86; sum_s91; sum_s92; sum_s93; sum_s94]` THEN
  SUBGOAL_THEN `(4294968273 * h + l) DIV 2 EXP 256 + 1 <= 2 EXP 33`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN `4294968273 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s94:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN

  ARM_STEPS_TAC BIGNUM_SQR_P256K1_EXEC [95] THEN
  ABBREV_TAC `q:int64 = word_add sum_s94 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s94:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation, with more hybrid mul fiddling ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P256K1_EXEC (96--99) (96--99) THEN

  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s99:int64)) + &(val(sum_s98:int64)) =
    &4294968273 * &(val(q:int64))`
  MP_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN EXPAND_TAC "mullo_s96" THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `q <= 2 EXP 33 ==> 977 MOD 2 EXP 64 * q < 2 EXP 64`] THEN
    ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P256K1_EXEC
    [100;101;102;103;105;106;107;108] (100--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s103` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s94:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN `word_add sum_s94 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s103:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_SQR_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x1bc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (n EXP 2) MOD p_256k1)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_SQR_P256K1_EXEC BIGNUM_SQR_P256K1_CORRECT);;
