(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery square mod p_256k1, the field characteristic for secp256k1.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_montsqr_p256k1.o";;
 ****)

let bignum_montsqr_p256k1_mc =
  define_assert_from_elf "bignum_montsqr_p256k1_mc" "arm/secp256k1/bignum_montsqr_p256k1.o"
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
  0xd286a62a;       (* arm_MOV X10 (rvalue (word 13617)) *)
  0xf2ba44aa;       (* arm_MOVK X10 (word 53797) 16 *)
  0xf2c123aa;       (* arm_MOVK X10 (word 2333) 32 *)
  0xf2fb070a;       (* arm_MOVK X10 (word 55352) 48 *)
  0xd2807a2b;       (* arm_MOV X11 (rvalue (word 977)) *)
  0xb260016b;       (* arm_ORR X11 X11 (rvalue (word 4294967296)) *)
  0x9b027d42;       (* arm_MUL X2 X10 X2 *)
  0x9bcb7c4c;       (* arm_UMULH X12 X2 X11 *)
  0xeb0c0063;       (* arm_SUBS X3 X3 X12 *)
  0x9b037d43;       (* arm_MUL X3 X10 X3 *)
  0x9bcb7c6c;       (* arm_UMULH X12 X3 X11 *)
  0xfa0c0084;       (* arm_SBCS X4 X4 X12 *)
  0x9b047d44;       (* arm_MUL X4 X10 X4 *)
  0x9bcb7c8c;       (* arm_UMULH X12 X4 X11 *)
  0xfa0c00a5;       (* arm_SBCS X5 X5 X12 *)
  0x9b057d45;       (* arm_MUL X5 X10 X5 *)
  0x9bcb7cac;       (* arm_UMULH X12 X5 X11 *)
  0xfa0c0042;       (* arm_SBCS X2 X2 X12 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0xab060042;       (* arm_ADDS X2 X2 X6 *)
  0xba070063;       (* arm_ADCS X3 X3 X7 *)
  0xba080084;       (* arm_ADCS X4 X4 X8 *)
  0x8a04006d;       (* arm_AND X13 X3 X4 *)
  0xba0900a5;       (* arm_ADCS X5 X5 X9 *)
  0x8a0501ad;       (* arm_AND X13 X13 X5 *)
  0x9a9f37ec;       (* arm_CSET X12 Condition_CS *)
  0xab0b005f;       (* arm_CMN X2 X11 *)
  0xba1f01bf;       (* arm_ADCS XZR X13 XZR *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0x9a9f116b;       (* arm_CSEL X11 X11 XZR Condition_NE *)
  0xab0b0042;       (* arm_ADDS X2 X2 X11 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_p256k1_mc;;

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

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(15580212934572586289 * val(x:int64)):int64)) * &4294968273
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(15580212934572586289 * val(x:int64)):int64)) *
            &4294968273`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; VAL_WORD_MUL; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_MONTSQR_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x1a0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x19c) /\
                  (a EXP 2 <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a EXP 2) MOD p_256k1))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_256k1  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_256k1` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_P256K1_EXEC (1--103)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256K1_EXEC
   [3; 4; 11; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29;
    30; 31; 32; 33; 34; 35; 39; 40; 41; 42; 43; 44; 45; 46; 47;
    48; 49; 50; 51; 52; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65]
   (1--65) THEN
  ABBREV_TAC
   `l = bignum_of_wordlist[mullo_s33; sum_s42; sum_s45; sum_s46;
                           sum_s62; sum_s63; sum_s64; sum_s65]` THEN
  SUBGOAL_THEN `l = a EXP 2` (SUBST_ALL_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["l"; "a"] THEN
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

  (*** The main Montgomery reduction to 4 words plus 1 bit ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256K1_EXEC
   [73;74;76;77;79;80;82;83;84;85;86;87;88;89;91]
   (66--93) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist[sum_s87; sum_s88; sum_s89; sum_s91;
                           word(bitval(carry_s91))]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256k1 /\ (2 EXP 256 * t == l) (mod p_256k1)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["l"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256k1; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["l"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Condensed comparison ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256K1_EXEC [94;95;96] (94--97) THEN
  SUBGOAL_THEN
   `val(word_add (word(bitval carry_s91))
                 (word(bitval carry_s95)):int64) = 0 <=>
    t < p_256k1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s91:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 256 <=
      bignum_of_wordlist[sum_s87;sum_s88;sum_s89;sum_s91] + 4294968273` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; p_256k1] THEN ARITH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `2 EXP 128 <=
      bignum_of_wordlist[sum_s87; word_and (word_and sum_s88 sum_s89) sum_s91] +
      4294968273` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l < 2 EXP 64 /\ (a < 2 EXP 64 - 1 <=> h < 2 EXP 192 - 1) /\
      (~(h < 2 EXP 192 - 1)
       ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
            2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273))
      ==> (2 EXP 128 <= (l + 2 EXP 64 * a) + 4294968273 <=>
           2 EXP 256 <= (l + 2 EXP 64 * h) + 4294968273)`) THEN
    SIMP_TAC[VAL_BOUND_64; BIGNUM_OF_WORDLIST_LT_MAX; LENGTH;
             ARITH_MULT; ARITH_ADD; ARITH_SUC; EX; DE_MORGAN_THM;
             WORD_BITWISE_RULE
              `word_and a b = word_not(word 0) <=>
               a = word_not(word 0) /\ b = word_not(word 0)`] THEN
    REWRITE_TAC[DISJ_ACI] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P256K1_EXEC [98;99;100;101] (98--103) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256k1` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == l) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * l) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256k1 then &t:real else &t - &p_256k1`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL; VAL_WORD_0] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x1a0) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a EXP 2) MOD p_256k1))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_MONTSQR_P256K1_EXEC BIGNUM_MONTSQR_P256K1_CORRECT);;
