(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_sm2.                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/sm2/bignum_montsqr_sm2.o";;
 ****)

let bignum_montsqr_sm2_mc =
  define_assert_from_elf "bignum_montsqr_sm2_mc" "arm/sm2/bignum_montsqr_sm2.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9ba27c4f;       (* arm_UMULL X15 W2 W2 *)
  0xd360fc4b;       (* arm_LSR X11 X2 32 *)
  0x9bab7d70;       (* arm_UMULL X16 W11 W11 *)
  0x9bab7c4b;       (* arm_UMULL X11 W2 W11 *)
  0xab0b85ef;       (* arm_ADDS X15 X15 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0210;       (* arm_ADC X16 X16 X11 *)
  0x9ba37c71;       (* arm_UMULL X17 W3 W3 *)
  0xd360fc6b;       (* arm_LSR X11 X3 32 *)
  0x9bab7d61;       (* arm_UMULL X1 W11 W11 *)
  0x9bab7c6b;       (* arm_UMULL X11 W3 W11 *)
  0x9b037c4c;       (* arm_MUL X12 X2 X3 *)
  0x9bc37c4d;       (* arm_UMULH X13 X2 X3 *)
  0xab0b8631;       (* arm_ADDS X17 X17 (Shiftedreg X11 LSL 33) *)
  0xd35ffd6b;       (* arm_LSR X11 X11 31 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab0c0210;       (* arm_ADDS X16 X16 X12 *)
  0xba0d0231;       (* arm_ADCS X17 X17 X13 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xd3607dec;       (* arm_LSL X12 X15 32 *)
  0xd360fdeb;       (* arm_LSR X11 X15 32 *)
  0xeb0f018e;       (* arm_SUBS X14 X12 X15 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0210;       (* arm_SUBS X16 X16 X14 *)
  0xfa0d0231;       (* arm_SBCS X17 X17 X13 *)
  0xfa0c0021;       (* arm_SBCS X1 X1 X12 *)
  0xda0b01ef;       (* arm_SBC X15 X15 X11 *)
  0xd3607e0c;       (* arm_LSL X12 X16 32 *)
  0xd360fe0b;       (* arm_LSR X11 X16 32 *)
  0xeb10018e;       (* arm_SUBS X14 X12 X16 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0231;       (* arm_SUBS X17 X17 X14 *)
  0xfa0d0021;       (* arm_SBCS X1 X1 X13 *)
  0xfa0c01ef;       (* arm_SBCS X15 X15 X12 *)
  0xda0b0210;       (* arm_SBC X16 X16 X11 *)
  0x9b047c46;       (* arm_MUL X6 X2 X4 *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xeb03004a;       (* arm_SUBS X10 X2 X3 *)
  0xda8a254a;       (* arm_CNEG X10 X10 Condition_CC *)
  0xda9f23ed;       (* arm_CSETM X13 Condition_CC *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x9b0c7d4b;       (* arm_MUL X11 X10 X12 *)
  0x9bcc7d4c;       (* arm_UMULH X12 X10 X12 *)
  0xda8d21ad;       (* arm_CINV X13 X13 Condition_CC *)
  0xca0d016b;       (* arm_EOR X11 X11 X13 *)
  0xca0d018c;       (* arm_EOR X12 X12 X13 *)
  0xab0800c7;       (* arm_ADDS X7 X6 X8 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0x9bc57c69;       (* arm_UMULH X9 X3 X5 *)
  0xab0e00e7;       (* arm_ADDS X7 X7 X14 *)
  0xba090108;       (* arm_ADCS X8 X8 X9 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0e0108;       (* arm_ADDS X8 X8 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xb10005bf;       (* arm_CMN X13 (rvalue (word 1)) *)
  0xba0b00e7;       (* arm_ADCS X7 X7 X11 *)
  0xba0c0108;       (* arm_ADCS X8 X8 X12 *)
  0x9a0d0129;       (* arm_ADC X9 X9 X13 *)
  0xab0600c6;       (* arm_ADDS X6 X6 X6 *)
  0xba0700e7;       (* arm_ADCS X7 X7 X7 *)
  0xba080108;       (* arm_ADCS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xab1100c6;       (* arm_ADDS X6 X6 X17 *)
  0xba0100e7;       (* arm_ADCS X7 X7 X1 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xd3607ccc;       (* arm_LSL X12 X6 32 *)
  0xd360fccb;       (* arm_LSR X11 X6 32 *)
  0xeb06018e;       (* arm_SUBS X14 X12 X6 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e00e7;       (* arm_SUBS X7 X7 X14 *)
  0xfa0d0108;       (* arm_SBCS X8 X8 X13 *)
  0xfa0c0129;       (* arm_SBCS X9 X9 X12 *)
  0xda0b00ce;       (* arm_SBC X14 X6 X11 *)
  0xab0e014a;       (* arm_ADDS X10 X10 X14 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xd3607cec;       (* arm_LSL X12 X7 32 *)
  0xd360fceb;       (* arm_LSR X11 X7 32 *)
  0xeb07018e;       (* arm_SUBS X14 X12 X7 *)
  0xda1f016d;       (* arm_SBC X13 X11 XZR *)
  0xeb0e0108;       (* arm_SUBS X8 X8 X14 *)
  0xfa0d0129;       (* arm_SBCS X9 X9 X13 *)
  0xfa0c014a;       (* arm_SBCS X10 X10 X12 *)
  0xda0b00ee;       (* arm_SBC X14 X7 X11 *)
  0xab0e00c6;       (* arm_ADDS X6 X6 X14 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0x9b047c8b;       (* arm_MUL X11 X4 X4 *)
  0xab0b0108;       (* arm_ADDS X8 X8 X11 *)
  0x9b057cac;       (* arm_MUL X12 X5 X5 *)
  0x9bc47c8b;       (* arm_UMULH X11 X4 X4 *)
  0xba0b0129;       (* arm_ADCS X9 X9 X11 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0x9bc57cac;       (* arm_UMULH X12 X5 X5 *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0x9bc57c8c;       (* arm_UMULH X12 X4 X5 *)
  0xab0b016b;       (* arm_ADDS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0x9a1f03ed;       (* arm_ADC X13 XZR XZR *)
  0xab0b0129;       (* arm_ADDS X9 X9 X11 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xb2607feb;       (* arm_MOV X11 (rvalue (word 18446744069414584320)) *)
  0xb1000505;       (* arm_ADDS X5 X8 (rvalue (word 1)) *)
  0xfa0b012b;       (* arm_SBCS X11 X9 X11 *)
  0x92c0002d;       (* arm_MOVN X13 (word 1) 32 *)
  0xba1f014c;       (* arm_ADCS X12 X10 XZR *)
  0xfa0d00cd;       (* arm_SBCS X13 X6 X13 *)
  0xfa1f00ff;       (* arm_SBCS XZR X7 XZR *)
  0x9a8820a8;       (* arm_CSEL X8 X5 X8 Condition_CS *)
  0x9a892169;       (* arm_CSEL X9 X11 X9 Condition_CS *)
  0x9a8a218a;       (* arm_CSEL X10 X12 X10 Condition_CS *)
  0x9a8621a6;       (* arm_CSEL X6 X13 X6 Condition_CS *)
  0xa9002408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa901180a;       (* arm_STP X10 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_SM2_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_MADDL_0 = prove
 (`!x y. val(word(0 + val(x:int32) * val(y:int32)):int64) = val x * val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; VAL_WORD_EQ_EQ] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[GSYM DIMINDEX_32; VAL_BOUND]);;

let DIVMOD_33_31 = prove
 (`!n. (2 EXP 33 * n) MOD 2 EXP 64 = 2 EXP 33 * n MOD 2 EXP 31`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let VAL_WORD_SPLIT32 = prove
 (`!x. 2 EXP 32 * val(word_zx(word_ushr x 32):int32) + val(word_zx x:int32) =
       val(x:int64)`,
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM MOD_MULT_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND_64]);;

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

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

let BIGNUM_MONTSQR_SM2_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x1fc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x1f8) /\
                  (a EXP 2 <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a EXP 2) MOD p_sm2))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_SM2_EXEC (1--126)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Squaring and Montgomery reduction of lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC
   [7;9;14;16;18;19;20;21;22;23;24;
    25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40]
   (1--40) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s37; sum_s38; sum_s39; sum_s40] =
    bignum_of_wordlist[x_0;x_1] EXP 2 +
    p_sm2 * bignum_of_wordlist[sum_s7; sum_s29]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `x_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC
   [41;42;49;54;55;57;58;59;60;61;63;64;65] (41--65) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s41; sum_s63; sum_s64; sum_s65] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Remaining Montgomery reduction and addition of remaining high terms ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC (66--113) (66--113) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
        [sum_s97; sum_s110; sum_s111; sum_s112; sum_s113]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 256 * t =
      a EXP 2 +
      p_sm2 * bignum_of_wordlist [sum_s7; sum_s29; sum_s71; sum_s80]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
       `(bignum_of_wordlist[x_0;x_1] EXP 2 +
         p_sm2 * bignum_of_wordlist[sum_s7; sum_s29]) +
        2 * 2 EXP 128 *
            bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3] +
        2 EXP 256 * bignum_of_wordlist[x_2;x_3] EXP 2 +
        2 EXP 128 * p_sm2 * bignum_of_wordlist [sum_s71; sum_s80]` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o
                           RAND_CONV o RAND_CONV) [SYM th]);
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC
   [115;116;118;119;120] (114--126) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_sm2 then &t:real else &t - &p_sm2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s120 <=> t < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x1fc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a EXP 2) MOD p_sm2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_SM2_EXEC
    BIGNUM_MONTSQR_SM2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 256 bits, may then not be fully reduced mod p_sm2.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTSQR_SM2_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x1fc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x1f8) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a EXP 2) (mod p_sm2))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Squaring and Montgomery reduction of lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC
   [7;9;14;16;18;19;20;21;22;23;24;
    25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40]
   (1--40) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `2 EXP 128 * bignum_of_wordlist [sum_s37; sum_s38; sum_s39; sum_s40] =
    bignum_of_wordlist[x_0;x_1] EXP 2 +
    p_sm2 * bignum_of_wordlist[sum_s7; sum_s29]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `x_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC
   [41;42;49;54;55;57;58;59;60;61;63;64;65] (41--65) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[mullo_s41; sum_s63; sum_s64; sum_s65] =
    bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Remaining Montgomery reduction and addition of remaining high terms ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC (66--113) (66--113) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
        [sum_s97; sum_s110; sum_s111; sum_s112; sum_s113]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_sm2 /\ (2 EXP 256 * t == a EXP 2) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 256 * t =
      a EXP 2 +
      p_sm2 * bignum_of_wordlist [sum_s7; sum_s29; sum_s71; sum_s80]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
       `(bignum_of_wordlist[x_0;x_1] EXP 2 +
         p_sm2 * bignum_of_wordlist[sum_s7; sum_s29]) +
        2 * 2 EXP 128 *
            bignum_of_wordlist[x_0;x_1] * bignum_of_wordlist[x_2;x_3] +
        2 EXP 256 * bignum_of_wordlist[x_2;x_3] EXP 2 +
        2 EXP 128 * p_sm2 * bignum_of_wordlist [sum_s71; sum_s80]` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o
                           RAND_CONV o RAND_CONV) [SYM th]);
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      MATCH_MP_TAC(ARITH_RULE `2 EXP 256 * x < 2 EXP 256 * y ==> x < y`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

  (*** Final correction ***)

 ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_SM2_EXEC
   [115;116;118;119;120] (114--126) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `carry_s120 <=> t < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * a EXP 2) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval(p_sm2 <= t)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 256 + p_sm2` THEN
    REWRITE_TAC[bitval; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LT; REAL_BITVAL_NOT] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_sm2] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTSQR_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x1fc) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a EXP 2) (mod p_sm2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_SM2_EXEC
    BIGNUM_AMONTSQR_SM2_CORRECT);;
