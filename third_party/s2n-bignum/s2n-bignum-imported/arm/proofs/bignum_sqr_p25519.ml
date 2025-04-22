(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squaring modulo p_25519, the field characteristic for curve25519.          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_sqr_p25519.o";;
 ****)

let bignum_sqr_p25519_mc = define_assert_from_elf "bignum_sqr_p25519_mc" "arm/curve25519/bignum_sqr_p25519.o"
[
  0xa9402c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&0))) *)
  0xa941342c;       (* arm_LDP X12 X13 X1 (Immediate_Offset (iword (&16))) *)
  0x9baa7d42;       (* arm_UMULL X2 W10 W10 *)
  0xd360fd4e;       (* arm_LSR X14 X10 32 *)
  0x9bae7dc3;       (* arm_UMULL X3 W14 W14 *)
  0x9bae7d4e;       (* arm_UMULL X14 W10 W14 *)
  0xab0e8442;       (* arm_ADDS X2 X2 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e0063;       (* arm_ADC X3 X3 X14 *)
  0x9bab7d64;       (* arm_UMULL X4 W11 W11 *)
  0xd360fd6e;       (* arm_LSR X14 X11 32 *)
  0x9bae7dc5;       (* arm_UMULL X5 W14 W14 *)
  0x9bae7d6e;       (* arm_UMULL X14 W11 W14 *)
  0x9b0b7d4f;       (* arm_MUL X15 X10 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0e8484;       (* arm_ADDS X4 X4 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e00a5;       (* arm_ADC X5 X5 X14 *)
  0xab0f01ef;       (* arm_ADDS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0xab0f0063;       (* arm_ADDS X3 X3 X15 *)
  0xba100084;       (* arm_ADCS X4 X4 X16 *)
  0x9a1f00a5;       (* arm_ADC X5 X5 XZR *)
  0x9bac7d86;       (* arm_UMULL X6 W12 W12 *)
  0xd360fd8e;       (* arm_LSR X14 X12 32 *)
  0x9bae7dc7;       (* arm_UMULL X7 W14 W14 *)
  0x9bae7d8e;       (* arm_UMULL X14 W12 W14 *)
  0xab0e84c6;       (* arm_ADDS X6 X6 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e00e7;       (* arm_ADC X7 X7 X14 *)
  0x9bad7da8;       (* arm_UMULL X8 W13 W13 *)
  0xd360fdae;       (* arm_LSR X14 X13 32 *)
  0x9bae7dc9;       (* arm_UMULL X9 W14 W14 *)
  0x9bae7dae;       (* arm_UMULL X14 W13 W14 *)
  0x9b0d7d8f;       (* arm_MUL X15 X12 X13 *)
  0x9bcd7d90;       (* arm_UMULH X16 X12 X13 *)
  0xab0e8508;       (* arm_ADDS X8 X8 (Shiftedreg X14 LSL 33) *)
  0xd35ffdce;       (* arm_LSR X14 X14 31 *)
  0x9a0e0129;       (* arm_ADC X9 X9 X14 *)
  0xab0f01ef;       (* arm_ADDS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0f00e7;       (* arm_ADDS X7 X7 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xeb0c014a;       (* arm_SUBS X10 X10 X12 *)
  0xfa0d016b;       (* arm_SBCS X11 X11 X13 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xca10014a;       (* arm_EOR X10 X10 X16 *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xca10016b;       (* arm_EOR X11 X11 X16 *)
  0xda10016b;       (* arm_SBC X11 X11 X16 *)
  0xab0400c6;       (* arm_ADDS X6 X6 X4 *)
  0xba0500e7;       (* arm_ADCS X7 X7 X5 *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0x9baa7d4c;       (* arm_UMULL X12 W10 W10 *)
  0xd360fd45;       (* arm_LSR X5 X10 32 *)
  0x9ba57cad;       (* arm_UMULL X13 W5 W5 *)
  0x9ba57d45;       (* arm_UMULL X5 W10 W5 *)
  0xab05858c;       (* arm_ADDS X12 X12 (Shiftedreg X5 LSL 33) *)
  0xd35ffca5;       (* arm_LSR X5 X5 31 *)
  0x9a0501ad;       (* arm_ADC X13 X13 X5 *)
  0x9bab7d6f;       (* arm_UMULL X15 W11 W11 *)
  0xd360fd65;       (* arm_LSR X5 X11 32 *)
  0x9ba57cae;       (* arm_UMULL X14 W5 W5 *)
  0x9ba57d65;       (* arm_UMULL X5 W11 W5 *)
  0x9b0b7d44;       (* arm_MUL X4 X10 X11 *)
  0x9bcb7d50;       (* arm_UMULH X16 X10 X11 *)
  0xab0585ef;       (* arm_ADDS X15 X15 (Shiftedreg X5 LSL 33) *)
  0xd35ffca5;       (* arm_LSR X5 X5 31 *)
  0x9a0501ce;       (* arm_ADC X14 X14 X5 *)
  0xab040084;       (* arm_ADDS X4 X4 X4 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0401ad;       (* arm_ADDS X13 X13 X4 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab060044;       (* arm_ADDS X4 X2 X6 *)
  0xba070065;       (* arm_ADCS X5 X3 X7 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0xba0900e7;       (* arm_ADCS X7 X7 X9 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xeb0c0084;       (* arm_SUBS X4 X4 X12 *)
  0xfa0d00a5;       (* arm_SBCS X5 X5 X13 *)
  0xfa0f00c6;       (* arm_SBCS X6 X6 X15 *)
  0xfa0e00e7;       (* arm_SBCS X7 X7 X14 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0x9a100129;       (* arm_ADC X9 X9 X16 *)
  0xd28004ca;       (* arm_MOV X10 (rvalue (word 38)) *)
  0x9baa7ccc;       (* arm_UMULL X12 W6 W10 *)
  0x8b22418c;       (* arm_ADD X12 X12 (Extendedreg W2 UXTW) *)
  0xd360fc42;       (* arm_LSR X2 X2 32 *)
  0xd360fcc6;       (* arm_LSR X6 X6 32 *)
  0x9baa08c6;       (* arm_UMADDL X6 W6 W10 X2 *)
  0xaa0c03e2;       (* arm_MOV X2 X12 *)
  0x9baa7cec;       (* arm_UMULL X12 W7 W10 *)
  0x8b23418c;       (* arm_ADD X12 X12 (Extendedreg W3 UXTW) *)
  0xd360fc63;       (* arm_LSR X3 X3 32 *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9baa0ce7;       (* arm_UMADDL X7 W7 W10 X3 *)
  0xaa0c03e3;       (* arm_MOV X3 X12 *)
  0x9baa7d0c;       (* arm_UMULL X12 W8 W10 *)
  0x8b24418c;       (* arm_ADD X12 X12 (Extendedreg W4 UXTW) *)
  0xd360fc84;       (* arm_LSR X4 X4 32 *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0x9baa1108;       (* arm_UMADDL X8 W8 W10 X4 *)
  0xaa0c03e4;       (* arm_MOV X4 X12 *)
  0x9baa7d2c;       (* arm_UMULL X12 W9 W10 *)
  0x8b25418c;       (* arm_ADD X12 X12 (Extendedreg W5 UXTW) *)
  0xd360fca5;       (* arm_LSR X5 X5 32 *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0x9baa1529;       (* arm_UMADDL X9 W9 W10 X5 *)
  0xaa0c03e5;       (* arm_MOV X5 X12 *)
  0xd35ffd2d;       (* arm_LSR X13 X9 31 *)
  0xd280026b;       (* arm_MOV X11 (rvalue (word 19)) *)
  0x9bad2d6b;       (* arm_UMADDL X11 W11 W13 X11 *)
  0x8b0b0042;       (* arm_ADD X2 X2 X11 *)
  0xab068042;       (* arm_ADDS X2 X2 (Shiftedreg X6 LSL 32) *)
  0x93c680ea;       (* arm_EXTR X10 X7 X6 32 *)
  0xba0a0063;       (* arm_ADCS X3 X3 X10 *)
  0x93c7810a;       (* arm_EXTR X10 X8 X7 32 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0x93c8812a;       (* arm_EXTR X10 X9 X8 32 *)
  0xd34101ab;       (* arm_LSL X11 X13 63 *)
  0xca0b00a5;       (* arm_EOR X5 X5 X11 *)
  0x9a0a00a5;       (* arm_ADC X5 X5 X10 *)
  0xd280026a;       (* arm_MOV X10 (rvalue (word 19)) *)
  0xf24100bf;       (* arm_TST X5 (rvalue (word 9223372036854775808)) *)
  0x9a9f514a;       (* arm_CSEL X10 X10 XZR Condition_PL *)
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
(* Lemmas to help with 32-bit breakdown of digits.                           *)
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

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let DIVMOD_63_64 = prove
 (`!n. (2 EXP 63 * n) MOD 2 EXP 64 = 2 EXP 63 * n MOD 2`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let p25519redlemma32 = prove
 (`!h l. h < 2 EXP 256 /\ l < 2 EXP 256
         ==> let q = (38 * h DIV 2 EXP 224 + l DIV 2 EXP 224) DIV 2 EXP 31 in
             q <= 77 /\
             q < 2 EXP 64 /\
             (q + 1) * p_25519 <= (38 * h + l) + p_25519 /\
             38 * h + l < (q + 1) * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let endp25519redlemma = prove
 (`(&z == &2 pow 255 + x) (mod (&2 pow 256)) /\
   --(&p_25519) <= x /\ x < &p_25519 /\ z < 2 EXP 256
   ==> x rem &p_25519 =
       if z < 2 EXP 255 then &z - &19  else &z - &2 pow 255`,
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&z:int < &2 pow 255 <=> x:int < &0` SUBST1_TAC THENL
   [ALL_TAC;
   COND_CASES_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
    [EXISTS_TAC `--(&1):int`; EXISTS_TAC `&0:int`]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_IMP_EQ)) THEN
  REWRITE_TAC[p_25519] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p_25519]) THEN ASM_INT_ARITH_TAC);;

let BIGNUM_SQR_P25519_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x22c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p25519_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x228) /\
                  bignum_from_memory (z,4) s = (n EXP 2) MOD p_25519)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** The initial squaring block, very similar to bignum_sqr_4_8 ***)
  (*** First of all, squaring the lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC
   [7;9;14;16;18;19;20;21;22;23;24] (1--24) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_0; n_1] EXP 2 =
    bignum_of_wordlist[sum_s7; sum_s22; sum_s23; sum_s24]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`n_0:int64`; `n_1:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Squaring the upper half ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC
   [29;31;36;38;40;41;42;43;44;45;46] (25--46) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[n_2; n_3] EXP 2 =
    bignum_of_wordlist[sum_s29; sum_s44; sum_s45; sum_s46]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`n_2:int64`; `n_3:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC [47;48;51;53] (47--53) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; WORD_UNMASK_64]) THEN
  SUBGOAL_THEN
   `abs(&(bignum_of_wordlist[n_0;n_1]) -
        &(bignum_of_wordlist[n_2;n_3])):real =
    &(bignum_of_wordlist[sum_s51;sum_s53])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_abs; REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN
     `bignum_of_wordlist [n_2; n_3] <= bignum_of_wordlist [n_0; n_1] <=>
      ~carry_s48`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
      EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      REWRITE_TAC[COND_SWAP] THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT] THEN
      REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64; VAL_WORD_BITVAL] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The augmented H' = H + L_top computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (54--57) (54--57) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[sum_s29; sum_s44; sum_s45; sum_s46]):real =
    &(bignum_of_wordlist[sum_s54; sum_s55; sum_s56; sum_s57]) -
    &(bignum_of_wordlist[sum_s23; sum_s24])`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
     (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
        MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Squaring the absolute difference ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC
   [62;64;69;71;73;74;75;76;77;78;79] (58--79) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; DIVMOD_33_31; VAL_WORD_USHR;
    VAL_WORD_SHL; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[sum_s51;sum_s53] EXP 2 =
    bignum_of_wordlist[sum_s62; sum_s77; sum_s78; sum_s79]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`sum_s51:int64`; `sum_s53:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The overall Karatsuba composition to get the full square ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (80--90) (80--90) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
    [COND_SWAP; WORD_UNMASK_64; REAL_BITVAL_NOT; DIMINDEX_64;
     GSYM WORD_NOT_MASK; REAL_VAL_WORD_NOT;REAL_VAL_WORD_MASK]) THEN

  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[sum_s7; sum_s22; sum_s85; sum_s86]`;
    `h = bignum_of_wordlist[sum_s87; sum_s88; sum_s89; sum_s90]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = n EXP 2` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL
       [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        BOUNDER_TAC[];
        ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(2,2)] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_ARITH
     `(l + &2 pow 128 * h) pow 2 =
      &2 pow 256 * h pow 2 + l pow 2 +
      &2 pow 128 * (h pow 2 + l pow 2 - (l - h) pow 2)`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
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

  MP_TAC(SPECL [`h:num`; `l:num`] p25519redlemma32) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    LET_TAC THEN STRIP_TAC] THEN

  (*** The somewhat fiddly reduction with 32-bit operations etc. ***)

  ARM_STEPS_TAC BIGNUM_SQR_P25519_EXEC (91--115) THEN

  MAP_EVERY (fun t -> REABBREV_TAC t THEN POP_ASSUM MP_TAC)
   [`u0 = read X2 s115`;
    `u1 = read X3 s115`;
    `u2 = read X4 s115`;
    `u3 = read X5 s115`;
    `u4 = read X6 s115`;
    `u5 = read X7 s115`;
    `u6 = read X8 s115`;
    `u7 = read X9 s115`] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [word_add; modular; ADD_CLAUSES; VAL_WORD; VAL_WORD_ZX_GEN;
    VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
   `n < 2 EXP 64 ==> n MOD 2 EXP 32 * 38 < 2 EXP 64`] THEN
  STRIP_TAC THEN
  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC [120;122;124;128] (116--128) THEN
  SUBGOAL_THEN `word_ushr u7 31:int64 = word q` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_USHR] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT] THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s86:int64) DIV 2 EXP 32 +
           val(sum_s90:int64) DIV 2 EXP 32 * 38):int64 = u7`)) THEN
    MAP_EVERY EXPAND_TAC ["q"; "l"; "h"] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD; ARITH_RULE `a + b * 38 = 38 * b + a`] THEN
    MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN
    REWRITE_TAC[GSYM VAL_WORD_USHR] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_add (u0:int64)
       (word(19 + 19 * val((word_zx:int64->int32)(word q)))))):real =
    &(val u0) + &19 * (&q + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; VAL_WORD; VAL_WORD_ZX_GEN;
                DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[ARITH_RULE `q <= 77 ==> q < 2 EXP MIN 64 32`; MOD_LT] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `19 + 19 * q = 19 * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s87:int64) MOD 2 EXP 32 * 38 +
           val(sum_s7:int64) MOD 2 EXP 32):int64 = u0`)) THEN
    MATCH_MP_TAC(ARITH_RULE
     `w <= 2 EXP 63 /\ q <= 77 ==> w + 19 * (q + 1) < 2 EXP 64`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_LE; FIRST_ASSUM ACCEPT_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  REWRITE_TAC[REAL_VAL_WORD_XOR; WORD_AND_POW2_BITVAL;
              REWRITE_RULE[DIMINDEX_64; NUM_REDUCE_CONV `64 - 1`]
                (ISPEC `x:int64` WORD_SHL_LSB)] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIVMOD_63_64] THEN
  SIMP_TAC[MOD_LT; BITVAL_BOUND_ALT; GSYM REAL_OF_NUM_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM VAL_MOD_2; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `r = bignum_of_wordlist[sum_s120; sum_s122; sum_s124; sum_s128]` THEN

  SUBGOAL_THEN
   `(&r:int == &2 pow 255 + &(38 * h + l) - (&q + &1) * &p_25519)
    (mod (&2 pow 256))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `38 * h + l =
      bignum_of_wordlist[u0;u1;u2;u3] +
      2 EXP 32 * bignum_of_wordlist[u4;u5;u6;u7]`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (can (term_match [] `word x = n`) o concl))) THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD; DIMINDEX_64] THEN
      SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
        `m < 2 EXP 64 /\ n < 2 EXP 64
         ==> m DIV 2 EXP 32 + n DIV 2 EXP 32 * 38 < 2 EXP 64`;
        ARITH_RULE `m MOD 2 EXP 32 * 38 + n MOD 2 EXP 32 < 2 EXP 64`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 32 * bignum_of_wordlist [u4; u5; u6; u7] =
      bignum_of_wordlist
       [word_shl u4 32;
        word_subword ((word_join:int64->int64->int128) u5 u4) (32,64);
        word_subword ((word_join:int64->int64->int128) u6 u5) (32,64);
        word_subword ((word_join:int64->int64->int128) u7 u6) (32,64);
        word_ushr u7 32]`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
                int_mul_th; int_pow_th] THEN
    EXPAND_TAC "r" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final optional correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_SQR_P25519_EXEC (132--135) (129--138) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`255`;
    `(if r < 2 EXP 255 then &r - &19 else &r - &2 pow 255):real`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s138" THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `r < 2 EXP 255 <=> r DIV 2 EXP 192 < 2 EXP 63`] THEN
    EXPAND_TAC "r" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
    ABBREV_TAC `bb <=> val(sum_s128:int64) < 2 EXP 63` THEN
    SUBGOAL_THEN
     `ival(word_and sum_s128 (word 9223372036854775808):int64) < &0 <=> ~bb`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM MSB_IVAL; BIT_WORD_AND] THEN
      REWRITE_TAC[MSB_VAL] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "bb" THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        endp25519redlemma)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_ARITH `--p:int <= x - y <=> y <= x + p`] THEN
      REWRITE_TAC[INT_ARITH `x - y:int < p <=> x < y + p`] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "r" THEN BOUNDER_TAC[];

      REWRITE_TAC[INT_ARITH `x - q * p:int = --q * p + x`] THEN
      REWRITE_TAC[INT_REM_MUL_ADD] THEN
      REWRITE_TAC[int_eq; int_of_num_th; INT_OF_NUM_REM] THEN
      DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[int_of_num_th; int_sub_th; int_pow_th]]]);;

let BIGNUM_SQR_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x22c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_sqr_p25519_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory(x,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (n EXP 2) MOD p_25519)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_SQR_P25519_EXEC BIGNUM_SQR_P25519_CORRECT);;
